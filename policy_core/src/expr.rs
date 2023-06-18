use std::fmt::{Debug, Display, Formatter};

use crate::{data_type::PrimitiveDataType, error::PolicyCarryingResult};

/// Represents the index of the element it points to in the arena.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Node(pub usize);

impl Default for Node {
    fn default() -> Self {
        Node(usize::MAX)
    }
}

/// The aggregation type.
#[derive(Clone, Debug)]
pub enum Aggregation {
    Min(Box<Expr>),
    Max(Box<Expr>),
    Sum(Box<Expr>),
    Mean(Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum AAggExpr {
    Min { input: Node, propagate_nans: bool },
    Max { input: Node, propagate_nans: bool },
    Sum(Node),
    Mean(Node),
}

impl Aggregation {
    pub fn as_expr(&self) -> &Expr {
        match self {
            Self::Min(min) => min,
            Self::Max(max) => max,
            Self::Sum(sum) => sum,
            Self::Mean(mean) => mean,
        }
    }
}

/// An expression type.
#[derive(Clone)]
pub enum Expr {
    /// Aggregation.
    Agg(Aggregation),
    /// Select a vector of column names.
    Column(String),
    /// Making alias.
    Alias {
        expr: Box<Expr>,
        name: String,
    },
    /// "*".
    Wildcard,
    /// Exclude some columns.
    Exclude(Box<Expr>, Vec<String>),
    /// Filter.
    Filter {
        input: Box<Expr>,
        filter: Box<Expr>,
    },
    /// Binary operations
    BinaryOp {
        left: Box<Expr>,
        op: BinaryOp,
        right: Box<Expr>,
    },
    Literal(Box<dyn PrimitiveDataType>),
}

/// AExpr is an arena-ed version of [`Expr`].
#[derive(Clone, Debug, Default)]
pub enum AExpr {
    Alias(Node, String),
    Column(String),
    Literal(Box<dyn PrimitiveDataType>),
    BinaryOp {
        left: Node,
        op: BinaryOp,
        right: Node,
    },
    Filter {
        input: Node,
        by: Node,
    },
    Agg(AAggExpr),
    #[default]
    Wildcard,
}

impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Agg(agg) => write!(f, "{agg:?}"),
            Self::Column(column) => write!(f, "{column}"),
            Self::Wildcard => write!(f, "*"),
            Self::Alias { expr, name } => write!(f, "ALIAS {expr:?} -> {name}"),
            Self::Exclude(expr, columns) => write!(f, "{expr:?} EXCEPT {columns:?}"),
            Self::Filter {
                input: data,
                filter,
            } => write!(f, "{data:?} WHERE {filter:?}"),
            Self::BinaryOp { left, op, right } => write!(f, "({left:?} {op:?} {right:?})"),
            Self::Literal(val) => write!(f, "{val:?}"),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinaryOp {
    Lt,
    Gt,
    Le,
    Ge,
    And,
    Or,
    Eq,
    Ne,
    Add,
    Sub,
    Mul,
    Div,
}

impl Debug for BinaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lt => write!(f, "<"),
            Self::Gt => write!(f, ">"),
            Self::Le => write!(f, "<="),
            Self::Ge => write!(f, ">="),
            Self::And => write!(f, "&&"),
            Self::Or => write!(f, "||"),
            Self::Eq => write!(f, "=="),
            Self::Ne => write!(f, "<>"),
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
        }
    }
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

pub struct ExprIterator<'a> {
    stack: Vec<&'a Expr>,
}

impl<'a> Iterator for ExprIterator<'a> {
    type Item = &'a Expr;

    /// Visit the expression tree.
    fn next(&mut self) -> Option<Self::Item> {
        let current_expr = self.stack.pop();

        match current_expr {
            Some(current_expr) => {
                match current_expr {
                    Expr::Wildcard | Expr::Column(_) | Expr::Literal(_) | Expr::Alias { .. } => {
                        None
                    }
                    Expr::Agg(agg) => Some(agg.as_expr()),
                    Expr::BinaryOp { left, right, .. } => {
                        // Push left and right but return the current one.
                        self.stack.push(right);
                        self.stack.push(left);
                        Some(current_expr)
                    }
                    Expr::Exclude(expr, _) => {
                        self.stack.push(expr);
                        Some(current_expr)
                    }
                    Expr::Filter {
                        input: data,
                        filter,
                    } => {
                        self.stack.push(filter);
                        self.stack.push(data);
                        Some(current_expr)
                    }
                }
            }
            None => None,
        }
    }
}

impl<'a> IntoIterator for &'a Expr {
    type Item = &'a Expr;
    type IntoIter = ExprIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        let mut stack = Vec::with_capacity(8);
        stack.push(self);
        Self::IntoIter { stack }
    }
}

impl Expr {
    /// Applies a function `f` on the expressiom; ignore error.
    pub fn apply<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Self) -> bool,
    {
        let _ = self.try_apply(|expr| Ok(f(expr)));
    }

    /// Tries to pply a function `f` on the expression.
    pub fn try_apply<F>(&mut self, mut f: F) -> PolicyCarryingResult<()>
    where
        F: FnMut(&mut Self) -> PolicyCarryingResult<bool>,
    {
        let mut stack = Vec::with_capacity(8);
        stack.push(self);

        while let Some(node) = stack.pop() {
            if !f(node)? {
                break;
            }

            match node {
                Expr::Wildcard
                | Expr::Column(_)
                | Expr::Literal(_)
                | Expr::Agg(_)
                | Expr::Alias { .. } => (),
                Expr::BinaryOp { left, right, .. } => {
                    // Push left and right but return the current one.
                    stack.push(right);
                    stack.push(left);
                }
                Expr::Exclude(expr, _) => {
                    stack.push(expr);
                }
                Expr::Filter {
                    input: data,
                    filter,
                } => {
                    stack.push(filter);
                    stack.push(data);
                }
            }
        }

        Ok(())
    }

    pub fn exclude(self, columns: Vec<String>) -> Self {
        Self::Exclude(Box::new(self), columns)
    }

    pub fn lt<T: PrimitiveDataType>(self, num: T) -> Self {
        Self::BinaryOp {
            left: Box::new(self),
            op: BinaryOp::Lt,
            right: Box::new(Self::Literal(Box::new(num))),
        }
    }

    pub fn le<T: PrimitiveDataType>(self, num: T) -> Self {
        Self::BinaryOp {
            left: Box::new(self),
            op: BinaryOp::Le,
            right: Box::new(Self::Literal(Box::new(num))),
        }
    }

    pub fn gt<T: PrimitiveDataType>(self, num: T) -> Self {
        Self::BinaryOp {
            left: Box::new(self),
            op: BinaryOp::Gt,
            right: Box::new(Self::Literal(Box::new(num))),
        }
    }

    pub fn ge<T: PrimitiveDataType>(self, num: T) -> Self {
        Self::BinaryOp {
            left: Box::new(self),
            op: BinaryOp::Ge,
            right: Box::new(Self::Literal(Box::new(num))),
        }
    }

    pub fn and(self, other: Self) -> Self {
        Self::BinaryOp {
            left: Box::new(self),
            op: BinaryOp::And,
            right: Box::new(other),
        }
    }
    pub fn or(self, other: Self) -> Self {
        Self::BinaryOp {
            left: Box::new(self),
            op: BinaryOp::Or,
            right: Box::new(other),
        }
    }

    pub fn sum(self) -> Self {
        Self::Agg(Aggregation::Sum(Box::new(self)))
    }

    pub fn max(self) -> Self {
        Self::Agg(Aggregation::Max(Box::new(self)))
    }

    pub fn min(self) -> Self {
        Self::Agg(Aggregation::Min(Box::new(self)))
    }

    pub fn mean(self) -> Self {
        Self::Agg(Aggregation::Mean(Box::new(self)))
    }
}

/// Constructs an vector of [`Expression::Column`] variant.
#[macro_export]
macro_rules! cols {
    ($($col:tt),*) => {{
        let mut vec = vec![];

        $(
            match $col {
                "*" => vec.push($crate::expr::Expr::Wildcard),
                _ => vec.push($crate::expr::Expr::Column(String::from($col))),
            }
        )*

        vec
    }};
}

#[macro_export]
macro_rules! col {
    ($col:tt) => {
        match $col {
            "*" => $crate::expr::Expr::Wildcard,
            _ => $crate::expr::Expr::Column(String::from($col)),
        }
    };
}

impl AExpr {
    pub(crate) fn is_leaf(&self) -> bool {
        matches!(self, AExpr::Column(_) | AExpr::Literal(_))
    }
}

#[cfg(test)]
mod test {
    use crate::data_type::Int8Type;

    #[test]
    fn test_visit() {
        let expr = (col!("some_column")
            .gt(Int8Type::new(100))
            .and(col!("some_column2").lt(Int8Type::new(123))))
        .or(col!("some_column3").lt(Int8Type::new(111)));

        println!("{:#?}", expr);
    }
}
