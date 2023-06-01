use papergrid::{
    config::{compact::CompactConfig, AlignmentHorizontal, Borders, Indent, Sides},
    dimension::Dimension,
    grid::compact::CompactGrid,
    records::IterRecords,
};

use crate::row::RowSet;

const STYLE: Borders<char> = Borders {
    top: Some('-'),
    top_left: Some('+'),
    top_right: Some('+'),
    top_intersection: Some('+'),
    bottom: Some('-'),
    bottom_left: Some('+'),
    bottom_right: Some('+'),
    bottom_intersection: Some('+'),
    horizontal: Some('-'),
    left_intersection: Some('+'),
    right_intersection: Some('+'),
    vertical: Some('|'),
    left: Some('|'),
    right: Some('|'),
    intersection: Some('+'),
};

struct ConstDims<'a>(&'a [usize], usize);

impl Dimension for ConstDims<'_> {
    fn get_width(&self, column: usize) -> usize {
        self.0[column]
    }

    fn get_height(&self, _: usize) -> usize {
        self.1
    }
}

/// Print the rows as a pretty table.
pub fn print_rows(rows: &RowSet) -> String {
    let config = CompactConfig::default()
        .set_borders(STYLE)
        .set_alignment_horizontal(AlignmentHorizontal::Center)
        .set_padding(Sides::new(
            Indent::spaced(1),
            Indent::spaced(1),
            Indent::spaced(0),
            Indent::spaced(0),
        ));

    let dim = ConstDims(&[40, 40, 80, 6], 4);
    let column_num = rows.schema.columns().len();
    let row_num = rows.rows.len();

    let mut content = vec![rows
        .schema
        .columns()
        .iter()
        .map(|field| field.name.clone())
        .collect::<Vec<_>>()];
    let mut rows = rows
        .rows
        .iter()
        .map(|row| row.stringify())
        .collect::<Vec<_>>();
    content.append(&mut rows);
    let records = IterRecords::new(content, column_num, None);

    format!(
        "{}\n{} rows in set",
        CompactGrid::new(records, &dim, &config),
        row_num,
    )
}
