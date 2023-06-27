#[macro_export]
macro_rules! push_type {
    ($vec:expr, $data:ident, $ty:tt, $data_type:ident) => {
        $vec.push($data_type::new(
            $data
                .parse::<$ty>()
                .map_err(|e| PolicyCarryingError::TypeMismatch(e.to_string()))?,
        ))
    };
}

#[macro_export]
macro_rules! define_schema {
    ($id:expr, $($name:expr => $ty:path), + $(,)?) => {{
        use policy_core::types::*;

        $crate::schema::SchemaBuilder::new()
            $(.add_field_raw($name, $ty, false))*
            .finish_with_executor($id)
    }};
}

#[macro_export]
macro_rules! pcd {
  ($($col_name:expr => $ty:path: $content:expr), + $(,)?) => {{
        use policy_core::types::*;

        let mut fields = Vec::new();
        let mut field_array = Vec::new();

        $(
            let field = std::sync::Arc::new($crate::field::Field::new($col_name.to_string(), $ty, false, Default::default()));
            let field_data:  std::sync::Arc<dyn $crate::field::FieldData> = match $ty {
                DataType::Int8 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| Int8Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::Int16 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| Int16Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::Int32 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| Int32Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::Int64 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| Int64Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::UInt8 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| UInt8Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::UInt16 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| UInt16Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::UInt32 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| UInt32Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::UInt64 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| UInt64Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::Float32 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| Float32Type::new(*e as _)).collect(),
                        )
                    ),
                DataType::Float64 => std::sync::Arc::new(
                    $crate::field::FieldDataArray::new(
                        field.clone(),
                        $content.iter().map(|e| Float64Type::new(*e as _)).collect(),
                        )
                    ),
                _ => unimplemented!(),
            };
            field_array.push(field_data);
            fields.push(field);
      )*

      $crate::DataFrame::new_with_cols(field_array)
  }};
}
