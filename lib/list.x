// List.x - 列表归纳类型定义

inductive List where
  | nil : List
  | cons : A → List → List
