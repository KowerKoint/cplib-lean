namespace List

def runLengthEncode [BEq α] : List α → List (α × Nat)
| [] => []
| x :: xs =>
  let res := runLengthEncode xs
  match res with
  | [] => [(x, 1)]
  | (a, c) :: tail =>
    if x == a then (a, c+1) :: tail
    else (x, 1) :: (a, c) :: tail

/-- 比較順でソートしつつ重複を除いた配列を返す。 -/
def uniqueSorted [Ord α] [BEq α] (xs : List α) : List α :=
  let xs := xs.mergeSort (le := (compare · · |> Ordering.isLE))
  xs.runLengthEncode.map (·.1)

def prefixSum' [Add α] (origin : α) : List α → List α
| [] => [origin]
| x :: xs => origin :: prefixSum' (origin+x) xs

/-- `ret[i]` が `xs` の先頭 `i` 要素の和となる、長さ `n + 1` の累積和ベクトルを返す。 -/
def prefixSum [Zero α] [Add α] := prefixSum' (0 : α)

end List

namespace Array

def runLengthEncode [BEq α] (xs : Array α) : Array (α × Nat) := xs.toList.runLengthEncode.toArray
def uniqueSorted [Ord α] [BEq α] (xs : Array α) : Array α := xs.toList.uniqueSorted.toArray
def prefixSum  [Zero α] [Add α] (xs : Array α) : Array α := xs.toList.prefixSum.toArray

end Array
