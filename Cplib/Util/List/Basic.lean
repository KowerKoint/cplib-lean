namespace List

/-- Run-length encoding: each run of equal elements becomes the element paired
with how many times it ran.

```lean
[2, 2, 2, 3, 3, 5].runLength = [(2, 3), (3, 2), (5, 1)]
```
-/
def runLength [BEq α] : List α → List (α × Nat)
  | [] => []
  | x :: rest =>
      match runLength rest with
      | (y, count) :: tail => if x == y then (y, count + 1) :: tail else (x, 1) :: (y, count) :: tail
      | [] => [(x, 1)]

end List
