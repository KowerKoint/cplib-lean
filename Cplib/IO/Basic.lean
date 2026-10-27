/-!
# IO.Basic

Standard input and output helpers for competitive programming.

Input is read **a line at a time**: `readString` and everything built on it
consume exactly one line, and the `read*List` family then splits that line on
spaces. So a problem whose input puts one value per line calls `readNat`
repeatedly, while one that puts several on a line calls `readNats2` or
`readNatArray`.

The `expect*` helpers raise `IO.userError` when a line does not hold exactly
the requested number of values, so a malformed input fails loudly rather than
silently.

Reading is line-buffered rather than slurped up front, which keeps these usable
for interactive problems.

```lean
def main : IO Unit := do
  let (n, m) ← readNats2
  let g ← readGraph n m          -- m edges, 1-indexed by default
  let xs ← readNatArray          -- one line of n numbers
  printArray xs
```
-/

namespace Cplib

/-- Read one line, with trailing whitespace removed. -/
def readString : IO String := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  return line.trimRight

def readNat : IO Nat := readString |>.map String.toNat!
def readInt : IO Int := readString |>.map String.toInt!

/-- Read one line and split it on spaces. -/
def readStringList : IO (List String) := readString |>.map (fun s => s.splitOn)
def readNatList : IO (List Nat) := readStringList |>.map (List.map String.toNat!)
def readIntList : IO (List Int) := readStringList |>.map (List.map String.toInt!)

def readStringArray : IO (Array String) := readStringList |>.map List.toArray
def readNatArray : IO (Array Nat) := readNatList |>.map List.toArray
def readIntArray : IO (Array Int) := readIntList |>.map List.toArray

private def expect2 (name : String) (xs : List α) : IO (α × α) :=
  match xs with
  | [a, b] => return (a, b)
  | _ => throw <| IO.userError s!"{name}: expected 2 values, got {xs.length}"

private def expect3 (name : String) (xs : List α) : IO (α × α × α) :=
  match xs with
  | [a, b, c] => return (a, b, c)
  | _ => throw <| IO.userError s!"{name}: expected 3 values, got {xs.length}"

private def expect4 (name : String) (xs : List α) : IO (α × α × α × α) :=
  match xs with
  | [a, b, c, d] => return (a, b, c, d)
  | _ => throw <| IO.userError s!"{name}: expected 4 values, got {xs.length}"

/-- Read exactly 2 space-separated strings from one line. -/
def readStrings2 : IO (String × String) := readStringList >>= expect2 "readStrings2"

/-- Read exactly 3 space-separated strings from one line. -/
def readStrings3 : IO (String × String × String) := readStringList >>= expect3 "readStrings3"

/-- Read exactly 4 space-separated strings from one line. -/
def readStrings4 : IO (String × String × String × String) :=
  readStringList >>= expect4 "readStrings4"

/-- Read exactly 2 space-separated natural numbers from one line. -/
def readNats2 : IO (Nat × Nat) := readNatList >>= expect2 "readNats2"

/-- Read exactly 3 space-separated natural numbers from one line. -/
def readNats3 : IO (Nat × Nat × Nat) := readNatList >>= expect3 "readNats3"

/-- Read exactly 4 space-separated natural numbers from one line. -/
def readNats4 : IO (Nat × Nat × Nat × Nat) := readNatList >>= expect4 "readNats4"

/-- Read exactly 2 space-separated integers from one line. -/
def readInts2 : IO (Int × Int) := readIntList >>= expect2 "readInts2"

/-- Read exactly 3 space-separated integers from one line. -/
def readInts3 : IO (Int × Int × Int) := readIntList >>= expect3 "readInts3"

/-- Read exactly 4 space-separated integers from one line. -/
def readInts4 : IO (Int × Int × Int × Int) := readIntList >>= expect4 "readInts4"

def readStringRowList (n : Nat) : IO (List String) :=
  List.range n |>.mapM (fun _ => readString)

def readNatRowList (n : Nat) : IO (List Nat) :=
  List.range n |>.mapM (fun _ => readNat)

def readIntRowList (n : Nat) : IO (List Int) :=
  List.range n |>.mapM (fun _ => readInt)

def readStringRowArray (n : Nat) : IO (Array String) :=
  Array.range n |>.mapM (fun _ => readString)

def readNatRowArray (n : Nat) : IO (Array Nat) :=
  Array.range n |>.mapM (fun _ => readNat)

def readIntRowArray (n : Nat) : IO (Array Int) :=
  Array.range n |>.mapM (fun _ => readInt)

def readStringListList (n : Nat) : IO (List (List String)) :=
  List.range n |>.mapM (fun _ => readStringList)

def readNatListList (n : Nat) : IO (List (List Nat)) :=
  List.range n |>.mapM (fun _ => readNatList)

def readIntListList (n : Nat) : IO (List (List Int)) :=
  List.range n |>.mapM (fun _ => readIntList)

def readStringMatrix (n : Nat) : IO (Array (Array String)) :=
  Array.range n |>.mapM (fun _ => readStringArray)

def readNatMatrix (n : Nat) : IO (Array (Array Nat)) :=
  Array.range n |>.mapM (fun _ => readNatArray)

def readIntMatrix (n : Nat) : IO (Array (Array Int)) :=
  Array.range n |>.mapM (fun _ => readIntArray)

/-- Read `m` undirected edges over `n` vertices, one per line, and return the
adjacency list. `offset` is subtracted from every endpoint, so the default of
`1` converts the usual 1-indexed input to 0-indexed vertices. -/
def readGraph (n m : Nat) (offset : Nat := 1) : IO (Array (List Nat)) :=
  Nat.foldM m (fun _ _ g => do
    let (a, b) ← readNats2
    let (a, b) := (a - offset, b - offset)
    return g.modify a (b :: ·) |>.modify b (a :: ·)
  ) (Array.replicate n [])

def printStringList (as : List String) (delim : String := " ") : IO Unit :=
  delim.intercalate as |> IO.println
def printList [ToString α] (as : List α) (delim : String := " ") : IO Unit :=
  as.map toString |> (printStringList · delim)
def printArray [ToString α] (as : Array α) (delim : String := " ") : IO Unit :=
  printList as.toList delim
def printMatrix [ToString α] (as : Array (Array α)) (delimRow : String := "\n") (delimColumn : String := " ") : IO Unit :=
  as.toList.map (fun row =>
    row.toList.map toString |> delimColumn.intercalate
  ) |> (printStringList · delimRow)

end Cplib
