
namespace Cplib
namespace SuffixArray

namespace Impl

def assignRanks {n : Nat} (order : Array (Fin n)) (sameKey : Fin n → Fin n → Bool) :
    Vector Nat n :=
  let initial : Vector Nat n × Option (Fin n) × Nat := (Vector.replicate n 0, none, 0)
  (order.foldl (fun (ranks, previous, rank) i =>
    let rank := match previous with
      | none => 0
      | some j => if sameKey j i then rank else rank + 1
    (ranks.set i rank, some i, rank)) initial).1

def secondRank {n : Nat} (ranks : Vector Nat n) (width : Nat) (i : Fin n) : Option Nat :=
  if h : i.val + width < n then some ranks[i.val + width] else none

def compareKey {n : Nat} (ranks : Vector Nat n) (width : Nat) (i j : Fin n) : Ordering :=
  match compare ranks[i] ranks[j] with
  | Ordering.lt => Ordering.lt
  | Ordering.gt => Ordering.gt
  | Ordering.eq =>
      match secondRank ranks width i, secondRank ranks width j with
      | none, none => Ordering.eq
      | none, some _ => Ordering.lt
      | some _, none => Ordering.gt
      | some x, some y => compare x y

/-- Stable counting sort by `key`.

Counts occurrences, turns them into bucket start positions by a prefix sum, then
places each element at its bucket cursor. No per-bucket container is allocated;
one output array of the same length is written instead.

Keys at or above `bucketCount` land in a final overflow slot. The callers never
produce such keys, but keeping the slot makes the result a permutation of the
input for any `key`. -/
def bucketSort {n : Nat} (bucketCount : Nat) (key : Fin n → Nat)
    (order : Array (Fin n)) : Array (Fin n) :=
  if hne : 0 < order.size then
    let slot (i : Fin n) : Fin (bucketCount + 1) :=
      ⟨min (key i) bucketCount, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    let counts : Vector Nat (bucketCount + 1) :=
      order.foldl (fun counts i => counts.set (slot i) (counts[slot i] + 1))
        (Vector.replicate (bucketCount + 1) 0)
    let starts : Vector Nat (bucketCount + 1) :=
      (Nat.fold (bucketCount + 1) (fun k hk (starts, acc) =>
        ((starts.set k acc : Vector Nat (bucketCount + 1)), acc + counts[k]))
        (Vector.replicate (bucketCount + 1) 0, 0)).1
    (order.foldl (fun (result, cursor) i =>
      (result.set! cursor[slot i] i, cursor.set (slot i) (cursor[slot i] + 1)))
      (Array.replicate order.size order[0], starts)).1
  else order

/-- The absent second half is key `0`; real ranks are shifted by one. -/
def secondKey {n : Nat} (ranks : Vector Nat n) (width : Nat) (i : Fin n) : Nat :=
  if h : i.val + width < n then
    ranks[i.val + width] + 1
  else 0

/-- Stable radix sort by `(rank[i], rank[i + width])`. -/
def radixSort {n : Nat} (ranks : Vector Nat n) (width : Nat)
    (order : Array (Fin n)) : Array (Fin n) :=
  let order := bucketSort (n + 1) (secondKey ranks width) order
  bucketSort n (fun i => ranks[i]) order

def loop {α : Type} [Ord α] (xs : Array α) : Nat → Nat →
    Array (Fin xs.size) → Vector Nat xs.size → Array (Fin xs.size)
  | 0, _, order, _ => order
  | fuel + 1, width, order, ranks =>
      if xs.size ≤ width then order
      else
        let order := radixSort ranks width order
        let ranks := assignRanks order (fun i j => compareKey ranks width i j == Ordering.eq)
        loop xs fuel (width * 2) order ranks

end Impl

/-- Starting positions of all suffixes in lexicographic order.

This is the prefix-doubling algorithm. The initial one-character ordering uses
merge sort; subsequent rank pairs are ordered by two stable counting-sort
passes, for `O(n log n)` total time and `O(n)` additional space.
-/
def suffixArray [Ord α] (xs : Array α) : Array Nat :=
  let order := (List.finRange xs.size).mergeSort
    (fun i j => compare xs[i] xs[j] != Ordering.gt) |>.toArray
  let ranks := Impl.assignRanks order (fun i j => compare xs[i] xs[j] == Ordering.eq)
  (Impl.loop xs xs.size 1 order ranks).map Fin.val

end SuffixArray

end Cplib
