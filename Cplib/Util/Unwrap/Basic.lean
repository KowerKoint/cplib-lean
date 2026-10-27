namespace Cplib

/-!
# Util.Unwrap.Basic

`!` 版 API の共通実装。

このライブラリでは、添字を `Fin` で受ける関数それぞれに次の2つを用意する:

- `foo? : … → Nat → Option _` … 範囲外なら `none`
- `foo! : … → Nat → _` … 範囲外なら停止する

`foo!` は `foo?` の薄いラッパとして `unwrap!` で書く。
-/

/-- `o` が `none` なら、添字が範囲外だったとして `name` を添えて停止する。

メッセージの組み立ては `none` の枝に入ってからしか起きないので、
正常系に文字列生成のコストは乗らない。 -/
@[inline] def unwrap! [Inhabited α] (name : String) : Option α → α
  | some x => x
  | none => panic! s!"{name}: index out of bounds"

end Cplib
