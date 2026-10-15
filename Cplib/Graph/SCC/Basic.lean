-- いずれもっときれいにしたい
partial def scc (n : Nat) (g: Array (List Nat)) : List (List Nat) :=
  let rec dfsPostOrder_rev (g : Array (List Nat)) (seen : Array Bool) (res : List Nat) (u : Nat) : (Array Bool × List Nat) :=
    let (seen, res) := g[u]!.foldl (fun (seen, res) v =>
      if seen[v]! then (seen, res)
      else
        let seen := seen.set! v true
        dfsPostOrder_rev g seen res v
    ) (seen, res)
    (seen, u :: res)
  let (_, postOrder_rev) := List.range n |>.foldl (fun (seen, postOrder_rev) u =>
    if seen[u]! then (seen, postOrder_rev)
    else dfsPostOrder_rev g (seen.set! u true) postOrder_rev u
  ) (Array.replicate n false, [])
  let rg := List.range n |>.foldl (fun rg u =>
    g[u]!.foldl (fun rg v => rg.modify v (u :: ·)) rg
  ) <| Array.replicate n []
  postOrder_rev.foldl (fun (seen, res) u =>
    if seen[u]! then (seen, res)
    else
      let seen := seen.set! u true
      let (seen, sc) := dfsPostOrder_rev rg seen [] u
      (seen, sc :: res)
  ) (Array.replicate n false, []) |>.2.reverse
