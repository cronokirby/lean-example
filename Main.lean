import LeanExample

open LeanExample

def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  let t := Tree.ofList [5, 3, 8, 1, 4, 7, 9]
  IO.println s!"in-order: {t.toList}"
  IO.println s!"size:     {t.size}"
  IO.println s!"mirrored: {t.mirror.toList}"
