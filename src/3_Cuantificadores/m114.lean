import data.int.parity
import tactic.apply_fun
import data.real.basic


namespace tactic.interactive
setup_tactic_parser

meta def compute_at_hyp (h : name) : tactic unit :=
let lo := loc.ns [h] in
do { ring none tactic.ring.normalize_mode.horner lo <|>
norm_num [] lo <|>
abel tactic.abel.normalize_mode.term lo } ; try (simp_core {} skip ff [] [] lo)

meta def compute_at_goal : tactic unit :=
do focus (tactic.iterate_at_most 3 `[refl <|> norm_num <|> ring <|> abel])

meta def compute_at (h : option name) :=
if H : h.is_some then compute_at_hyp (option.get H) else compute_at_goal

meta def compute (l : parse location) : tactic unit :=
  match l with
  | loc.ns ll := ll.mmap' compute_at
  | loc.wildcard := tactic.local_context >>= list.mmap' (compute_at_hyp ∘ expr.local_pp_name)
  end
end tactic.interactive

notation `|`:1024 x:1 `|`:1 := abs x
