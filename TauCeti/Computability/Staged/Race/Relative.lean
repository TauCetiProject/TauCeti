/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.RecursiveIn
public import TauCeti.Computability.Staged.Race

/-!
# Relative computability of finite races

A race inspects only the observations through its current stage. Collecting those observations
in finite lists reduces racing oracle-computable streams to primitive-recursive racing.
-/

public section

namespace TauCeti.Staged

variable {α β : Type*}

/-- Racing uniformly effective streams is effective in the same oracle family. -/
theorem computableIn₂_race {γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {G : Set (ℕ →. ℕ)} {l : γ → ℕ → Option α} {r : γ → ℕ → Option β}
    (hl : ComputableIn₂ G l) (hr : ComputableIn₂ G r) :
    ComputableIn₂ G fun x s => race (l x) (r x) s := by
  let left (L : List (Option α × Option β)) (t : ℕ) := L[t]?.bind Prod.fst
  let right (L : List (Option α × Option β)) (t : ℕ) := L[t]?.bind Prod.snd
  have hleft : Primrec₂ left :=
    (Primrec.option_bind₁ Primrec.fst).comp Primrec.list_getElem?
  have hright : Primrec₂ right :=
    (Primrec.option_bind₁ Primrec.snd).comp Primrec.list_getElem?
  have hobs : ComputableIn₂ G fun x t => (l x t, r x t) := hl.pair hr
  have hprefix : ComputableIn₂ G fun x s => (List.range (s + 1)).map (fun t => (l x t, r x t)) :=
    hobs.list_range_map.comp
      (ComputableIn.fst.pair (Primrec.succ.computableIn.comp ComputableIn.snd))
  refine RecursiveIn.of_eq ((primrec_race hleft hright).computableIn.comp
    (hprefix.pair ComputableIn.snd)) ?_
  rintro ⟨x, s⟩
  let L := (List.range (s + 1)).map (fun t => (l x t, r x t))
  have hl' (t : ℕ) (ht : t ≤ s) : left L t = l x t := by
    simp [left, L, Nat.lt_succ_of_le ht]
  have hr' (t : ℕ) (ht : t ≤ s) : right L t = r x t := by
    simp [right, L, Nat.lt_succ_of_le ht]
  exact congrArg Part.some (race_congr hl' hr')

end TauCeti.Staged
