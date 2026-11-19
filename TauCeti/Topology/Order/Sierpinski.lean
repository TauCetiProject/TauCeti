/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order

/-!
# Open sets of the Sierpiński space

Mathlib equips `Prop` with `sierpinskiSpace`, in which `{True}` is open and `nhds False = ⊤`. We
classify all open subsets of `Prop` (`TauCeti.isOpen_sierpinski_iff`) as `∅`, `{True}`, and
`Set.univ`.
-/

public section

/-- **Exact open sets of the Sierpiński space `Prop`**: a subset of `Prop` is open in
`sierpinskiSpace` if and only if it is `∅`, `{True}`, or `Set.univ`. -/
theorem TauCeti.isOpen_sierpinski_iff {s : Set Prop} :
    IsOpen s ↔ s = ∅ ∨ s = {True} ∨ s = Set.univ := by
  refine ⟨fun hs ↦ ?_, fun h ↦ ?_⟩
  · by_cases hF : False ∈ s
    · exact Or.inr (Or.inr (Filter.mem_top.1 (nhds_false ▸ hs.mem_nhds hF)))
    · by_cases hT : True ∈ s
      · exact Or.inr (Or.inl (Set.ext fun p ↦ ⟨fun hp ↦ by by_cases hp' : p <;> simp_all,
          fun hp ↦ hp.symm ▸ hT⟩))
      · exact Or.inl (Set.eq_empty_iff_forall_notMem.2 fun p hp ↦ by by_cases hp' : p <;> simp_all)
  · rcases h with rfl | rfl | rfl; exacts [isOpen_empty, isOpen_singleton_true, isOpen_univ]

end
