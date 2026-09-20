/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Order.OrderIsoNat

/-!
# Finite decreasing filtrations of groups

An antitone sequence of subgroups whose first term is finite eventually stabilizes at its
intersection. In particular, it is eventually trivial whenever its intersection is trivial.
This elementary observation is useful for ramification filtrations.

## Main results

* `TauCeti.Subgroup.exists_forall_eq_iInf_of_antitone`: a decreasing filtration with finite first
  term eventually equals its intersection.
* `TauCeti.Subgroup.exists_forall_eq_bot_of_antitone_iInf_eq_bot`: a decreasing filtration with
  finite first term and trivial intersection is eventually trivial.
-/

public section

namespace TauCeti.Subgroup

variable {G : Type*} [Group G]

/-- An antitone sequence of subgroups with finite first term eventually equals its intersection. -/
theorem exists_forall_eq_iInf_of_antitone (f : ℕ → Subgroup G) (hf : Antitone f)
    [Finite (f 0)] : ∃ N, ∀ i, N ≤ i → f i = ⨅ j, f j := by
  classical
  let _ := Fintype.ofFinite (f 0)
  have hsubgroupOf : Antitone fun i ↦ (f i).subgroupOf (f 0) :=
    fun _ _ hij ↦ Subgroup.subgroupOf_mono _ (hf hij)
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hsubgroupOf
  have hstable : ∀ i, N ≤ i → f N = f i := by
    intro i hi
    apply le_antisymm
    · intro g hg
      have hg0 : g ∈ f 0 := hf (Nat.zero_le N) hg
      exact (show (⟨g, hg0⟩ : f 0) ∈ (f i).subgroupOf (f 0) from
        (hN i hi ▸ hg))
    · exact hf hi
  have hN_iInf : f N = ⨅ j, f j := by
    apply le_antisymm
    · refine le_iInf fun j ↦ ?_
      rcases le_total N j with hNj | hjN
      · exact (hstable j hNj).le
      · exact hf hjN
    · exact iInf_le f N
  exact ⟨N, fun i hi ↦ (hstable i hi).symm.trans hN_iInf⟩

/-- An antitone sequence of subgroups with finite first term and trivial intersection is
eventually the trivial subgroup. -/
theorem exists_forall_eq_bot_of_antitone_iInf_eq_bot (f : ℕ → Subgroup G) (hf : Antitone f)
    [Finite (f 0)] (hInf : ⨅ i, f i = ⊥) : ∃ N, ∀ i, N ≤ i → f i = ⊥ := by
  simpa only [hInf] using exists_forall_eq_iInf_of_antitone f hf

end TauCeti.Subgroup
