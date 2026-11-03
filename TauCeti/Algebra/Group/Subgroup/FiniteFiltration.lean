/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

Both results also hold for additive subgroups, under the names in `TauCeti.AddSubgroup`.
-/

public section

namespace TauCeti.Subgroup

variable {G : Type*} [Group G]

/-- An antitone sequence of subgroups with finite first term eventually equals its intersection. -/
@[to_additive TauCeti.AddSubgroup.exists_forall_eq_iInf_of_antitone
/-- An antitone sequence of additive subgroups with finite first term eventually equals its
intersection. -/]
theorem exists_forall_eq_iInf_of_antitone (f : ℕ → Subgroup G) (hf : Antitone f)
    [Finite (f 0)] : ∃ N, ∀ i, N ≤ i → f i = ⨅ j, f j := by
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition
    (f := fun i ↦ (f i).subgroupOf (f 0)) fun _ _ hij ↦ Subgroup.subgroupOf_mono _ (hf hij)
  have hstable (i : ℕ) (hi : N ≤ i) : f i = f N := by
    simpa only [Subgroup.subgroupOf_inj, inf_of_le_left (hf (Nat.zero_le _)), eq_comm] using
      hN i hi
  refine ⟨N, fun i hi ↦ ?_⟩
  rw [hstable i hi, ← hf.iInf_nat_add N]
  simp only [hstable _ (Nat.le_add_left N _), iInf_const]

/-- An antitone sequence of subgroups with finite first term and trivial intersection is
eventually the trivial subgroup. -/
@[to_additive TauCeti.AddSubgroup.exists_forall_eq_bot_of_antitone_iInf_eq_bot
/-- An antitone sequence of additive subgroups with finite first term and trivial intersection
is eventually the trivial subgroup. -/]
theorem exists_forall_eq_bot_of_antitone_iInf_eq_bot (f : ℕ → Subgroup G) (hf : Antitone f)
    [Finite (f 0)] (hInf : ⨅ i, f i = ⊥) : ∃ N, ∀ i, N ≤ i → f i = ⊥ := by
  simpa only [hInf] using exists_forall_eq_iInf_of_antitone f hf

end TauCeti.Subgroup
