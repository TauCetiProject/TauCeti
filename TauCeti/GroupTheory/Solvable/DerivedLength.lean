/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Nilpotent
import TauCeti.GroupTheory.Nilpotent.LowerCentralSeries

/-!
# The derived length of a group

The derived length `TauCeti.derivedLength G` of a group `G` is the least `n` for which the `n`-th
derived subgroup `Subgroup.derivedSeries G n` is trivial. It is the number of steps of the
shortest abelian series of a solvable group: the derived length is `1` exactly for nontrivial
abelian groups and `2` exactly for metabelian nonabelian groups.

The derived length is defined as an `sInf` on `ℕ`, so it takes the junk value `0` on a group that
is not solvable, as well as on the trivial group. The theorems below that read the derived series
off the derived length therefore carry a solvability hypothesis, while the bounds of the form
`derivedLength G ≤ n` only need `Subgroup.derivedSeries G n = ⊥`.

## Main definitions

* `TauCeti.derivedLength G`: the least `n` with `Subgroup.derivedSeries G n = ⊥`, or `0` if `G`
  is not solvable.

## Main results

* `TauCeti.derivedLength_le_iff`: for solvable `G`, `derivedLength G ≤ n` exactly when the `n`-th
  derived subgroup is trivial.
* `TauCeti.derivedLength_eq_zero_iff`: the derived length vanishes exactly for trivial groups and
  for groups that are not solvable.
* `TauCeti.derivedLength_eq_succ_iff`, `TauCeti.derivedLength_eq_one_iff`,
  `TauCeti.derivedLength_eq_two_iff`: the derived length is `1` exactly for nontrivial abelian
  groups, and `2` exactly for nonabelian groups with abelian commutator subgroup.
* `MulEquiv.derivedLength_eq`: the derived length is an isomorphism invariant.
* `TauCeti.derivedLength_le_of_injective`, `Subgroup.derivedLength_le`: subgroups of a solvable
  group have smaller derived length.
* `TauCeti.derivedLength_le_of_surjective`, `Subgroup.derivedLength_quotient_le`: so do quotients
  of a solvable group.
* `TauCeti.derivedLength_le_log_nilpotencyClass_add_one`: a nilpotent group of class `c` has
  derived length at most `⌊log₂ c⌋ + 1`.

## References

* D. J. S. Robinson, *A Course in the Theory of Groups*, 2nd ed., Graduate Texts in
  Mathematics 80, Springer, 1996, §5.1.
-/

public section

open Subgroup

namespace TauCeti

variable (G : Type*) [Group G]

/-- The derived length of a group `G`: the least `n` such that the `n`-th derived subgroup
`Subgroup.derivedSeries G n` is trivial. A group that is not solvable gets the junk value `0`. -/
noncomputable def derivedLength : ℕ :=
  sInf {n | Subgroup.derivedSeries G n = ⊥}

variable {G}

/-- If the `n`-th derived subgroup is trivial, then the derived length is at most `n`. -/
theorem derivedLength_le_of_derivedSeries_eq_bot {n : ℕ}
    (h : Subgroup.derivedSeries G n = ⊥) : derivedLength G ≤ n :=
  Nat.sInf_le h

/-- Below the derived length, the derived subgroups are nontrivial. -/
theorem derivedSeries_ne_bot_of_lt_derivedLength {n : ℕ} (h : n < derivedLength G) :
    Subgroup.derivedSeries G n ≠ ⊥ :=
  Nat.notMem_of_lt_sInf h

/-- The derived subgroup indexed by the derived length of a solvable group is trivial. -/
@[simp]
theorem derivedSeries_derivedLength [Group.IsSolvable G] :
    Subgroup.derivedSeries G (derivedLength G) = ⊥ :=
  Nat.sInf_mem (s := {n | Subgroup.derivedSeries G n = ⊥}) Group.IsSolvable.solvable

/-- For a solvable group, `derivedLength G ≤ n` exactly when the `n`-th derived subgroup is
trivial. -/
theorem derivedLength_le_iff [Group.IsSolvable G] {n : ℕ} :
    derivedLength G ≤ n ↔ Subgroup.derivedSeries G n = ⊥ :=
  ⟨fun h ↦ eq_bot_iff.2 ((Subgroup.derivedSeries_antitone G h).trans
      derivedSeries_derivedLength.le),
    derivedLength_le_of_derivedSeries_eq_bot⟩

/-- For a solvable group, `n < derivedLength G` exactly when the `n`-th derived subgroup is
nontrivial. -/
theorem lt_derivedLength_iff [Group.IsSolvable G] {n : ℕ} :
    n < derivedLength G ↔ Subgroup.derivedSeries G n ≠ ⊥ := by
  rw [← not_le, derivedLength_le_iff]

/-- A group that is not solvable has the junk derived length `0`. -/
theorem derivedLength_eq_zero_of_not_isSolvable (h : ¬Group.IsSolvable G) :
    derivedLength G = 0 := by
  refine Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_iff_forall_notMem.2 fun n hn ↦ h ?_))
  exact ⟨n, hn⟩

/-- A group of nonzero derived length is solvable. -/
theorem isSolvable_of_derivedLength_ne_zero (h : derivedLength G ≠ 0) : Group.IsSolvable G := by
  by_contra hG
  exact h (derivedLength_eq_zero_of_not_isSolvable hG)

/-- The derived length vanishes exactly for trivial groups and for groups that are not
solvable. -/
theorem derivedLength_eq_zero_iff :
    derivedLength G = 0 ↔ Subsingleton G ∨ ¬Group.IsSolvable G := by
  refine ⟨fun h ↦ or_iff_not_imp_right.2 fun hG ↦ ?_, ?_⟩
  · rw [not_not] at hG
    have h0 := derivedSeries_derivedLength (G := G)
    rw [h, Subgroup.derivedSeries_zero] at h0
    exact Subgroup.subsingleton_iff.1 (subsingleton_of_bot_eq_top h0.symm)
  · rintro (hG | hG)
    · exact Nat.le_zero.1 (derivedLength_le_of_derivedSeries_eq_bot (Subsingleton.elim _ _))
    · exact derivedLength_eq_zero_of_not_isSolvable hG

/-- The derived length is positive exactly for nontrivial solvable groups. -/
theorem derivedLength_pos_iff : 0 < derivedLength G ↔ Nontrivial G ∧ Group.IsSolvable G := by
  rw [Nat.pos_iff_ne_zero, Ne, derivedLength_eq_zero_iff, not_or, not_subsingleton_iff_nontrivial,
    not_not]

/-- The derived length is `n + 1` exactly when the `(n + 1)`-st derived subgroup is trivial and
the `n`-th one is not. -/
theorem derivedLength_eq_succ_iff {n : ℕ} :
    derivedLength G = n + 1 ↔
      Subgroup.derivedSeries G (n + 1) = ⊥ ∧ Subgroup.derivedSeries G n ≠ ⊥ := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · have := isSolvable_of_derivedLength_ne_zero (G := G) (by omega)
    exact ⟨derivedLength_le_iff.1 h.le, lt_derivedLength_iff.1 (by omega)⟩
  · have : Group.IsSolvable G := ⟨⟨n + 1, h₁⟩⟩
    have := derivedLength_le_of_derivedSeries_eq_bot h₁
    have := lt_derivedLength_iff.2 h₂
    omega

/-- The derived length is `1` exactly for nontrivial abelian groups. -/
theorem derivedLength_eq_one_iff : derivedLength G = 1 ↔ Nontrivial G ∧ IsMulCommutative G := by
  rw [derivedLength_eq_succ_iff, Subgroup.derivedSeries_one, commutator_eq_bot_iff,
    Subgroup.derivedSeries_zero, ne_comm, Ne, subsingleton_iff_bot_eq_top,
    Subgroup.subsingleton_iff, not_subsingleton_iff_nontrivial, and_comm]

/-- The derived length is `2` exactly for metabelian nonabelian groups: groups whose commutator
subgroup is abelian but which are not abelian themselves. -/
theorem derivedLength_eq_two_iff :
    derivedLength G = 2 ↔ IsMulCommutative (commutator G) ∧ ¬IsMulCommutative G := by
  rw [derivedLength_eq_succ_iff, Subgroup.derivedSeries_succ, Subgroup.derivedSeries_one,
    commutator_self_eq_bot_iff, Ne, commutator_eq_bot_iff]

end TauCeti

/-- Isomorphic groups have the same derived length. -/
theorem MulEquiv.derivedLength_eq {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    TauCeti.derivedLength G = TauCeti.derivedLength G' := by
  refine congrArg sInf (Set.ext fun n ↦ ?_)
  simp only [Set.mem_ofPred_eq,
    ← Subgroup.map_derivedSeries_eq (f := e.toMonoidHom) e.surjective n,
    map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective]

namespace TauCeti

variable {G G' : Type*} [Group G] [Group G']

/-- A group that embeds into a solvable group has at most its derived length. -/
theorem derivedLength_le_of_injective [Group.IsSolvable G] (f : G' →* G)
    (hf : Function.Injective f) :
    derivedLength G' ≤ derivedLength G := by
  refine derivedLength_le_of_derivedSeries_eq_bot ((map_eq_bot_iff_of_injective _ hf).1 ?_)
  exact eq_bot_iff.2 ((Subgroup.map_derivedSeries_le_derivedSeries f _).trans
    derivedSeries_derivedLength.le)

/-- A quotient of a solvable group, given as the target of a surjective homomorphism, has at most
its derived length. -/
theorem derivedLength_le_of_surjective [Group.IsSolvable G] (f : G →* G')
    (hf : Function.Surjective f) :
    derivedLength G' ≤ derivedLength G := by
  refine derivedLength_le_of_derivedSeries_eq_bot (eq_bot_iff.2 ?_)
  simpa using Subgroup.derivedSeries_le_map_derivedSeries hf (derivedLength G)

/-- A nilpotent group of nilpotency class `c` has derived length at most `⌊log₂ c⌋ + 1`, because
its `k`-th derived subgroup lies in the `2^k`-th term of the lower central series. -/
theorem derivedLength_le_log_nilpotencyClass_add_one [Group.IsNilpotent G] :
    derivedLength G ≤ Nat.log 2 (Group.nilpotencyClass G) + 1 := by
  refine derivedLength_le_of_derivedSeries_eq_bot (eq_bot_iff.2 ?_)
  refine (derivedSeries_le_lowerCentralSeries_top_two_pow_sub_one _).trans ?_
  rw [← lowerCentralSeries_nilpotencyClass]
  refine lowerCentralSeries_antitone _ ?_
  have := Nat.lt_pow_succ_log_self Nat.one_lt_two (Group.nilpotencyClass G)
  omega

end TauCeti

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup of a solvable group has at most its derived length. -/
theorem derivedLength_le [Group.IsSolvable G] (H : Subgroup G) :
    TauCeti.derivedLength H ≤ TauCeti.derivedLength G :=
  TauCeti.derivedLength_le_of_injective H.subtype H.subtype_injective

/-- A quotient of a solvable group has at most its derived length. -/
theorem derivedLength_quotient_le [Group.IsSolvable G] (N : Subgroup G) [N.Normal] :
    TauCeti.derivedLength (G ⧸ N) ≤ TauCeti.derivedLength G :=
  TauCeti.derivedLength_le_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end Subgroup
