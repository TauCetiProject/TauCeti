/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.Tactic.Module

/-!
# A symmetry criterion for reduced root pairings

A root pairing over a domain in which `2 ≠ 0`, with torsion-free weight module, is reduced as
soon as its pairing is symmetric on roots and coroots. Indeed, if the roots indexed by `i` and
`j` are linearly dependent, then `P.pairing j i • P.root i = 2 • P.root j` and
`P.pairing i j • P.root j = 2 • P.root i`. Symmetry makes these two pairing values equal, so
their common value squares to `4` and is `2` or `-2`; cancelling the factor `2` then identifies
the two roots up to sign. No finiteness of the index type is needed.

This criterion is useful for root data presented in dual coordinate bases. Their roots and
coroots need not be equal as coordinate vectors, while the pairing can still visibly be the
symmetric form of a simply-laced Cartan matrix.

## Main results

* `RootPairing.isReduced_of_pairing_comm`: a root pairing with symmetric pairings is reduced.
* `RootPairing.flip_isReduced`: a reduced root pairing on a finite index type has reduced coroots.
* `RootPairing.ne_neg_of_root_eq_add_nsmul`: in a reduced root pairing, a root string through a
  root `j ≠ -s` in the direction `s` never reaches `-s`.
* `RootPairing.root_ne_and_root_ne_neg_of_root_eq_add`: in a reduced root pairing, a summand of a
  root that is a sum of two roots is neither that root nor its negative.
* `RootPairing.two_smul_sub_coroot'_smul_root_mem_ker_coroot'` and
  `RootPairing.eq_or_eq_reflectionPerm_self_of_ker_coroot'_le`: in a root pairing with reduced
  coroots and `2 ≠ 0`, inclusion of coroot kernels forces the indices to agree up to root negation.
* `RootPairing.root_add_root_notMem_range_root_and_ne_zero_of_root_eq_add_of_root_eq_add`:
  if `γ = α + β` and `δ = α + γ` are roots, then `β + δ` is neither a root nor zero.
* `RootPairing.not_linearIndependent_root_iff`: two roots of a finite crystallographic pairing fail
  to be linearly independent iff they are equal, opposite, or one is `±2` times the other.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- A root pairing whose root--coroot pairing is symmetric is reduced. -/
theorem isReduced_of_pairing_comm
    (hcomm : ∀ i j, P.pairing i j = P.pairing j i) : P.IsReduced := by
  refine ⟨fun i j hdependent => ?_⟩
  have hi := P.pairing_smul_root_eq_of_not_linearIndependent hdependent
  have hj := P.pairing_smul_root_eq_of_not_linearIndependent
    (by rwa [LinearIndependent.pair_symm_iff] at hdependent)
  rw [hcomm] at hj
  have hsquare : P.pairing j i * P.pairing j i = 2 * 2 := by
    refine smul_left_injective R (P.ne_zero i) ?_
    simp only [mul_smul, hi, hj, smul_comm (P.pairing j i) (2 : R)]
  rcases mul_self_eq_mul_self_iff.mp hsquare with htwo | hnegTwo
  · exact .inl (smul_right_injective M two_ne_zero (htwo ▸ hi))
  · rw [hnegTwo, neg_smul, neg_eq_iff_eq_neg, ← smul_neg] at hi
    exact .inr (smul_right_injective M two_ne_zero hi)

omit [IsDomain R] [NeZero (2 : R)] [Module.IsTorsionFree R M] in
/-- A root `k = j + n • s` with `j ≠ -s` is not `-s`: otherwise `-j` would be a positive multiple
of `s`, which a reduced root pairing excludes. -/
lemma ne_neg_of_root_eq_add_nsmul [CharZero R] [HasUniqueDiv M] [P.IsReduced] (s : ι) {j k : ι}
    (hj : let _i := P.indexNeg; j ≠ -s) {n : ℕ} (hkroot : P.root k = P.root j + n • P.root s) :
    let _i := P.indexNeg; k ≠ -s := by
  intro _i
  rintro rfl
  replace hkroot : P.root (-j) = (n + 1) • P.root s := by
    simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self,
      neg_eq_iff_add_eq_zero, add_smul, one_smul] at hkroot ⊢
    rw [← hkroot]
    module
  rcases n.eq_zero_or_pos with rfl | hn
  · apply hj
    rw [zero_add, one_smul, EmbeddingLike.apply_eq_iff_eq] at hkroot
    simp [← hkroot, -indexNeg_neg]
  · have _i : (n + 1).AtLeastTwo := ⟨by omega⟩
    exact P.nsmul_notMem_range_root (n := n + 1) (i := s) ⟨-j, hkroot⟩

section Sum

variable [P.IsReduced]

omit [Module.IsTorsionFree R M] in
/-- If a root is the sum of two roots, then each summand is neither that root nor its negative. -/
theorem root_ne_and_root_ne_neg_of_root_eq_add [CharZero R] {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    P.root i ≠ P.root k ∧ P.root i ≠ -P.root k := by
  have hadd : P.root i + P.root j ∈ Set.range P.root := ⟨k, hk⟩
  have hlin := P.linearIndependent_of_add_mem_range_root' hadd
  refine ⟨fun h ↦ P.ne_zero j (by simpa [hk] using h), fun h ↦ ?_⟩
  have hrel : (2 : R) • P.root i + (1 : R) • P.root j = 0 := by
    rw [one_smul, two_smul, add_assoc, ← hk, h, neg_add_cancel]
  exact one_ne_zero (hlin.eq_zero_of_pair hrel).2

omit [NeZero (2 : R)] [Module.IsTorsionFree R M] in
/-- The sum of the initial and last roots of a double chain is twice its middle root,
and hence is neither a root nor zero. No bound on Cartan integers is needed. -/
theorem root_add_root_notMem_range_root_and_ne_zero_of_root_eq_add_of_root_eq_add [CharZero R]
    {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    P.root β + P.root δ ∉ Set.range P.root ∧ P.root β + P.root δ ≠ 0 := by
  let : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  let : HasUniqueDiv M := .of_isTorsionFree R M
  have heq : P.root β + P.root δ = 2 • P.root γ := by
    rw [hδ, hγ]
    abel
  rw [heq]
  exact ⟨P.nsmul_notMem_range_root, smul_ne_zero (by decide : (2 : ℕ) ≠ 0) (P.ne_zero γ)⟩

end Sum

omit [NeZero (2 : R)] [Module.IsTorsionFree R M] in
/-- A reduced root pairing has reduced coroots: both the weight and the coweight module are
reflexive, being perfectly paired with each other, hence torsion free, which is what
`RootPairing.instFlipIsReduced` needs. So `P.flip.IsReduced` need not be assumed separately. -/
theorem flip_isReduced [Finite ι] [CharZero R] [P.IsReduced] : P.flip.IsReduced :=
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  inferInstance

omit [IsDomain R] [NeZero (2 : R)] [Module.IsTorsionFree R M] in
/-- For any root `α` and weight `x`, `2 • x - ⟨x, α^∨⟩ • α` lies in `ker (P.coroot' α)`. -/
theorem two_smul_sub_coroot'_smul_root_mem_ker_coroot' (α : ι) (x : M) :
    (2 : R) • x - P.coroot' α x • P.root α ∈ LinearMap.ker (P.coroot' α) := by
  simp [mul_comm]

omit [IsDomain R] [Module.IsTorsionFree R M] in
/-- If `ker (P.coroot' α) ≤ ker (P.coroot' β)` in a root pairing with reduced coroots and `2 ≠ 0`,
then `β` is either `α` or its negated index `P.reflectionPerm α α`. -/
theorem eq_or_eq_reflectionPerm_self_of_ker_coroot'_le [P.flip.IsReduced] {α β : ι}
    (h : LinearMap.ker (P.coroot' α) ≤ LinearMap.ker (P.coroot' β)) :
    β = α ∨ β = P.reflectionPerm α α := by
  have hprop : (2 : R) • P.coroot' β = P.coroot' β (P.root α) • P.coroot' α := by
    ext x
    have hβx : P.coroot' β ((2 : R) • x - P.coroot' α x • P.root α) = 0 :=
      h (P.two_smul_sub_coroot'_smul_root_mem_ker_coroot' α x)
    simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hβx
    simp only [LinearMap.smul_apply, smul_eq_mul, hβx, mul_comm]
  have hcoroot : (2 : R) • P.coroot β = P.coroot' β (P.root α) • P.coroot α :=
    P.toLinearMap.flip.toPerfPair.injective (by simpa [map_smul] using hprop)
  have hdep : ¬ LinearIndependent R ![P.coroot α, P.coroot β] := by
    rw [LinearIndependent.pair_iff]
    push Not
    exact ⟨-P.coroot' β (P.root α), 2, by rw [neg_smul, ← hcoroot, neg_add_cancel],
      fun _ ↦ NeZero.ne (2 : R)⟩
  rcases IsReduced.eq_or_eq_neg (P := P.flip) α β hdep with hpos | hneg
  · exact Or.inl (P.coroot.injective hpos.symm)
  · refine Or.inr (P.coroot.injective ?_)
    simp only [flip_root] at hneg
    rw [coroot_reflectionPerm, coreflection_apply_self]
    exact neg_eq_iff_eq_neg.mp hneg.symm

omit [IsDomain R] [NeZero (2 : R)] [Module.IsTorsionFree R M] in
private theorem not_linearIndependent_of_root_eq_smul [Nontrivial R] {i j : ι} {c : R}
    (h : P.root i = c • P.root j) : ¬ LinearIndependent R ![P.root i, P.root j] := fun hli ↦
  one_ne_zero ((LinearIndependent.pair_iff.mp hli 1 (-c) (by simp [h])).1)

omit [NeZero (2 : R)] [Module.IsTorsionFree R M] in
/-- In a finite crystallographic root pairing over a domain of characteristic zero, two roots fail
to be linearly independent if and only if they are equal, opposite, or one is `±2` times the other
(Bourbaki, Ch. VI, §1, no. 3, Proposition 8). -/
theorem not_linearIndependent_root_iff [Finite ι] [CharZero R] [P.IsCrystallographic] {i j : ι} :
    ¬ LinearIndependent R ![P.root i, P.root j] ↔
      i = j ∨ P.root i = -P.root j ∨ P.root j = (2 : R) • P.root i ∨
        P.root i = (2 : R) • P.root j ∨ P.root j = (-2 : R) • P.root i ∨
        P.root i = (-2 : R) • P.root j := by
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  have := Module.IsReflexive.of_isPerfPair P.flip.toLinearMap
  refine ⟨fun hdep ↦ ?_, fun h ↦ ?_⟩
  · set a := P.pairingIn ℤ i j; set b := P.pairingIn ℤ j i
    have h4 : a * b = 4 := (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hdep
    have hab : -4 ≤ a ∧ a ≤ 4 := by
      rcases lt_trichotomy b 0 with hb | hb | hb
      · have ha : a < 0 := by_contra fun ha ↦ by
          have := Int.mul_nonpos_of_nonneg_of_nonpos (not_lt.mp ha) hb.le; omega
        have hle := Int.mul_le_mul_of_nonneg_left (a := 1) (b := -b) (c := -a) (by omega) (by omega)
        rw [neg_mul_neg, h4] at hle; omega
      · simp [hb] at h4
      · have ha : 0 < a := by_contra fun ha ↦ by
          have := Int.mul_nonpos_of_nonpos_of_nonneg (not_lt.mp ha) hb.le; omega
        have hle := Int.mul_le_mul_of_nonneg_left (a := 1) (b := b) (c := a) hb (by omega)
        rw [h4] at hle; omega
    have hc : (a = 2 ∧ b = 2) ∨ (a = -2 ∧ b = -2) ∨ (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨
        (a = -1 ∧ b = -4) ∨ (a = -4 ∧ b = -1) := by
      rcases (by omega : a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨
        a = 4) with ha | ha | ha | ha | ha | ha | ha | ha | ha <;> (rw [ha] at h4; omega)
    rcases hc with h | h | h | h | h | h
    exacts [.inl ((P.pairingIn_two_two_iff ℤ i j).mp h),
      .inr (.inl ((P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h)),
      .inr (.inr (.inl ((P.pairingIn_one_four_iff ℤ i j).mp h))),
      .inr (.inr (.inr (.inl ((P.pairingIn_one_four_iff ℤ j i).mp h.symm)))),
      .inr (.inr (.inr (.inr (.inl ((P.pairingIn_neg_one_neg_four_iff ℤ i j).mp h))))),
      .inr (.inr (.inr (.inr (.inr ((P.pairingIn_neg_one_neg_four_iff ℤ j i).mp h.symm)))))]
  · rcases h with rfl | h | h | h | h | h
    exacts [P.not_linearIndependent_of_root_eq_smul (one_smul R _).symm,
      P.not_linearIndependent_of_root_eq_smul (h.trans (neg_one_smul R _).symm),
      mt LinearIndependent.pair_symm_iff.mp (P.not_linearIndependent_of_root_eq_smul h),
      P.not_linearIndependent_of_root_eq_smul h,
      mt LinearIndependent.pair_symm_iff.mp (P.not_linearIndependent_of_root_eq_smul h),
      P.not_linearIndependent_of_root_eq_smul h]

end RootPairing
