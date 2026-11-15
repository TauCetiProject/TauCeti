/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.Chamber
import Mathlib.LinearAlgebra.RootSystem.BaseChange
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.LinearAlgebra.RootSystem.Flip

/-!
# Indivisible roots of a root pairing

In a possibly non-reduced crystallographic root pairing `P`, a root `α` is *indivisible* if it is
not twice another root (`∀ j, P.root i ≠ (2 : R) • P.root j`). Every reflection of `P` preserves
the set of indivisible roots, so restricting `P` to the subtype `{i // P.IsIndivisible i}` produces
a root pairing `P.indivisiblePairing` on the same weight and coweight modules.

When `P` is finite and crystallographic over a characteristic-zero domain with torsion-free weight
and coweight modules, two linearly dependent roots have ratio in `{±1, ±2, ±1/2}`. Consequently:

* `P.indivisiblePairing` is reduced (`RootPairing.instIsReducedIndivisiblePairing`);
* every root of `P` is either indivisible or twice an indivisible root
  (`RootPairing.isIndivisible_or_exists_root_eq_two_smul`);
* proportional roots determine the same reflection, coreflection, index permutation, and Weyl-group
  generator (`RootPairing.reflection_eq_of_root_eq_smul`, `RootPairing.ofIdx_eq_of_root_eq_smul`),
  so `P.indivisiblePairing.weylGroup` and `P.weylGroup` are canonically isomorphic via their
  faithful action on the weight space (`RootPairing.indivisibleWeylGroupEquiv`).

Over a linearly ordered field, any regular coweight `v` (`∀ i, P.root' i v ≠ 0`) cuts out a base
`P.indivisibleBaseOf v hv` of `P.indivisiblePairing` whose positive roots are precisely the
indivisible roots positive on `v`, without assuming `P.IsRootSystem`. Together with the transitive
Weyl action on chambers of the flipped pairing, any two regular coweights have Weyl-conjugate
positive root sets (`RootPairing.exists_weylGroup_root'_pos_iff`).

We also record `RootPairing.weylGroupToPerm_injective_of_isAnisotropic` and
`RootPairing.finite_weylGroup_of_isAnisotropic`, showing that the Weyl group of a finite anisotropic
root pairing over a domain acts faithfully on the root indices and is finite without assuming that
the roots span the weight space.

## Main definitions

* `RootPairing.IsIndivisible`: a root `i` is not `2 • P.root j` for any root `j`.
* `RootPairing.indivisiblePairing`: the sub-pairing indexed by `{i // P.IsIndivisible i}`.
* `RootPairing.indivisibleWeylGroupEquiv`: the isomorphism
  `P.indivisiblePairing.weylGroup ≃* P.weylGroup`.
* `RootPairing.indivisibleBaseOf`: the base of `P.indivisiblePairing` cut out by a regular coweight.

## Main results

* `RootPairing.weylGroupToPerm_injective_of_isAnisotropic` and
  `RootPairing.finite_weylGroup_of_isAnisotropic`: faithfulness and finiteness of `P.weylGroup`
  without spanning hypotheses.
* `RootPairing.instIsReducedIndivisiblePairing`: `P.indivisiblePairing` is reduced.
* `RootPairing.isIndivisible_or_exists_root_eq_two_smul`: every root is indivisible or twice an
  indivisible root.
* `RootPairing.indivisibleBaseOf_isPos_iff`: positivity with respect to `P.indivisibleBaseOf v hv`
  agrees with positivity on `v`.
* `RootPairing.exists_weylGroup_root'_pos_iff`: any regular coweight can be moved by the Weyl group
  to match the sign pattern of another regular coweight.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI, §1, no. 3–4,
  Propositions 8, 13, and 14.
-/

public section

open Function Set Submodule

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section Anisotropic

variable (P : RootPairing ι R M N) [Fintype ι] [IsDomain R] [P.IsAnisotropic]

/-- The permutation representation of the Weyl group on the root indices is faithful for any finite
anisotropic root pairing over a domain, whether or not the roots span the weight space. -/
theorem weylGroupToPerm_injective_of_isAnisotropic :
    Function.Injective P.weylGroupToPerm := by
  intro v w hvw
  rw [← inv_mul_eq_one]
  refine weylGroup.eq_one_of_forall_smul_root_eq fun i ↦ ?_
  have hi : P.weylGroupToPerm (v⁻¹ * w) i = i := by
    rw [map_mul, map_inv, _root_.Equiv.Perm.mul_apply, _root_.Equiv.Perm.inv_def, hvw,
      _root_.Equiv.symm_apply_apply]
  rw [P.weylGroup_apply_root, hi]

/-- The Weyl group of a finite anisotropic root pairing over a domain is finite, without assuming
that the roots span the weight space. -/
theorem finite_weylGroup_of_isAnisotropic : Finite P.weylGroup :=
  Finite.of_injective P.weylGroupToPerm P.weylGroupToPerm_injective_of_isAnisotropic

end Anisotropic

section Proportional

variable {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]

/-- Proportional roots define the same reflection on the weight space. -/
theorem reflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflection j = P.reflection i := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv M := .of_isTorsionFree R M
  have : HasUniqueDiv N := .of_isTorsionFree R N
  have hc : P.coroot i = t • P.coroot j := P.coroot_eq_smul_coroot_iff.mpr h
  ext x
  simp only [reflection_apply, sub_right_inj]
  calc P.coroot' j x • P.root j
      = P.coroot' j x • (t • P.root i) := by rw [h]
    _ = (t * P.coroot' j x) • P.root i := by rw [smul_smul, mul_comm]
    _ = P.coroot' i x • P.root i := by
        congr 1
        simp [coroot', hc]

/-- Proportional roots define the same coreflection on the coweight space. -/
theorem coreflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.coreflection j = P.coreflection i := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv M := .of_isTorsionFree R M
  have : HasUniqueDiv N := .of_isTorsionFree R N
  exact (P.flip.reflection_eq_of_root_eq_smul (P.coroot_eq_smul_coroot_iff.mpr h)).symm

/-- Proportional roots induce the same reflection permutation on root indices. -/
theorem reflectionPerm_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflectionPerm j = P.reflectionPerm i := by
  ext k
  refine P.root.injective ?_
  rw [P.root_reflectionPerm, P.root_reflectionPerm, P.reflection_eq_of_root_eq_smul h]

/-- Proportional roots define the same reflection in the Weyl group. -/
theorem weylGroup.ofIdx_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    weylGroup.ofIdx P j = weylGroup.ofIdx P i := by
  refine weylGroup.ext fun x ↦ ?_
  simp [P.reflection_eq_of_root_eq_smul h]

end Proportional

section Indivisible

variable (P : RootPairing ι R M N)

/-- A root of `P` is *indivisible* if it is not twice another root of `P`. -/
def IsIndivisible (i : ι) : Prop :=
  ∀ j : ι, P.root i ≠ (2 : R) • P.root j

theorem isIndivisible_iff {i : ι} :
    P.IsIndivisible i ↔ ∀ j : ι, P.root i ≠ (2 : R) • P.root j :=
  Iff.rfl

variable {P} in
/-- Every reflection permutation preserves indivisible roots. -/
theorem IsIndivisible.reflectionPerm {k : ι} (hk : P.IsIndivisible k) (i : ι) :
    P.IsIndivisible (P.reflectionPerm i k) := by
  intro j hj
  refine hk (P.reflectionPerm i j) ?_
  have h1 := congrArg (P.reflection i) hj
  rwa [← P.root_reflectionPerm, P.reflectionPerm_self, map_smul, ← P.root_reflectionPerm] at h1

variable {P} in
/-- The negative of an indivisible root is indivisible. -/
theorem IsIndivisible.neg {k : ι} (hk : P.IsIndivisible k) :
    P.IsIndivisible (P.reflectionPerm k k) :=
  hk.reflectionPerm k

/-- The root pairing obtained by restricting `P` to its indivisible roots. -/
def indivisiblePairing : RootPairing {i : ι // P.IsIndivisible i} R M N where
  toLinearMap := P.toLinearMap
  isPerfPair_toLinearMap := P.isPerfPair_toLinearMap
  root := ⟨fun i ↦ P.root i.1, fun _ _ h ↦ Subtype.ext (P.root.injective h)⟩
  coroot := ⟨fun i ↦ P.coroot i.1, fun _ _ h ↦ Subtype.ext (P.coroot.injective h)⟩
  root_coroot_two i := P.root_coroot_two i.1
  reflectionPerm i :=
    { toFun := fun j ↦ ⟨P.reflectionPerm i.1 j.1, j.2.reflectionPerm i.1⟩
      invFun := fun j ↦ ⟨P.reflectionPerm i.1 j.1, j.2.reflectionPerm i.1⟩
      left_inv := fun j ↦ Subtype.ext (P.reflectionPerm_self i.1 j.1)
      right_inv := fun j ↦ Subtype.ext (P.reflectionPerm_self i.1 j.1) }
  reflectionPerm_root i j := P.reflectionPerm_root i.1 j.1
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i.1 j.1

@[simp]
theorem indivisiblePairing_toLinearMap : P.indivisiblePairing.toLinearMap = P.toLinearMap :=
  (rfl)

@[simp]
theorem indivisiblePairing_root (a : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.root a = P.root a.1 :=
  (rfl)

@[simp]
theorem indivisiblePairing_coroot (a : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.coroot a = P.coroot a.1 :=
  (rfl)

@[simp]
theorem indivisiblePairing_root' (a : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.root' a = P.root' a.1 :=
  (rfl)

@[simp]
theorem indivisiblePairing_coroot' (a : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.coroot' a = P.coroot' a.1 :=
  (rfl)

@[simp]
theorem indivisiblePairing_pairing (a b : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.pairing a b = P.pairing a.1 b.1 :=
  (rfl)

@[simp]
theorem indivisiblePairing_reflection (a : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.reflection a = P.reflection a.1 :=
  (rfl)

@[simp]
theorem indivisiblePairing_coreflection (a : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.coreflection a = P.coreflection a.1 :=
  (rfl)

@[simp]
theorem coe_indivisiblePairing_reflectionPerm (a b : {i : ι // P.IsIndivisible i}) :
    (P.indivisiblePairing.reflectionPerm a b : ι) = P.reflectionPerm a.1 b.1 :=
  (rfl)

instance {S : Type*} [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    P.indivisiblePairing.IsValuedIn S where
  exists_value a b := P.exists_value a.1 b.1

private theorem exists_weylGroup_smul_eq (w : P.indivisiblePairing.weylGroup) :
    ∃ w' : P.weylGroup, ∀ x : M, w' • x = w • x := by
  obtain ⟨g, hg⟩ := w
  induction hg using weylGroup.induction with
  | mem a => exact ⟨weylGroup.ofIdx P a.1, fun _ ↦ rfl⟩
  | one => exact ⟨1, fun _ ↦ rfl⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    obtain ⟨w₁, hw₁⟩ := ih₁
    obtain ⟨w₂, hw₂⟩ := ih₂
    refine ⟨w₁ * w₂, fun x ↦ ?_⟩
    rw [mul_smul, hw₁, hw₂]
    rfl

section Crystallographic

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]

/-- In a finite crystallographic root pairing over a characteristic-zero domain, two linearly
dependent roots are equal up to sign or differ by a factor of `±2`. -/
theorem not_linearIndependent_root_iff {i j : ι} :
    ¬ LinearIndependent R ![P.root i, P.root j] ↔
      i = j ∨ P.root i = -P.root j ∨ P.root j = (2 : R) • P.root i ∨
        P.root i = (2 : R) • P.root j ∨ P.root j = (-2 : R) • P.root i ∨
        P.root i = (-2 : R) • P.root j := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : Module.IsTorsionFree R M := inferInstance
  have : Module.IsTorsionFree R N := inferInstance
  constructor
  · intro hdep
    have h4 : P.pairingIn ℤ i j * P.pairingIn ℤ j i = 4 :=
      (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hdep
    have hmem := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    have hcases : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
        ({(2, 2), (-2, -2), (1, 4), (4, 1), (-1, -4), (-4, -1)} : Set (ℤ × ℤ)) := by
      simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_zero_zero, Prod.mk_one_one,
        Prod.mk_eq_zero, Prod.mk_eq_one, Prod.mk.injEq] at hmem ⊢
      rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        rcases h with ⟨h₁, h₂⟩ <;>
        rw [h₁, h₂] at h4 <;>
        norm_num at h4 <;>
        simp [h₁, h₂]
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hcases
    rcases hcases with h | h | h | h | h | h
    · exact .inl ((P.pairingIn_two_two_iff ℤ i j).mp h)
    · exact .inr (.inl ((P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h))
    · exact .inr (.inr (.inl ((P.pairingIn_one_four_iff ℤ i j).mp h)))
    · exact .inr (.inr (.inr (.inl ((P.pairingIn_one_four_iff ℤ j i).mp h.symm))))
    · exact .inr (.inr (.inr (.inr (.inl ((P.pairingIn_neg_one_neg_four_iff ℤ i j).mp h)))))
    · exact .inr (.inr (.inr (.inr (.inr ((P.pairingIn_neg_one_neg_four_iff ℤ j i).mp h.symm)))))
  · intro h
    rw [LinearIndependent.pair_iff]
    push Not
    rcases h with rfl | h | h | h | h | h
    · exact ⟨1, -1, by simp, fun h0 ↦ absurd h0 one_ne_zero⟩
    · exact ⟨1, 1, by simp [h], fun h0 ↦ absurd h0 one_ne_zero⟩
    · exact ⟨2, -1, by simp [h], fun h0 ↦ absurd h0 two_ne_zero⟩
    · exact ⟨1, -2, by simp [h], fun h0 ↦ absurd h0 one_ne_zero⟩
    · exact ⟨2, 1, by simp [h, neg_smul], fun h0 ↦ absurd h0 two_ne_zero⟩
    · exact ⟨1, 2, by simp [h, neg_smul], fun h0 ↦ absurd h0 one_ne_zero⟩

/-- The sub-pairing of indivisible roots of a finite crystallographic root pairing is reduced. -/
instance instIsReducedIndivisiblePairing : P.indivisiblePairing.IsReduced where
  eq_or_eq_neg a b hdep := by
    rcases (P.not_linearIndependent_root_iff).mp hdep with h | h | h | h | h | h
    · exact .inl (by rw [Subtype.ext h])
    · exact .inr h
    · exact False.elim (b.2 a.1 h)
    · exact False.elim (a.2 b.1 h)
    · refine False.elim (b.2 (P.reflectionPerm a.1 a.1) ?_)
      rw [P.root_reflectionPerm, P.reflection_apply_self, smul_neg, ← neg_smul]
      exact h
    · refine False.elim (a.2 (P.reflectionPerm b.1 b.1) ?_)
      rw [P.root_reflectionPerm, P.reflection_apply_self, smul_neg, ← neg_smul]
      exact h

/-- Every root of a finite crystallographic root pairing is either indivisible or twice an
indivisible root. -/
theorem isIndivisible_or_exists_root_eq_two_smul (i : ι) :
    P.IsIndivisible i ∨ ∃ j : ι, P.IsIndivisible j ∧ P.root i = (2 : R) • P.root j := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsTorsionFree R M := inferInstance
  by_cases hi : P.IsIndivisible i
  · exact .inl hi
  · right
    rw [isIndivisible_iff] at hi
    push Not at hi
    obtain ⟨j, hj⟩ := hi
    refine ⟨j, fun k hk ↦ ?_, hj⟩
    have hik : P.root i = (4 : R) • P.root k := by
      rw [hj, hk, smul_smul]
      norm_num
    have hdep : ¬ LinearIndependent R ![P.root i, P.root k] := by
      rw [LinearIndependent.pair_iff]
      push Not
      exact ⟨1, -4, by simp [hik], fun h0 ↦ absurd h0 one_ne_zero⟩
    have hinj := smul_left_injective R (P.ne_zero k)
    rcases (P.not_linearIndependent_root_iff).mp hdep with rfl | h | h | h | h | h
    · have h' : (1 : R) • P.root i = (4 : R) • P.root i := by
        conv_lhs => rw [one_smul, hik]
      exact absurd (hinj h') (by norm_num)
    · have h' : (4 : R) • P.root k = (-1 : R) • P.root k := by rw [← hik, h, neg_one_smul]
      exact absurd (hinj h') (by norm_num)
    · have h' : (1 : R) • P.root k = ((2 : R) * 4) • P.root k := by
        conv_lhs => rw [one_smul, h, hik, smul_smul]
      exact absurd (hinj h') (by norm_num)
    · exact absurd (hinj (hik.symm.trans h) : (4 : R) = 2) (by norm_num)
    · have h' : (1 : R) • P.root k = ((-2 : R) * 4) • P.root k := by
        conv_lhs => rw [one_smul, h, hik, smul_smul]
      exact absurd (hinj h') (by norm_num)
    · exact absurd (hinj (hik.symm.trans h) : (4 : R) = -2) (by norm_num)

private theorem exists_indivisible_weylGroup_smul_eq (w : P.weylGroup) :
    ∃ w₀ : P.indivisiblePairing.weylGroup, ∀ x : M, w₀ • x = w • x := by
  obtain ⟨g, hg⟩ := w
  induction hg using weylGroup.induction with
  | mem i =>
    rcases P.isIndivisible_or_exists_root_eq_two_smul i with hi | ⟨j, hj, hij⟩
    · exact ⟨weylGroup.ofIdx P.indivisiblePairing ⟨i, hi⟩, fun _ ↦ rfl⟩
    · refine ⟨weylGroup.ofIdx P.indivisiblePairing ⟨j, hj⟩, fun x ↦ ?_⟩
      change P.reflection j x = P.reflection i x
      rw [P.reflection_eq_of_root_eq_smul hij]
  | one => exact ⟨1, fun _ ↦ rfl⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    obtain ⟨w₁, hw₁⟩ := ih₁
    obtain ⟨w₂, hw₂⟩ := ih₂
    refine ⟨w₁ * w₂, fun x ↦ ?_⟩
    rw [mul_smul, hw₁, hw₂]
    rfl

/-- The Weyl group of the indivisible sub-pairing is canonically isomorphic to the Weyl group of `P`
via their faithful actions on the weight space `M`. -/
noncomputable def indivisibleWeylGroupEquiv :
    P.indivisiblePairing.weylGroup ≃* P.weylGroup where
  toFun w := (P.exists_weylGroup_smul_eq w).choose
  invFun w := (P.exists_indivisible_weylGroup_smul_eq w).choose
  left_inv w := weylGroup.ext fun x ↦
    ((P.exists_indivisible_weylGroup_smul_eq _).choose_spec x).trans
      ((P.exists_weylGroup_smul_eq w).choose_spec x)
  right_inv w := weylGroup.ext fun x ↦
    ((P.exists_weylGroup_smul_eq _).choose_spec x).trans
      ((P.exists_indivisible_weylGroup_smul_eq w).choose_spec x)
  map_mul' u v := weylGroup.ext fun x ↦ by
    rw [(P.exists_weylGroup_smul_eq (u * v)).choose_spec x, mul_smul, mul_smul,
      (P.exists_weylGroup_smul_eq v).choose_spec x,
      (P.exists_weylGroup_smul_eq u).choose_spec (v • x)]

@[simp]
theorem indivisibleWeylGroupEquiv_smul (w : P.indivisiblePairing.weylGroup) (x : M) :
    P.indivisibleWeylGroupEquiv w • x = w • x :=
  (P.exists_weylGroup_smul_eq w).choose_spec x

@[simp]
theorem indivisibleWeylGroupEquiv_symm_smul (w : P.weylGroup) (x : M) :
    (P.indivisibleWeylGroupEquiv.symm w) • x = w • x := by
  conv_rhs => rw [← P.indivisibleWeylGroupEquiv.apply_symm_apply w]
  exact (P.indivisibleWeylGroupEquiv_smul _ x).symm

@[simp]
theorem indivisibleWeylGroupEquiv_ofIdx (a : {i : ι // P.IsIndivisible i}) :
    P.indivisibleWeylGroupEquiv (weylGroup.ofIdx P.indivisiblePairing a) =
      weylGroup.ofIdx P a.1 := by
  refine weylGroup.ext fun x ↦ ?_
  rw [P.indivisibleWeylGroupEquiv_smul]
  rfl

theorem coe_weylGroupToPerm_indivisibleWeylGroupEquiv
    (w : P.indivisiblePairing.weylGroup) (a : {i : ι // P.IsIndivisible i}) :
    (P.indivisiblePairing.weylGroupToPerm w a : ι) =
      P.weylGroupToPerm (P.indivisibleWeylGroupEquiv w) a.1 := by
  refine P.root.injective ?_
  rw [← P.indivisiblePairing_root, ← P.indivisiblePairing.weylGroup_apply_root,
    ← P.weylGroup_apply_root, P.indivisibleWeylGroupEquiv_smul, P.indivisiblePairing_root]

@[simp]
theorem coweightEquiv_indivisibleWeylGroupEquiv (w : P.indivisiblePairing.weylGroup) :
    (P.indivisibleWeylGroupEquiv w : P.Aut).coweightEquiv =
      (w : P.indivisiblePairing.Aut).coweightEquiv := by
  ext y
  refine P.flip.toPerfPair.injective <| LinearMap.ext fun x ↦ ?_
  change P.toLinearMap x ((P.indivisibleWeylGroupEquiv w : P.Aut).coweightEquiv y) =
    P.toLinearMap x ((w : P.indivisiblePairing.Aut).coweightEquiv y)
  rw [← (P.indivisibleWeylGroupEquiv w : P.Aut).toLinearMap_weightEquiv x y,
    ← P.indivisiblePairing_toLinearMap,
    ← (w : P.indivisiblePairing.Aut).toLinearMap_weightEquiv x y]
  exact congrArg (fun z ↦ P.toLinearMap z y) (P.indivisibleWeylGroupEquiv_smul w x)

end Crystallographic

end Indivisible

end CommRing

section OrderedField

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic]

private theorem indivisibleBaseOf_coroot_mem_or_neg_mem
    {s : Set {i : ι // P.IsIndivisible i}}
    (hli : LinearIndepOn R P.indivisiblePairing.root s)
    (hsp : ∀ a, P.indivisiblePairing.root a ∈ AddSubmonoid.closure (P.indivisiblePairing.root '' s)
      ∨ -P.indivisiblePairing.root a ∈ AddSubmonoid.closure (P.indivisiblePairing.root '' s))
    (a : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.coroot a ∈ AddSubmonoid.closure (P.indivisiblePairing.coroot '' s) ∨
      -P.indivisiblePairing.coroot a ∈ AddSubmonoid.closure (P.indivisiblePairing.coroot '' s) := by
  let P₀ := P.indivisiblePairing
  let _ := P₀.indexNeg
  have : Fintype {i : ι // P.IsIndivisible i} := Fintype.ofFinite _
  let Q := P₀.restrictScalars' R
  have : Q.IsCrystallographic :=
    { exists_value a b := by
        obtain ⟨z, hz⟩ := P₀.exists_value (S := ℤ) a b
        exact ⟨z, hz.trans (by simpa using (P₀.restrictScalars_pairing (K := R) a b).symm)⟩ }
  have : Q.IsReduced :=
    { eq_or_eq_neg a b hdep := by
        refine (IsReduced.eq_or_eq_neg (P := P₀) a b fun hli' ↦ hdep ?_).imp
          Subtype.ext Subtype.ext
        rw [← LinearMap.linearIndependent_iff (span R (range P₀.root)).subtype
          (LinearMap.ker_eq_bot.mpr (injective_subtype _))]
        convert hli' using 1
        ext k; fin_cases k <;> rfl }
  have hliQ : LinearIndepOn R Q.root s :=
    LinearIndepOn.of_comp (span R (range P₀.root)).subtype hli
  have hspQ : ∀ c, Q.root c ∈ AddSubmonoid.closure (Q.root '' s) ∨
      -Q.root c ∈ AddSubmonoid.closure (Q.root '' s) := fun c ↦ by
    have hmap : ∀ u : span R (range P₀.root),
        (u : M) ∈ AddSubmonoid.closure (P₀.root '' s) →
          u ∈ AddSubmonoid.closure (Q.root '' s) := fun u hu ↦ by
      have himg : P₀.root '' s = (span R (range P₀.root)).subtype '' (Q.root '' s) := by
        rw [← Set.image_comp]; rfl
      rw [himg, ← AddMonoidHom.map_mclosure] at hu
      obtain ⟨w, hw, hwu⟩ := hu
      exact Subtype.ext hwu ▸ hw
    exact (hsp c).imp (hmap (Q.root c)) (hmap (-Q.root c))
  have hcor := Q.coroot_mem_or_neg_mem_closure_of_root s hliQ hspQ a
  have himg : P₀.coroot '' s = (span R (range P₀.coroot)).subtype '' (Q.coroot '' s) := by
    rw [← Set.image_comp]; rfl
  rw [himg, ← AddMonoidHom.map_mclosure]
  exact hcor.imp (fun hc ↦ ⟨Q.coroot a, hc, rfl⟩) (fun hc ↦ ⟨-Q.coroot a, hc, rfl⟩)

/-- Any regular coweight `v` (`∀ i, P.root' i v ≠ 0`) defines a base of `P.indivisiblePairing`
whose simple roots are the `v`-indecomposable indivisible roots, without assuming `P.IsRootSystem`.
-/
noncomputable def indivisibleBaseOf (v : N) (hv : ∀ i : ι, P.root' i v ≠ 0) :
    P.indivisiblePairing.Base := by
  let P₀ := P.indivisiblePairing
  let _ := P₀.indexNeg
  have : Fintype {i : ι // P.IsIndivisible i} := Fintype.ofFinite _
  let f : Module.Dual R M := P₀.flip.toPerfPair v
  have hf : ∀ a, f (P₀.root a) ≠ 0 := fun a ↦ hv a.1
  let s : Set {i : ι // P.IsIndivisible i} :=
    IsAddIndecomposable.baseOf P₀.root (f : M →+ R)
  have hli : LinearIndepOn R P₀.root s := P₀.linearIndepOn_root_baseOf' f hf
  have hsp : ∀ a, P₀.root a ∈ AddSubmonoid.closure (P₀.root '' s) ∨
      -P₀.root a ∈ AddSubmonoid.closure (P₀.root '' s) := fun a ↦
    IsAddIndecomposable.mem_or_neg_mem_closure_baseOf P₀.root (f : M →+ R) a (hf a) (by simp)
  exact
    { support := (Set.toFinite s).toFinset
      linearIndepOn_root := by rw [Set.Finite.coe_toFinset]; exact hli
      linearIndepOn_coroot := by
        rw [Set.Finite.coe_toFinset]; exact P₀.linearIndepOn_coroot_iff.mpr hli
      root_mem_or_neg_mem := fun a ↦ by rw [Set.Finite.coe_toFinset]; exact hsp a
      coroot_mem_or_neg_mem := fun a ↦ by
        rw [Set.Finite.coe_toFinset]
        exact P.indivisibleBaseOf_coroot_mem_or_neg_mem hli hsp a }

/-- Every simple root of `P.indivisibleBaseOf v hv` is strictly positive on `v`. -/
theorem root'_pos_of_mem_indivisibleBaseOf {v : N} {hv : ∀ i : ι, P.root' i v ≠ 0}
    {a : {i : ι // P.IsIndivisible i}} (ha : a ∈ (P.indivisibleBaseOf v hv).support) :
    0 < P.root' a.1 v := by
  simp only [indivisibleBaseOf, Set.Finite.mem_toFinset] at ha
  exact ha.1

/-- An indivisible root is positive with respect to `P.indivisibleBaseOf v hv` if and only if it is
strictly positive on `v`. -/
@[simp]
theorem indivisibleBaseOf_isPos_iff {v : N} (hv : ∀ i : ι, P.root' i v ≠ 0)
    (a : {i : ι // P.IsIndivisible i}) :
    (P.indivisibleBaseOf v hv).IsPos a ↔ 0 < P.root' a.1 v := by
  have hsupp : ∀ c ∈ (P.indivisibleBaseOf v hv).support,
      0 < P.indivisiblePairing.root' c v :=
    fun c hc ↦ P.root'_pos_of_mem_indivisibleBaseOf hc
  refine ⟨root'_pos_of_isPos hsupp, fun ha ↦ ?_⟩
  by_contra hna
  exact ha.not_gt (root'_neg_of_not_isPos hsupp hna)

omit [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
private theorem autFlip_symm_mem_weylGroup {g : P.indivisiblePairing.flip.Aut}
    (hg : g ∈ P.indivisiblePairing.flip.weylGroup) :
    (Equiv.autFlip P.indivisiblePairing).symm g ∈ P.indivisiblePairing.weylGroup := by
  induction hg using weylGroup.induction with
  | mem a =>
    have : (Equiv.autFlip P.indivisiblePairing).symm
        (Equiv.reflection P.indivisiblePairing.flip a) =
        Equiv.reflection P.indivisiblePairing a :=
      (Equiv.autFlip P.indivisiblePairing).symm_apply_eq.mpr (Equiv.autFlip_reflection a).symm
    rw [this]
    exact (weylGroup.ofIdx P.indivisiblePairing a).2
  | one => simp
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    rw [map_mul]
    exact mul_mem ih₁ ih₂

/-- Given two regular coweights `x` and `v`, some Weyl-group element `w : P.weylGroup` matches the
positive roots of `x` with those of `v`: `0 < P.root' i x ↔ 0 < P.root' (w i) v`. -/
theorem exists_weylGroup_root'_pos_iff {x v : N}
    (hx : ∀ i : ι, P.root' i x ≠ 0) (hv : ∀ i : ι, P.root' i v ≠ 0) :
    ∃ w : P.weylGroup, ∀ i : ι,
      0 < P.root' i x ↔ 0 < P.root' (P.weylGroupToPerm w i) v := by
  let P₀ := P.indivisiblePairing
  let b := P.indivisibleBaseOf v hv
  have : Fintype {i : ι // P.IsIndivisible i} := Fintype.ofFinite _
  have : Finite P₀.flip.weylGroup := P₀.flip.finite_weylGroup_of_isAnisotropic
  have hx_reg : IsRegularWeight P₀.flip x := (isRegularWeight_iff P₀.flip x).mpr fun a ↦ hx a.1
  obtain ⟨u, hu⟩ := exists_mem_dominantChamber_of_finite_weylGroup P₀.flip b.flip x
  have hu_open : u • x ∈ openDominantChamber P₀.flip b.flip :=
    mem_openDominantChamber_of_isRegularWeight P₀.flip b.flip hu
      ((isRegularWeight_smul P₀.flip u x).mpr hx_reg)
  let w₀ : P₀.weylGroup :=
    ⟨(Equiv.autFlip P₀).symm (u : P₀.flip.Aut), P.autFlip_symm_mem_weylGroup u.2⟩
  let w : P.weylGroup := P.indivisibleWeylGroupEquiv w₀
  refine ⟨w, fun i ↦ ?_⟩
  have hkey : ∀ a : {i : ι // P.IsIndivisible i},
      0 < P.root' a.1 x ↔ 0 < P.root' (P.weylGroupToPerm w a.1) v := fun a ↦ by
    have hperm : P₀.weylGroupToPerm w₀ a = (u : P₀.flip.Aut).indexEquiv a := by
      change ((Equiv.autFlip P₀).symm (u : P₀.flip.Aut)).indexEquiv a = _
      rw [← Equiv.indexEquiv_autFlip, MulEquiv.apply_symm_apply]
    have hux : P₀.flip.coroot' ((u : P₀.flip.Aut).indexEquiv a) (u • x) = P.root' a.1 x :=
      P₀.flip.coroot'_weylGroupToPerm_smul u a x
    have hdom : ∀ c ∈ b.support, 0 < P₀.root' c (u • x) := fun c hc ↦
      (mem_openDominantChamber P₀.flip b.flip (u • x)).mp hu_open c (by rwa [Base.flip_support])
    rw [← hux, ← hperm, ← P.coe_weylGroupToPerm_indivisibleWeylGroupEquiv w₀ a,
      ← P.indivisibleBaseOf_isPos_iff hv (P₀.weylGroupToPerm w₀ a)]
    change 0 < P₀.root' (P₀.weylGroupToPerm w₀ a) (u • x) ↔ b.IsPos (P₀.weylGroupToPerm w₀ a)
    refine ⟨fun hpos ↦ ?_, root'_pos_of_isPos hdom⟩
    by_contra hneg
    exact hpos.not_gt (root'_neg_of_not_isPos hdom hneg)
  rcases P.isIndivisible_or_exists_root_eq_two_smul i with hi | ⟨j, hj, hij⟩
  · exact hkey ⟨i, hi⟩
  · have hx2 : P.root' i x = 2 * P.root' j x := by simp [root', hij]
    have hv2 : P.root' (P.weylGroupToPerm w i) v = 2 * P.root' (P.weylGroupToPerm w j) v := by
      have hw : P.root (P.weylGroupToPerm w i) = (2 : R) • P.root (P.weylGroupToPerm w j) := by
        rw [← P.weylGroup_apply_root, ← P.weylGroup_apply_root, hij]
        exact LinearEquiv.map_smul (w : P.Aut).weightEquiv (2 : R) (P.root j)
      change P.toLinearMap (P.root (P.weylGroupToPerm w i)) v =
        2 * P.toLinearMap (P.root (P.weylGroupToPerm w j)) v
      rw [hw, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hx2, hv2, mul_pos_iff_of_pos_left two_pos, mul_pos_iff_of_pos_left two_pos]
    exact hkey ⟨j, hj⟩

end OrderedField

end RootPairing
