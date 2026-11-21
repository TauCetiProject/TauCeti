/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Parabolic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl
import TauCeti.GroupTheory.Coxeter.Dihedral
import TauCeti.GroupTheory.Coxeter.Length

/-!
# The Weyl group of a realization is a Coxeter group

Let `A` be a generalized Cartan matrix: an integral matrix with diagonal entries `2`, nonpositive
entries off the diagonal, and `A i j = 0` exactly when `A j i = 0`. Let `R` be a realization of `A`
over a field `K`, with simple roots `αᵢ` in the dual `H*`, and let `W` be the Coxeter group of the
matrix `mᵢⱼ = 2, 3, 4, 6, ∞` for `A i j * A j i = 0, 1, 2, 3, ≥ 4`
(`TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A`). The simple reflections satisfy the Coxeter
relations, so `W` acts on `H*` through `TauCeti.CartanRealization.coxeterHom`, with image the Weyl
group.

This file proves the **sign criterion**: for `w ∈ W` the root `w αᵢ` lies in the positive root cone
`Q₊ = ⊕ᵢ ℕ αᵢ` when `ℓ(w sᵢ) > ℓ(w)`, and in `-Q₊` when `ℓ(w sᵢ) < ℓ(w)`. Over a field of
characteristic zero `Q₊` is pointed, so the two cases are exclusive and the criterion becomes an
equivalence. Its consequence is that, over a field of characteristic zero, `W` acts faithfully on
the root lattice: an element `w ≠ 1` has a right descent `i`, so `w αᵢ ∈ -Q₊` is not `αᵢ`. Hence,
still over a field of characteristic zero, `coxeterHom` is injective and the Weyl group, with the
simple reflections, is a Coxeter system for the matrix `mᵢⱼ`
(`TauCeti.CartanRealization.weylCoxeterSystem`). Its length function is the length of the Weyl
group in the simple reflections, and the sign criterion reads `ℓ(w sᵢ) < ℓ(w)` exactly when
`w αᵢ ∈ -Q₊`. Nothing here needs the matrix to be symmetrizable, nonsingular or of finite type,
and the Weyl group may be infinite, as in affine type `A₁⁽¹⁾`.

The proof is Tits' argument for the geometric representation of a Coxeter group, transported to
the action on `H*`, which is not the geometric representation when `A` is not symmetric or has a
Cartan product larger than `4`. One inducts on the length of `w`
(`CoxeterSystem.parabolic_pair_induction`): a right descent `j` of `w`
factors `w = u v` with `u` a minimal coset representative for the standard parabolic subgroup on
`{i, j}` and `v` in it, the lengths adding, and the induction hypothesis applies to `u` at `i` and
at `j`. The rank-two input is that an alternating word `⋯ sᵢ sⱼ` shorter than `mᵢⱼ` sends `αᵢ` to
an integral combination `c αᵢ + c' αⱼ` with `c, c' ≥ 0`. The coefficients satisfy
`cₙ₊₂ = bₙ cₙ₊₁ - cₙ` with multipliers `bₙ` alternating between `-A j i` and `-A i j`; they are
checked directly for the four finite Cartan products, and for a Cartan product at least `4` the
two-step recurrence `cₙ₊₄ = (A i j A j i - 2) cₙ₊₂ - cₙ` keeps them nondecreasing.

## Main results

* `TauCeti.CartanRealization.exists_coxeterHom_apply_root_eq_of_mem_parabolic_pair`: the rank-two
  case of the sign criterion.
* `TauCeti.CartanRealization.coxeterHom_apply_root_mem_posRootCone` and
  `TauCeti.CartanRealization.neg_coxeterHom_apply_root_mem_posRootCone`: **the sign criterion**,
  and over a field of characteristic zero its equivalence forms
  `TauCeti.CartanRealization.coxeterHom_apply_root_mem_posRootCone_iff` and
  `TauCeti.CartanRealization.neg_coxeterHom_apply_root_mem_posRootCone_iff`.
* `TauCeti.CartanRealization.eq_one_of_forall_coxeterHom_apply_root_eq`: an element of the Coxeter
  group fixing every simple root is trivial.
* `TauCeti.CartanRealization.coxeterHom_injective`: **the Coxeter group acts faithfully**.
* `TauCeti.CartanRealization.weylCoxeterSystem`: **the Weyl group is a Coxeter system** on the
  simple reflections (`TauCeti.CartanRealization.coe_weylCoxeterSystem_simple`), whose length
  function is that of the Coxeter group
  (`TauCeti.CartanRealization.length_weylCoxeterSystem_mulEquiv_symm_apply`), with the descent
  criterion `TauCeti.CartanRealization.weylCoxeterSystem_isRightDescent_iff`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Lemma 3.11 (the sign criterion)
  and Proposition 3.13 (the Weyl group is a Coxeter group).
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 5.4 (Tits'
  argument for the geometric representation).
-/

public section

open Module

namespace TauCeti

namespace CartanRealization

/-! ### The rank-two coefficients -/

/-- The coefficients of the images of a simple root under the alternating words of a rank-two
Weyl group: `c 0 = 0`, `c 1 = 1` and `c (n + 2) = b * c (n + 1) - c n` for even `n`,
`c (n + 2) = a * c (n + 1) - c n` for odd `n`. -/
private def rankTwoCoeff (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => (if Even n then b else a) * rankTwoCoeff a b (n + 1) - rankTwoCoeff a b n

private theorem rankTwoCoeff_add_two (a b : ℤ) (n : ℕ) :
    rankTwoCoeff a b (n + 2) =
      (if Even n then b else a) * rankTwoCoeff a b (n + 1) - rankTwoCoeff a b n := by
  rw [rankTwoCoeff]

/-- The two-step recurrence, in which the two multipliers combine into the Cartan product. -/
private theorem rankTwoCoeff_add_four (a b : ℤ) (n : ℕ) :
    rankTwoCoeff a b (n + 4) = (a * b - 2) * rankTwoCoeff a b (n + 2) - rankTwoCoeff a b n := by
  have h₂ := rankTwoCoeff_add_two a b n
  have h₃ := rankTwoCoeff_add_two a b (n + 1)
  have h₄ := rankTwoCoeff_add_two a b (n + 2)
  have hpar : Even (n + 2) ↔ Even n := by simp [Nat.even_add]
  have hpar' : Even (n + 1) ↔ ¬Even n := Nat.even_add_one
  simp only [hpar, hpar'] at h₃ h₄
  by_cases hn : Even n
  · simp only [hn, ↓reduceIte, not_true_eq_false] at h₂ h₃ h₄
    linear_combination h₄ + b * h₃ + h₂
  · simp only [hn, ↓reduceIte, not_false_eq_true] at h₂ h₃ h₄
    linear_combination h₄ + a * h₃ + h₂

/-- For a Cartan product at least `4` the coefficients are nonnegative. -/
private theorem rankTwoCoeff_nonneg_of_four_le {a b : ℤ} (hb : 0 ≤ b) (h4 : 4 ≤ a * b) (n : ℕ) :
    0 ≤ rankTwoCoeff a b n := by
  have key (n : ℕ) : 0 ≤ rankTwoCoeff a b n ∧ rankTwoCoeff a b n ≤ rankTwoCoeff a b (n + 2) := by
    induction n using Nat.twoStepInduction with
    | zero => simp [rankTwoCoeff, hb]
    | one =>
      simp [rankTwoCoeff]
      linarith
    | more n ih _ =>
      obtain ⟨h₀, h₁⟩ := ih
      refine ⟨h₀.trans h₁, ?_⟩
      rw [rankTwoCoeff_add_four]
      nlinarith [mul_nonneg (sub_nonneg.mpr h4) (h₀.trans h₁)]
  exact (key n).1

/-- For a Cartan product `0`, `1`, `2` or `3` of nonnegative multipliers vanishing together, the
coefficients are nonnegative up to the Coxeter order. -/
private theorem rankTwoCoeff_nonneg_of_lt_four {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a = 0 ↔ b = 0) (h4 : a * b < 4) {n : ℕ} (hn : n ≤ coxeterOrder (a * b)) :
    0 ≤ rankTwoCoeff a b n := by
  -- both multipliers vanish, or both are at least `1` and hence at most `3`
  have hpos : a = 0 ∧ b = 0 ∨ 1 ≤ a ∧ 1 ≤ b := by
    by_cases ha0 : a = 0
    · exact .inl ⟨ha0, hab.mp ha0⟩
    · exact .inr ⟨by omega, by have := mt hab.mpr ha0; omega⟩
  have ha3 : a ≤ 3 := by rcases hpos with h | h <;> nlinarith
  have hb3 : b ≤ 3 := by rcases hpos with h | h <;> nlinarith
  clear hpos
  interval_cases a <;> interval_cases b <;> revert n hab h4 <;> norm_num <;> decide

variable {I : Type*} [DecidableEq I] {A : Matrix I I ℤ}

/-- The rank-two coefficients are nonnegative up to the Coxeter-matrix entry, or at every index
when that entry is infinite. -/
private theorem rankTwoCoeff_nonneg (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (hneg : ∀ i j, i ≠ j → A i j ≤ 0) (i j : I) {n : ℕ}
    (hn : n ≤ coxeterMatrixOfGeneralizedCartanMatrix A i j ∨
      coxeterMatrixOfGeneralizedCartanMatrix A i j = 0) :
    0 ≤ rankTwoCoeff (-A i j) (-A j i) n := by
  rcases eq_or_ne i j with rfl | hij
  · -- on the diagonal the entry is `1`, so only `c 0 = 0` and `c 1 = 1` occur
    have hn : n ≤ 1 := by simpa using hn
    interval_cases n <;> simp [rankTwoCoeff]
  have ha : 0 ≤ -A i j := neg_nonneg.mpr (hneg i j hij)
  have hb : 0 ≤ -A j i := neg_nonneg.mpr (hneg j i hij.symm)
  have hprod : -A i j * -A j i = A i j * A j i := neg_mul_neg _ _
  rcases lt_or_ge (A i j * A j i) 4 with h4 | h4
  · rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_lt_four A hij h4] at hn
    refine rankTwoCoeff_nonneg_of_lt_four ha hb (by rw [neg_eq_zero, neg_eq_zero]; exact hzero i j)
      (by rwa [hprod]) ?_
    rw [hprod]
    refine hn.resolve_right (ne_of_gt (lt_of_lt_of_le two_pos (two_le_coxeterOrder ?_)))
    have : 0 ≤ A i j * A j i := hprod ▸ mul_nonneg ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · exact rankTwoCoeff_nonneg_of_four_le hb (hprod ▸ h4) n

/-! ### The rank-two case -/

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hA : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
  (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (hneg : ∀ i j, i ≠ j → A i j ≤ 0)

/-- The alternating word of length `k` ending in `j` sends `αᵢ` to an explicit integral combination
of `αᵢ` and `αⱼ`, whose two coefficients are consecutive terms of `rankTwoCoeff` and exchange places
at each step. -/
private theorem coxeterHom_wordProd_alternatingWord_root (i j : I) (k : ℕ) :
    R.coxeterHom hA hzero
        ((coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.wordProd
          (CoxeterSystem.alternatingWord i j k)) (R.root i) =
      if Even k then
        rankTwoCoeff (-A i j) (-A j i) (k + 1) • R.root i +
          rankTwoCoeff (-A i j) (-A j i) k • R.root j
      else
        rankTwoCoeff (-A i j) (-A j i) k • R.root i +
          rankTwoCoeff (-A i j) (-A j i) (k + 1) • R.root j := by
  induction k with
  | zero => simp [CoxeterSystem.alternatingWord, rankTwoCoeff]
  | succ k ih =>
    rw [CoxeterSystem.alternatingWord_succ', CoxeterSystem.wordProd_cons, map_mul,
      mul_apply_eq_comp, ih, rankTwoCoeff_add_two]
    by_cases hk : Even k
    · have hk' : ¬Even (k + 1) := Nat.not_even_iff_odd.mpr hk.add_one
      simp only [hk, hk', ↓reduceIte, CoxeterMatrix.toCoxeterSystem_simple, coxeterHom_simple,
        map_add, map_zsmul, simpleReflection_root_self]
      simp only [simpleReflection_root, Matrix.map_apply]
      module
    · have hk' : Even (k + 1) := Nat.even_add_one.mpr hk
      simp only [hk, hk', ↓reduceIte, CoxeterMatrix.toCoxeterSystem_simple, coxeterHom_simple,
        map_add, map_zsmul, simpleReflection_root_self]
      simp only [simpleReflection_root, Matrix.map_apply]
      module

include hneg in
/-- **The rank-two case of the sign criterion.** An element `v` of the standard parabolic subgroup
on `{i, j}` without right descent at `i` sends `αᵢ` to a combination of `αᵢ` and `αⱼ` with natural
coefficients. -/
theorem exists_coxeterHom_apply_root_eq_of_mem_parabolic_pair {i j : I}
    {v : (coxeterMatrixOfGeneralizedCartanMatrix A).Group}
    (hv : v ∈ (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.parabolic {i, j})
    (hvi : ¬(coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent v i) :
    ∃ a b : ℕ, R.coxeterHom hA hzero v (R.root i) = a • R.root i + b • R.root j := by
  set cs := (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem
  have hk := cs.length_lt_of_mem_parabolic_pair_of_not_isRightDescent hv hvi
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (rankTwoCoeff_nonneg hzero hneg i j
    (n := cs.length v) (by omega))
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (rankTwoCoeff_nonneg hzero hneg i j
    (n := cs.length v + 1) (by omega))
  rw [← cs.wordProd_alternatingWord_eq_of_mem_parabolic_pair_of_not_isRightDescent hv hvi,
    R.coxeterHom_wordProd_alternatingWord_root, hp, hq]
  split_ifs
  · exact ⟨q, p, by simp only [natCast_zsmul]⟩
  · exact ⟨p, q, by simp only [natCast_zsmul]⟩

/-! ### The sign criterion -/

/-- The simple reflection `sᵢ` negates `αᵢ`, so `w sᵢ` sends `αᵢ` to `-w αᵢ`. -/
theorem coxeterHom_mul_simple_apply_root (w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group)
    (i : I) :
    R.coxeterHom hA hzero (w * (coxeterMatrixOfGeneralizedCartanMatrix A).simple i) (R.root i) =
      -R.coxeterHom hA hzero w (R.root i) := by
  rw [map_mul, mul_apply_eq_comp, coxeterHom_simple, simpleReflection_root_self, map_neg]

include hneg in
/-- **The sign criterion, positive case.** If `i` is not a right descent of `w`, that is
`ℓ(w sᵢ) = ℓ(w) + 1`, then `w αᵢ` lies in the positive root cone `Q₊`. -/
theorem coxeterHom_apply_root_mem_posRootCone
    {w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group} {i : I}
    (h : ¬(coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent w i) :
    R.coxeterHom hA hzero w (R.root i) ∈ R.posRootCone := by
  refine (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.parabolic_pair_induction
    (P := fun w i ↦ R.coxeterHom hA hzero w (R.root i) ∈ R.posRootCone)
    (fun i ↦ by simpa using R.root_mem_posRootCone i) (fun hv hvi hu hu' ↦ ?_) h
  obtain ⟨a, b, hab⟩ := R.exists_coxeterHom_apply_root_eq_of_mem_parabolic_pair hA hzero hneg hv hvi
  rw [map_mul, mul_apply_eq_comp, hab, map_add, map_nsmul, map_nsmul]
  exact add_mem (Submodule.smul_mem _ a hu) (Submodule.smul_mem _ b hu')

include hneg in
/-- **The sign criterion, negative case.** If `i` is a right descent of `w`, that is
`ℓ(w sᵢ) + 1 = ℓ(w)`, then `w αᵢ` lies in `-Q₊`. -/
theorem neg_coxeterHom_apply_root_mem_posRootCone
    {w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group} {i : I}
    (h : (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent w i) :
    -R.coxeterHom hA hzero w (R.root i) ∈ R.posRootCone := by
  rw [CoxeterSystem.isRightDescent_iff_not_isRightDescent_mul,
    CoxeterMatrix.toCoxeterSystem_simple] at h
  rw [← R.coxeterHom_mul_simple_apply_root hA hzero]
  exact R.coxeterHom_apply_root_mem_posRootCone hA hzero hneg h

section CharZero

variable [CharZero K]

include hneg in
/-- **The sign criterion.** Over a field of characteristic zero, `w αᵢ` lies in the positive root
cone `Q₊` exactly when `i` is not a right descent of `w`. -/
theorem coxeterHom_apply_root_mem_posRootCone_iff
    (w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group) (i : I) :
    R.coxeterHom hA hzero w (R.root i) ∈ R.posRootCone ↔
      ¬(coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent w i := by
  refine ⟨fun hpos hd ↦ ?_, R.coxeterHom_apply_root_mem_posRootCone hA hzero hneg⟩
  have h0 := R.isPointed_posRootCone _ hpos
    (R.neg_coxeterHom_apply_root_mem_posRootCone hA hzero hneg hd)
  rw [LinearEquiv.map_eq_zero_iff] at h0
  exact R.root_linearIndependent.ne_zero i h0

include hneg in
/-- **The sign criterion.** Over a field of characteristic zero, `w αᵢ` lies in `-Q₊` exactly when
`i` is a right descent of `w`. -/
theorem neg_coxeterHom_apply_root_mem_posRootCone_iff
    (w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group) (i : I) :
    -R.coxeterHom hA hzero w (R.root i) ∈ R.posRootCone ↔
      (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent w i := by
  rw [← R.coxeterHom_mul_simple_apply_root hA hzero, R.coxeterHom_apply_root_mem_posRootCone_iff hA
    hzero hneg, ← CoxeterMatrix.toCoxeterSystem_simple,
    ← CoxeterSystem.isRightDescent_iff_not_isRightDescent_mul]

include hneg in
/-- **The Coxeter group acts faithfully on the simple roots.** Over a field of characteristic zero,
an element of the Coxeter group fixing every simple root is trivial. -/
theorem eq_one_of_forall_coxeterHom_apply_root_eq
    {w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group}
    (hw : ∀ i, R.coxeterHom hA hzero w (R.root i) = R.root i) : w = 1 := by
  by_contra hw₁
  obtain ⟨i, hi⟩ :=
    (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.exists_rightDescent_of_ne_one hw₁
  have hneg' := R.neg_coxeterHom_apply_root_mem_posRootCone hA hzero hneg hi
  rw [hw] at hneg'
  exact R.root_linearIndependent.ne_zero i
    (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) hneg')

include hneg in
/-- **The homomorphism from the Coxeter group to the Weyl group is injective.** Over a field of
characteristic zero, the Coxeter group of `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A` acts
faithfully on `H*` through the simple reflections. -/
theorem coxeterHom_injective : Function.Injective (R.coxeterHom hA hzero) :=
  (injective_iff_map_eq_one _).mpr fun _ hw ↦
    R.eq_one_of_forall_coxeterHom_apply_root_eq hA hzero hneg fun i ↦ by rw [hw]; rfl

/-! ### The Weyl group as a Coxeter system -/

/-- **The Weyl group is a Coxeter system.** Over a field of characteristic zero, the Weyl group of
a realization of a generalized Cartan matrix `A`, with the simple reflections, is a Coxeter system
for the Coxeter matrix `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A`: it is the image of the
Coxeter group under the injective homomorphism `TauCeti.CartanRealization.coxeterHom`. -/
noncomputable def weylCoxeterSystem :
    CoxeterSystem (coxeterMatrixOfGeneralizedCartanMatrix A) (R.weylGroup hA) :=
  (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.map
    ((MonoidHom.ofInjective (R.coxeterHom_injective hA hzero hneg)).trans
      (MulEquiv.subgroupCongr (R.range_coxeterHom hA hzero)))

/-- The isomorphism from the Coxeter group to the Weyl group underlying
`TauCeti.CartanRealization.weylCoxeterSystem` is `TauCeti.CartanRealization.coxeterHom`. -/
@[simp]
theorem coe_weylCoxeterSystem_mulEquiv_symm_apply
    (w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group) :
    ((R.weylCoxeterSystem hA hzero hneg).mulEquiv.symm w : Dual K H ≃ₗ[K] Dual K H) =
      R.coxeterHom hA hzero w := by
  simp [weylCoxeterSystem, CoxeterMatrix.toCoxeterSystem, MonoidHom.ofInjective_apply]

/-- The simple reflections of the Coxeter system of the Weyl group are the simple reflections
`sᵢ λ = λ - λ(hᵢ) αᵢ`. -/
@[simp]
theorem coe_weylCoxeterSystem_simple (i : I) :
    ((R.weylCoxeterSystem hA hzero hneg).simple i : Dual K H ≃ₗ[K] Dual K H) =
      R.simpleReflection hA i := by
  rw [← CoxeterSystem.mulEquiv_symm_simple, coe_weylCoxeterSystem_mulEquiv_symm_apply,
    coxeterHom_simple]

/-- The length of an element of the Weyl group in the simple reflections is the length of the
corresponding element of the Coxeter group. -/
@[simp]
theorem length_weylCoxeterSystem_mulEquiv_symm_apply
    (w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group) :
    (R.weylCoxeterSystem hA hzero hneg).length
        ((R.weylCoxeterSystem hA hzero hneg).mulEquiv.symm w) =
      (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.length w :=
  -- `weylCoxeterSystem` is `toCoxeterSystem.map e`, whose stored isomorphism has inverse `e` by
  -- definition of `CoxeterSystem.map`
  (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.length_map _ w

/-- **The descent criterion**: `ℓ(w sᵢ) < ℓ(w)` in the Weyl group exactly when `w αᵢ ∈ -Q₊`. -/
theorem weylCoxeterSystem_isRightDescent_iff (w : R.weylGroup hA) (i : I) :
    (R.weylCoxeterSystem hA hzero hneg).IsRightDescent w i ↔
      -(w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.posRootCone := by
  obtain ⟨g, rfl⟩ := (R.weylCoxeterSystem hA hzero hneg).mulEquiv.symm.surjective w
  rw [coe_weylCoxeterSystem_mulEquiv_symm_apply, R.neg_coxeterHom_apply_root_mem_posRootCone_iff hA
    hzero hneg]
  rw [CoxeterSystem.IsRightDescent, CoxeterSystem.IsRightDescent,
    ← CoxeterSystem.mulEquiv_symm_simple, ← map_mul, length_weylCoxeterSystem_mulEquiv_symm_apply,
    length_weylCoxeterSystem_mulEquiv_symm_apply, CoxeterMatrix.toCoxeterSystem_simple]

end CharZero

end CartanRealization

end TauCeti

/-! ### Examples -/

section Examples

open TauCeti CartanRealization

/-- Affine type `A₁⁽¹⁾`: over a field of characteristic zero the Coxeter group of the matrix,
the infinite dihedral group, acts faithfully on the dual of any realization. -/
example {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K)) H)
    (hA : ∀ i, (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K) i i = 2) :
    Function.Injective (R.coxeterHom hA (by simp [Fin.forall_fin_two])) :=
  R.coxeterHom_injective hA _ (by simp [Fin.forall_fin_two])

end Examples
