/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField

import TauCeti.NumberTheory.NumberField.FinitePlace

/-!
# Euclidean heights over number fields

This file defines the degree-normalized Euclidean height `height2` of a finite tuple over a
number field. At an infinite place it uses the Euclidean norm of the tuple, while at a finite
place it uses the maximum norm. The relative Arakelov height `arakelovMulHeight` is its
field-degree power, with the usual projective junk value one at the zero tuple.

The local formula and its normalization follow Evertse--Ferretti, where this Euclidean height is
used for Plücker coordinates of subspaces. The elementary API here records the zero convention,
reindexing, sign changes of coordinates, and the corresponding logarithmic and affine heights.
Over `ℚ`, the Euclidean height of a tuple of coprime integers is its Euclidean norm
(`TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one`), and for any tuple of integers it is the
Euclidean norm divided by the greatest common divisor of the entries
(`TauCeti.gcd_mul_height2_intCast`).

## Main definitions

* `TauCeti.height2`: the absolute Euclidean height of a tuple over a number field.
* `TauCeti.arakelovMulHeight`: the relative Euclidean projective height.
* `TauCeti.arakelovLogHeight`: the logarithm of the relative Euclidean projective height.
* `TauCeti.arakelovMulHeightAff`: the relative affine Euclidean height of a finite tuple.
* `TauCeti.arakelovLogHeightAff`: its logarithm.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §6.1 and §6.3.

`TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one` is adapted from Ralf Stephan's
`NumberField.arakelovMulHeight_intCast_of_gcd_eq_one` in `ArithmeticHeights/RationalLattice.lean`
of [`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/9894a1c4baf805296b249e95575f0e16e8e1afa3/ArithmeticHeights/RationalLattice.lean),
commit `9894a1c4baf805296b249e95575f0e16e8e1afa3` (Apache 2.0), and
`TauCeti.gcd_mul_height2_intCast` from his `NumberField.gcd_mul_arakelovMulHeight_intCast` in
`ArithmeticHeights/BombieriVaaler.lean` of the same repository at
[commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`](https://github.com/rwst/Subspace-Theorems/blob/09835cb23557ae5ae0cf55a9c4ab9055f5d60338/ArithmeticHeights/BombieriVaaler.lean).
-/

public noncomputable section

open scoped BigOperators
open Function Module NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

-- The elementary arguments below follow Mathlib's `Height.mulHeight`, notably
-- `Height.mulHeight_smul_eq_mulHeight` and `Height.one_le_mulHeight`.

/-- The degree-normalized Euclidean height of a finite tuple over a number field. It uses the
Euclidean norm at infinite places and the maximum norm at finite places. In particular, its
value at the zero tuple is zero. -/
def height2 {ι : Type*} [Finite ι] (y : ι → K) : ℝ :=
  letI := Fintype.ofFinite ι
  (∏ w : InfinitePlace K,
      (∑ i, ‖w.embedding (y i)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ K))) *
    ∏ᶠ v : FinitePlace K, (⨆ i, v (y i)) ^ ((1 : ℝ) / finrank ℚ K)

/-- The local formula defining the Euclidean height. -/
theorem height2_eq {ι : Type*} [Finite ι] (y : ι → K) :
    height2 y =
      letI := Fintype.ofFinite ι
      (∏ w : InfinitePlace K,
          (∑ i, ‖w.embedding (y i)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ K))) *
        ∏ᶠ v : FinitePlace K, (⨆ i, v (y i)) ^ ((1 : ℝ) / finrank ℚ K) :=
  (rfl)

/-- The Euclidean height is nonnegative. -/
theorem height2_nonneg {ι : Type*} [Finite ι] (y : ι → K) : 0 ≤ height2 y := by
  let _ := Fintype.ofFinite ι
  apply mul_nonneg
  · exact Finset.prod_nonneg fun _ _ ↦
      Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) _
  · exact finprod_nonneg fun _ ↦ Real.rpow_nonneg (Real.iSup_nonneg_of_nonnegHomClass _ _) _

/-- The Euclidean height of the zero tuple is zero. -/
@[simp]
theorem height2_zero {ι : Type*} [Finite ι] : height2 (0 : ι → K) = 0 := by
  let _ := Fintype.ofFinite ι
  let w : InfinitePlace K := Classical.choice inferInstance
  have hD : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have hw : (w.mult : ℝ) / (2 * finrank ℚ K) ≠ 0 :=
    div_ne_zero InfinitePlace.mult_coe_ne_zero (mul_ne_zero two_ne_zero hD)
  have hprod :
      ∏ v : InfinitePlace K, (∑ i : ι, ‖v.embedding ((0 : ι → K) i)‖ ^ 2) ^
        ((v.mult : ℝ) / (2 * finrank ℚ K)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    simp [Real.zero_rpow hw]
  rw [height2, hprod, zero_mul]

/-- The Euclidean height is unchanged by a bijective reindexing of the coordinates. -/
@[simp]
theorem height2_comp_equiv {ι ι' : Type*} [Finite ι] [Finite ι'] (e : ι ≃ ι')
    (y : ι' → K) : height2 (y ∘ e) = height2 y := by
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite ι'
  simp only [height2, comp_apply]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    exact congrArg (fun z : ℝ ↦ z ^ ((w.mult : ℝ) / (2 * finrank ℚ K)))
      (e.sum_comp fun i ↦ ‖w.embedding (y i)‖ ^ 2)
  · apply finprod_congr
    intro v
    exact congrArg (fun z : ℝ ↦ z ^ ((1 : ℝ) / finrank ℚ K))
      (e.iSup_comp (g := fun i ↦ v (y i)))

open Classical in
/-- The relative Euclidean projective height. It is the field-degree power of `height2` away
from zero, and has the projective junk value one at the zero tuple. -/
def arakelovMulHeight {ι : Type*} [Finite ι] (y : ι → K) : ℝ :=
  if y = 0 then 1 else height2 y ^ finrank ℚ K

/-- The relative logarithmic Euclidean projective height. -/
def arakelovLogHeight {ι : Type*} [Finite ι] (y : ι → K) : ℝ :=
  Real.log (arakelovMulHeight y)

/-- The relative affine Euclidean height of a finite tuple, obtained by adjoining the coordinate
one. -/
def arakelovMulHeightAff {ι : Type*} [Finite ι] (x : ι → K) : ℝ :=
  arakelovMulHeight fun o : Option ι ↦ o.elim 1 x

/-- The affine height is the projective height of the tuple with the coordinate one adjoined. -/
theorem arakelovMulHeightAff_def {ι : Type*} [Finite ι] (x : ι → K) :
    arakelovMulHeightAff x = arakelovMulHeight fun o : Option ι ↦ o.elim 1 x :=
  (rfl)

/-- The relative logarithmic affine Euclidean height of a finite tuple. -/
def arakelovLogHeightAff {ι : Type*} [Finite ι] (x : ι → K) : ℝ :=
  Real.log (arakelovMulHeightAff x)

/-- The relative Euclidean projective height assigns its junk value one to the zero tuple. -/
@[simp]
theorem arakelovMulHeight_zero {ι : Type*} [Finite ι] :
    arakelovMulHeight (0 : ι → K) = 1 := by
  simp [arakelovMulHeight]

/-- Away from zero, the relative height is the field-degree power of `height2`. -/
theorem arakelovMulHeight_of_ne_zero {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    arakelovMulHeight y = height2 y ^ finrank ℚ K := by
  simp [arakelovMulHeight, hy]

/-- The relative Euclidean projective height is nonnegative. -/
theorem arakelovMulHeight_nonneg {ι : Type*} [Finite ι] (y : ι → K) :
    0 ≤ arakelovMulHeight y := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [arakelovMulHeight_of_ne_zero hy]
    exact pow_nonneg (height2_nonneg y) _

/-- The local formula for the relative Euclidean projective height of a nonzero tuple. The
degree power removes the normalizing field-degree roots from `height2`. -/
theorem arakelovMulHeight_eq {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    arakelovMulHeight y =
      letI := Fintype.ofFinite ι
      (∏ w : InfinitePlace K,
        (∑ i, ‖w.embedding (y i)‖ ^ 2) ^ ((w.mult : ℝ) / 2)) *
      ∏ᶠ v : FinitePlace K, ⨆ i, v (y i) := by
  let _ := Fintype.ofFinite ι
  rw [arakelovMulHeight_of_ne_zero hy, height2, mul_pow,
    ← Finset.prod_pow Finset.univ]
  have hD : finrank ℚ K ≠ 0 := finrank_pos.ne'
  have hrpow :
      (fun v : FinitePlace K ↦ (⨆ i, v (y i)) ^ ((1 : ℝ) / finrank ℚ K)).HasFiniteMulSupport :=
    (NumberField.FinitePlace.hasFiniteMulSupport_iSup hy).comp
      (g := fun z : ℝ ↦ z ^ ((1 : ℝ) / finrank ℚ K)) (by simp)
  rw [finprod_pow hrpow]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    rw [← Real.rpow_mul_natCast (Finset.sum_nonneg fun _ _ ↦ by positivity)]
    congr 1
    field_simp
  · apply finprod_congr
    intro v
    simpa [one_div] using Real.rpow_inv_natCast_pow
      (Real.iSup_nonneg_of_nonnegHomClass v _) hD

/-- For a nonzero integral tuple, multiplying its relative Euclidean height by the norm of
its coordinate ideal leaves precisely the archimedean Euclidean factors. -/
theorem arakelovMulHeight_mul_absNorm_span_range {ι : Type*} [Finite ι]
    {y : ι → 𝓞 K} (hy : y ≠ 0) :
    arakelovMulHeight (fun i ↦ (y i : K)) * (Ideal.span (Set.range y)).absNorm =
      letI := Fintype.ofFinite ι
      ∏ w : InfinitePlace K, (∑ i, ‖w.embedding (y i)‖ ^ 2) ^ ((w.mult : ℝ) / 2) := by
  have hy' : (fun i ↦ (y i : K)) ≠ 0 := by
    contrapose hy
    ext i
    exact congrFun hy i
  rw [arakelovMulHeight_eq hy', mul_assoc, mul_comm (∏ᶠ _, _),
    NumberField.absNorm_mul_finprod_finitePlace_eq_one hy, mul_one]

/-- Multiplication by a nonzero number-field scalar preserves the relative Euclidean projective
height. -/
@[simp]
theorem arakelovMulHeight_smul {ι : Type*} [Finite ι] (y : ι → K) {c : K} (hc : c ≠ 0) :
    arakelovMulHeight (c • y) = arakelovMulHeight y := by
  let _ := Fintype.ofFinite ι
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hcy : c • y ≠ 0 := by simp [hc, hy]
  rw [arakelovMulHeight_eq hcy, arakelovMulHeight_eq hy]
  have hinf (w : InfinitePlace K) :
      (∑ i, ‖w.embedding ((c • y) i)‖ ^ 2) ^ ((w.mult : ℝ) / 2) =
        w c ^ w.mult * (∑ i, ‖w.embedding (y i)‖ ^ 2) ^ ((w.mult : ℝ) / 2) := by
    have hsum : ∑ i, ‖w.embedding ((c • y) i)‖ ^ 2 =
        ‖w.embedding c‖ ^ 2 * ∑ i, ‖w.embedding (y i)‖ ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum, Real.mul_rpow (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ by positivity)]
    congr 1
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _),
      Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero, Real.rpow_natCast,
      InfinitePlace.norm_embedding_eq]
  have hfin (v : FinitePlace K) :
      (⨆ i, v ((c • y) i)) = v c * ⨆ i, v (y i) := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact (Real.mul_iSup_of_nonneg (v.val.nonneg c) fun i ↦ v (y i)).symm
  simp_rw [hinf, hfin]
  rw [Finset.prod_mul_distrib,
    finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hc)
      (NumberField.FinitePlace.hasFiniteMulSupport_iSup hy),
    mul_mul_mul_comm, NumberField.prod_abs_eq_one hc, one_mul]

/-- The relative Euclidean projective height is at least one. -/
theorem one_le_arakelovMulHeight {ι : Type*} [Finite ι] (y : ι → K) :
    1 ≤ arakelovMulHeight y := by
  let _ := Fintype.ofFinite ι
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  have hi' : y i ≠ 0 := by simpa using hi
  have hscaled : (y i)⁻¹ • y ≠ 0 := by simp [hi', hy]
  rw [← arakelovMulHeight_smul y (inv_ne_zero hi'), arakelovMulHeight_eq hscaled]
  apply one_le_mul_of_one_le_of_one_le
  · apply Finset.one_le_prod₀
    intro w _
    apply Real.one_le_rpow
    · calc
        1 = ‖w.embedding (((y i)⁻¹ • y) i)‖ ^ 2 := by
          simp [inv_mul_cancel₀ hi']
        _ ≤ ∑ j, ‖w.embedding (((y i)⁻¹ • y) j)‖ ^ 2 :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun j ↦ ‖w.embedding (((y i)⁻¹ • y) j)‖ ^ 2)
            (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)
    · positivity
  · apply one_le_finprod
    intro v
    refine Finite.le_ciSup_of_le i ?_
    simp [inv_mul_cancel₀ hi']

/-- The relative Euclidean projective height is positive. -/
theorem arakelovMulHeight_pos {ι : Type*} [Finite ι] (y : ι → K) :
    0 < arakelovMulHeight y :=
  zero_lt_one.trans_le (one_le_arakelovMulHeight y)

/-- The relative Euclidean projective height is nonzero. -/
theorem arakelovMulHeight_ne_zero {ι : Type*} [Finite ι] (y : ι → K) :
    arakelovMulHeight y ≠ 0 :=
  (arakelovMulHeight_pos y).ne'

open Classical in
/-- Taking the field-degree root recovers `height2` away from zero and preserves the projective
junk value at zero. -/
theorem arakelovMulHeight_eq_height2 {ι : Type*} [Finite ι] (y : ι → K) :
    arakelovMulHeight y ^ ((1 : ℝ) / finrank ℚ K) = if y = 0 then 1 else height2 y := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [ite_eq_right hy, arakelovMulHeight_of_ne_zero hy, ← Real.rpow_natCast,
      ← Real.rpow_mul (height2_nonneg y)]
    have hD : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
    rw [mul_div_cancel₀ _ hD, Real.rpow_one]

/-- A nonzero tuple has Euclidean height at least one. -/
theorem one_le_height2_of_ne_zero {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    1 ≤ height2 y := by
  have hroot := arakelovMulHeight_eq_height2 y
  rw [ite_eq_right hy] at hroot
  rw [← hroot]
  exact Real.one_le_rpow (one_le_arakelovMulHeight y) (by positivity)

/-- The Euclidean height of a nonzero tuple is positive. -/
theorem height2_pos {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    0 < height2 y :=
  zero_lt_one.trans_le (one_le_height2_of_ne_zero hy)

/-- The Euclidean height vanishes exactly on the zero tuple. -/
@[simp]
theorem height2_eq_zero_iff {ι : Type*} [Finite ι] {y : ι → K} :
    height2 y = 0 ↔ y = 0 := by
  constructor
  · intro h
    by_contra hy
    exact (height2_pos hy).ne' h
  · rintro rfl
    exact height2_zero

/-- Multiplication by a nonzero number-field scalar preserves the degree-normalized Euclidean
height. -/
@[simp]
theorem height2_smul {ι : Type*} [Finite ι] (y : ι → K) {c : K} (hc : c ≠ 0) :
    height2 (c • y) = height2 y := by
  classical
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hcy : c • y ≠ 0 := by simp [hc, hy]
  have h := congrArg (fun z : ℝ ↦ z ^ ((1 : ℝ) / finrank ℚ K))
    (arakelovMulHeight_smul y hc)
  rw [arakelovMulHeight_eq_height2, arakelovMulHeight_eq_height2] at h
  simpa [hy, hcy] using h

/-- The relative Euclidean projective height is unchanged by a bijective reindexing of the
coordinates. -/
@[simp]
theorem arakelovMulHeight_comp_equiv {ι ι' : Type*} [Finite ι] [Finite ι'] (e : ι ≃ ι')
    (y : ι' → K) : arakelovMulHeight (y ∘ e) = arakelovMulHeight y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hye : y ∘ e ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      exact Function.ne_iff.mpr ⟨e.symm i, by simpa using hi⟩
    rw [arakelovMulHeight_of_ne_zero hye, arakelovMulHeight_of_ne_zero hy,
      height2_comp_equiv]

/-- The Euclidean height is unchanged by changing the signs of some coordinates. -/
theorem height2_eq_of_forall_eq_or_eq_neg {ι : Type*} [Finite ι] {x y : ι → K}
    (h : ∀ i, y i = x i ∨ y i = -x i) : height2 y = height2 x := by
  let _ := Fintype.ofFinite ι
  simp only [height2]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by rcases h i with h | h <;> simp [h]
  · refine finprod_congr fun v ↦ ?_
    congr 1
    exact iSup_congr fun i ↦ by rcases h i with h | h <;> simp [h]

/-- The relative Euclidean projective height is unchanged by changing the signs of some
coordinates. -/
theorem arakelovMulHeight_eq_of_forall_eq_or_eq_neg {ι : Type*} [Finite ι] {x y : ι → K}
    (h : ∀ i, y i = x i ∨ y i = -x i) : arakelovMulHeight y = arakelovMulHeight x := by
  have hy : y = 0 ↔ x = 0 := by
    simp only [funext_iff, Pi.zero_apply]
    exact forall_congr' fun i ↦ by rcases h i with h | h <;> simp [h]
  rcases eq_or_ne x 0 with hx | hx
  · rw [hy.2 hx, hx]
  · rw [arakelovMulHeight_of_ne_zero hx, arakelovMulHeight_of_ne_zero (hy.not.2 hx),
      height2_eq_of_forall_eq_or_eq_neg h]

/-- The logarithmic projective height of the zero tuple is zero. -/
@[simp]
theorem arakelovLogHeight_zero {ι : Type*} [Finite ι] :
    arakelovLogHeight (0 : ι → K) = 0 := by
  simp [arakelovLogHeight]

/-- The multiplicative and logarithmic relative Euclidean heights agree by definition. -/
theorem arakelovLogHeight_eq_log_arakelovMulHeight {ι : Type*} [Finite ι] (y : ι → K) :
    arakelovLogHeight y = Real.log (arakelovMulHeight y) := (rfl)

/-- The relative logarithmic Euclidean height is nonnegative. -/
theorem arakelovLogHeight_nonneg {ι : Type*} [Finite ι] (y : ι → K) :
    0 ≤ arakelovLogHeight y :=
  Real.log_nonneg (one_le_arakelovMulHeight y)

/-- The relative logarithmic Euclidean height is invariant under nonzero scalar multiplication. -/
@[simp]
theorem arakelovLogHeight_smul {ι : Type*} [Finite ι] (y : ι → K) {c : K} (hc : c ≠ 0) :
    arakelovLogHeight (c • y) = arakelovLogHeight y := by
  simp [arakelovLogHeight, hc]

/-- The relative logarithmic height is unchanged by a bijective reindexing. -/
@[simp]
theorem arakelovLogHeight_comp_equiv {ι ι' : Type*} [Finite ι] [Finite ι'] (e : ι ≃ ι')
    (y : ι' → K) : arakelovLogHeight (y ∘ e) = arakelovLogHeight y := by
  simp [arakelovLogHeight]

/-- The logarithmic projective height is unchanged by changing the signs of some coordinates. -/
theorem arakelovLogHeight_eq_of_forall_eq_or_eq_neg {ι : Type*} [Finite ι] {x y : ι → K}
    (h : ∀ i, y i = x i ∨ y i = -x i) : arakelovLogHeight y = arakelovLogHeight x := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovLogHeight_eq_log_arakelovMulHeight,
    arakelovMulHeight_eq_of_forall_eq_or_eq_neg h]

/-- The affine multiplicative and logarithmic heights agree by definition. -/
theorem arakelovLogHeightAff_eq_log_arakelovMulHeightAff {ι : Type*} [Finite ι] (x : ι → K) :
    arakelovLogHeightAff x = Real.log (arakelovMulHeightAff x) := (rfl)

/-- The relative affine Euclidean height is at least one. -/
theorem one_le_arakelovMulHeightAff {ι : Type*} [Finite ι] (x : ι → K) :
    1 ≤ arakelovMulHeightAff x :=
  one_le_arakelovMulHeight _

/-- The relative logarithmic affine Euclidean height is nonnegative. -/
theorem arakelovLogHeightAff_nonneg {ι : Type*} [Finite ι] (x : ι → K) :
    0 ≤ arakelovLogHeightAff x :=
  Real.log_nonneg (one_le_arakelovMulHeightAff x)

/-- The relative affine Euclidean height is unchanged by a bijective reindexing. -/
@[simp]
theorem arakelovMulHeightAff_comp_equiv {ι ι' : Type*} [Finite ι] [Finite ι']
    (e : ι ≃ ι') (x : ι' → K) :
    arakelovMulHeightAff (x ∘ e) = arakelovMulHeightAff x := by
  let e' := Equiv.optionCongr e
  have h : (fun o : Option ι ↦ o.elim 1 (x ∘ e)) =
      (fun o : Option ι' ↦ o.elim 1 x) ∘ e' := by
    ext o
    cases o <;> rfl
  rw [arakelovMulHeightAff, arakelovMulHeightAff, h, arakelovMulHeight_comp_equiv]

/-- The relative logarithmic affine Euclidean height is unchanged by a bijective reindexing. -/
@[simp]
theorem arakelovLogHeightAff_comp_equiv {ι ι' : Type*} [Finite ι] [Finite ι']
    (e : ι ≃ ι') (x : ι' → K) :
    arakelovLogHeightAff (x ∘ e) = arakelovLogHeightAff x := by
  simp [arakelovLogHeightAff]

/-- The affine height of the zero tuple is one because the adjoined coordinate is one. -/
@[simp]
theorem arakelovMulHeightAff_zero {ι : Type*} [Finite ι] :
    arakelovMulHeightAff (0 : ι → K) = 1 := by
  have hy : (fun o : Option ι ↦ o.elim 1 (0 : ι → K)) ≠ 0 := by
    intro h
    simpa using congrFun h none
  rw [arakelovMulHeightAff, arakelovMulHeight_eq hy]
  have hfin (v : FinitePlace K) :
      ⨆ o : Option ι, v (o.elim 1 (0 : ι → K)) = 1 := by
    apply le_antisymm
    · refine ciSup_le fun o ↦ ?_
      cases o <;> simp
    · exact Finite.le_ciSup_of_le none (by simp)
  simp_rw [hfin]
  rw [finprod_one, mul_one]
  apply Finset.prod_eq_one
  intro w _
  rw [Finset.sum_eq_single none]
  · simp
  · intro o _ ho
    cases o with
    | none => exact (ho rfl).elim
    | some i => simp
  · simp

/-- The logarithmic affine height of the zero tuple is zero. -/
@[simp]
theorem arakelovLogHeightAff_zero {ι : Type*} [Finite ι] :
    arakelovLogHeightAff (0 : ι → K) = 0 := by
  simp [arakelovLogHeightAff]

/-- Over `ℚ`, the Euclidean height of a tuple of coprime integers is its Euclidean norm: the finite
places do not contribute. This is the Euclidean analogue of Mathlib's
`Rat.mulHeight_eq_max_abs_of_gcd_eq_one`. -/
theorem height2_intCast_eq_sqrt_of_gcd_eq_one {ι : Type*} [Fintype ι] {x : ι → ℤ}
    (hx : Finset.univ.gcd x = 1) :
    height2 (((↑) : ℤ → ℚ) ∘ x) = √(∑ i, (x i : ℝ) ^ 2) := by
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hx
  have hw : (default : InfinitePlace ℚ).IsReal := by
    rw [Subsingleton.elim default Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
  rw [height2_eq, finprod_eq_one_of_forall_eq_one fun v ↦ by
    rw [Function.comp_def, Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one v hx, Real.one_rpow]]
  simp only [Finset.univ_unique, comp_apply, map_intCast, Complex.norm_intCast, sq_abs,
    finrank_self, Nat.cast_one, mul_one, Finset.prod_singleton, InfinitePlace.mult, hw, ite_true,
    one_div, Real.sqrt_eq_rpow]
  -- The two sides differ only in the `Fintype` instance on `ι` used to form the sums.
  convert rfl

/-- Over `ℚ`, the Euclidean height of a tuple of integers, multiplied by the greatest common divisor
of its entries, is its Euclidean norm. Both sides vanish for the zero tuple. This is the Euclidean
analogue of the sup-norm statement that the height of an integer tuple is its largest absolute value
divided by the greatest common divisor of its entries. -/
theorem gcd_mul_height2_intCast {ι : Type*} [Fintype ι] (x : ι → ℤ) :
    ((Finset.univ.gcd x : ℤ) : ℝ) * height2 (((↑) : ℤ → ℚ) ∘ x) = √(∑ i, (x i : ℝ) ^ 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Finset.gcd_eq_zero_iff.mpr]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  -- Write `x = g • y` with `g = gcd(x) ≠ 0` and `gcd(y) = 1`.
  obtain ⟨y, hxy, hy⟩ := Finset.univ.extract_gcd x ⟨i₀, Finset.mem_univ _⟩
  have hg : Finset.univ.gcd x ≠ 0 := fun h ↦
    hi₀ (Finset.gcd_eq_zero_iff.mp h i₀ (Finset.mem_univ _))
  have hcast : ((↑) : ℤ → ℚ) ∘ x = ((Finset.univ.gcd x : ℤ) : ℚ) • (((↑) : ℤ → ℚ) ∘ y) := by
    ext i
    simp [hxy i (Finset.mem_univ i)]
  have hnn : (0 : ℝ) ≤ (Finset.univ.gcd x : ℤ) := mod_cast Finset.Int.finsetGcd_nonneg
  rw [hcast, height2_smul _ (Int.cast_ne_zero.mpr hg), height2_intCast_eq_sqrt_of_gcd_eq_one hy,
    ← Real.sqrt_sq hnn, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
  simp_rw [hxy _ (Finset.mem_univ _), Int.cast_mul, mul_pow]

end TauCeti
