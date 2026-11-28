/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Weighted
public import TauCeti.Analysis.InnerProductSpace.Gram.Integral
public import TauCeti.NumberTheory.NumberField.Quadratic.EmbeddingBound
import Mathlib.Analysis.InnerProductSpace.Basic
import TauCeti.Analysis.Complex.Sqrt

/-!
# Euclidean realizations and integer Gram matrices for `ℤ[√d]`-families

A tuple `v : κ → QuadraticAlgebra ℤ d 0` maps `ℤ`-linearly into `EuclideanSpace ℝ (κ × Fin 2)`
via `QuadraticAlgebra.famToLp d κ`, defined as the composition of integer coordinate extraction
`QuadraticAlgebra.famCoords d κ` with `TauCeti.weightedToLp (QuadraticAlgebra.famWeight d κ)`
(scaling the real part by `√2` and the imaginary part by `√(2 * |d|)`). This map is injective
whenever `d ≠ 0` (`QuadraticAlgebra.famToLp_injective`). Its real inner product recovers the
weighted Euclidean integer Gram pairing
`QuadraticAlgebra.intGram d v i j =`
`∑ k, 2 * ((v i k).re * (v j k).re + |d| * (v i k).im * (v j k).im)`, and its squared Euclidean
norm equals the sum over `k` of `‖σ₊ (v k)‖ ^ 2 + ‖σ₋ (v k)‖ ^ 2`, where
`σ₊ = QuadraticAlgebra.sqrtEmbedding (d : ℚ)` and `σ₋ = QuadraticAlgebra.negSqrtEmbedding (d : ℚ)`
evaluated via `algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ))`.

## Main results

* `QuadraticAlgebra.famCoords`, `QuadraticAlgebra.famWeight`: bundled `ℤ`-linear coordinate
  equivalence and real weights.
* `QuadraticAlgebra.famWeight_pos`: positivity of `QuadraticAlgebra.famWeight` when `d ≠ 0`.
* `QuadraticAlgebra.famToLp`: bundled `ℤ`-linear Euclidean realization
  `(κ → QuadraticAlgebra ℤ d 0) →ₗ[ℤ] EuclideanSpace ℝ (κ × Fin 2)`.
* `QuadraticAlgebra.famToLp_injective`: injectivity of `QuadraticAlgebra.famToLp` when `d ≠ 0`.
* `QuadraticAlgebra.famToLp_eq_weightedToLp`, `QuadraticAlgebra.famToLp_apply`: explicit
  factorization through `TauCeti.weightedToLp`.
* `QuadraticAlgebra.famToLp_ofLp_zero`, `QuadraticAlgebra.famToLp_ofLp_one`: coordinate
  evaluations.
* `QuadraticAlgebra.inner_famToLp`, `QuadraticAlgebra.norm_sq_famToLp`: inner product and
  squared norm formulas.
* `QuadraticAlgebra.intGram`, `QuadraticAlgebra.mul_dvd_intGram`,
  `QuadraticAlgebra.map_intGram_eq_gram`, `QuadraticAlgebra.intCast_det_intGram`: integer Gram
  matrix of a finite family in `(QuadraticAlgebra ℤ d 0) ^ κ`, entry divisibility from pointwise
  scalar divisors, and agreement with `Matrix.gram ℝ`.
-/

public section

open scoped InnerProductSpace

namespace QuadraticAlgebra

/-- Bundled `ℤ`-linear coordinate equivalence
`(κ → QuadraticAlgebra ℤ d 0) ≃ₗ[ℤ] (κ × Fin 2 → ℤ)`, sending `v` to `(k, 0) ↦ (v k).re` and
`(k, 1) ↦ (v k).im`, with inverse `f ↦ fun k ↦ ⟨f (k, 0), f (k, 1)⟩`. -/
def famCoords (d : ℤ) (κ : Type*) :
    (κ → QuadraticAlgebra ℤ d 0) ≃ₗ[ℤ] (κ × Fin 2 → ℤ) where
  toFun v p := if p.2 = 0 then (v p.1).re else (v p.1).im
  invFun f k := ⟨f (k, 0), f (k, 1)⟩
  left_inv v := by
    ext k <;> rfl
  right_inv f := by
    ext ⟨k, i⟩
    fin_cases i <;> rfl
  map_add' v w := by
    ext p
    by_cases h : p.2 = 0 <;> simp [h]
  map_smul' c v := by
    ext p
    by_cases h : p.2 = 0 <;> simp [h, zsmul_eq_mul]

/-- Real-part coordinate extraction of `QuadraticAlgebra.famCoords`. -/
@[simp]
theorem famCoords_zero (d : ℤ) {κ : Type*} (v : κ → QuadraticAlgebra ℤ d 0) (k : κ) :
    famCoords d κ v (k, 0) = (v k).re := by
  simp [famCoords]

/-- Imaginary-part coordinate extraction of `QuadraticAlgebra.famCoords`. -/
@[simp]
theorem famCoords_one (d : ℤ) {κ : Type*} (v : κ → QuadraticAlgebra ℤ d 0) (k : κ) :
    famCoords d κ v (k, 1) = (v k).im := by
  simp [famCoords]

/-- Reconstruction of a `QuadraticAlgebra ℤ d 0`-tuple from its coordinates under
`(QuadraticAlgebra.famCoords d κ).symm`. -/
@[simp]
theorem famCoords_symm_apply (d : ℤ) {κ : Type*} (f : κ × Fin 2 → ℤ) (k : κ) :
    (famCoords d κ).symm f k = ⟨f (k, 0), f (k, 1)⟩ := by
  simp [famCoords]

/-- Real coordinate weights for `QuadraticAlgebra.famToLp`: `2` on real-part coordinates `(k, 0)`
and `2 * |d|` on imaginary-part coordinates `(k, 1)`. -/
def famWeight (d : ℤ) (κ : Type*) (p : κ × Fin 2) : ℝ :=
  if p.2 = 0 then 2 else 2 * d.natAbs

/-- Nonnegativity of `QuadraticAlgebra.famWeight`. -/
theorem famWeight_nonneg (d : ℤ) (κ : Type*) (p : κ × Fin 2) : 0 ≤ famWeight d κ p := by
  dsimp [famWeight]
  split_ifs <;> positivity

/-- Positivity of `QuadraticAlgebra.famWeight` whenever `d ≠ 0`. -/
theorem famWeight_pos {d : ℤ} (hd : d ≠ 0) (κ : Type*) (p : κ × Fin 2) :
    0 < famWeight d κ p := by
  dsimp [famWeight]
  split_ifs
  · positivity
  · have : (0 : ℝ) < d.natAbs := Nat.cast_pos.mpr (Int.natAbs_pos.mpr hd)
    positivity

/-- Weight `2` on real-part coordinates `(k, 0)` in `QuadraticAlgebra.famWeight`. -/
@[simp]
theorem famWeight_zero (d : ℤ) {κ : Type*} (k : κ) : famWeight d κ (k, 0) = 2 := by
  simp [famWeight]

/-- Weight `2 * |d|` on imaginary-part coordinates `(k, 1)` in `QuadraticAlgebra.famWeight`. -/
@[simp]
theorem famWeight_one (d : ℤ) {κ : Type*} (k : κ) :
    famWeight d κ (k, 1) = 2 * d.natAbs := by
  simp [famWeight]

/-- Bundled `ℤ`-linear Euclidean realization of a tuple in `(QuadraticAlgebra ℤ d 0) ^ κ` whose
real inner product recovers the weighted Euclidean pairing
`∑ k, 2 * (re₁ * re₂ + |d| * im₁ * im₂)`. -/
noncomputable def famToLp (d : ℤ) (κ : Type*) :
    (κ → QuadraticAlgebra ℤ d 0) →ₗ[ℤ] EuclideanSpace ℝ (κ × Fin 2) :=
  (TauCeti.weightedToLp (famWeight d κ)).comp (famCoords d κ).toLinearMap

/-- Relation between `QuadraticAlgebra.famToLp` and `TauCeti.weightedToLp`. -/
theorem famToLp_eq_weightedToLp (d : ℤ) (κ : Type*) :
    famToLp d κ = (TauCeti.weightedToLp (famWeight d κ)).comp (famCoords d κ).toLinearMap := by
  rfl

/-- Applying `QuadraticAlgebra.famToLp` evaluates `TauCeti.weightedToLp` on
`QuadraticAlgebra.famCoords`. -/
theorem famToLp_apply (d : ℤ) {κ : Type*} (v : κ → QuadraticAlgebra ℤ d 0) :
    famToLp d κ v = TauCeti.weightedToLp (famWeight d κ) (famCoords d κ v) := by
  rfl

/-- `QuadraticAlgebra.famToLp d κ` is injective whenever `d ≠ 0`. -/
theorem famToLp_injective {d : ℤ} (hd : d ≠ 0) (κ : Type*) :
    Function.Injective (famToLp d κ) :=
  (TauCeti.weightedToLp_injective (famWeight_pos hd κ)).comp (famCoords d κ).injective

/-- Real-part coordinate evaluation of `QuadraticAlgebra.famToLp`. -/
@[simp]
theorem famToLp_ofLp_zero (d : ℤ) {κ : Type*} (v : κ → QuadraticAlgebra ℤ d 0) (k : κ) :
    (famToLp d κ v).ofLp (k, 0) = Real.sqrt 2 * (v k).re := by
  simp [famToLp_apply]

/-- Imaginary-part coordinate evaluation of `QuadraticAlgebra.famToLp`. -/
@[simp]
theorem famToLp_ofLp_one (d : ℤ) {κ : Type*} (v : κ → QuadraticAlgebra ℤ d 0) (k : κ) :
    (famToLp d κ v).ofLp (k, 1) = Real.sqrt (2 * d.natAbs) * (v k).im := by
  simp [famToLp_apply]

/-- Inner product of two `QuadraticAlgebra ℤ d 0`-tuple realizations in terms of coordinates. -/
theorem inner_famToLp (d : ℤ) {κ : Type*} [Fintype κ] (v w : κ → QuadraticAlgebra ℤ d 0) :
    ⟪famToLp d κ v, famToLp d κ w⟫_ℝ =
      ((∑ k : κ, 2 * ((v k).re * (w k).re + (d.natAbs : ℤ) * (v k).im * (w k).im) : ℤ) : ℝ) := by
  rw [famToLp_apply, famToLp_apply, TauCeti.inner_weightedToLp (famWeight_nonneg d κ),
    Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Fin.sum_univ_two]
  simp only [famWeight_zero, famWeight_one, famCoords_zero, famCoords_one, Nat.cast_natAbs,
    Int.cast_abs]
  ring

/-- Squared norm of a `QuadraticAlgebra ℤ d 0`-tuple realization in terms of
`QuadraticAlgebra.sqrtEmbedding` and `QuadraticAlgebra.negSqrtEmbedding`. -/
theorem norm_sq_famToLp (d : ℤ) {κ : Type*} [Fintype κ] (v : κ → QuadraticAlgebra ℤ d 0) :
    ‖famToLp d κ v‖ ^ 2 =
      ∑ k : κ,
        (‖sqrtEmbedding (d : ℚ)
            (algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ))
              (v k))‖ ^ 2 +
          ‖negSqrtEmbedding (d : ℚ)
            (algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ))
              (v k))‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_famToLp, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hpar := parallelogram_law_with_norm ℂ ((v k).re : ℂ) (((v k).im : ℂ) * Complex.sqrt d)
  have hsq : ‖Complex.sqrt (d : ℂ)‖ ^ 2 = (d.natAbs : ℝ) := by
    rw [Complex.norm_sqrt_intCast, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hpos :
      sqrtEmbedding (d : ℚ)
          (algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ)) (v k)) =
        ((v k).re : ℂ) + ((v k).im : ℂ) * Complex.sqrt d := by
    rw [sqrtEmbedding_apply, QuadraticAlgebra.Int.re_algebraMap (a := d) (b := 0),
      QuadraticAlgebra.Int.im_algebraMap (a := d) (b := 0)]
    simp only [Rat.cast_intCast]
  have hneg :
      negSqrtEmbedding (d : ℚ)
          (algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ)) (v k)) =
        ((v k).re : ℂ) - ((v k).im : ℂ) * Complex.sqrt d := by
    rw [negSqrtEmbedding_apply, QuadraticAlgebra.Int.re_algebraMap (a := d) (b := 0),
      QuadraticAlgebra.Int.im_algebraMap (a := d) (b := 0)]
    simp only [Rat.cast_intCast]
  rw [hpos, hneg, hpar, Complex.norm_intCast, Complex.norm_mul, Complex.norm_intCast, mul_pow,
    sq_abs, sq_abs, hsq]
  push_cast
  simp only [Nat.cast_natAbs, Int.cast_abs]
  ring

/-- Integer Gram matrix of a finite family of tuples in `(QuadraticAlgebra ℤ d 0) ^ κ` with
respect to the weighted Euclidean pairing `∑ k, 2 * (re₁ * re₂ + |d| * im₁ * im₂)`. -/
def intGram (d : ℤ) {κ ι : Type*} [Fintype κ] (v : ι → κ → QuadraticAlgebra ℤ d 0) :
    Matrix ι ι ℤ :=
  Matrix.of fun i j ↦
    ∑ k : κ, 2 * ((v i k).re * (v j k).re + (d.natAbs : ℤ) * (v i k).im * (v j k).im)

/-- Entry evaluation of `QuadraticAlgebra.intGram`. -/
@[simp]
theorem intGram_apply (d : ℤ) {κ ι : Type*} [Fintype κ] (v : ι → κ → QuadraticAlgebra ℤ d 0)
    (i j : ι) :
    intGram d v i j =
      ∑ k : κ, 2 * ((v i k).re * (v j k).re + (d.natAbs : ℤ) * (v i k).im * (v j k).im) := by
  rfl

/-- If integers `m` and `n` divide every entry of `v i` and `v j` in `QuadraticAlgebra ℤ d 0`,
respectively, then `m * n` divides the `(i, j)` entry of `QuadraticAlgebra.intGram d v`. -/
theorem mul_dvd_intGram (d : ℤ) {κ ι : Type*} [Fintype κ]
    {v : ι → κ → QuadraticAlgebra ℤ d 0} {i j : ι} {m n : ℤ}
    (hm : ∀ k, (m : QuadraticAlgebra ℤ d 0) ∣ v i k)
    (hn : ∀ k, (n : QuadraticAlgebra ℤ d 0) ∣ v j k) :
    m * n ∣ intGram d v i j := by
  rw [intGram_apply]
  refine Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_right ?_ 2
  have hm' : algebraMap ℤ (QuadraticAlgebra ℤ d 0) m ∣ v i k := by
    rw [eq_intCast]
    exact hm k
  have hn' : algebraMap ℤ (QuadraticAlgebra ℤ d 0) n ∣ v j k := by
    rw [eq_intCast]
    exact hn k
  obtain ⟨hm_re, hm_im⟩ := algebraMap_dvd_iff.mp hm'
  obtain ⟨hn_re, hn_im⟩ := algebraMap_dvd_iff.mp hn'
  exact dvd_add (mul_dvd_mul hm_re hn_re)
    (mul_dvd_mul (dvd_mul_of_dvd_right hm_im _) hn_im)

/-- Coercing `QuadraticAlgebra.intGram d v` to `ℝ` produces the Euclidean Gram matrix of
`famToLp d κ ∘ v`. -/
theorem map_intGram_eq_gram (d : ℤ) {κ ι : Type*} [Fintype κ]
    (v : ι → κ → QuadraticAlgebra ℤ d 0) :
    (intGram d v).map (Int.castRingHom ℝ) = Matrix.gram ℝ (fun i ↦ famToLp d κ (v i)) := by
  ext i j
  simp [Matrix.gram_apply, inner_famToLp]

/-- The integer determinant of `QuadraticAlgebra.intGram d v` agrees in `ℝ` with the real Gram
determinant of `famToLp d κ ∘ v`. -/
theorem intCast_det_intGram (d : ℤ) {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (v : ι → κ → QuadraticAlgebra ℤ d 0) :
    ((intGram d v).det : ℝ) = (Matrix.gram ℝ (fun i ↦ famToLp d κ (v i))).det :=
  Matrix.intCast_det_eq_det_gram (map_intGram_eq_gram d v)

end QuadraticAlgebra
