/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import TauCeti.NumberTheory.Zsqrtd.ComplexEmbedding
import TauCeti.Analysis.InnerProductSpace.Gram.Integral

/-!
# Euclidean realizations and integer Gram matrices for `ℤ√d`-families

A tuple `v : κ → ℤ√d` embeds `ℤ`-linearly into `EuclideanSpace ℝ (κ × Fin 2)` via
`Zsqrtd.famToLp d κ`, scaling the real part by `√2` and the imaginary part by `√(2 * |d|)`.
Its real inner product recovers the trace-type integer Gram pairing
`Zsqrtd.intGram d v i j = ∑ k, 2 * ((v i k).re * (v j k).re + |d| * (v i k).im * (v j k).im)`,
and its squared Euclidean norm equals `∑ k, (‖embPos d (v k)‖ ^ 2 + ‖embNeg d (v k)‖ ^ 2)`.

## Main results

* `Zsqrtd.famToLp`: bundled `ℤ`-linear Euclidean realization
  `(κ → ℤ√d) →ₗ[ℤ] EuclideanSpace ℝ (κ × Fin 2)`.
* `Zsqrtd.famToLp_ofLp_zero`, `Zsqrtd.famToLp_ofLp_one`: coordinate evaluations.
* `Zsqrtd.famToLp_sum_zsmul`: compatibility with `ℤ`-linear combinations.
* `Zsqrtd.inner_famToLp`, `Zsqrtd.norm_sq_famToLp`: inner product and squared norm formulas.
* `Zsqrtd.intGram`, `Zsqrtd.map_intGram_eq_gram`, `Zsqrtd.intCast_det_intGram`: integer Gram
  matrix of a finite family in `(ℤ√d) ^ κ` and its agreement with `Matrix.gram ℝ`.
-/

public section

open scoped InnerProductSpace

namespace Zsqrtd

/-- Bundled `ℤ`-linear Euclidean realization of a tuple in `(ℤ√d) ^ κ` whose real inner product
recovers the trace pairing `∑ k, 2 * (re₁ * re₂ + |d| * im₁ * im₂)`. -/
noncomputable def famToLp (d : ℤ) (κ : Type*) :
    (κ → ℤ√d) →ₗ[ℤ] EuclideanSpace ℝ (κ × Fin 2) where
  toFun v := WithLp.toLp 2 fun p ↦
    if p.2 = 0 then Real.sqrt 2 * (v p.1).re else Real.sqrt (2 * d.natAbs) * (v p.1).im
  map_add' v w := by
    ext p
    rcases Fin.eq_zero_or_eq_succ p.2 with hp | ⟨j, hj⟩
    · simp [hp, mul_add]
    · simp [hj, mul_add]
  map_smul' c v := by
    ext p
    rcases Fin.eq_zero_or_eq_succ p.2 with hp | ⟨j, hj⟩
    · simp [hp, zsmul_eq_mul]; ring
    · simp [hj, zsmul_eq_mul]; ring

/-- Real-part coordinate evaluation of `Zsqrtd.famToLp`. -/
@[simp]
theorem famToLp_ofLp_zero (d : ℤ) {κ : Type*} (v : κ → ℤ√d) (k : κ) :
    (famToLp d κ v).ofLp (k, 0) = Real.sqrt 2 * (v k).re := by
  rfl

/-- Imaginary-part coordinate evaluation of `Zsqrtd.famToLp`. -/
@[simp]
theorem famToLp_ofLp_one (d : ℤ) {κ : Type*} (v : κ → ℤ√d) (k : κ) :
    (famToLp d κ v).ofLp (k, 1) = Real.sqrt (2 * d.natAbs) * (v k).im := by
  simp [famToLp]

/-- Compatibility of `Zsqrtd.famToLp` with finite `ℤ`-linear combinations. -/
theorem famToLp_sum_zsmul (d : ℤ) {κ ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (v : ι → κ → ℤ√d) :
    famToLp d κ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, (c i : ℝ) • famToLp d κ (v i) := by
  simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]

/-- Inner product of two `ℤ√d`-tuple realizations in terms of coordinates. -/
theorem inner_famToLp (d : ℤ) {κ : Type*} [Fintype κ] (v w : κ → ℤ√d) :
    ⟪famToLp d κ v, famToLp d κ w⟫_ℝ =
      ((∑ k : κ, 2 * ((v k).re * (w k).re + (d.natAbs : ℤ) * (v k).im * (w k).im) : ℤ) : ℝ) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Fin.sum_univ_two]
  simp only [famToLp_ofLp_zero, famToLp_ofLp_one, RCLike.inner_apply, conj_trivial]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by positivity)
  have hd : Real.sqrt (2 * (d.natAbs : ℝ)) * Real.sqrt (2 * (d.natAbs : ℝ)) = 2 * |(d : ℝ)| := by
    rw [Real.mul_self_sqrt (by positivity), Nat.cast_natAbs, Int.cast_abs]
  linear_combination (v k).re * (w k).re * h2 + (v k).im * (w k).im * hd

/-- Squared norm of a `ℤ√d`-tuple realization in terms of the two complex embeddings. -/
theorem norm_sq_famToLp (d : ℤ) {κ : Type*} [Fintype κ] (v : κ → ℤ√d) :
    ‖famToLp d κ v‖ ^ 2 = ∑ k : κ, (‖embPos d (v k)‖ ^ 2 + ‖embNeg d (v k)‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_famToLp]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := two_mul_re_sq_add_im_sq_eq d (v k)
  rw [Nat.cast_natAbs, Int.cast_abs] at h
  linear_combination h

/-- Integer Gram matrix of a finite family of tuples in `(ℤ√d) ^ κ` with respect to the trace
pairing `∑ k, 2 * (re₁ * re₂ + |d| * im₁ * im₂)`. -/
def intGram (d : ℤ) {κ ι : Type*} [Fintype κ] (v : ι → κ → ℤ√d) : Matrix ι ι ℤ :=
  Matrix.of fun i j ↦
    ∑ k : κ, 2 * ((v i k).re * (v j k).re + (d.natAbs : ℤ) * (v i k).im * (v j k).im)

/-- Entry evaluation of `Zsqrtd.intGram`. -/
@[simp]
theorem intGram_apply (d : ℤ) {κ ι : Type*} [Fintype κ] (v : ι → κ → ℤ√d) (i j : ι) :
    intGram d v i j =
      ∑ k : κ, 2 * ((v i k).re * (v j k).re + (d.natAbs : ℤ) * (v i k).im * (v j k).im) := by
  rfl

/-- Coercing `Zsqrtd.intGram d v` to `ℝ` produces the Euclidean Gram matrix of `famToLp d κ ∘ v`. -/
theorem map_intGram_eq_gram (d : ℤ) {κ ι : Type*} [Fintype κ] (v : ι → κ → ℤ√d) :
    (intGram d v).map (Int.castRingHom ℝ) = Matrix.gram ℝ (fun i ↦ famToLp d κ (v i)) := by
  ext i j
  simp [Matrix.gram_apply, inner_famToLp]

/-- The integer determinant of `Zsqrtd.intGram d v` agrees in `ℝ` with the real Gram determinant
of `famToLp d κ ∘ v`. -/
theorem intCast_det_intGram (d : ℤ) {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (v : ι → κ → ℤ√d) :
    ((intGram d v).det : ℝ) = (Matrix.gram ℝ (fun i ↦ famToLp d κ (v i))).det :=
  Matrix.intCast_det_eq_det_gram (map_intGram_eq_gram d v)

end Zsqrtd
