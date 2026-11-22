/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import TauCeti.Analysis.InnerProductSpace.Gram.Integral
public import TauCeti.NumberTheory.Zsqrtd.ComplexEmbedding

/-!
# Euclidean realizations and integer Gram matrices for `ℤ√d`-families

A tuple `v : κ → ℤ√d` maps `ℤ`-linearly into `EuclideanSpace ℝ (κ × Fin 2)` via
`Zsqrtd.famToLp d κ`, defined as the composition of integer coordinate extraction
`Zsqrtd.famCoords d κ` with `TauCeti.weightedToLp (Zsqrtd.famWeight d κ)` (scaling the real part
by `√2` and the imaginary part by `√(2 * |d|)`). This map is injective whenever `d ≠ 0`
(`Zsqrtd.famToLp_injective`). Its real inner product recovers the weighted Euclidean integer Gram
pairing
`Zsqrtd.intGram d v i j = ∑ k, 2 * ((v i k).re * (v j k).re + |d| * (v i k).im * (v j k).im)`,
and its squared Euclidean norm equals `∑ k, (‖embPos d (v k)‖ ^ 2 + ‖embNeg d (v k)‖ ^ 2)`.

## Main results

* `Zsqrtd.famCoords`, `Zsqrtd.famWeight`: integer coordinate extraction and real weights.
* `Zsqrtd.famWeight_pos`: positivity of `Zsqrtd.famWeight` when `d ≠ 0`.
* `Zsqrtd.famToLp`: bundled `ℤ`-linear Euclidean realization
  `(κ → ℤ√d) →ₗ[ℤ] EuclideanSpace ℝ (κ × Fin 2)`.
* `Zsqrtd.famToLp_injective`: injectivity of `Zsqrtd.famToLp` when `d ≠ 0`.
* `Zsqrtd.famToLp_eq_weightedToLp`, `Zsqrtd.famToLp_apply`: explicit factorization through
  `TauCeti.weightedToLp`.
* `Zsqrtd.famToLp_ofLp_zero`, `Zsqrtd.famToLp_ofLp_one`: coordinate evaluations.
* `Zsqrtd.famToLp_sum_zsmul`: compatibility with `ℤ`-linear combinations.
* `Zsqrtd.inner_famToLp`, `Zsqrtd.norm_sq_famToLp`: inner product and squared norm formulas.
* `Zsqrtd.intGram`, `Zsqrtd.map_intGram_eq_gram`, `Zsqrtd.intCast_det_intGram`: integer Gram
  matrix of a finite family in `(ℤ√d) ^ κ` and its agreement with `Matrix.gram ℝ`.
-/

public section

open scoped InnerProductSpace

namespace Zsqrtd

/-- Bundled `ℤ`-linear coordinate extraction `(κ → ℤ√d) →ₗ[ℤ] (κ × Fin 2 → ℤ)`, sending `v` to
`(k, 0) ↦ (v k).re` and `(k, 1) ↦ (v k).im`. -/
def famCoords (d : ℤ) (κ : Type*) : (κ → ℤ√d) →ₗ[ℤ] (κ × Fin 2 → ℤ) where
  toFun v p := if p.2 = 0 then (v p.1).re else (v p.1).im
  map_add' v w := by
    ext p
    by_cases h : p.2 = 0 <;> simp [h]
  map_smul' c v := by
    ext p
    by_cases h : p.2 = 0 <;> simp [h, zsmul_eq_mul]

/-- Real-part coordinate extraction of `Zsqrtd.famCoords`. -/
@[simp]
theorem famCoords_zero (d : ℤ) {κ : Type*} (v : κ → ℤ√d) (k : κ) :
    famCoords d κ v (k, 0) = (v k).re := by
  simp [famCoords]

/-- Imaginary-part coordinate extraction of `Zsqrtd.famCoords`. -/
@[simp]
theorem famCoords_one (d : ℤ) {κ : Type*} (v : κ → ℤ√d) (k : κ) :
    famCoords d κ v (k, 1) = (v k).im := by
  simp [famCoords]

/-- Real coordinate weights for `Zsqrtd.famToLp`: `2` on real-part coordinates `(k, 0)` and
`2 * |d|` on imaginary-part coordinates `(k, 1)`. -/
def famWeight (d : ℤ) (κ : Type*) (p : κ × Fin 2) : ℝ :=
  if p.2 = 0 then 2 else 2 * d.natAbs

/-- Nonnegativity of `Zsqrtd.famWeight`. -/
theorem famWeight_nonneg (d : ℤ) (κ : Type*) (p : κ × Fin 2) : 0 ≤ famWeight d κ p := by
  dsimp [famWeight]
  split_ifs <;> positivity

/-- Positivity of `Zsqrtd.famWeight` whenever `d ≠ 0`. -/
theorem famWeight_pos {d : ℤ} (hd : d ≠ 0) (κ : Type*) (p : κ × Fin 2) :
    0 < famWeight d κ p := by
  dsimp [famWeight]
  split_ifs
  · positivity
  · have : (0 : ℝ) < d.natAbs := Nat.cast_pos.mpr (Int.natAbs_pos.mpr hd)
    positivity

/-- Weight `2` on real-part coordinates `(k, 0)` in `Zsqrtd.famWeight`. -/
@[simp]
theorem famWeight_zero (d : ℤ) {κ : Type*} (k : κ) : famWeight d κ (k, 0) = 2 := by
  simp [famWeight]

/-- Weight `2 * |d|` on imaginary-part coordinates `(k, 1)` in `Zsqrtd.famWeight`. -/
@[simp]
theorem famWeight_one (d : ℤ) {κ : Type*} (k : κ) :
    famWeight d κ (k, 1) = 2 * d.natAbs := by
  simp [famWeight]

/-- Bundled `ℤ`-linear Euclidean realization of a tuple in `(ℤ√d) ^ κ` whose real inner product
recovers the weighted Euclidean pairing `∑ k, 2 * (re₁ * re₂ + |d| * im₁ * im₂)`. -/
noncomputable def famToLp (d : ℤ) (κ : Type*) :
    (κ → ℤ√d) →ₗ[ℤ] EuclideanSpace ℝ (κ × Fin 2) :=
  (TauCeti.weightedToLp (famWeight d κ)).comp (famCoords d κ)

/-- Relation between `Zsqrtd.famToLp` and `TauCeti.weightedToLp`. -/
theorem famToLp_eq_weightedToLp (d : ℤ) (κ : Type*) :
    famToLp d κ = (TauCeti.weightedToLp (famWeight d κ)).comp (famCoords d κ) := by
  rfl

/-- Applying `Zsqrtd.famToLp` evaluates `TauCeti.weightedToLp` on `Zsqrtd.famCoords`. -/
theorem famToLp_apply (d : ℤ) {κ : Type*} (v : κ → ℤ√d) :
    famToLp d κ v = TauCeti.weightedToLp (famWeight d κ) (famCoords d κ v) := by
  rfl

/-- `Zsqrtd.famToLp d κ` is injective whenever `d ≠ 0`. -/
theorem famToLp_injective {d : ℤ} (hd : d ≠ 0) (κ : Type*) :
    Function.Injective (famToLp d κ) :=
  (TauCeti.weightedToLp_injective (famWeight_pos hd κ)).comp fun v w h ↦ by
    ext k
    · exact congrArg (fun f ↦ f (k, 0)) h
    · exact congrArg (fun f ↦ f (k, 1)) h

/-- Real-part coordinate evaluation of `Zsqrtd.famToLp`. -/
@[simp]
theorem famToLp_ofLp_zero (d : ℤ) {κ : Type*} (v : κ → ℤ√d) (k : κ) :
    (famToLp d κ v).ofLp (k, 0) = Real.sqrt 2 * (v k).re := by
  simp [famToLp_apply]

/-- Imaginary-part coordinate evaluation of `Zsqrtd.famToLp`. -/
@[simp]
theorem famToLp_ofLp_one (d : ℤ) {κ : Type*} (v : κ → ℤ√d) (k : κ) :
    (famToLp d κ v).ofLp (k, 1) = Real.sqrt (2 * d.natAbs) * (v k).im := by
  simp [famToLp_apply]

/-- Compatibility of `Zsqrtd.famToLp` with finite `ℤ`-linear combinations. -/
theorem famToLp_sum_zsmul (d : ℤ) {κ ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (v : ι → κ → ℤ√d) :
    famToLp d κ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, (c i : ℝ) • famToLp d κ (v i) := by
  simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]

/-- Inner product of two `ℤ√d`-tuple realizations in terms of coordinates. -/
theorem inner_famToLp (d : ℤ) {κ : Type*} [Fintype κ] (v w : κ → ℤ√d) :
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

/-- Squared norm of a `ℤ√d`-tuple realization in terms of the two complex embeddings. -/
theorem norm_sq_famToLp (d : ℤ) {κ : Type*} [Fintype κ] (v : κ → ℤ√d) :
    ‖famToLp d κ v‖ ^ 2 = ∑ k : κ, (‖embPos d (v k)‖ ^ 2 + ‖embNeg d (v k)‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_famToLp]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := two_mul_re_sq_add_im_sq_eq d (v k)
  rw [Nat.cast_natAbs, Int.cast_abs] at h
  linear_combination h

/-- Integer Gram matrix of a finite family of tuples in `(ℤ√d) ^ κ` with respect to the weighted
Euclidean pairing `∑ k, 2 * (re₁ * re₂ + |d| * im₁ * im₂)`. -/
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
