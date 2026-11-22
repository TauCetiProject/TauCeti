/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.NumberTheory.NumberField.Quadratic.ComplexEmbedding
import TauCeti.Analysis.Complex.Sqrt

/-!
# The two complex algebra maps of `ℚ[√r]` and the coordinate bound

For every rational `r`, the quadratic algebra `QuadraticAlgebra ℚ r 0 = ℚ[ω]/(ω² - r)` has two
`ℚ`-algebra maps to `ℂ`, `σ₊` and `σ₋`, sending the generator `ω` to the two complex square roots
`±s` of `r`, where `s = Complex.sqrt (r : ℂ)` is `√r` for `r ≥ 0` and `√(-r) · i` for `r < 0`.
Every `ℚ`-algebra map to `ℂ` is one of them, for every `r`, since it sends `ω` to a square root
of `r`. The two maps are distinct exactly when `r ≠ 0`, and they are injective exactly when `r` is
not a square in `ℚ`. Only in that case is `QuadraticAlgebra ℚ r 0` the quadratic field `ℚ(√r)`
and are `σ₊`, `σ₋` its two complex embeddings.

The main result is the archimedean coordinate bound: for every `ℚ`-algebra map
`σ : QuadraticAlgebra ℚ r 0 →ₐ[ℚ] ℂ` and every `z = u + vω`, `‖σ z‖ ≤ |u| + |v| √|r|`. It needs
no nonsquare hypothesis, and specializes to the presented order `ℤ[√r]` for an integer `r`
through the inclusion `QuadraticAlgebra ℤ r 0 → QuadraticAlgebra ℚ r 0`. Conversely the
coordinates are recovered from the two maps, with `|u|` and `|v| √|r|` bounded by the mean
of `‖σ₊ z‖` and `‖σ₋ z‖`.

For `r ≤ 0` the map `σ₊` is the distinguished map `QuadraticAlgebra.complexEmbedding`, and `σ₋`
is its complex conjugate. For `r ≥ 0` both take real values, and they are exchanged by the
quadratic involution `star`, which is then not complex conjugation.

## Main definitions and results

* `QuadraticAlgebra.sqrtEmbedding r`, `QuadraticAlgebra.negSqrtEmbedding r`: the algebra maps
  `σ₊ : ω ↦ Complex.sqrt r` and `σ₋ : ω ↦ -Complex.sqrt r`, which coincide at `r = 0`.
* `QuadraticAlgebra.norm_embedding_le`: `‖σ z‖ ≤ |u| + |v| √|r|` for every `ℚ`-algebra map `σ`.
* `QuadraticAlgebra.norm_embedding_algebraMap_le`: the same bound on `ℤ[√r]`.
* `QuadraticAlgebra.algHom_eq_sqrtEmbedding_or_eq_negSqrtEmbedding`: every `ℚ`-algebra map to
  `ℂ` is `σ₊` or `σ₋`.
* `QuadraticAlgebra.algHom_injective_iff`: such a map is injective exactly when `r` is not a
  square.
* `QuadraticAlgebra.negSqrtEmbedding_eq_comp_starAlgEquiv`: `σ₋ = σ₊ ∘ star`.
* `QuadraticAlgebra.sqrtEmbedding_mul_negSqrtEmbedding`,
  `QuadraticAlgebra.sqrtEmbedding_add_negSqrtEmbedding`: `σ₊ z · σ₋ z = norm z` and
  `σ₊ z + σ₋ z = trace z`; by `QuadraticAlgebra.sqrtEmbedding_mul_negSqrtEmbedding_eq_algebraNorm`
  the product is also the algebra norm `Algebra.norm ℚ z`, which for nonsquare `r` is the field
  norm of `ℚ(√r)/ℚ`.
* `QuadraticAlgebra.abs_re_le`, `QuadraticAlgebra.abs_im_le`: coordinate recovery bounds.
* `QuadraticAlgebra.sqrtEmbedding_ne_negSqrtEmbedding`: `σ₊ ≠ σ₋` for `r ≠ 0`.
* `QuadraticAlgebra.isReal_sqrtEmbedding`: for a nonsquare `r ≥ 0` the embedding `σ₊` of the
  field `ℚ(√r)` is real.
* `QuadraticAlgebra.forall_norm_sq_sqrtEmbedding_eq_norm_iff`: `‖σ₊ z‖² = norm z` for every `z`
  exactly when `r ≤ 0`.
-/

public section

open Complex ComplexConjugate NumberField

namespace QuadraticAlgebra

private theorem sqrt_ratCast_of_nonneg {r : ℚ} (hr : 0 ≤ r) :
    Complex.sqrt (r : ℂ) = (√(r : ℝ) : ℂ) := by
  open scoped ComplexOrder in
  have hc : (0 : ℂ) ≤ (r : ℂ) := by
    rw [← Complex.ofReal_ratCast]
    exact Complex.zero_le_real.mpr (by exact_mod_cast hr)
  rw [Complex.sqrt_of_nonneg hc, Complex.ratCast_re]

private theorem sqrt_ratCast_of_nonpos {r : ℚ} (hr : r ≤ 0) :
    Complex.sqrt (r : ℂ) = (√(-(r : ℝ)) : ℂ) * I := by
  open scoped ComplexOrder in
  have hc : (0 : ℂ) ≤ -(r : ℂ) := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_neg]
    exact Complex.zero_le_real.mpr (by exact_mod_cast neg_nonneg.mpr hr)
  rw [← neg_neg (r : ℂ), Complex.sqrt_neg_of_nonneg hc, Complex.sqrt_of_nonneg hc,
    Complex.neg_re, Complex.ratCast_re, mul_comm]

variable (r : ℚ)

/-- The `ℚ`-algebra map `σ₊ : QuadraticAlgebra ℚ r 0 → ℂ` sending `ω` to `Complex.sqrt (r : ℂ)`.
It is an embedding of the field `ℚ(√r)` when `r` is not a square. -/
noncomputable def sqrtEmbedding : QuadraticAlgebra ℚ r 0 →ₐ[ℚ] ℂ :=
  lift ⟨Complex.sqrt (r : ℂ), by
    rw [Rat.smul_def, mul_one, zero_smul, add_zero, ← sq, Complex.sq_sqrt]⟩

/-- The `ℚ`-algebra map `σ₋ : QuadraticAlgebra ℚ r 0 → ℂ` sending `ω` to
`-Complex.sqrt (r : ℂ)`. It is an embedding of the field `ℚ(√r)` when `r` is not a square, and
equals `σ₊` when `r = 0`. -/
noncomputable def negSqrtEmbedding : QuadraticAlgebra ℚ r 0 →ₐ[ℚ] ℂ :=
  lift ⟨-Complex.sqrt (r : ℂ), by
    rw [Rat.smul_def, mul_one, zero_smul, add_zero, neg_mul_neg, ← sq, Complex.sq_sqrt]⟩

@[simp] theorem sqrtEmbedding_omega : sqrtEmbedding r ω = Complex.sqrt (r : ℂ) := by
  simp [sqrtEmbedding]

@[simp] theorem negSqrtEmbedding_omega : negSqrtEmbedding r ω = -Complex.sqrt (r : ℂ) := by
  simp [negSqrtEmbedding]

theorem sqrtEmbedding_apply (z : QuadraticAlgebra ℚ r 0) :
    sqrtEmbedding r z = z.re + z.im * Complex.sqrt (r : ℂ) := by
  simp [sqrtEmbedding, Rat.smul_def]

theorem negSqrtEmbedding_apply (z : QuadraticAlgebra ℚ r 0) :
    negSqrtEmbedding r z = z.re - z.im * Complex.sqrt (r : ℂ) := by
  simp [negSqrtEmbedding, Rat.smul_def, sub_eq_add_neg]

/-- **`σ₋ = σ₊ ∘ star`**, for every `r`. -/
theorem negSqrtEmbedding_eq_comp_starAlgEquiv :
    negSqrtEmbedding r = (sqrtEmbedding r).comp (starAlgEquiv : _ ≃ₐ[ℚ] _).toAlgHom := by
  have h : star (ω : QuadraticAlgebra ℚ r 0) = -ω := by ext <;> simp
  exact algHom_ext (by simp [h])

theorem negSqrtEmbedding_apply_eq_sqrtEmbedding_star (z : QuadraticAlgebra ℚ r 0) :
    negSqrtEmbedding r z = sqrtEmbedding r (star z) := by
  rw [negSqrtEmbedding_eq_comp_starAlgEquiv]
  rfl

/-- **`σ₊ z · σ₋ z = norm z`**, for every `r`. -/
theorem sqrtEmbedding_mul_negSqrtEmbedding (z : QuadraticAlgebra ℚ r 0) :
    sqrtEmbedding r z * negSqrtEmbedding r z = ((QuadraticAlgebra.norm z : ℚ) : ℂ) := by
  rw [negSqrtEmbedding_apply_eq_sqrtEmbedding_star, ← map_mul, ← algebraMap_norm_eq_mul_star,
    AlgHom.commutes, eq_ratCast]

/-- **`σ₊ z · σ₋ z` is the algebra norm.** The product of the two maps is `Algebra.norm ℚ z`,
the determinant of multiplication by `z`, which for nonsquare `r` is the norm of the field
extension `ℚ(√r)/ℚ`. -/
theorem sqrtEmbedding_mul_negSqrtEmbedding_eq_algebraNorm (z : QuadraticAlgebra ℚ r 0) :
    sqrtEmbedding r z * negSqrtEmbedding r z = (Algebra.norm ℚ z : ℂ) := by
  have h : Algebra.norm ℚ z = QuadraticAlgebra.norm z := by
    rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
    rfl
  rw [h, sqrtEmbedding_mul_negSqrtEmbedding]

/-- **`σ₊ z + σ₋ z = trace z`**, for every `r`. -/
theorem sqrtEmbedding_add_negSqrtEmbedding (z : QuadraticAlgebra ℚ r 0) :
    sqrtEmbedding r z + negSqrtEmbedding r z = ((QuadraticAlgebra.trace z : ℚ) : ℂ) := by
  rw [negSqrtEmbedding_apply_eq_sqrtEmbedding_star, ← map_add, ← algebraMap_trace_eq_add_star,
    AlgHom.commutes, eq_ratCast]

/-- Coordinate recovery for the first coordinate: `u = (σ₊ z + σ₋ z) / 2`. -/
theorem re_eq_sqrtEmbedding_add_negSqrtEmbedding (z : QuadraticAlgebra ℚ r 0) :
    (z.re : ℂ) = (sqrtEmbedding r z + negSqrtEmbedding r z) / 2 := by
  rw [sqrtEmbedding_apply, negSqrtEmbedding_apply]
  ring

/-- Coordinate recovery for the second coordinate: `v s = (σ₊ z - σ₋ z) / 2`. -/
theorem im_mul_sqrt_eq (z : QuadraticAlgebra ℚ r 0) :
    (z.im : ℂ) * Complex.sqrt (r : ℂ) = (sqrtEmbedding r z - negSqrtEmbedding r z) / 2 := by
  rw [sqrtEmbedding_apply, negSqrtEmbedding_apply]
  ring

variable {r}

/-- Coordinate recovery for the second coordinate, for `r ≠ 0`: `v = (σ₊ z - σ₋ z) / (2 s)`. -/
theorem im_eq_sqrtEmbedding_sub_negSqrtEmbedding (hr : r ≠ 0) (z : QuadraticAlgebra ℚ r 0) :
    (z.im : ℂ) = (sqrtEmbedding r z - negSqrtEmbedding r z) / (2 * Complex.sqrt (r : ℂ)) := by
  have hs : Complex.sqrt (r : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.sqrt_eq_zero_iff, Rat.cast_eq_zero]
    exact hr
  rw [eq_div_iff (mul_ne_zero two_ne_zero hs), sqrtEmbedding_apply, negSqrtEmbedding_apply]
  ring

/-- The first coordinate is bounded by the mean of the two maps: `|u| ≤ (‖σ₊ z‖ + ‖σ₋ z‖)/2`.
-/
theorem abs_re_le (z : QuadraticAlgebra ℚ r 0) :
    |(z.re : ℝ)| ≤ (‖sqrtEmbedding r z‖ + ‖negSqrtEmbedding r z‖) / 2 := by
  rw [← norm_ratCast, re_eq_sqrtEmbedding_add_negSqrtEmbedding, norm_div, Complex.norm_two]
  gcongr
  exact norm_add_le _ _

/-- The second coordinate, scaled by `√|r|`, is bounded by the mean of the two maps:
`|v| √|r| ≤ (‖σ₊ z‖ + ‖σ₋ z‖)/2`. -/
theorem abs_im_mul_sqrt_le (z : QuadraticAlgebra ℚ r 0) :
    |(z.im : ℝ)| * √|(r : ℝ)| ≤ (‖sqrtEmbedding r z‖ + ‖negSqrtEmbedding r z‖) / 2 := by
  have hnorm : ‖Complex.sqrt (r : ℂ)‖ = √|(r : ℝ)| := by
    rw [Complex.norm_sqrt, Complex.norm_ratCast]
  rw [← norm_ratCast, ← hnorm, ← norm_mul, im_mul_sqrt_eq, norm_div, Complex.norm_two]
  gcongr
  exact norm_sub_le _ _

/-- For `r ≠ 0`, the second coordinate is bounded by the two maps:
`|v| ≤ (‖σ₊ z‖ + ‖σ₋ z‖)/(2 √|r|)`. -/
theorem abs_im_le (hr : r ≠ 0) (z : QuadraticAlgebra ℚ r 0) :
    |(z.im : ℝ)| ≤ (‖sqrtEmbedding r z‖ + ‖negSqrtEmbedding r z‖) / (2 * √|(r : ℝ)|) := by
  rw [le_div_iff₀ (by positivity)]
  linarith [abs_im_mul_sqrt_le z]

/-- **Every `ℚ`-algebra map `QuadraticAlgebra ℚ r 0 → ℂ` is `σ₊` or `σ₋`**, for every rational
`r`: it sends `ω` to a square root of `r`. -/
theorem algHom_eq_sqrtEmbedding_or_eq_negSqrtEmbedding (σ : QuadraticAlgebra ℚ r 0 →ₐ[ℚ] ℂ) :
    σ = sqrtEmbedding r ∨ σ = negSqrtEmbedding r := by
  have hσ : σ ω * σ ω = Complex.sqrt (r : ℂ) * Complex.sqrt (r : ℂ) := by
    rw [← map_mul, omega_mul_omega_eq_algebraMap]
    simp [← sq]
  rcases mul_self_eq_mul_self_iff.mp hσ with h | h
  · exact Or.inl (algHom_ext (by simp [h]))
  · exact Or.inr (algHom_ext (by simp [h]))

/-- A `ℚ`-algebra map `QuadraticAlgebra ℚ r 0 → ℂ` sends `ω` to a complex number of norm `√|r|`. -/
theorem norm_apply_omega (σ : QuadraticAlgebra ℚ r 0 →ₐ[ℚ] ℂ) : ‖σ ω‖ = √|(r : ℝ)| := by
  rcases algHom_eq_sqrtEmbedding_or_eq_negSqrtEmbedding σ with rfl | rfl <;>
    simp [Complex.norm_sqrt, Complex.norm_ratCast]

/-- **The coordinate bound for a complex algebra map.** For every `ℚ`-algebra map
`σ : QuadraticAlgebra ℚ r 0 → ℂ` and every `z = u + vω`, `‖σ z‖ ≤ |u| + |v| √|r|`. No nonsquare
hypothesis is needed. -/
theorem norm_embedding_le (σ : QuadraticAlgebra ℚ r 0 →ₐ[ℚ] ℂ) (z : QuadraticAlgebra ℚ r 0) :
    ‖σ z‖ ≤ |(z.re : ℝ)| + |(z.im : ℝ)| * √|(r : ℝ)| := by
  have hz : σ z = (z.re : ℂ) + z.im * σ ω := by
    rcases algHom_eq_sqrtEmbedding_or_eq_negSqrtEmbedding σ with rfl | rfl
    · simp [sqrtEmbedding_apply]
    · simp [negSqrtEmbedding_apply, sub_eq_add_neg]
  rw [hz, ← norm_ratCast, ← norm_ratCast, ← norm_apply_omega σ, ← norm_mul]
  exact norm_add_le _ _

/-- **The coordinate bound on `ℤ[√r]`.** For an integer `r`, every `ℚ`-algebra map
`σ : QuadraticAlgebra ℚ r 0 → ℂ` and every `z = u + vω` in the presented order
`QuadraticAlgebra ℤ r 0`, `‖σ z‖ ≤ |u| + |v| √|r|`. -/
theorem norm_embedding_algebraMap_le {r : ℤ} (σ : QuadraticAlgebra ℚ r 0 →ₐ[ℚ] ℂ)
    (z : QuadraticAlgebra ℤ r 0) :
    ‖σ (algebraMap (QuadraticAlgebra ℤ r 0) (QuadraticAlgebra ℚ r ((0 : ℤ) : ℚ)) z)‖ ≤
      |(z.re : ℝ)| + |(z.im : ℝ)| * √|(r : ℝ)| := by
  have h : ‖σ (algebraMap (QuadraticAlgebra ℤ r 0) (QuadraticAlgebra ℚ r ((0 : ℤ) : ℚ)) z)‖ ≤
      |((z.re : ℚ) : ℝ)| + |((z.im : ℚ) : ℝ)| * √|((r : ℚ) : ℝ)| :=
    norm_embedding_le σ _
  simpa only [Rat.cast_intCast] using h

/-- **Injectivity of the algebra maps.** A `ℚ`-algebra map `QuadraticAlgebra ℚ r 0 → ℂ` is
injective exactly when `r` is not a square in `ℚ`. For a square `r = t²` it sends `ω - t` or
`ω + t` to `0`. -/
theorem algHom_injective_iff (σ : QuadraticAlgebra ℚ r 0 →ₐ[ℚ] ℂ) :
    Function.Injective σ ↔ ¬ IsSquare r := by
  refine ⟨fun hσ ⟨t, ht⟩ => ?_, fun hr => ?_⟩
  · have h : σ ω * σ ω = (t : ℂ) * t := by
      rw [← map_mul, omega_mul_omega_eq_algebraMap]
      simp [ht]
    rcases mul_self_eq_mul_self_iff.mp h with h | h
    · have h0 : σ (ω - algebraMap ℚ _ t) = σ 0 := by simp [h]
      simpa [QuadraticAlgebra.ext_iff] using hσ h0
    · have h0 : σ (ω + algebraMap ℚ _ t) = σ 0 := by simp [h]
      simpa [QuadraticAlgebra.ext_iff] using hσ h0
  · have : Fact (¬ IsSquare r) := ⟨hr⟩
    exact σ.injective

theorem sqrtEmbedding_injective [Fact (¬ IsSquare r)] : Function.Injective (sqrtEmbedding r) :=
  (algHom_injective_iff _).mpr Fact.out

theorem negSqrtEmbedding_injective [Fact (¬ IsSquare r)] :
    Function.Injective (negSqrtEmbedding r) :=
  (algHom_injective_iff _).mpr Fact.out

/-- For `r ≠ 0`, the two algebra maps are distinct; at `r = 0` they coincide. -/
theorem sqrtEmbedding_ne_negSqrtEmbedding (hr : r ≠ 0) :
    sqrtEmbedding r ≠ negSqrtEmbedding r := by
  intro h
  have h0 : Complex.sqrt (r : ℂ) = -Complex.sqrt (r : ℂ) := by
    simpa using AlgHom.congr_fun h ω
  exact (Complex.sqrt_eq_zero_iff.not.mpr (by exact_mod_cast hr)) (CharZero.eq_neg_self_iff.mp h0)

/-! ### Comparison with complex conjugation and the distinguished algebra map -/

/-- For `r ≤ 0`, `σ₊` is the distinguished algebra map `complexEmbedding`. -/
theorem sqrtEmbedding_eq_complexEmbedding (hr : r ≤ 0) :
    sqrtEmbedding r = complexEmbedding hr :=
  algHom_ext (by simp [sqrt_ratCast_of_nonpos hr])

/-- For `r ≤ 0`, `σ₋` is the complex conjugate of `σ₊`. -/
theorem negSqrtEmbedding_apply_eq_conj (hr : r ≤ 0) (z : QuadraticAlgebra ℚ r 0) :
    negSqrtEmbedding r z = conj (sqrtEmbedding r z) := by
  simp [sqrtEmbedding_apply, negSqrtEmbedding_apply, sqrt_ratCast_of_nonpos hr, sub_eq_add_neg]

/-- For `r ≥ 0`, `σ₊` takes real values. -/
@[simp] theorem im_sqrtEmbedding (hr : 0 ≤ r) (z : QuadraticAlgebra ℚ r 0) :
    (sqrtEmbedding r z).im = 0 := by
  simp [sqrtEmbedding_apply, sqrt_ratCast_of_nonneg hr]

/-- For `r ≥ 0`, `σ₋` takes real values. -/
@[simp] theorem im_negSqrtEmbedding (hr : 0 ≤ r) (z : QuadraticAlgebra ℚ r 0) :
    (negSqrtEmbedding r z).im = 0 := by
  simp [negSqrtEmbedding_apply, sqrt_ratCast_of_nonneg hr]

/-- For a nonsquare `r > 0`, `σ₊` is a real embedding of the field `ℚ(√r)`. -/
theorem isReal_sqrtEmbedding [Fact (¬ IsSquare r)] (hr : 0 ≤ r) :
    ComplexEmbedding.IsReal (sqrtEmbedding r : QuadraticAlgebra ℚ r 0 →+* ℂ) :=
  ComplexEmbedding.isReal_iff.mpr <| RingHom.ext fun z =>
    conj_eq_iff_im.mpr (im_sqrtEmbedding hr z)

/-- For a nonsquare `r > 0`, `σ₋` is a real embedding of the field `ℚ(√r)`. -/
theorem isReal_negSqrtEmbedding [Fact (¬ IsSquare r)] (hr : 0 ≤ r) :
    ComplexEmbedding.IsReal (negSqrtEmbedding r : QuadraticAlgebra ℚ r 0 →+* ℂ) :=
  ComplexEmbedding.isReal_iff.mpr <| RingHom.ext fun z =>
    conj_eq_iff_im.mpr (im_negSqrtEmbedding hr z)

/-- **`‖σ₊ z‖² = norm z` for every `z` exactly when `r ≤ 0`.** For `r ≤ 0` this is
`‖u + v√(-r) i‖² = u² - r v²`; for `r > 0`, `‖σ₊ ω‖² = r ≠ -r = norm ω`. -/
theorem forall_norm_sq_sqrtEmbedding_eq_norm_iff :
    (∀ z : QuadraticAlgebra ℚ r 0, ‖sqrtEmbedding r z‖ ^ 2 = ((QuadraticAlgebra.norm z : ℚ) : ℝ)) ↔
      r ≤ 0 := by
  refine ⟨fun h => ?_, fun hr z => ?_⟩
  · have hω := h ω
    rw [sqrtEmbedding_omega, Complex.norm_sqrt, Complex.norm_ratCast,
      Real.sq_sqrt (abs_nonneg _)] at hω
    simpa [norm_def] using hω
  · have h1 := sqrtEmbedding_mul_negSqrtEmbedding r z
    rw [negSqrtEmbedding_apply_eq_conj hr, mul_conj] at h1
    rw [← normSq_eq_norm_sq]
    exact_mod_cast h1

end QuadraticAlgebra
