/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.ChangeOfVariables
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# The rescaled Hilbert norms of Taubes's gluing construction

In Taubes's construction of Seiberg–Witten solutions from pseudoholomorphic curves, the
equations at parameter `r` are solved near an approximate solution `(a_app, χ_app)` by a
contraction in Hilbert norms adapted to the length scale `h = λ⁻¹` of the vortices, where
`λ = √(2 r)`. A connection increment `b` and a normalized spinor increment `ζ` are measured by

`‖(b, ζ)‖_(E_(r,s))² = ∑_{j ≤ s} λ^(-2j) (λ⁻² ‖∇ʲ b‖₂² + ‖∇ʲ ζ‖₂² / 4)`,

and the values `y = (f, τ, ν)` of the gauge-fixed Seiberg–Witten section, in the gauge, curvature
and negative-spinor target, by

`‖y‖_(F_(r,s-1))² = ∑_{j ≤ s - 1} λ^(-2j) ‖∇ʲ y‖₂²`.

This file defines these two quantities for fields on a finite-dimensional real inner product
space `V`, a flat chart, with the derivatives `∇ʲ` read as the iterated derivatives
`iteratedFDeriv ℝ j`, and with `h = λ⁻¹` as the parameter:
`TauCeti.SeibergWitten.rescaledFieldNormSq s h b ζ` and
`TauCeti.SeibergWitten.rescaledTargetNormSq s h y`. It proves:

* **The scaling check.** In the rescaled coordinate `w = λ y`, the connection has plane
  coefficient `b_w(w) = λ⁻¹ b(λ⁻¹ w)` and the spinor is `ζ_w(w) = ζ(λ⁻¹ w)`, and
  `‖(b, ζ)‖_(E_(r,s))² = λ⁻ⁿ ∑_{j ≤ s} (‖∇ʲ b_w‖₂² + ‖∇ʲ ζ_w‖₂² / 4)` for `n = dim V`
  (`TauCeti.SeibergWitten.rescaledFieldNormSq_eq_rpow_mul`): the rescaled norm is the unit-scale
  norm of the rescaled fields, with the coefficient metric `|b|² + |δα|² / 4` of the plane vortex
  equations and the volume factor `λ⁻ⁿ`. The weight `λ⁻²` on `b` is what makes the connection and
  the section scale alike. The same holds for the target norm
  (`TauCeti.SeibergWitten.rescaledTargetNormSq_eq_rpow_mul`).
* **Equivalence with the fixed-order norms.** For `0 < h ≤ 1`, that is `λ ≥ 1`, the rescaled norm
  lies between `h^(2s+2)` times and one times the unit-scale norm of the same fields
  (`TauCeti.SeibergWitten.pow_mul_rescaledFieldNormSq_one_le`,
  `TauCeti.SeibergWitten.rescaledFieldNormSq_le_rescaledFieldNormSq_one`, and for the target
  `TauCeti.SeibergWitten.pow_mul_rescaledTargetNormSq_one_le`,
  `TauCeti.SeibergWitten.rescaledTargetNormSq_le_rescaledTargetNormSq_one`). The constants
  degenerate as `h → 0`, which is why the estimates of the construction are stated in the
  rescaled norms.
* **Comparison with the semiclassical norms.** Up to the factor `hⁿ` and the constant `s + 1`,
  the rescaled field norm is the square of the semiclassical Sobolev norms
  `‖f‖_{s,h} = h^(-n/2) ∑_{i ≤ s} hⁱ ‖Dⁱ f‖₂` (`TauCeti.semiclassicalSobolevNorm`):
  `hⁿ (h² ‖b‖_{s,h}² + ‖ζ‖_{s,h}² / 4)` lies between `‖(b, ζ)‖_(E_(r,s))²` and `s + 1` times it
  (`TauCeti.SeibergWitten.rescaledFieldNormSq_le_rpow_mul`,
  `TauCeti.SeibergWitten.rpow_mul_le_mul_rescaledFieldNormSq`). So the Sobolev embedding,
  algebra, multiplier and change-of-chart estimates of the semiclassical norms, all with
  constants independent of `h`, hold for the rescaled field norm.
* **Gauge, bundle and tube charts.** Multiplying the spinor increment by a gauge `g` with
  semiclassical bounds `hⁱ ‖Dⁱ g‖ ≤ M` for `i ≤ s`, such as a change of unitary gauge varying on the
  scale `h`, changes the rescaled norm by at most a factor depending only on `s` and `M`
  (`TauCeti.SeibergWitten.rescaledFieldNormSq_smul_le`). The same holds for changes of frame of
  the connection and spinor bundles, `(b, ζ) ↦ (A b, A' ζ)` with operator-valued `A` and `A'`
  obeying such bounds (`TauCeti.SeibergWitten.rescaledFieldNormSq_clm_apply_le`, and
  `TauCeti.SeibergWitten.rescaledTargetNormSq_clm_apply_le` for the target), and for reading the
  fields in a chart `Φ` controlled at the scale `h`
  (`TauCeti.SeibergWitten.rescaledFieldNormSq_comp_le`). These rest on the semiclassical
  multiplier and change-of-chart estimates
  (`TauCeti.semiclassicalSobolevNorm_clm_apply_le_of_le_left`,
  `TauCeti.semiclassicalSobolevNorm_comp_le`).
* **The algebra estimate.** For `n < 2k` and a continuous bilinear map `L` between
  finite-dimensional spaces,
  `‖L (f, g)‖_(F_(r,k)) ≤ C ‖L‖ h^(-n/2) ‖f‖_(F_(r,k)) ‖g‖_(F_(r,k))` with `C` independent of `h`
  (`TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_bilinear_le`), from the algebra
  estimate of the semiclassical norms (`TauCeti.exists_semiclassicalSobolevNorm_bilinear_le`).
  The components of the rescaled norm are bounded by it, `h ‖b‖_(F_(r,s)) ≤ ‖(b, ζ)‖_(E_(r,s))`
  and `‖ζ‖_(F_(r,s)) ≤ 2 ‖(b, ζ)‖_(E_(r,s))`
  (`TauCeti.SeibergWitten.mul_sqrt_rescaledTargetNormSq_le_sqrt_rescaledFieldNormSq`,
  `TauCeti.SeibergWitten.sqrt_rescaledTargetNormSq_le_two_mul_sqrt_rescaledFieldNormSq`), so this
  controls the quadratic terms of the Seiberg–Witten equations in the rescaled norms.
* **Seminorm.** The square roots satisfy the triangle inequality on fields with square-integrable
  derivatives (`TauCeti.SeibergWitten.sqrt_rescaledFieldNormSq_add_le`,
  `TauCeti.SeibergWitten.sqrt_rescaledTargetNormSq_add_le`), by Minkowski's inequality.

The derivatives are measured in the operator norm of `iteratedFDeriv`, which is equivalent to
the Hilbert–Schmidt norm of the tensor `∇ʲ` with constants depending only on `j` and `n`; with it
the quantities above are equivalent to Hilbert norms, but are not themselves defined by an inner
product. The fields are smooth functions on a flat chart; the completion to the Sobolev spaces of
sections of the bundles over a four-manifold, with its reference connections, is not treated here.

## Main definitions

* `TauCeti.SeibergWitten.rescaledFieldNormSq s h b ζ`: the square of the norm of
  `(b, ζ)` in `E_(r,s)`, at the scale `h = (2 r)^(-1/2)`.
* `TauCeti.SeibergWitten.rescaledTargetNormSq s h y`: the square of the norm of `y` in
  `F_(r,s-1)`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open MeasureTheory Module

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]

/-! ### Definitions -/

/-- The square of the **rescaled norm** `E_(r,s)` of a connection increment `b` and a
normalized spinor increment `ζ`, at the scale `h = λ⁻¹ = (2 r)^(-1/2)`, with the derivatives in
the operator norm:
`‖(b, ζ)‖_(E_(r,s))² = ∑_{j ≤ s} h^(2j) (h² ‖Dʲ b‖₂² + ‖Dʲ ζ‖₂² / 4)`. A derivative contributes
`0` when it is not square integrable (`MeasureTheory.lpNorm_of_not_memLp`). -/
noncomputable def rescaledFieldNormSq (s : ℕ) (h : ℝ) (b : V → B) (ζ : V → S) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), h ^ (2 * j) *
    (h ^ 2 * lpNorm (iteratedFDeriv ℝ j b) 2 volume ^ 2 +
      lpNorm (iteratedFDeriv ℝ j ζ) 2 volume ^ 2 / 4)

/-- The square of the **rescaled target norm** `F_(r,s-1)` of a field `y` with values in the
gauge, curvature and negative-spinor target, at the scale `h = λ⁻¹ = (2 r)^(-1/2)`:
`‖y‖_(F_(r,s-1))² = ∑_{j < s} h^(2j) ‖Dʲ y‖₂²`, through the derivatives of order `s - 1`. -/
noncomputable def rescaledTargetNormSq (s : ℕ) (h : ℝ) (y : V → T) : ℝ :=
  ∑ j ∈ Finset.range s, h ^ (2 * j) * lpNorm (iteratedFDeriv ℝ j y) 2 volume ^ 2

theorem rescaledFieldNormSq_def (s : ℕ) (h : ℝ) (b : V → B) (ζ : V → S) :
    rescaledFieldNormSq s h b ζ = ∑ j ∈ Finset.range (s + 1), h ^ (2 * j) *
      (h ^ 2 * lpNorm (iteratedFDeriv ℝ j b) 2 volume ^ 2 +
        lpNorm (iteratedFDeriv ℝ j ζ) 2 volume ^ 2 / 4) :=
  (rfl)

theorem rescaledTargetNormSq_def (s : ℕ) (h : ℝ) (y : V → T) :
    rescaledTargetNormSq s h y =
      ∑ j ∈ Finset.range s, h ^ (2 * j) * lpNorm (iteratedFDeriv ℝ j y) 2 volume ^ 2 :=
  (rfl)

/-- The rescaled norm in terms of the target norm through order `s`:
`‖(b, ζ)‖_(E_(r,s))² = h² ‖b‖_(F_(r,s))² + ‖ζ‖_(F_(r,s))² / 4`. -/
theorem rescaledFieldNormSq_eq_rescaledTargetNormSq (s : ℕ) (h : ℝ) (b : V → B) (ζ : V → S) :
    rescaledFieldNormSq s h b ζ =
      h ^ 2 * rescaledTargetNormSq (s + 1) h b + rescaledTargetNormSq (s + 1) h ζ / 4 := by
  rw [rescaledFieldNormSq, rescaledTargetNormSq, rescaledTargetNormSq, Finset.mul_sum,
    Finset.sum_div, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The target norm as a sum of squares of the scaled `L²` norms of the derivatives:
`‖y‖_(F_(r,s-1))² = ∑_{j < s} (hʲ ‖Dʲ y‖₂)²`. -/
theorem rescaledTargetNormSq_eq_sum_sq (s : ℕ) (h : ℝ) (y : V → T) :
    rescaledTargetNormSq s h y =
      ∑ j ∈ Finset.range s, (h ^ j * lpNorm (iteratedFDeriv ℝ j y) 2 volume) ^ 2 :=
  Finset.sum_congr rfl fun j _ ↦ by ring

/-- The rescaled norm as a sum of squares of the scaled `L²` norms of the derivatives:
`‖(b, ζ)‖_(E_(r,s))² = h² ∑_{j ≤ s} (hʲ ‖Dʲ b‖₂)² + (∑_{j ≤ s} (hʲ ‖Dʲ ζ‖₂)²) / 4`. -/
theorem rescaledFieldNormSq_eq_sum_sq (s : ℕ) (h : ℝ) (b : V → B) (ζ : V → S) :
    rescaledFieldNormSq s h b ζ =
      h ^ 2 * ∑ j ∈ Finset.range (s + 1), (h ^ j * lpNorm (iteratedFDeriv ℝ j b) 2 volume) ^ 2 +
        (∑ j ∈ Finset.range (s + 1), (h ^ j * lpNorm (iteratedFDeriv ℝ j ζ) 2 volume) ^ 2) /
          4 := by
  rw [rescaledFieldNormSq_eq_rescaledTargetNormSq, rescaledTargetNormSq_eq_sum_sq,
    rescaledTargetNormSq_eq_sum_sq]

@[simp]
theorem rescaledTargetNormSq_zero (s : ℕ) (h : ℝ) : rescaledTargetNormSq s h (0 : V → T) = 0 := by
  simp [rescaledTargetNormSq]

@[simp]
theorem rescaledFieldNormSq_zero (s : ℕ) (h : ℝ) :
    rescaledFieldNormSq s h (0 : V → B) (0 : V → S) = 0 := by
  simp [rescaledFieldNormSq_eq_rescaledTargetNormSq]

@[simp]
theorem rescaledTargetNormSq_neg (s : ℕ) (h : ℝ) (y : V → T) :
    rescaledTargetNormSq s h (-y) = rescaledTargetNormSq s h y := by
  simp [rescaledTargetNormSq, iteratedFDeriv_neg]

@[simp]
theorem rescaledFieldNormSq_neg (s : ℕ) (h : ℝ) (b : V → B) (ζ : V → S) :
    rescaledFieldNormSq s h (-b) (-ζ) = rescaledFieldNormSq s h b ζ := by
  simp [rescaledFieldNormSq_eq_rescaledTargetNormSq]

/-- Scaling the field by `c` scales the target norm by `c²`. -/
theorem rescaledTargetNormSq_smul (s : ℕ) (h c : ℝ) (y : V → T) :
    rescaledTargetNormSq s h (c • y) = c ^ 2 * rescaledTargetNormSq s h y := by
  have hy (j : ℕ) : iteratedFDeriv ℝ j (c • y) = c • iteratedFDeriv ℝ j y :=
    funext fun x ↦ iteratedFDeriv_fun_const_smul_apply y c x j
  simp only [rescaledTargetNormSq, hy, lpNorm_const_smul, coe_nnNorm, Real.norm_eq_abs, mul_pow,
    sq_abs, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- Scaling both increments by `c` scales the rescaled norm by `c²`. -/
theorem rescaledFieldNormSq_smul (s : ℕ) (h c : ℝ) (b : V → B) (ζ : V → S) :
    rescaledFieldNormSq s h (c • b) (c • ζ) = c ^ 2 * rescaledFieldNormSq s h b ζ := by
  rw [rescaledFieldNormSq_eq_rescaledTargetNormSq, rescaledFieldNormSq_eq_rescaledTargetNormSq,
    rescaledTargetNormSq_smul, rescaledTargetNormSq_smul]
  ring

theorem rescaledTargetNormSq_nonneg (s : ℕ) (h : ℝ) (y : V → T) :
    0 ≤ rescaledTargetNormSq s h y := by
  rw [rescaledTargetNormSq]
  refine Finset.sum_nonneg fun j _ ↦ ?_
  rw [pow_mul]
  positivity

theorem rescaledFieldNormSq_nonneg (s : ℕ) (h : ℝ) (b : V → B) (ζ : V → S) :
    0 ≤ rescaledFieldNormSq s h b ζ := by
  rw [rescaledFieldNormSq_eq_rescaledTargetNormSq]
  have := rescaledTargetNormSq_nonneg (s + 1) h b
  have := rescaledTargetNormSq_nonneg (s + 1) h ζ
  positivity

/-- The connection component is controlled by the rescaled norm with its weight:
`h ‖b‖_(F_(r,s)) ≤ ‖(b, ζ)‖_(E_(r,s))`. -/
theorem mul_sqrt_rescaledTargetNormSq_le_sqrt_rescaledFieldNormSq (s : ℕ) (h : ℝ) (b : V → B)
    (ζ : V → S) :
    h * √(rescaledTargetNormSq (s + 1) h b) ≤ √(rescaledFieldNormSq s h b ζ) := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [mul_pow, Real.sq_sqrt (rescaledTargetNormSq_nonneg _ _ _),
    rescaledFieldNormSq_eq_rescaledTargetNormSq]
  exact le_add_of_nonneg_right (div_nonneg (rescaledTargetNormSq_nonneg _ _ _) (by norm_num))

/-- The spinor component is controlled by the rescaled norm:
`‖ζ‖_(F_(r,s)) ≤ 2 ‖(b, ζ)‖_(E_(r,s))`. -/
theorem sqrt_rescaledTargetNormSq_le_two_mul_sqrt_rescaledFieldNormSq (s : ℕ) (h : ℝ)
    (b : V → B) (ζ : V → S) :
    √(rescaledTargetNormSq (s + 1) h ζ) ≤ 2 * √(rescaledFieldNormSq s h b ζ) := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two],
    ← Real.sqrt_mul zero_le_four, rescaledFieldNormSq_eq_rescaledTargetNormSq]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [rescaledTargetNormSq_nonneg (s + 1) h b, sq_nonneg h,
    mul_nonneg (sq_nonneg h) (rescaledTargetNormSq_nonneg (s + 1) h b)]

/-! ### The scaling check -/

/-- The dilation law of a single term: for `ζ` of class `Cʲ` and `h > 0`,
`h^(2j) ‖Dʲ ζ‖₂² = hⁿ ‖Dʲ (ζ (h • ·))‖₂²`. -/
private theorem pow_mul_lpNorm_sq_eq {j : ℕ} {ζ : V → S} (hζ : ContDiff ℝ j ζ) {h : ℝ}
    (hh : 0 < h) :
    h ^ (2 * j) * lpNorm (iteratedFDeriv ℝ j ζ) 2 volume ^ 2 =
      h ^ (finrank ℝ V : ℝ) * lpNorm (iteratedFDeriv ℝ j fun w ↦ ζ (h • w)) 2 volume ^ 2 := by
  rw [Measure.lpNorm_iteratedFDeriv_comp_smul volume hζ hh.ne', abs_of_pos hh, mul_pow,
    ← mul_assoc, ← Real.rpow_natCast (h ^ _) 2, ← Real.rpow_mul hh.le, ← Real.rpow_add hh,
    ← Real.rpow_natCast]
  congr 2
  simp only [ENNReal.toReal_ofNat]
  push_cast
  ring

/-- **The scaling check for the target norm.** For `y` of class `C^(s-1)` and `h > 0`,
`‖y‖_(F_(r,s-1))² = hⁿ ∑_{j < s} ‖Dʲ y_w‖₂²` with `y_w(w) = y(h w)`, `n = dim V`. -/
theorem rescaledTargetNormSq_eq_rpow_mul {s : ℕ} {y : V → T} (hy : ContDiff ℝ (s - 1 : ℕ) y)
    {h : ℝ} (hh : 0 < h) :
    rescaledTargetNormSq s h y =
      h ^ (finrank ℝ V : ℝ) * rescaledTargetNormSq s 1 (fun w ↦ y (h • w)) := by
  rw [rescaledTargetNormSq, rescaledTargetNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjs : j ≤ s - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.1 hj)
  rw [one_pow, one_mul]
  exact pow_mul_lpNorm_sq_eq (hy.of_le (by exact_mod_cast hjs)) hh

/-- **The scaling check for the rescaled norm.** In the rescaled coordinate `w = λ y`,
`λ = h⁻¹`, the connection increment has plane coefficient `b_w(w) = h b(h w)` and the spinor
increment is `ζ_w(w) = ζ(h w)`, and
`‖(b, ζ)‖_(E_(r,s))² = hⁿ ∑_{j ≤ s} (‖Dʲ b_w‖₂² + ‖Dʲ ζ_w‖₂² / 4)`, for `b` and `ζ` of class
`Cˢ` and `n = dim V`: the unit-scale norm of the rescaled fields, in the coefficient metric
`|b|² + |δα|² / 4`, times the volume factor `hⁿ`. -/
theorem rescaledFieldNormSq_eq_rpow_mul {s : ℕ} {b : V → B} {ζ : V → S} (hb : ContDiff ℝ s b)
    (hζ : ContDiff ℝ s ζ) {h : ℝ} (hh : 0 < h) :
    rescaledFieldNormSq s h b ζ = h ^ (finrank ℝ V : ℝ) *
      rescaledFieldNormSq s 1 (fun w ↦ h • b (h • w)) (fun w ↦ ζ (h • w)) := by
  rw [rescaledFieldNormSq_eq_rescaledTargetNormSq, rescaledFieldNormSq_eq_rescaledTargetNormSq,
    rescaledTargetNormSq_eq_rpow_mul hb hh, rescaledTargetNormSq_eq_rpow_mul hζ hh]
  -- The rescaled connection `h • b (h • ·)` is `h` times `b (h • ·)`.
  linear_combination
    -h ^ (finrank ℝ V : ℝ) * rescaledTargetNormSq_smul (s + 1) 1 h fun w ↦ b (h • w)

/-! ### Equivalence with the fixed-order norms -/

/-- **The target norm below the unit-scale norm.** For `0 ≤ h ≤ 1`,
`‖y‖_(F_(r,s-1))² ≤ ∑_{j < s} ‖Dʲ y‖₂²`. -/
theorem rescaledTargetNormSq_le_rescaledTargetNormSq_one (s : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (hh₁ : h ≤ 1) (y : V → T) :
    rescaledTargetNormSq s h y ≤ rescaledTargetNormSq s 1 y := by
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [one_pow, one_mul]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hh hh₁)

/-- **The unit-scale target norm below the rescaled one.** For `0 ≤ h ≤ 1`,
`h^(2(s-1)) ∑_{j < s} ‖Dʲ y‖₂² ≤ ‖y‖_(F_(r,s-1))²`. -/
theorem pow_mul_rescaledTargetNormSq_one_le (s : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (y : V → T) :
    h ^ (2 * (s - 1)) * rescaledTargetNormSq s 1 y ≤ rescaledTargetNormSq s h y := by
  rw [rescaledTargetNormSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  rw [one_pow, one_mul]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one hh hh₁ (by have := Finset.mem_range.1 hj; omega)) (sq_nonneg _)

/-- **The rescaled norm below the unit-scale norm.** For `0 ≤ h ≤ 1`,
`‖(b, ζ)‖_(E_(r,s))² ≤ ∑_{j ≤ s} (‖Dʲ b‖₂² + ‖Dʲ ζ‖₂² / 4)`. -/
theorem rescaledFieldNormSq_le_rescaledFieldNormSq_one (s : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (b : V → B) (ζ : V → S) : rescaledFieldNormSq s h b ζ ≤ rescaledFieldNormSq s 1 b ζ := by
  rw [rescaledFieldNormSq_eq_rescaledTargetNormSq, rescaledFieldNormSq_eq_rescaledTargetNormSq,
    one_pow, one_mul]
  gcongr ?_ + ?_ / 4
  · exact (mul_le_of_le_one_left (rescaledTargetNormSq_nonneg _ h b) (pow_le_one₀ hh hh₁)).trans
      (rescaledTargetNormSq_le_rescaledTargetNormSq_one _ hh hh₁ b)
  · exact rescaledTargetNormSq_le_rescaledTargetNormSq_one _ hh hh₁ ζ

/-- **The unit-scale norm below the rescaled norm.** For `0 ≤ h ≤ 1`, the unit-scale norm loses at
most `h^(2s+2)`: `h^(2s+2) ∑_{j ≤ s} (‖Dʲ b‖₂² + ‖Dʲ ζ‖₂² / 4) ≤ ‖(b, ζ)‖_(E_(r,s))²`. -/
theorem pow_mul_rescaledFieldNormSq_one_le (s : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (b : V → B) (ζ : V → S) :
    h ^ (2 * s + 2) * rescaledFieldNormSq s 1 b ζ ≤ rescaledFieldNormSq s h b ζ := by
  rw [rescaledFieldNormSq_eq_rescaledTargetNormSq, rescaledFieldNormSq_eq_rescaledTargetNormSq,
    one_pow, one_mul]
  have hb := pow_mul_rescaledTargetNormSq_one_le (s + 1) hh hh₁ b
  have hζ := pow_mul_rescaledTargetNormSq_one_le (s + 1) hh hh₁ ζ
  rw [Nat.add_sub_cancel] at hb hζ
  -- The connection gains the factor `h²`; the spinor loses it, as `h^(2s+2) ≤ h^(2s)`.
  have hs : h ^ (2 * s + 2) ≤ h ^ (2 * s) := pow_le_pow_of_le_one hh hh₁ (by omega)
  have h1 := rescaledTargetNormSq_nonneg (s + 1) 1 ζ
  rw [pow_add, mul_comm (h ^ (2 * s))] at hs ⊢
  nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg h), mul_le_mul_of_nonneg_right hs h1]

/-! ### Comparison with the semiclassical norms -/

/-- **The rescaled norm below the semiclassical norms.** For `h > 0`,
`‖(b, ζ)‖_(E_(r,s))² ≤ hⁿ (h² ‖b‖_{s,h}² + ‖ζ‖_{s,h}² / 4)`, where `‖·‖_{s,h}` is the
semiclassical Sobolev norm `TauCeti.semiclassicalSobolevNorm`. -/
theorem rescaledFieldNormSq_le_rpow_mul (s : ℕ) {h : ℝ} (hh : 0 < h) (b : V → B) (ζ : V → S) :
    rescaledFieldNormSq s h b ζ ≤ h ^ (finrank ℝ V : ℝ) *
      (h ^ 2 * semiclassicalSobolevNorm s h b ^ 2 + semiclassicalSobolevNorm s h ζ ^ 2 / 4) := by
  rw [rescaledFieldNormSq_eq_sum_sq, mul_add, mul_left_comm, mul_div_assoc']
  gcongr
  · exact sum_sq_le_rpow_mul_semiclassicalSobolevNorm_sq s hh b
  · exact sum_sq_le_rpow_mul_semiclassicalSobolevNorm_sq s hh ζ

/-- **The semiclassical norms below the rescaled norm.** For `h > 0`,
`hⁿ (h² ‖b‖_{s,h}² + ‖ζ‖_{s,h}² / 4) ≤ (s + 1) ‖(b, ζ)‖_(E_(r,s))²`. -/
theorem rpow_mul_le_mul_rescaledFieldNormSq (s : ℕ) {h : ℝ} (hh : 0 < h) (b : V → B)
    (ζ : V → S) :
    h ^ (finrank ℝ V : ℝ) *
        (h ^ 2 * semiclassicalSobolevNorm s h b ^ 2 + semiclassicalSobolevNorm s h ζ ^ 2 / 4) ≤
      (s + 1) * rescaledFieldNormSq s h b ζ := by
  have hb := rpow_mul_semiclassicalSobolevNorm_sq_le s hh b
  have hζ := rpow_mul_semiclassicalSobolevNorm_sq_le s hh ζ
  rw [rescaledFieldNormSq_eq_sum_sq]
  nlinarith [sq_nonneg h]

/-! ### Gauge, bundle and tube charts -/

/-- If the square sums of `b'` and `ζ'` are at most `c₁` and `c₂` times those of `b` and `ζ`,
then `‖(b', ζ')‖_(E_(r,s))² ≤ max c₁ c₂ ‖(b, ζ)‖_(E_(r,s))²`. -/
private theorem rescaledFieldNormSq_le_max_mul {s : ℕ} {h c₁ c₂ : ℝ} {b : V → B} {ζ : V → S}
    {B' S' : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B'] [NormedAddCommGroup S']
    [NormedSpace ℝ S'] {b' : V → B'} {ζ' : V → S'}
    (hb : ∑ j ∈ Finset.range (s + 1), (h ^ j * lpNorm (iteratedFDeriv ℝ j b') 2 volume) ^ 2 ≤
      c₁ * ∑ j ∈ Finset.range (s + 1), (h ^ j * lpNorm (iteratedFDeriv ℝ j b) 2 volume) ^ 2)
    (hζ : ∑ j ∈ Finset.range (s + 1), (h ^ j * lpNorm (iteratedFDeriv ℝ j ζ') 2 volume) ^ 2 ≤
      c₂ * ∑ j ∈ Finset.range (s + 1), (h ^ j * lpNorm (iteratedFDeriv ℝ j ζ) 2 volume) ^ 2) :
    rescaledFieldNormSq s h b' ζ' ≤ max c₁ c₂ * rescaledFieldNormSq s h b ζ := by
  rw [rescaledFieldNormSq_eq_sum_sq, rescaledFieldNormSq_eq_sum_sq]
  have hb0 : 0 ≤ ∑ j ∈ Finset.range (s + 1),
      (h ^ j * lpNorm (iteratedFDeriv ℝ j b) 2 volume) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hζ0 : 0 ≤ ∑ j ∈ Finset.range (s + 1),
      (h ^ j * lpNorm (iteratedFDeriv ℝ j ζ) 2 volume) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right (le_max_left c₁ c₂) (mul_nonneg (sq_nonneg h) hb0),
    mul_le_mul_of_nonneg_right (le_max_right c₁ c₂) hζ0, mul_le_mul_of_nonneg_left hb (sq_nonneg h)]

section Gauge

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 S] [IsScalarTower ℝ 𝕜 S]

/-- **Multiplication of the spinor increment by a gauge with semiclassical bounds.** Let `ζ` be of
class `Cˢ` with square-integrable derivatives through order `s`, and let `g : V → 𝕜` be of class
`Cˢ` with `hⁱ ‖Dⁱ g‖ ≤ M` everywhere for `i ≤ s`, such as a unitary gauge varying on the scale
`h`. Then `‖(b, g ζ)‖_(E_(r,s))² ≤ max 1 ((s + 1) ((s + 1) 2ˢ M)²) ‖(b, ζ)‖_(E_(r,s))²`, with a
constant depending only on `s` and `M`, not on `h`. -/
theorem rescaledFieldNormSq_smul_le {s : ℕ} {h M : ℝ} {g : V → 𝕜} {ζ : V → S}
    (hg : ContDiff ℝ s g) (hζ : ContDiff ℝ s ζ) (hζm : ∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ) 2)
    (hh : 0 < h) (hM : ∀ i ≤ s, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i g x‖ ≤ M) (b : V → B) :
    rescaledFieldNormSq s h b (fun y ↦ g y • ζ y) ≤
      max 1 ((s + 1) * ((s + 1) * 2 ^ s * M) ^ 2) * rescaledFieldNormSq s h b ζ :=
  rescaledFieldNormSq_le_max_mul (one_mul _).symm.le
    (sum_sq_le_mul_sum_sq_of_semiclassicalSobolevNorm_le s hh
      (semiclassicalSobolevNorm_smul_le_of_le_left hg hζ hζm hh hM).2)

end Gauge

/-- **Changes of bundle frames.** Let `b` and `ζ` be of class `Cˢ` with square-integrable
derivatives through order `s`, and let `A : V → B →L[ℝ] B'` and `A' : V → S →L[ℝ] S'` be of class
`Cˢ` with `hⁱ ‖Dⁱ A‖ ≤ M` and `hⁱ ‖Dⁱ A'‖ ≤ M'` everywhere for `i ≤ s`, such as changes of
unitary frames of the connection and spinor bundles varying on the scale `h`. Then
`‖(A b, A' ζ)‖_(E_(r,s))² ≤ max c c' ‖(b, ζ)‖_(E_(r,s))²` with `c = (s + 1) ((s + 1) 2ˢ M)²` and
`c' = (s + 1) ((s + 1) 2ˢ M')²`, constants depending only on `s`, `M` and `M'`, not on `h`. -/
theorem rescaledFieldNormSq_clm_apply_le {s : ℕ} {h M M' : ℝ} {b : V → B} {ζ : V → S}
    {B' S' : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B'] [NormedAddCommGroup S']
    [NormedSpace ℝ S'] {A : V → B →L[ℝ] B'} {A' : V → S →L[ℝ] S'} (hA : ContDiff ℝ s A)
    (hA' : ContDiff ℝ s A') (hb : ContDiff ℝ s b) (hζ : ContDiff ℝ s ζ)
    (hbm : ∀ i ≤ s, MemLp (iteratedFDeriv ℝ i b) 2) (hζm : ∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ) 2)
    (hh : 0 < h) (hM : ∀ i ≤ s, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hM' : ∀ i ≤ s, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i A' x‖ ≤ M') :
    rescaledFieldNormSq s h (fun y ↦ A y (b y)) (fun y ↦ A' y (ζ y)) ≤
      max ((s + 1) * ((s + 1) * 2 ^ s * M) ^ 2) ((s + 1) * ((s + 1) * 2 ^ s * M') ^ 2) *
        rescaledFieldNormSq s h b ζ :=
  rescaledFieldNormSq_le_max_mul
    (sum_sq_le_mul_sum_sq_of_semiclassicalSobolevNorm_le s hh
      (semiclassicalSobolevNorm_clm_apply_le_of_le_left hA hb hbm hh hM).2)
    (sum_sq_le_mul_sum_sq_of_semiclassicalSobolevNorm_le s hh
      (semiclassicalSobolevNorm_clm_apply_le_of_le_left hA' hζ hζm hh hM').2)

/-- **Changes of tube charts.** Let `Φ : V → V` be a chart at scale `h`: an injective map of class
`Cˢ` with `h^(i-1) ‖Dⁱ Φ‖ ≤ L` for `1 ≤ i ≤ s` and `c ≤ |det DΦ|` with `c > 0`, as in
`TauCeti.semiclassicalSobolevNorm_comp_le`. For `b` and `ζ` of class `Cˢ` with square-integrable
derivatives through order `s`, the fields read in the chart satisfy
`‖(b ∘ Φ, ζ ∘ Φ)‖_(E_(r,s))² ≤ (s + 1) K² ‖(b, ζ)‖_(E_(r,s))²` with
`K = TauCeti.Wkp.compLBound 2 s L c`, a constant depending only on `s`, `L` and `c`, not on `h`.
The components of a connection form are then transformed by the transpose of `DΦ`, a change of
frame as in `TauCeti.SeibergWitten.rescaledFieldNormSq_clm_apply_le`. -/
theorem rescaledFieldNormSq_comp_le {s : ℕ} {h L c : ℝ} {b : V → B} {ζ : V → S} {Φ : V → V}
    (hb : ContDiff ℝ s b) (hζ : ContDiff ℝ s ζ) (hbm : ∀ i ≤ s, MemLp (iteratedFDeriv ℝ i b) 2)
    (hζm : ∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ) 2) (hΦ : ContDiff ℝ s Φ)
    (hΦd : Differentiable ℝ Φ) (hinj : Function.Injective Φ) (hh : 0 < h)
    (hL : ∀ i, 1 ≤ i → i ≤ s → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ Φ x).det|) :
    rescaledFieldNormSq s h (b ∘ Φ) (ζ ∘ Φ) ≤
      (s + 1) * Wkp.compLBound 2 s L c ^ 2 * rescaledFieldNormSq s h b ζ := by
  have := rescaledFieldNormSq_le_max_mul (s := s) (h := h) (b := b) (ζ := ζ) (b' := b ∘ Φ)
    (ζ' := ζ ∘ Φ) (sum_sq_le_mul_sum_sq_of_semiclassicalSobolevNorm_le s hh
      (semiclassicalSobolevNorm_comp_le hb hbm hΦ hΦd hinj hh hL hc hdet))
    (sum_sq_le_mul_sum_sq_of_semiclassicalSobolevNorm_le s hh
      (semiclassicalSobolevNorm_comp_le hζ hζm hΦ hΦd hinj hh hL hc hdet))
  rwa [max_self] at this

/-! ### The target norm against the semiclassical norms -/

/-- **The target norm below the semiclassical norm.** For `h > 0`,
`‖y‖_(F_(r,k))² ≤ hⁿ ‖y‖_{k,h}²`. -/
theorem rescaledTargetNormSq_succ_le_rpow_mul (k : ℕ) {h : ℝ} (hh : 0 < h) (y : V → T) :
    rescaledTargetNormSq (k + 1) h y ≤
      h ^ (finrank ℝ V : ℝ) * semiclassicalSobolevNorm k h y ^ 2 := by
  rw [rescaledTargetNormSq_eq_sum_sq]
  exact sum_sq_le_rpow_mul_semiclassicalSobolevNorm_sq k hh y

/-- **The semiclassical norm below the target norm.** For `h > 0`,
`hⁿ ‖y‖_{k,h}² ≤ (k + 1) ‖y‖_(F_(r,k))²`. -/
theorem rpow_mul_le_mul_rescaledTargetNormSq_succ (k : ℕ) {h : ℝ} (hh : 0 < h) (y : V → T) :
    h ^ (finrank ℝ V : ℝ) * semiclassicalSobolevNorm k h y ^ 2 ≤
      (k + 1) * rescaledTargetNormSq (k + 1) h y := by
  rw [rescaledTargetNormSq_eq_sum_sq]
  exact rpow_mul_semiclassicalSobolevNorm_sq_le k hh y

/-- **Changes of frame of the target bundle.** If `y` is of class `Cᵏ` with square-integrable
derivatives through order `k`, and `A : V → T →L[ℝ] T'` is of class `Cᵏ` with `hⁱ ‖Dⁱ A‖ ≤ M`
everywhere for `i ≤ k`, then
`‖A y‖_(F_(r,k))² ≤ (k + 1) ((k + 1) 2ᵏ M)² ‖y‖_(F_(r,k))²`. -/
theorem rescaledTargetNormSq_clm_apply_le {k : ℕ} {h M : ℝ} {y : V → T} {T' : Type*}
    [NormedAddCommGroup T'] [NormedSpace ℝ T'] {A : V → T →L[ℝ] T'} (hA : ContDiff ℝ k A)
    (hy : ContDiff ℝ k y) (hym : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i y) 2) (hh : 0 < h)
    (hM : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M) :
    rescaledTargetNormSq (k + 1) h (fun x ↦ A x (y x)) ≤
      (k + 1) * ((k + 1) * 2 ^ k * M) ^ 2 * rescaledTargetNormSq (k + 1) h y := by
  rw [rescaledTargetNormSq_eq_sum_sq, rescaledTargetNormSq_eq_sum_sq]
  exact sum_sq_le_mul_sum_sq_of_semiclassicalSobolevNorm_le k hh
    (semiclassicalSobolevNorm_clm_apply_le_of_le_left hA hy hym hh hM).2

/-! ### The algebra estimate -/

/-- The square-root form of `rpow_mul_le_mul_rescaledTargetNormSq_succ`:
`h^(n/2) ‖y‖_{k,h} ≤ √(k + 1) ‖y‖_(F_(r,k))`. -/
private theorem rpow_mul_semiclassicalSobolevNorm_le_sqrt {T' : Type*} [NormedAddCommGroup T']
    [NormedSpace ℝ T'] (k : ℕ) {h : ℝ} (hh : 0 < h) (y : V → T') :
    h ^ ((finrank ℝ V : ℝ) / 2) * semiclassicalSobolevNorm k h y ≤
      √(k + 1 : ℝ) * √(rescaledTargetNormSq (k + 1) h y) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt (le_trans (le_of_eq ?_)
    (rpow_mul_le_mul_rescaledTargetNormSq_succ k hh y)))
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]
  norm_num

/-- **The algebra estimate for the target norm.** Let `B` and `S` be finite-dimensional and
`n = dim V < 2k`. There is a constant `C ≥ 0` such that for every `h > 0`, every continuous bilinear
map `L : B →L[ℝ] S →L[ℝ] T` and all `f`, `g` of class `Cᵏ` with square-integrable derivatives
through order `k`, the derivatives of `L (f, g)` through order `k` are square integrable and

`‖L (f, g)‖_(F_(r,k)) ≤ C ‖L‖ h^(-n/2) ‖f‖_(F_(r,k)) ‖g‖_(F_(r,k))`.

The factor `h^(-n/2)` is the price of the missing volume normalization: the target norm is
comparable to `h^(n/2)` times the semiclassical norm,
`‖y‖_(F_(r,k))² ≤ hⁿ ‖y‖_{k,h}² ≤ (k + 1) ‖y‖_(F_(r,k))²`, and the semiclassical norm is an
algebra norm uniformly in `h` (`TauCeti.exists_semiclassicalSobolevNorm_bilinear_le`). -/
theorem exists_sqrt_rescaledTargetNormSq_bilinear_le {k : ℕ} (hk : finrank ℝ V < 2 * k)
    [FiniteDimensional ℝ B] [FiniteDimensional ℝ S] :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ (L : B →L[ℝ] S →L[ℝ] T) (f : V → B) (g : V → S),
      ContDiff ℝ k f → ContDiff ℝ k g → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) 2) →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i fun x ↦ L (f x) (g x)) 2) ∧
        √(rescaledTargetNormSq (k + 1) h fun x ↦ L (f x) (g x)) ≤
          C * ‖L‖ * h ^ (-(finrank ℝ V : ℝ) / 2) * √(rescaledTargetNormSq (k + 1) h f) *
            √(rescaledTargetNormSq (k + 1) h g) := by
  obtain ⟨C₀, hC₀, hL⟩ := exists_semiclassicalSobolevNorm_bilinear_le (E := V) (F := B) hk S T
  refine ⟨C₀ * (k + 1), by positivity, fun h hh L f g hf hg hfm hgm ↦ ?_⟩
  obtain ⟨hm, hle⟩ := hL h hh L f g hf hg hfm hgm
  refine ⟨hm, ?_⟩
  -- With `a = h^(n/2)`: `√F(y) ≤ a ‖y‖_{k,h}` and `a ‖y‖_{k,h} ≤ √(k + 1) √F(y)`.
  set a := h ^ ((finrank ℝ V : ℝ) / 2) with ha
  have ha₀ : 0 < a := Real.rpow_pos_of_pos hh _
  have ha2 : h ^ (finrank ℝ V : ℝ) = a ^ 2 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  have hainv : h ^ (-(finrank ℝ V : ℝ) / 2) = a⁻¹ := by
    rw [ha, ← Real.rpow_neg hh.le, neg_div]
  have hup : √(rescaledTargetNormSq (k + 1) h fun x ↦ L (f x) (g x)) ≤
      a * semiclassicalSobolevNorm k h (fun x ↦ L (f x) (g x)) := by
    rw [← Real.sqrt_sq (mul_nonneg ha₀.le (semiclassicalSobolevNorm_nonneg k hh.le _))]
    exact Real.sqrt_le_sqrt
      ((rescaledTargetNormSq_succ_le_rpow_mul k hh _).trans_eq (by rw [ha2]; ring))
  have hf' := rpow_mul_semiclassicalSobolevNorm_le_sqrt k hh f
  have hg' := rpow_mul_semiclassicalSobolevNorm_le_sqrt k hh g
  have hc₀ : 0 ≤ C₀ * ‖L‖ * a⁻¹ := by positivity
  have hk1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ k + 1 by positivity)
  rw [hainv]
  calc √(rescaledTargetNormSq (k + 1) h fun x ↦ L (f x) (g x))
      ≤ a * (C₀ * ‖L‖ * semiclassicalSobolevNorm k h f * semiclassicalSobolevNorm k h g) :=
        hup.trans (mul_le_mul_of_nonneg_left hle ha₀.le)
    _ = C₀ * ‖L‖ * a⁻¹ * (a * semiclassicalSobolevNorm k h f) *
          (a * semiclassicalSobolevNorm k h g) := by
        field_simp
    _ ≤ C₀ * ‖L‖ * a⁻¹ * (√(k + 1 : ℝ) * √(rescaledTargetNormSq (k + 1) h f)) *
          (√(k + 1 : ℝ) * √(rescaledTargetNormSq (k + 1) h g)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hf' hc₀) hg'
          (mul_nonneg ha₀.le (semiclassicalSobolevNorm_nonneg k hh.le g))
          (mul_nonneg hc₀ (by positivity))
    _ = C₀ * (k + 1) * ‖L‖ * a⁻¹ * √(rescaledTargetNormSq (k + 1) h f) *
          √(rescaledTargetNormSq (k + 1) h g) := by
        linear_combination (C₀ * ‖L‖ * a⁻¹ * √(rescaledTargetNormSq (k + 1) h f) *
          √(rescaledTargetNormSq (k + 1) h g)) * hk1

/-! ### The triangle inequality -/

/-- **The triangle inequality for the target norm.** For `y` and `y'` of class `C^(s-1)` with
square-integrable derivatives through order `s - 1`, and `h ≥ 0`,
`‖y + y'‖_(F_(r,s-1)) ≤ ‖y‖_(F_(r,s-1)) + ‖y'‖_(F_(r,s-1))`. -/
theorem sqrt_rescaledTargetNormSq_add_le {s : ℕ} {y y' : V → T}
    (hy : ContDiff ℝ (s - 1 : ℕ) y) (hy' : ContDiff ℝ (s - 1 : ℕ) y')
    (hym : ∀ j < s, MemLp (iteratedFDeriv ℝ j y) 2) {h : ℝ} (hh : 0 ≤ h) :
    √(rescaledTargetNormSq s h (y + y')) ≤
      √(rescaledTargetNormSq s h y) + √(rescaledTargetNormSq s h y') := by
  rw [rescaledTargetNormSq_eq_sum_sq, rescaledTargetNormSq_eq_sum_sq,
    rescaledTargetNormSq_eq_sum_sq]
  -- Minkowski's inequality in `ℓ²`, after bounding each term by the triangle inequality in `L²`.
  have hM := Real.Lp_add_le (Finset.range s)
    (fun j ↦ h ^ j * lpNorm (iteratedFDeriv ℝ j y) 2 volume)
    (fun j ↦ h ^ j * lpNorm (iteratedFDeriv ℝ j y') 2 volume) (p := 2) one_le_two
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at hM
  refine (Real.sqrt_le_sqrt (Finset.sum_le_sum fun j hj ↦ pow_le_pow_left₀
    (mul_nonneg (pow_nonneg hh j) lpNorm_nonneg) ?_ 2)).trans hM
  have hjs : j < s := Finset.mem_range.1 hj
  have hjs' : j ≤ s - 1 := Nat.le_sub_one_of_lt hjs
  rw [iteratedFDeriv_add (hy.of_le (by exact_mod_cast hjs')) (hy'.of_le (by exact_mod_cast hjs')),
    ← mul_add]
  exact mul_le_mul_of_nonneg_left (lpNorm_add_le (hym j hjs) one_le_two) (pow_nonneg hh j)

/-- **The triangle inequality for the rescaled norm.** For connection and spinor increments of
class `Cˢ`, with `b` and `ζ` having square-integrable derivatives through order `s`, and `h ≥ 0`,
`‖(b + b', ζ + ζ')‖_(E_(r,s)) ≤ ‖(b, ζ)‖_(E_(r,s)) + ‖(b', ζ')‖_(E_(r,s))`. -/
theorem sqrt_rescaledFieldNormSq_add_le {s : ℕ} {b b' : V → B} {ζ ζ' : V → S}
    (hb : ContDiff ℝ s b) (hb' : ContDiff ℝ s b') (hζ : ContDiff ℝ s ζ) (hζ' : ContDiff ℝ s ζ')
    (hbm : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j b) 2)
    (hζm : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j ζ) 2) {h : ℝ} (hh : 0 ≤ h) :
    √(rescaledFieldNormSq s h (b + b') (ζ + ζ')) ≤
      √(rescaledFieldNormSq s h b ζ) + √(rescaledFieldNormSq s h b' ζ') := by
  have hb₁ := sqrt_rescaledTargetNormSq_add_le (s := s + 1) (by simpa using hb)
    (by simpa using hb') (fun j hj ↦ hbm j (Nat.lt_succ_iff.1 hj)) hh
  have hζ₁ := sqrt_rescaledTargetNormSq_add_le (s := s + 1) (by simpa using hζ)
    (by simpa using hζ') (fun j hj ↦ hζm j (Nat.lt_succ_iff.1 hj)) hh
  simp only [rescaledFieldNormSq_eq_rescaledTargetNormSq]
  -- Minkowski's inequality in `ℝ²` for the vectors `(h ‖b‖_F, ‖ζ‖_F / 2)` of target norms.
  have hM := Real.Lp_add_le Finset.univ
    ![h * √(rescaledTargetNormSq (s + 1) h b), √(rescaledTargetNormSq (s + 1) h ζ) / 2]
    ![h * √(rescaledTargetNormSq (s + 1) h b'), √(rescaledTargetNormSq (s + 1) h ζ') / 2]
    (p := 2) one_le_two
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_two, sq_abs,
    ← Real.sqrt_eq_rpow, mul_pow, div_pow, Real.sq_sqrt (rescaledTargetNormSq_nonneg _ _ _),
    (by norm_num : (2 : ℝ) ^ 2 = 4)] at hM
  refine le_trans (Real.sqrt_le_sqrt ?_) hM
  calc _ ≤ h ^ 2 *
          (√(rescaledTargetNormSq (s + 1) h b) + √(rescaledTargetNormSq (s + 1) h b')) ^ 2 +
        (√(rescaledTargetNormSq (s + 1) h ζ) + √(rescaledTargetNormSq (s + 1) h ζ')) ^ 2 / 4 := by
        gcongr h ^ 2 * ?_ + ?_ / 4
        · exact (Real.sqrt_le_iff.1 hb₁).2
        · exact (Real.sqrt_le_iff.1 hζ₁).2
    _ = _ := by ring

end TauCeti.SeibergWitten
