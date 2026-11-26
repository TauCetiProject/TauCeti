/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Diffeomorph
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Adapted pseudo-gradients of the quadratic well and the saddle

A pseudo-gradient field adapted to a Morse function (`TauCeti.IsAdaptedPseudoGradient`) is, near
each critical point, the linear field `z ↦ (-wᵢ zᵢ)ᵢ` of a Morse chart, in which
`f = f(p) + (1/2) Σᵢ wᵢ zᵢ²` with weights `wᵢ = ±1`. This normalizes the speed of the field near
`p`, not only its direction: a positive multiple of an adapted pseudo-gradient need not be one.
This file tests the definition on the two simplest Morse functions.

* **The quadratic well `f(x) = x²` on `ℝ`.** Its Morse charts at `0` are `z = ±√2 x`
  (`TauCeti.MorseChart.sqReal` is the chart `z = √2 x`): every
  weight is `1` (`TauCeti.MorseChart.weight_eq_one_sq_real`) and `z² = 2 x²`
  (`TauCeti.MorseChart.sum_coord_toChart_sq_real`). So every pseudo-gradient adapted to `x²` is
  the field `x ↦ -x` near `0`
  (`TauCeti.IsAdaptedPseudoGradient.eventually_eq_neg_sq_real`), and the field `x ↦ -x` is one
  (`TauCeti.isAdaptedPseudoGradient_sq_real_neg`), with trajectories `t ↦ x₀ e⁻ᵗ`
  (`TauCeti.isMIntegralCurve_mul_exp_neg_neg`), and along it `df = -2 x²`
  (`TauCeti.mvfderiv_sq_real_apply`). The Euclidean negative
  gradient `x ↦ -2 x`, which reads `z ↦ -2 z` in the Morse chart, is not adapted
  (`TauCeti.not_isAdaptedPseudoGradient_sq_real_neg_mgradient`).
* **Metrics in which the negative gradient is adapted.** For the metric `a dx²` on `ℝ`
  (`TauCeti.scaledLineMetric`) the negative gradient of `x²` is `x ↦ -2 x / a`, so it is adapted
  exactly when `a = 2` (`TauCeti.isAdaptedPseudoGradient_neg_mgradient_sq_scaledLineMetric_iff`).
  The metric `2 dx²` is the Euclidean metric `dz²` of the Morse chart `z = √2 x`, in which the
  negative gradient of `x² = z² / 2` is `z ↦ -z`.
* **The saddle `f(u, v) = -u² + v²` on `ℝ²`.** In the Morse chart `z = √2 (u, v)` with weights
  `(-1, 1)` the field `(u, v) ↦ (u, -v)` reads `(z₁, -z₂)`, and it is adapted
  (`TauCeti.isAdaptedPseudoGradient_neg_sq_add_sq_prodMk_neg`), as the product of the adapted
  fields of `-u²` and `v²`; its trajectories are `t ↦ (u₀ eᵗ, v₀ e⁻ᵗ)`
  (`TauCeti.isMIntegralCurve_mul_exp_prodMk_mul_exp_neg`). The field `(u, v) ↦ (-u, -v)`,
  which reads `(-z₁, -z₂)`, is not adapted
  (`TauCeti.not_isAdaptedPseudoGradient_neg_sq_add_sq_neg`): along it `df = 2 u² - 2 v²`, which
  increases `f` on the `u`-axis.
* **A normalized field on a band.** On the band `1 ≤ x² ≤ 4`, the field `x ↦ -1 / (2 x)` lowers
  `x²` at unit speed (`TauCeti.mvfderiv_sq_real_apply_neg_inv`), as do the fields that deform a
  sublevel across a critical-free band
  (`TauCeti.exists_flow_apply_eq_sub_of_mvfderiv_lt_zero`). It is the normalized negative
  gradient `-grad f / ‖grad f‖²` of the standard metric
  (`TauCeti.inv_norm_mgradient_sq_real_sq_smul_neg_mgradient_sq_real`), the field along which
  `TauCeti.exists_sublevelDeformation_neg_mgradient` deforms sublevels.
  Its trajectory from `x = 2` is `t ↦ √(4 - t)` (`TauCeti.isMIntegralCurveOn_sqrt_four_sub`),
  which reaches `x = 1` at the time `3 = f(2) - 1`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Definition 2.2.1 (pseudo-gradient fields adapted to a Morse function).
-/

public section

open Filter Set Topology TauCeti.Manifold
open scoped Bundle ContDiff Manifold

namespace TauCeti

/-! ### The quadratic well -/

namespace MorseChart

/-- **The Morse chart `z = √2 x` of the quadratic well** at `0`: the identity chart of `ℝ`, with the
coordinate `z = √2 x` and the weight `1`, in which `x² = z² / 2`. -/
noncomputable def sqReal : MorseChart ℝ (fun x : ℝ ↦ x ^ 2) 0 where
  toChart := OpenPartialHomeomorph.refl ℝ
  mem_maximalAtlas := by
    simpa using IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, ℝ)) (n := ∞) (0 : ℝ)
  mem_source := mem_univ _
  apply_self := rfl
  coord :=
    letI : Unique (Fin (Module.finrank ℝ ℝ)) := by
      rw [Module.finrank_self]
      infer_instance
    (LinearEquiv.smulOfNeZero ℝ ℝ √2 (by positivity)).trans
      (LinearEquiv.funUnique (Fin (Module.finrank ℝ ℝ)) ℝ ℝ).symm
  weight := fun _ ↦ 1
  weight_eq_neg_one_or_eq_one := fun _ ↦ Or.inr rfl
  ncard_weight_neg := by
    rw [manifoldMorseIndex_sq_real_zero, Set.ncard_eq_zero]
    exact Set.eq_empty_of_forall_notMem fun _ hi ↦ not_lt.2 zero_le_one (Set.mem_ofPred.1 hi)
  eq_quadratic y _ := by
    simp [Real.sq_sqrt, mul_pow]

/-- The chart of `MorseChart.sqReal` is the identity of `ℝ`. -/
@[simp]
theorem sqReal_toChart : sqReal.toChart = OpenPartialHomeomorph.refl ℝ := by
  rw [sqReal]

/-- The weights of `MorseChart.sqReal` are `1`. -/
@[simp]
theorem sqReal_weight (i : Fin (Module.finrank ℝ ℝ)) : sqReal.weight i = 1 := by
  rw [sqReal]

/-- The coordinate of `MorseChart.sqReal` is `z = √2 x`. -/
@[simp]
theorem sqReal_coord_apply (v : ℝ) (i : Fin (Module.finrank ℝ ℝ)) :
    sqReal.coord v i = √2 * v := by
  rw [sqReal]
  simp

variable (φ : MorseChart ℝ (fun x : ℝ ↦ x ^ 2) 0)

/-- Every weight of a Morse chart of `x ↦ x²` at its minimum `0` is `1`. -/
theorem weight_eq_one_sq_real (i : Fin (Module.finrank ℝ ℝ)) : φ.weight i = 1 :=
  φ.weight_eq_one_of_manifoldMorseIndex_eq_zero manifoldMorseIndex_sq_real_zero i

/-- **Morse charts of the quadratic well.** In every Morse chart of `x ↦ x²` at `0`, the
coordinates `z` of a point `y` satisfy `Σᵢ zᵢ² = 2 y²`: the chart is `z = ±√2 y`. -/
theorem sum_coord_toChart_sq_real {y : ℝ} (hy : y ∈ φ.toChart.source) :
    ∑ i, φ.coord (φ.toChart y) i ^ 2 = 2 * y ^ 2 := by
  have h := φ.eq_quadratic y hy
  simp only [φ.weight_eq_one_sq_real, one_mul] at h
  linarith

end MorseChart

namespace IsAdaptedPseudoGradient

/-- **Adapted pseudo-gradients of the quadratic well.** Every pseudo-gradient adapted to
`x ↦ x²` on `ℝ` is the field `x ↦ -x` near the critical point `0`. -/
theorem eventually_eq_neg_sq_real {X : ℝ → ℝ}
    (hX : IsAdaptedPseudoGradient (fun x : ℝ ↦ x ^ 2) X) : ∀ᶠ y in 𝓝 0, X y = -y := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart 0 mfderiv_sq_real_zero
  filter_upwards [φ.toChart.open_source.mem_nhds φ.mem_source] with y hy
  have hd := φ.mvfderiv_field_apply hy
  rw [← φ.eq_field_of_coord_mfderiv hy (hφ y hy), φ.sum_coord_toChart_sq_real hy] at hd
  have hd' := (mvfderiv_sq_real_apply y (X y)).symm.trans hd
  rcases eq_or_ne y 0 with rfl | hy0
  · exact (hX.eq_zero_of_mfderiv_eq_zero mfderiv_sq_real_zero).trans neg_zero.symm
  · exact mul_left_cancel₀ (mul_ne_zero two_ne_zero hy0) (by linear_combination hd')

end IsAdaptedPseudoGradient

/-- **The field `x ↦ -x` is a pseudo-gradient adapted to `x ↦ x²`.** In the Morse chart
`z = √2 x` at `0` (`MorseChart.sqReal`), where `x² = z² / 2`, it reads `z ↦ -z`. -/
theorem isAdaptedPseudoGradient_sq_real_neg :
    IsAdaptedPseudoGradient (fun x : ℝ ↦ x ^ 2) fun x ↦ (-x : ℝ) where
  contMDiff := contMDiff_vectorSpace_iff_contDiff.2 contDiff_neg
  mvfderiv_apply_lt_zero x hx := by
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx mfderiv_sq_real_zero
    rw [mvfderiv_sq_real_apply x (-x)]
    nlinarith [sq_pos_of_ne_zero hx0]
  exists_morseChart x hx := by
    obtain rfl : x = 0 := by
      have h : x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) :=
        mem_criticalPoints_iff_mfderiv_eq_zero.2 hx
      rwa [criticalPoints_sq_real] at h
    refine ⟨MorseChart.sqReal, fun y _ ↦ ?_⟩
    -- The chart is the identity of `ℝ`, whose derivative is the identity.
    ext i
    rw [MorseChart.sqReal_toChart, OpenPartialHomeomorph.refl_apply, mfderiv_id]
    -- The identity of the tangent space at `y` sends `-y` to the real number `-y`.
    have hv : ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) y) (-y) = (-y : ℝ) := rfl
    simp only [id_eq, MorseChart.sqReal_weight, one_mul, MorseChart.sqReal_coord_apply, hv]
    ring

/-- The flow of the adapted pseudo-gradient `x ↦ -x` of `x ↦ x²`: its trajectory through `x₀` is
`t ↦ x₀ e⁻ᵗ`. -/
theorem isMIntegralCurve_mul_exp_neg_neg (x₀ : ℝ) :
    IsMIntegralCurve (I := 𝓘(ℝ, ℝ)) (fun t ↦ x₀ * Real.exp (-t)) fun x : ℝ ↦ (-x : ℝ) := by
  refine isMIntegralCurve_iff_isMIntegralCurveOn.2
    (isMIntegralCurveOn_iff_isIntegralCurveOn.2 fun t _ ↦ ?_)
  exact ((hasDerivAt_neg t).exp.const_mul x₀).hasDerivWithinAt.congr_deriv (by ring)

/-- The Euclidean negative gradient `x ↦ -2 x` of `x ↦ x²` is not an adapted pseudo-gradient:
near `0` an adapted pseudo-gradient is `x ↦ -x`. -/
theorem not_isAdaptedPseudoGradient_sq_real_neg_mgradient :
    ¬ IsAdaptedPseudoGradient (fun x : ℝ ↦ x ^ 2) (-mgradient 𝓘(ℝ, ℝ) fun x : ℝ ↦ x ^ 2) := by
  intro hX
  obtain ⟨y, hy, hy0⟩ := ((hX.eventually_eq_neg_sq_real.filter_mono nhdsWithin_le_nhds).and
    self_mem_nhdsWithin).exists (f := 𝓝[≠] (0 : ℝ))
  rw [neg_mgradient_sq_real_apply] at hy
  exact hy0 (by simp only [mem_singleton_iff]; linarith)

/-! ### Metrics in which the negative gradient is adapted -/

section ScaledMetric

open WithMetric

variable {a : ℝ} (ha : 0 < a)

/-- Read on `ℝ` through the identity `toWithMetric`, the negative gradient of `x ↦ x²` for the
metric `a dx²` is the field `x ↦ -2 x / a`. -/
private theorem mpullback_toWithMetric_neg_mgradient_sq_scaledLineMetric_apply (y : ℝ) :
    VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (toWithMetric (scaledLineMetric ha))
        (-mgradient 𝓘(ℝ, ℝ) fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2) y =
      (-(2 / a * y) : ℝ) := by
  have h := (diffeomorph (I := 𝓘(ℝ, ℝ)) (scaledLineMetric ha) ∞).symm.mfderiv_apply_mpullback
    (by simp) (-mgradient 𝓘(ℝ, ℝ) fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2) y
  rwa [coe_diffeomorph_symm, mfderiv_toWithMetric_apply, neg_mgradient_sq_scaledLineMetric_apply,
    ofWithMetric_toWithMetric] at h

/-- Pushed forward along the identity `toWithMetric`, the field `x ↦ -2 x / a` of `ℝ` is the
negative gradient of `x ↦ x²` for the metric `a dx²`. -/
private theorem mpullback_ofWithMetric_neg_mul_eq_neg_mgradient_sq_scaledLineMetric :
    VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (ofWithMetric (g := scaledLineMetric ha))
        (fun x : ℝ ↦ (-(2 / a * x) : ℝ)) =
      -mgradient 𝓘(ℝ, ℝ) fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2 := by
  funext y
  have h := (diffeomorph (I := 𝓘(ℝ, ℝ)) (scaledLineMetric ha) ∞).mfderiv_apply_mpullback
    (by simp) (fun x : ℝ ↦ (-(2 / a * x) : ℝ)) y
  rw [coe_diffeomorph, mfderiv_ofWithMetric_apply] at h
  rw [h, neg_mgradient_sq_scaledLineMetric_apply]

/-- **The negative gradient of the quadratic well is adapted exactly for the metric `2 dx²`.** For
the metric `a dx²` on `ℝ` (`TauCeti.scaledLineMetric`, on the copy
`WithMetric (scaledLineMetric ha)` of `ℝ`), the negative gradient of `x ↦ x²` is `x ↦ -2 x / a`
(`TauCeti.mgradient_sq_scaledLineMetric`), and it is a pseudo-gradient adapted to `x ↦ x²` if and
only if `a = 2`. The metric `2 dx²` is the Euclidean metric `dz²` of the Morse chart `z = √2 x`
(`MorseChart.sqReal`), in which the negative gradient of `x² = z² / 2` is the linear field
`z ↦ -z`. For the standard metric `a = 1`, the negative gradient `x ↦ -2 x` reads `z ↦ -2 z` and is
not adapted. -/
theorem isAdaptedPseudoGradient_neg_mgradient_sq_scaledLineMetric_iff :
    IsAdaptedPseudoGradient (fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2)
        (-mgradient 𝓘(ℝ, ℝ) fun y : WithMetric (scaledLineMetric ha) ↦ y.ofWithMetric ^ 2) ↔
      a = 2 := by
  let σ := WithMetric.diffeomorph (I := 𝓘(ℝ, ℝ)) (scaledLineMetric ha) ∞
  constructor
  · intro hX
    -- Pull the field back to `ℝ` along the identity `toWithMetric`, where it is `x ↦ -2 x / a`.
    have h := hX.mpullback σ.symm
    rw [coe_diffeomorph_symm] at h
    -- Near `0` the pulled-back field is `x ↦ -x`; compare at a point `y ≠ 0`.
    obtain ⟨y, hy, hy0⟩ := ((h.eventually_eq_neg_sq_real.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin).exists (f := 𝓝[≠] (0 : ℝ))
    rw [mpullback_toWithMetric_neg_mgradient_sq_scaledLineMetric_apply] at hy
    have h2 : 2 / a = 1 := mul_right_cancel₀ (show y ≠ 0 from hy0) (by linarith)
    exact ((div_eq_one_iff_eq ha.ne').1 h2).symm
  · rintro rfl
    -- Push the adapted field `x ↦ -x` of `ℝ` forward along the identity `ofWithMetric`.
    have h := isAdaptedPseudoGradient_sq_real_neg.mpullback σ
    rw [coe_diffeomorph] at h
    have hX : (fun x : ℝ ↦ (-x : ℝ)) = fun x ↦ (-(2 / 2 * x) : ℝ) := by
      rw [div_self two_ne_zero]
      simp only [one_mul]
    rwa [hX, mpullback_ofWithMetric_neg_mul_eq_neg_mgradient_sq_scaledLineMetric] at h

end ScaledMetric

/-! ### The saddle -/

/-- **The field `(u, v) ↦ (u, -v)` is a pseudo-gradient adapted to the saddle `-u² + v²`** on
`ℝ²`. In the Morse chart `z = √2 (u, v)` with weights `(-1, 1)` it reads `(z₁, -z₂)`. -/
theorem isAdaptedPseudoGradient_neg_sq_add_sq_prodMk_neg :
    IsAdaptedPseudoGradient (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) fun p ↦ ((p.1, -p.2) : ℝ × ℝ) := by
  have h := (isAdaptedPseudoGradient_sq_real_neg.neg isMorse_sq_real).prod_chartedSpaceSelf
    isAdaptedPseudoGradient_sq_real_neg
  -- Rewrite the function and the field of `h` pointwise.
  have key : ∀ (f g : ℝ × ℝ → ℝ) (X Y : ℝ × ℝ → ℝ × ℝ), f = g → X = Y →
      IsAdaptedPseudoGradient f X → IsAdaptedPseudoGradient g Y := by
    rintro f g X Y rfl rfl hX
    exact hX
  refine key _ _ _ _ ?_ ?_ h
  · ext p
    simp
  · refine funext fun p ↦ Prod.ext ?_ ?_
    · exact (Manifold.prodVectorField_fst _ _ p).trans (neg_neg p.1)
    · exact Manifold.prodVectorField_snd _ _ p

/-- The flow of the adapted pseudo-gradient `(u, v) ↦ (u, -v)` of the saddle `-u² + v²`: its
trajectory through `(u₀, v₀)` is `t ↦ (u₀ eᵗ, v₀ e⁻ᵗ)`. -/
theorem isMIntegralCurve_mul_exp_prodMk_mul_exp_neg (u₀ v₀ : ℝ) :
    IsMIntegralCurve (I := 𝓘(ℝ, ℝ × ℝ)) (fun t ↦ ((u₀ * Real.exp t, v₀ * Real.exp (-t)) : ℝ × ℝ))
      fun p : ℝ × ℝ ↦ ((p.1, -p.2) : ℝ × ℝ) := by
  refine isMIntegralCurve_iff_isMIntegralCurveOn.2
    (isMIntegralCurveOn_iff_isIntegralCurveOn.2 fun t _ ↦ ?_)
  refine (((Real.hasDerivAt_exp t).const_mul u₀).prodMk
    ((hasDerivAt_neg t).exp.const_mul v₀)).hasDerivWithinAt.congr_deriv ?_
  ext <;> simp

/-- The derivative of the saddle `-u² + v²` at `p`, applied to a tangent vector `v`. -/
theorem mvfderiv_neg_sq_add_sq_apply (p v : ℝ × ℝ) :
    mvfderiv 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) p v =
      -(2 * p.1 * v.1) + 2 * p.2 * v.2 := by
  have h : HasFDerivAt (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2) _ p :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2).neg.add ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2)
  refine (mvfderiv_eq_fderiv_apply _ p v).trans ?_
  rw [h.fderiv]
  simp

/-- **The field `(u, v) ↦ (-u, -v)` is not adapted to the saddle `-u² + v²`.** Along it the
derivative of the saddle is `2 u² - 2 v²`, which is positive on the `u`-axis away from `0`. -/
theorem not_isAdaptedPseudoGradient_neg_sq_add_sq_neg :
    ¬ IsAdaptedPseudoGradient (fun p : ℝ × ℝ ↦ -p.1 ^ 2 + p.2 ^ 2)
      fun p ↦ ((-p.1, -p.2) : ℝ × ℝ) := by
  intro hX
  have hd := mvfderiv_neg_sq_add_sq_apply (1, 0) (1, 0)
  have hlt := hX.mvfderiv_apply_lt_zero (1, 0) fun h ↦ by
    rw [mvfderiv_eq_zero_iff.2 h] at hd
    exact absurd ((zero_apply _).symm.trans hd) (by norm_num)
  have h2 := (mvfderiv_neg_sq_add_sq_apply (1, 0) _).symm.trans_lt hlt
  norm_num at h2

/-! ### A normalized field on a band -/

/-- Along the field `x ↦ -1 / (2 x)`, the function `x²` decreases at unit speed. -/
theorem mvfderiv_sq_real_apply_neg_inv {x : ℝ} (hx : x ≠ 0) :
    mvfderiv 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) x (-(2 * x)⁻¹) = -1 := by
  rw [mvfderiv_sq_real_apply]
  field_simp

/-- **The normalized negative gradient of the quadratic well.** For the standard metric on `ℝ`,
the normalized negative gradient `-grad f / ‖grad f‖²` of `f(x) = x²` is `x ↦ -1 / (2 x)`. At the
critical point `0` both sides vanish, by the convention `0⁻¹ = 0`. -/
theorem inv_norm_mgradient_sq_real_sq_smul_neg_mgradient_sq_real (x : ℝ) :
    (‖mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) x‖ ^ 2)⁻¹ •
        -mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) x = (-(2 * x)⁻¹ : ℝ) := by
  have h := neg_mgradient_sq_real_apply x
  rw [Pi.neg_apply] at h
  have hn : ‖mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) x‖ = |2 * x| := by
    rw [← norm_neg, norm_tangentSpace_vectorSpace, h]
    -- `NormedSpace.fromTangentSpace x` is the identity of `ℝ` by definition.
    exact (Real.norm_eq_abs (-(2 * x))).trans (abs_neg _)
  rw [hn, sq_abs, h]
  -- The scalar action of `ℝ` on its tangent space is multiplication.
  have hx : ((2 * x) ^ 2)⁻¹ * -(2 * x) = -(2 * x)⁻¹ := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · field_simp
  exact hx

/-- The trajectory of the normalized field `x ↦ -1 / (2 x)` through `2` is `t ↦ √(4 - t)`: it
crosses the band `1 ≤ x² ≤ 4` from `x = 2` to `x = 1` in the time `3 = f(2) - 1`. -/
theorem isMIntegralCurveOn_sqrt_four_sub :
    IsMIntegralCurveOn (I := 𝓘(ℝ, ℝ)) (fun t ↦ √(4 - t)) (fun x : ℝ ↦ (-(2 * x)⁻¹ : ℝ))
      (Iio 4) := by
  refine isMIntegralCurveOn_iff_isIntegralCurveOn.2 fun t (ht : t < 4) ↦ ?_
  have hpos : 0 < 4 - t := by linarith
  refine (((hasDerivAt_id' t).const_sub 4).sqrt hpos.ne').hasDerivWithinAt.congr_deriv ?_
  field_simp

end TauCeti
