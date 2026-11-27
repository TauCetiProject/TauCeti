/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Hyperplane
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.MeanInequalitiesPow
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Flat `L²` traces of the derivatives of a compactly supported function

For a compactly supported `C¹` function `u` on `ℝ × E`, with the Euclidean norm of
`WithLp 2 (ℝ × E)`, the flat trace inequality
`∫ ‖u(a, y)‖² dy ≤ ∫ (‖u‖² + ‖Du‖²)`
(`TauCeti.integral_hyperplane_norm_rpow_le_integral` with exponent two) gives, after taking square
roots, the bound

`‖u(a, ·)‖₂ ≤ ‖u‖₂ + ‖Du‖₂`

on the `L²` norm of the restriction of `u` to the hyperplane `{a} × E`
(`TauCeti.lpNorm_hyperplane_le`).

The derivatives of the restriction are the derivatives of `u` along the hyperplane: the restriction
is `u` composed with the isometric embedding `y ↦ (a, y)`, so the `i`-th derivative of the
restriction at `y` is the `i`-th derivative of `u` at `(a, y)` restricted to the directions
`(0, w)`, and its norm is at most `‖Dⁱ u(a, y)‖`. Applying the trace inequality to the compactly
supported `C¹` function `Dⁱ u` therefore gives, for `u` of class `Cⁱ⁺¹`,

`‖Dⁱ(u(a, ·))‖₂ ≤ ‖Dⁱ u‖₂ + ‖Dⁱ⁺¹ u‖₂`

(`TauCeti.lpNorm_iteratedFDeriv_hyperplane_le`). Restriction to a hyperplane thus loses one
derivative, with constants independent of `a`. These are the estimates behind the trace bounds for
the semiclassical Sobolev norms in `TauCeti.Analysis.Sobolev.Semiclassical.Trace`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5 (traces).
-/

public section

namespace TauCeti

open MeasureTheory

section General

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [OpensMeasurableSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G] {μ : Measure F}

/-- The square root of the integrated `L²` energy `‖u‖² + ‖Du‖²` of a compactly supported `C¹`
function, written as on the right of `TauCeti.integral_hyperplane_norm_rpow_le_integral` with
exponent two, is at most `‖u‖₂ + ‖Du‖₂`. -/
private theorem integral_energy_two_rpow_inv_le [IsFiniteMeasureOnCompacts μ] {u : F → G}
    (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u) :
    (∫ x, (2 - 1) * ‖u x‖ ^ (2 : ℝ) + ‖fderiv ℝ u x‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ ≤
      lpNorm u 2 μ + lpNorm (fderiv ℝ u) 2 μ := by
  have h2 : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hDu : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hum : MemLp u 2 μ := hu.continuous.memLp_of_hasCompactSupport hsupp
  have hDum : MemLp (fderiv ℝ u) 2 μ := hDu.memLp_of_hasCompactSupport (hsupp.fderiv (𝕜 := ℝ))
  have hint1 : Integrable (fun x ↦ ‖u x‖ ^ (2 : ℝ)) μ := by
    simpa only [ENNReal.toReal_ofNat] using hum.integrable_norm_rpow two_ne_zero h2
  have hint2 : Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ (2 : ℝ)) μ := by
    simpa only [ENNReal.toReal_ofNat] using hDum.integrable_norm_rpow two_ne_zero h2
  rw [lpNorm_eq_integral_norm_rpow_toReal two_ne_zero h2 hum.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal two_ne_zero h2 hDum.aestronglyMeasurable,
    show (2 : ℝ) - 1 = 1 by norm_num]
  simp only [one_mul, ENNReal.toReal_ofNat]
  rw [integral_add hint1 hint2]
  exact Real.rpow_add_le_add_rpow (integral_nonneg fun _ ↦ by positivity)
    (integral_nonneg fun _ ↦ by positivity) (by norm_num) (by norm_num)

end General

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The flat `L²` trace inequality in norm form.** For a compactly supported `C¹` function `u` on
`ℝ × E`, the restriction of `u` to the hyperplane `{a} × E` satisfies
`‖u(a, ·)‖₂ ≤ ‖u‖₂ + ‖Du‖₂`. -/
theorem lpNorm_hyperplane_le {u : WithLp 2 (ℝ × E) → G} (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) (a : ℝ) :
    lpNorm (fun y : E ↦ u (WithLp.toLp 2 (a, y))) 2 volume ≤
      lpNorm u 2 volume + lpNorm (fderiv ℝ u) 2 volume := by
  have hcont : Continuous fun y : E ↦ u (WithLp.toLp 2 (a, y)) :=
    hu.continuous.comp (by fun_prop)
  rw [lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
    hcont.aestronglyMeasurable, ENNReal.toReal_ofNat]
  refine (Real.rpow_le_rpow (integral_nonneg fun _ ↦ by positivity)
    (integral_hyperplane_norm_rpow_le_integral hu hsupp a one_le_two) (by norm_num)).trans ?_
  exact integral_energy_two_rpow_inv_le hu hsupp

/-- **Flat `L²` traces of the derivatives.** For a compactly supported function `u` of class
`Cⁱ⁺¹` on `ℝ × E`, the `i`-th derivative of its restriction to the hyperplane `{a} × E`
satisfies `‖Dⁱ(u(a, ·))‖₂ ≤ ‖Dⁱ u‖₂ + ‖Dⁱ⁺¹ u‖₂`. -/
theorem lpNorm_iteratedFDeriv_hyperplane_le {i : ℕ} {u : WithLp 2 (ℝ × E) → G}
    (hu : ContDiff ℝ (i + 1) u) (hsupp : HasCompactSupport u) (a : ℝ) :
    lpNorm (iteratedFDeriv ℝ i fun y : E ↦ u (WithLp.toLp 2 (a, y))) 2 volume ≤
      lpNorm (iteratedFDeriv ℝ i u) 2 volume + lpNorm (iteratedFDeriv ℝ (i + 1) u) 2 volume := by
  set ι := WithLp.inrL2 ℝ ℝ E
  set c : WithLp 2 (ℝ × E) := WithLp.toLp 2 (a, 0)
  set w := iteratedFDeriv ℝ i u
  have hι : ‖ι‖ ≤ 1 := ι.opNorm_le_bound zero_le_one fun y ↦ by simp [ι]
  have hrestr : (fun y : E ↦ u (WithLp.toLp 2 (a, y))) = (fun x ↦ u (x + c)) ∘ ι := by
    ext y
    simp [ι, c, ← WithLp.toLp_add]
  have hw : ContDiff ℝ 1 w := hu.iteratedFDeriv_right (le_of_eq (add_comm _ _))
  have hshift : ContDiff ℝ (i + 1) fun x ↦ u (x + c) := hu.comp (contDiff_id.add contDiff_const)
  have hwc : HasCompactSupport w := hsupp.iteratedFDeriv i
  -- The derivatives of the restriction are those of `u` along the hyperplane.
  have hpt (y : E) : ‖iteratedFDeriv ℝ i (fun y : E ↦ u (WithLp.toLp 2 (a, y))) y‖ ≤
      ‖w (WithLp.toLp 2 (a, y))‖ := by
    have hy : ι y + c = WithLp.toLp 2 (a, y) := by simp [ι, c, ← WithLp.toLp_add]
    rw [hrestr]
    refine (ι.norm_iteratedFDeriv_comp_right_le hshift y (by norm_cast; omega)).trans ?_
    rw [iteratedFDeriv_comp_add_right, hy]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hι)
  have hwcont : Continuous fun y : E ↦ w (WithLp.toLp 2 (a, y)) :=
    hw.continuous.comp (by fun_prop)
  have hmem : MemLp (fun y : E ↦ ‖w (WithLp.toLp 2 (a, y))‖) 2 volume :=
    hwcont.norm.memLp_of_hasCompactSupport
      (hwc.comp_isClosedEmbedding (WithLp.isClosedEmbedding_toLp_prodMk_left 2 a)).norm
  refine (lpNorm_mono_real hmem hpt).trans ?_
  rw [lpNorm_norm hwcont.aestronglyMeasurable]
  exact (lpNorm_hyperplane_le hw hwc a).trans_eq (by rw [lpNorm_fderiv_iteratedFDeriv])

end TauCeti
