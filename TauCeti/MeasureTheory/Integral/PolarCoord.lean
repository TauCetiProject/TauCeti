/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic.Module

/-!
# Polar-coordinate derivatives and integration over a closed annulus

The polar-coordinate change of variables for a translated closed annulus is the integral on
`[a, b] × [-π, π]` with radial Jacobian `r`, when `a > 0`. The two angular endpoints have
measure zero, so the closed polar rectangle gives the same integral as the slit-plane chart.
This form of Mathlib's `Complex.integral_comp_polarCoord_symm` is suitable for combining polar
integration with Green's formula on a rectangle, without extending a map across the inner disc.

The derivative formulas describe the radial and angular vectors of the inverse complex polar
map. Evaluating the alternating part of a bilinear pairing on those vectors gives its value on
`1` and `Complex.I`, multiplied by the radial Jacobian.
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti

open Complex

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The derivative of the translated inverse complex polar-coordinate map at any `(r, θ)`.
No restriction to the positive-radius chart is needed for this derivative formula. -/
theorem hasFDerivAt_add_polarCoord_symm (p : ℝ × ℝ) (z₀ : ℂ) :
  HasFDerivAt (fun p ↦ z₀ + Complex.polarCoord.symm p)
    (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p)) p := by
  exact (Complex.equivRealProdCLM.symm.hasFDerivAt.comp p
    (hasFDerivAt_polarCoord_symm p)).const_add z₀

/-- The radial derivative of the inverse polar-coordinate map, expressed as a complex number,
is the unit vector at the given angle. -/
theorem equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (fderivPolarCoordSymm p (1, 0)) =
      Complex.exp (p.2 * I) := by
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.exp_mul_I]

/-- The angular derivative of the inverse polar-coordinate map, expressed as a complex number,
is the tangent vector to the circle with the given radius and angle. -/
theorem equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (fderivPolarCoordSymm p (0, 1)) =
      circleMap 0 p.1 p.2 * I := by
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.exp_mul_I, circleMap]
  ring_nf
  simp [I_sq]

/-- The alternating part of a continuous bilinear map, after a real-linear map `L`, evaluated
on the radial and angular polar-coordinate vectors is the radius times its value on `1` and `I`.
The identity holds for every real radius, including zero and negative radii. -/
theorem _root_.ContinuousLinearMap.apply_exp_circleMap_sub_swap
    (B : V →L[ℝ] V →L[ℝ] W) (L : ℂ →L[ℝ] V) (r θ : ℝ) :
    B (L (Complex.exp (θ * I))) (L (circleMap 0 r θ * I)) -
        B (L (circleMap 0 r θ * I)) (L (Complex.exp (θ * I))) =
      r • (B (L 1) (L I) - B (L I) (L 1)) := by
  have he : Complex.exp (θ * I) = Real.cos θ • (1 : ℂ) + Real.sin θ • I := by
    simp [Complex.exp_mul_I, real_smul]
  have hI : circleMap 0 r θ * I = (-r * Real.sin θ) • (1 : ℂ) +
      (r * Real.cos θ) • I := by
    simp [circleMap, he, real_smul]
    ring_nf
    simp [I_sq, sub_eq_add_neg]
  rw [he, hI]
  simp only [map_add, map_smul, add_apply, smul_apply]
  have htrig := Real.sin_sq_add_cos_sq θ
  match_scalars <;> nlinarith [congrArg (r * ·) htrig]

end TauCeti

namespace Complex

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Polar integration over the closed annulus of radii `a` and `b` about `z₀`, with radial
Jacobian `p.1`. The angular interval includes both endpoints, whose contribution is null. -/
theorem integral_comp_polarCoord_symm_Icc (f : ℂ → W) (z₀ : ℂ) {a b : ℝ} (ha : 0 < a) :
    (∫ p in Icc (a, -π) (b, π), p.1 • f (z₀ + Complex.polarCoord.symm p)) =
      ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, f z := by
  let S : Set ℂ := {z | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  have hS : MeasurableSet S := by
    have hn : Continuous (fun z : ℂ ↦ ‖z - z₀‖) := by fun_prop
    exact (isClosed_le continuous_const hn).measurableSet.inter
      (isClosed_le hn continuous_const).measurableSet
  rw [← integral_indicator hS, ← integral_add_left_eq_self (S.indicator f) z₀,
    ← Complex.integral_comp_polarCoord_symm]
  have hEq : EqOn (fun p : ℝ × ℝ ↦ p.1 • S.indicator f (z₀ + Complex.polarCoord.symm p))
      ((Icc a b ×ˢ (univ : Set ℝ)).indicator
        (fun p : ℝ × ℝ ↦ p.1 • f (z₀ + Complex.polarCoord.symm p)))
      _root_.polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    have hn : ‖z₀ + Complex.polarCoord.symm (r, θ) - z₀‖ = r := by
      simp only [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos (mem_Ioi.mp hr)]
    simp only [S, indicator_apply, mem_ofPred_eq, hn, mem_prod, mem_Icc, mem_univ, and_true]
    split_ifs <;> simp
  rw [setIntegral_congr_fun (by simp [_root_.polarCoord_target]; measurability) hEq,
    setIntegral_indicator (measurableSet_Icc.prod MeasurableSet.univ)]
  have he : _root_.polarCoord.target ∩ (Icc a b ×ˢ (univ : Set ℝ)) =
      Icc a b ×ˢ Ioo (-π) π := by
    ext ⟨r, θ⟩
    simp only [mem_inter_iff, _root_.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo, mem_Icc,
      mem_univ, and_true]
    constructor
    · exact fun h ↦ ⟨h.2, h.1.2⟩
    · exact fun h ↦ ⟨⟨lt_of_lt_of_le ha h.1.1, h.2⟩, h.1⟩
  rw [he, Icc_prod_eq, Measure.volume_eq_prod]
  exact setIntegral_congr_set (Measure.set_prod_ae_eq (Filter.EventuallyEq.rfl)
    Ioo_ae_eq_Icc).symm

end Complex
