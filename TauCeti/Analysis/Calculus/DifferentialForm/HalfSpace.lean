/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.HalfSpace
public import TauCeti.Analysis.Calculus.DifferentialForm.Coordinates

/-!
# Stokes' theorem on a coordinate half-space

The actual exterior derivative of a compactly supported form integrates to its outward-first
boundary coefficient. The sign is minus in every dimension because the outward normal is
`-e₀` and is placed first. No regularity outside the closed half-space is required.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

/-- Flat half-space Stokes for a compactly supported form that is `C¹` only on the half-space.
The actual exterior derivative and boundary coefficient are both integrable. -/
theorem _root_.ContDiffOn.integral_extDerivWithin_coordinate_halfSpace {n : ℕ}
    {ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hω : ContDiffOn ℝ 1 ω {x | 0 ≤ x 0}) (hc : HasCompactSupport ω) :
    IntegrableOn (fun x ↦ extDerivWithin ω {y | 0 ≤ y 0} x (Pi.basisFun ℝ (Fin (n + 1))))
        {x | 0 ≤ x 0} ∧
      Integrable (fun y : Fin n → ℝ ↦ ω (Fin.cons 0 y) (fun i ↦ Pi.single i.succ 1)) ∧
      (∫ x in {x | 0 ≤ x 0}, extDerivWithin ω {y | 0 ≤ y 0} x
        (Pi.basisFun ℝ (Fin (n + 1)))) =
          -(∫ y : Fin n → ℝ, ω (Fin.cons 0 y) (fun i ↦ Pi.single i.succ 1)) := by
  let e := Pi.basisFun ℝ (Fin (n + 1))
  let H : Set (Fin (n + 1) → ℝ) := {x | 0 ≤ x 0}
  let L := ContinuousAlternatingMap.signedRemoveNth (𝕜 := ℝ) (F := ℝ) e
  let f := L ∘ ω
  have hF : ContDiffOn ℝ 1 f H := L.contDiff.comp_contDiffOn hω
  have hFc : HasCompactSupport f := hc.comp_left L.map_zero
  have hresult := ContDiffOn.integral_divergence_coordinate_halfSpace hF hFc
  have huniq : UniqueDiffOn ℝ H := TauCeti.uniqueDiffOn_pi_halfSpace 0 0
  have hD : EqOn (fun x ↦ ∑ i : Fin (n + 1),
      fderivWithin ℝ f H x (Pi.single i 1) i)
      (fun x ↦ extDerivWithin ω H x e) H := by
    intro x hx
    simpa only [e, Pi.basisFun_apply] using
      DifferentiableWithinAt.sum_fderivWithin_signedRemoveNth
        ((hω.differentiableOn one_ne_zero) x hx) (huniq x hx) e
  have hb (y : Fin n → ℝ) : f (Fin.cons 0 y) 0 =
      ω (Fin.cons 0 y) (fun i ↦ Pi.single i.succ 1) := by
    simp only [f, Function.comp_apply, L, ContinuousAlternatingMap.signedRemoveNth_apply,
      Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero]
    congr 1
    funext i
    exact Pi.basisFun_apply ℝ (Fin (n + 1)) i.succ
  have hHm : MeasurableSet H := isClosed_le continuous_const (continuous_apply 0) |>.measurableSet
  refine ⟨hresult.1.congr_fun hD hHm, ?_, ?_⟩
  · simpa only [hb] using hresult.2.1
  · rw [← setIntegral_congr_fun hHm hD]
    simpa only [hb] using hresult.2.2

end TauCeti
