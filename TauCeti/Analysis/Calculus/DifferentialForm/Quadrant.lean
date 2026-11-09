/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Quadrant
public import TauCeti.Analysis.Calculus.DifferentialForm.Coordinates
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# Stokes' theorem on the coordinate quadrant

The closed coordinate quadrant `Set.Ici 0 = {x | ∀ i, 0 ≤ x i}` of `Fin (n + 1) → ℝ` is the local
model of a manifold with corners. The integral of the actual exterior derivative of a compactly
supported `n`-form over the quadrant is a signed sum of the integrals of the form over its
`n + 1` faces `x i = 0`, each parametrized by the quadrant one dimension down through
`Fin.insertNth i 0` and evaluated on the remaining standard basis vectors `e_{i.succAbove j}`.

The sign of the face `x i = 0` is `(-1) ^ (i + 1)`: its outward normal is `-eᵢ`, and the
outward-first tuple `(-eᵢ, e_{i.succAbove 0}, …, e_{i.succAbove (n - 1)})` differs from the
standard basis by that sign, so each face integral is taken with its outward-first
orientation. For `i = 0` this is the
coefficient of the half-space formula `ContDiffOn.integral_extDerivWithin_coordinate_halfSpace`.
No regularity outside the closed quadrant is required.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 16.25 (Stokes' theorem on
  manifolds with corners), whose local computation in the quadrant this is.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Flat Stokes on the closed coordinate quadrant for a compactly supported form that is `C¹`
only on the quadrant. The integral of the exterior derivative is the sum over the faces
`x i = 0` of `(-1) ^ (i + 1)` times the integral of the form over the face, evaluated on the
remaining standard basis vectors. The exterior derivative and every face integrand are
integrable. -/
theorem _root_.ContDiffOn.integral_extDerivWithin_coordinate_quadrant {n : ℕ}
    {ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω (Ici 0)) (hc : HasCompactSupport ω) :
    IntegrableOn (fun x ↦ extDerivWithin ω (Ici 0) x (Pi.basisFun ℝ (Fin (n + 1)))) (Ici 0) ∧
      (∀ i : Fin (n + 1), IntegrableOn (fun y : Fin n → ℝ ↦
        ω (i.insertNth 0 y) (fun j ↦ Pi.single (i.succAbove j) 1)) (Ici 0)) ∧
      (∫ x in Ici 0, extDerivWithin ω (Ici 0) x (Pi.basisFun ℝ (Fin (n + 1)))) =
        ∑ i : Fin (n + 1), (-1 : ℝ) ^ ((i : ℕ) + 1) •
          ∫ y in Ici 0, ω (i.insertNth 0 y) (fun j ↦ Pi.single (i.succAbove j) 1) := by
  let e := Pi.basisFun ℝ (Fin (n + 1))
  let Q : Set (Fin (n + 1) → ℝ) := Ici 0
  let L := ContinuousAlternatingMap.signedRemoveNth (𝕜 := ℝ) (F := F) e
  let f := L ∘ ω
  have hF : ContDiffOn ℝ 1 f Q := L.contDiff.comp_contDiffOn hω
  have hFc : HasCompactSupport f := hc.comp_left L.map_zero
  obtain ⟨hDi, hbi, hint⟩ := ContDiffOn.integral_divergence_coordinate_quadrant hF hFc
  have huniq : UniqueDiffOn ℝ Q := uniqueDiffOn_pi_Ici 0
  have hD : EqOn (fun x ↦ ∑ i : Fin (n + 1),
      fderivWithin ℝ f Q x (Pi.single i 1) i)
      (fun x ↦ extDerivWithin ω Q x e) Q := by
    intro x hx
    simpa only [e, Pi.basisFun_apply] using
      DifferentiableWithinAt.sum_fderivWithin_signedRemoveNth
        ((hω.differentiableOn one_ne_zero) x hx) (huniq x hx) e
  have hb (i : Fin (n + 1)) : (fun y : Fin n → ℝ ↦ f (i.insertNth 0 y) i) =
      fun y ↦ (-1 : ℝ) ^ (i : ℕ) • ω (i.insertNth 0 y) (fun j ↦ Pi.single (i.succAbove j) 1) := by
    funext y
    simp only [f, Function.comp_apply, L, ContinuousAlternatingMap.signedRemoveNth_apply]
    congr 2
    funext j
    exact Pi.basisFun_apply ℝ (Fin (n + 1)) (i.succAbove j)
  have hQm : MeasurableSet Q := measurableSet_Ici
  refine ⟨hDi.congr_fun hD hQm, fun i ↦ ?_, ?_⟩
  · have h := hbi i
    rw [hb] at h
    exact (integrable_smul_iff (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) _).1 h
  · rw [← setIntegral_congr_fun hQm hD, hint, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hb, integral_smul, pow_succ, mul_neg_one, neg_smul]

end TauCeti
