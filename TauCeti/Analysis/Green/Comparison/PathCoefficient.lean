/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Boundary.Basic

/-!
# Actual tangent coefficients along a path

The manifold derivative chain rule identifies evaluation of a pulled-back circulation form on
an actual path tangent with the existing real circulation integrand.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti.Green

local notation "E" => EuclideanSpace ℝ (Fin 1)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N]

/-- Evaluation on an actual path tangent equals the raw planar circulation integrand.
Only differentiability at the current parameter and its image is required. -/
theorem _root_.Path.mpullback_manifoldOneForm_coefficient {p r : N} (q : Path p r)
    (f : N → ℂ) (hc : Continuous f) (P Q : ℂ → ℝ) (z : E)
    (L : E →L[ℝ] TangentSpace 𝓘(ℝ, E) (q.extend (z 0)))
    (hL : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E ↦ q.extend (w 0)) z
      (L.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (q.extend (z 0))) :
    mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q) (q.extend (z 0))
      (fun i ↦ L ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis i)) =
        circulationFun P Q (q.map hc).extend (z 0) := by
  let R := fun w : E ↦ q.extend (w 0)
  let γ := q.map hc
  have hmap (w : E) : f (R w) = γ.extend (w 0) := rfl
  have hleft := hf.hasMFDerivAt.comp z hL
  have hflat : HasFDerivAt (f ∘ R)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (R z))).toContinuousLinearMap.comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (R z)).comp L)) z := by
    -- The normed source and target tangent identifications cancel in the composed derivative.
    convert hleft.hasFDerivAt using 1
    rfl
  let invProj := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hproj_inv (t : ℝ) : (invProj t) 0 = t := invProj.symm_apply_apply t
  have he : (f ∘ R) ∘ invProj = γ.extend := by
    funext t
    simp only [Function.comp_apply, hmap, hproj_inv]
  have hγ : DifferentiableAt ℝ γ.extend (z 0) := by
    have hinv : invProj (z 0) = z := invProj.apply_symm_apply z
    have hd : DifferentiableAt ℝ (f ∘ R) (invProj (z 0)) := hinv.symm ▸ hflat.differentiableAt
    exact he ▸ hd.comp (z 0) invProj.differentiableAt
  have hright := hγ.hasDerivAt.hasFDerivAt.comp z
    (EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt
  have heq : f ∘ R = γ.extend ∘ EuclideanSpace.proj 0 := by funext w; exact hmap w
  rw [heq] at hflat
  have hproj : EuclideanSpace.proj (𝕜 := ℝ) 0
      ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0) = 1 := by
    -- The projection evaluates the unique coordinate of the Euclidean basis vector.
    change ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0) 0 = 1
    simp [EuclideanSpace.basisFun_apply]
  have hv := congrArg (fun A : E →L[ℝ] ℂ ↦
    A ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0)) (hflat.unique hright)
  rw [mpullback_apply, manifoldOneForm_apply, circulationFun_eq_oneForm]
  apply congrArg (oneForm P Q (f (R z)))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.toSpanSingleton_apply, hproj, one_smul, hmap] using hv

end TauCeti.Green
