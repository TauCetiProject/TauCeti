/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Unit
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Native gradients of nonzero linear defining functions

Every nonzero linear coordinate has a nonzero native gradient in every genuine positive
Riemannian metric. Its actual normalized gradient therefore gives the inward unit normal of
a linear boundary chart without any Euclidean-metric assumption.
-/

public noncomputable section
open Bundle Manifold
open scoped ContDiff Manifold Topology InnerProductSpace
namespace TauCeti.Manifold
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
/-- A genuine nonzero linear defining functional has nonzero native metric gradient. -/
theorem mgradient_continuousLinearMap_ne_zero (L : F →L[ℝ] ℝ) (hL : L ≠ 0) (x : F) :
    mgradient 𝓘(ℝ, F) L x ≠ 0 := by
  intro hz
  apply hL
  ext v
  have hd := mgradient_eq_zero_iff.mp hz
  have he := congrArg
    (fun A : TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ ↦
      A ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm v)) hd
  rw [zero_apply] at he
  have hval : mvfderiv 𝓘(ℝ, F) L x
      ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm v) = L v := by
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
    rfl
  exact hval.symm.trans he

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [RiemannianBundle (fun x : ℝ × G ↦ TangentSpace 𝓘(ℝ, ℝ × G) x)]
/-- The actual normal-coordinate differential has nonzero native gradient in every
positive Riemannian metric. -/
theorem mgradient_fst_ne_zero (x : ℝ × G) :
    mgradient 𝓘(ℝ, ℝ × G) (Prod.fst : ℝ × G → ℝ) x ≠ 0 := by
  apply mgradient_continuousLinearMap_ne_zero (ContinuousLinearMap.fst ℝ ℝ G) ?_ x
  intro hzero
  have he := congrArg (fun A : (ℝ × G) →L[ℝ] ℝ ↦ A (1, 0)) hzero
  change (1 : ℝ) = 0 at he
  exact one_ne_zero he
end TauCeti.Manifold
