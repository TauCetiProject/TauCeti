/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Surjective differentials in local coordinates

A surjective continuous linear map composed with a local diffeomorphism has a surjective
vector-valued manifold derivative. In particular, selecting distinct coordinates of a local
coordinate system gives independent local equations for transverse intersections.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 E H M F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A surjective continuous linear map composed with a local diffeomorphism has a surjective
vector-valued manifold derivative. No finite-dimensionality assumption is needed. -/
theorem mvfderiv_comp_surjective_of_isLocalDiffeomorphAt {n : ℕ∞ω} {f : M → F} {x : M}
    (hf : IsLocalDiffeomorphAt I 𝓘(𝕜, F) n f x) (hn : n ≠ 0)
    (L : F →L[𝕜] G) (hL : Function.Surjective L) :
    Function.Surjective (mvfderiv I (L ∘ f) x) := by
  rw [mvfderiv_comp x ((L.contMDiffAt (n := n)).mdifferentiableAt hn)
    (hf.mdifferentiableAt hn), mvfderiv_eq_fderiv, L.fderiv]
  exact hL.comp ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).surjective.comp
    (hf.mfderivToContinuousLinearEquiv hn).surjective)

end TauCeti
