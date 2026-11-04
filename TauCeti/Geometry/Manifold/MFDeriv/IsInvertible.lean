/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Invertible manifold derivatives of composites

If `f` has invertible manifold derivative at `x` and `g` has invertible manifold derivative at
`f x`, then `g ∘ f` has invertible manifold derivative at `x`. No differentiability hypothesis is
needed, since an invertible derivative forces differentiability
(`mdifferentiableAt_of_isInvertible_mfderiv`), and no finite-dimensionality or smoothness of the
manifolds is assumed.

Conversely, between manifolds modelled on finite-dimensional spaces of the same dimension over a
complete field, if a composite of differentiable maps has invertible manifold derivative then so do
both factors (`isInvertible_mfderiv_of_isInvertible_mfderiv_comp`).

Without any finite-dimensionality, a differentiable map with a differentiable left inverse near a
point has a manifold derivative admitting a continuous linear left inverse there
(`hasLeftInverse_mfderiv_of_comp_eventuallyEq_id`).
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' H'' M'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} [TopologicalSpace M'']
  [ChartedSpace H'' M'']

/-- A composite of maps with invertible manifold derivatives at `x` and `f x` has invertible
manifold derivative at `x`. -/
theorem isInvertible_mfderiv_comp {f : M → M'} {g : M' → M''} {x : M}
    (hdg : (mfderiv I' I'' g (f x)).IsInvertible) (hdf : (mfderiv I I' f x).IsInvertible) :
    (mfderiv I I'' (g ∘ f) x).IsInvertible := by
  rw [mfderiv_comp x (mdifferentiableAt_of_isInvertible_mfderiv hdg)
    (mdifferentiableAt_of_isInvertible_mfderiv hdf)]
  exact hdg.comp hdf

/-- Between manifolds modelled on finite-dimensional spaces of the same dimension over a complete
field, if a composite of differentiable maps has invertible manifold derivative, then so do both
factors. -/
theorem isInvertible_mfderiv_of_isInvertible_mfderiv_comp [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] [FiniteDimensional 𝕜 E'']
    {f : M → M'} {g : M' → M''} {x : M}
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E')
    (hdim' : Module.finrank 𝕜 E' = Module.finrank 𝕜 E'')
    (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x)
    (h : (mfderiv I I'' (g ∘ f) x).IsInvertible) :
    (mfderiv I I' f x).IsInvertible ∧ (mfderiv I' I'' g (f x)).IsInvertible := by
  rw [mfderiv_comp x hg hf] at h
  -- The derivative of `f` is injective and that of `g` surjective, since the composite is
  -- bijective; between spaces of the same finite dimension either property gives bijectivity.
  have hinj : Function.Injective (mfderiv I I' f x) := .of_comp h.injective
  have hsurj : Function.Surjective (mfderiv I' I'' g (f x)) := .of_comp h.surjective
  exact ⟨⟨(LinearEquiv.ofBijective (mfderiv I I' f x : TangentSpace I x →ₗ[𝕜] TangentSpace I' (f x))
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
      ).toContinuousLinearEquiv, ContinuousLinearMap.ext fun _ ↦ rfl⟩,
    ⟨(LinearEquiv.ofBijective
      (mfderiv I' I'' g (f x) : TangentSpace I' (f x) →ₗ[𝕜] TangentSpace I'' (g (f x)))
      ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').2 hsurj, hsurj⟩
      ).toContinuousLinearEquiv, ContinuousLinearMap.ext fun _ ↦ rfl⟩⟩

/-- A map with a differentiable left inverse near a point has a manifold derivative admitting a
continuous linear left inverse there: if `g ∘ f` agrees with the identity near `x`, then
`mfderiv g (f x) ∘ mfderiv f x` is the identity. -/
theorem hasLeftInverse_mfderiv_of_comp_eventuallyEq_id {f : M → M'} {g : M' → M} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' I g (f x))
    (hgf : g ∘ f =ᶠ[nhds x] id) : (mfderiv I I' f x).HasLeftInverse := by
  have h := mfderiv_comp x hg hf
  rw [hgf.mfderiv_eq, mfderiv_id] at h
  -- Transport the derivative of `g` back to the tangent space at `x`.
  let C := tangentSpaceCast I x (g (f x))
  refine ⟨C.symm.toContinuousLinearMap.comp (mfderiv I' I g (f x)), fun v => ?_⟩
  simpa [C, ContinuousLinearMap.comp_apply] using
    congrArg C.symm (DFunLike.congr_fun h.symm v)

end TauCeti
