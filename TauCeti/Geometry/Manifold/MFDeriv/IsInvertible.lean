/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

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

If the source is modelled on a finite-dimensional space over a complete field and the derivative
carries a tangent basis `b` onto a basis `b'`, then it is the continuous linear equivalence mapping
`b` to `b'` (`exists_coe_eq_mfderiv_of_basis`), so it is invertible
(`isInvertible_mfderiv_of_basis`).
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

/-- If the source is modelled on a finite-dimensional space over a complete field and the
derivative at `x` carries a basis `b` of the tangent space at `x` to a basis `b'` of the tangent
space at `f x`, then the derivative is a continuous linear equivalence mapping `b` to `b'`. -/
theorem exists_coe_eq_mfderiv_of_basis [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] {ι : Type*}
    {f : M → M'} {x : M} (b : Module.Basis ι 𝕜 (TangentSpace I x))
    (b' : Module.Basis ι 𝕜 (TangentSpace I' (f x))) (hbb' : ∀ i, mfderiv I I' f x (b i) = b' i) :
    ∃ e : TangentSpace I x ≃L[𝕜] TangentSpace I' (f x),
      (e : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) = mfderiv I I' f x ∧
        b.map e.toLinearEquiv = b' := by
  refine ⟨(b.equiv b' (Equiv.refl ι)).toContinuousLinearEquiv,
    ContinuousLinearMap.coe_injective <| b.ext fun i ↦ ?_, Module.Basis.eq_of_apply_eq fun i ↦ ?_⟩
  · simp [Module.Basis.equiv_apply, hbb']
  · simp

/-- If the source is modelled on a finite-dimensional space over a complete field and the
derivative at `x` carries a basis `b` of the tangent space at `x` to a basis `b'` of the tangent
space at `f x`, then it is invertible. -/
theorem isInvertible_mfderiv_of_basis [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] {ι : Type*}
    {f : M → M'} {x : M} (b : Module.Basis ι 𝕜 (TangentSpace I x))
    (b' : Module.Basis ι 𝕜 (TangentSpace I' (f x))) (hbb' : ∀ i, mfderiv I I' f x (b i) = b' i) :
    (mfderiv I I' f x).IsInvertible :=
  let ⟨e, he, _⟩ := exists_coe_eq_mfderiv_of_basis b b' hbb'
  ⟨e, he⟩

end TauCeti
