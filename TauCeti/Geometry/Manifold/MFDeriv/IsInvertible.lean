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

Between manifolds modelled on finite-dimensional spaces of the same dimension over a complete
field, an injective manifold derivative is invertible (`isInvertible_mfderiv_of_injective`).
Conversely to the first statement, if the middle manifold is modelled on a finite-dimensional
space and the target model has the same dimension, and a composite of differentiable maps has
invertible manifold derivative, then so do both factors
(`isInvertible_mfderiv_of_isInvertible_mfderiv_comp`); neither completeness of the field nor
finite-dimensionality of the source or target model is assumed (the target is a quotient of the
middle space).

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
field, an injective manifold derivative is invertible. -/
theorem isInvertible_mfderiv_of_injective [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 E'] {f : M → M'} {x : M}
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E')
    (hinj : Function.Injective (mfderiv I I' f x)) : (mfderiv I I' f x).IsInvertible :=
  ⟨(LinearEquiv.ofBijective (mfderiv I I' f x : TangentSpace I x →ₗ[𝕜] TangentSpace I' (f x))
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
    ).toContinuousLinearEquiv, ContinuousLinearMap.ext fun _ ↦ rfl⟩

/-- Between manifolds whose middle model is finite-dimensional and whose target model has the same
dimension, if a composite of differentiable maps has invertible manifold derivative, then so do
both factors. The source and target models need not be assumed finite-dimensional (the target is a
quotient of the middle space), and the field need not be complete. -/
theorem isInvertible_mfderiv_of_isInvertible_mfderiv_comp
    [FiniteDimensional 𝕜 E']
    {f : M → M'} {g : M' → M''} {x : M}
    (hdim : Module.finrank 𝕜 E' = Module.finrank 𝕜 E'')
    (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x)
    (h : (mfderiv I I'' (g ∘ f) x).IsInvertible) :
    (mfderiv I I' f x).IsInvertible ∧ (mfderiv I' I'' g (f x)).IsInvertible := by
  rw [mfderiv_comp x hg hf] at h
  -- The derivative of `g` is surjective since the composite is bijective, hence injective between
  -- spaces of the same finite dimension.
  have hsurj : Function.Surjective (mfderiv I' I'' g (f x)) := .of_comp h.surjective
  have : FiniteDimensional 𝕜 E'' :=
    Module.Finite.of_surjective (mfderiv I' I'' g (f x) :
      TangentSpace I' (f x) →ₗ[𝕜] TangentSpace I'' (g (f x))) hsurj
  have hinj : Function.Injective (mfderiv I' I'' g (f x)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (mfderiv I' I'' g (f x) :
      TangentSpace I' (f x) →ₗ[𝕜] TangentSpace I'' (g (f x)))) hdim).2 hsurj
  obtain ⟨e, he⟩ := h
  have hcomp (v : TangentSpace I x) :
      mfderiv I' I'' g (f x) (mfderiv I I' f x v) = e v := by
    rw [← ContinuousLinearMap.comp_apply, ← he]
    rfl
  -- The inverse of the derivative of `f` is `e.symm ∘ g'`, so it is continuous without any
  -- completeness assumption on the field.
  let s : TangentSpace I'' (g (f x)) →L[𝕜] TangentSpace I x := e.symm.toContinuousLinearMap
  have hright (y : TangentSpace I' (f x)) :
      mfderiv I I' f x (s (mfderiv I' I'' g (f x) y)) = y :=
    hinj (by rw [hcomp]; exact e.apply_symm_apply _)
  exact ⟨⟨ContinuousLinearEquiv.equivOfInverse (mfderiv I I' f x)
      (s.comp (mfderiv I' I'' g (f x)))
      (fun v ↦ by simp only [s, ContinuousLinearMap.comp_apply, hcomp]; exact e.symm_apply_apply v)
      hright, rfl⟩,
    ⟨ContinuousLinearEquiv.equivOfInverse (mfderiv I' I'' g (f x)) ((mfderiv I I' f x).comp s)
      (fun y ↦ hright y)
      (fun z ↦ by simp only [s, ContinuousLinearMap.comp_apply, hcomp]; exact e.apply_symm_apply z),
    rfl⟩⟩

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
