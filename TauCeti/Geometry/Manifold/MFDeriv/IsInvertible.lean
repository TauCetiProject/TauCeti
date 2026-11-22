/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Invertible manifold derivatives of composites

If `f` has invertible manifold derivative at `x` and `g` has invertible manifold derivative at
`f x`, then `g ∘ f` has invertible manifold derivative at `x`. No differentiability hypothesis is
needed, since an invertible derivative forces differentiability
(`mdifferentiableAt_of_isInvertible_mfderiv`), and no finite-dimensionality or smoothness of the
manifolds is assumed. Precomposing with such an `f` also preserves criticality: for a map `g` into
a normed space which is differentiable at `f x`, `d(g ∘ f)_x = 0` exactly when `dg_(f x) = 0`
(`mvfderiv_comp_eq_zero_iff_of_isInvertible`).

If the target is modelled on a finite-dimensional space over a complete field and the source model
has the same dimension, a manifold derivative is invertible exactly when it is injective
(`isInvertible_mfderiv_iff_injective`); the source model need not be assumed finite-dimensional,
since an injective derivative embeds it into the target model.
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

/-- If `f` has invertible manifold derivative at `x` and `g` is a map into a normed space which is
differentiable at `f x`, then the derivative of `g ∘ f` vanishes at `x` exactly when the derivative
of `g` vanishes at `f x`. This is the manifold version of
`TauCeti.fderiv_comp_eq_zero_iff_of_isInvertible`. -/
theorem mvfderiv_comp_eq_zero_iff_of_isInvertible {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : M → M'} {g : M' → F} {x : M}
    (hg : MDifferentiableAt I' 𝓘(𝕜, F) g (f x)) (hf : (mfderiv I I' f x).IsInvertible) :
    mvfderiv I (g ∘ f) x = 0 ↔ mvfderiv I' g (f x) = 0 := by
  rw [mvfderiv_comp x hg (mdifferentiableAt_of_isInvertible_mfderiv hf)]
  obtain ⟨e, he⟩ := hf
  rw [← he]
  exact ContinuousLinearMap.comp_continuousLinearEquiv_eq_zero_iff _ e

/-- If the target is modelled on a finite-dimensional space over a complete field and the source
model has the same dimension, a manifold derivative is invertible exactly when it is injective. The
source model need not be assumed finite-dimensional: an injective derivative embeds it into the
target model. -/
theorem isInvertible_mfderiv_iff_injective [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E']
    {f : M → M'} {x : M} (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E') :
    (mfderiv I I' f x).IsInvertible ↔ Function.Injective (mfderiv I I' f x) := by
  refine ⟨ContinuousLinearMap.IsInvertible.injective, fun hinj ↦ ?_⟩
  let A : TangentSpace I x →ₗ[𝕜] TangentSpace I' (f x) := mfderiv I I' f x
  have : FiniteDimensional 𝕜 (TangentSpace I x) := .of_injective A hinj
  exact ⟨(A.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv,
    ContinuousLinearMap.ext (A.linearEquivOfInjective_apply hinj hdim)⟩

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
  set f' := mfderiv I I' f x
  set g' := mfderiv I' I'' g (f x)
  -- `g'` is surjective since the composite is bijective, hence injective between spaces of the
  -- same finite dimension.
  have hsurj : Function.Surjective g' := .of_comp h.surjective
  have : FiniteDimensional 𝕜 E'' :=
    Module.Finite.of_surjective (g' : TangentSpace I' (f x) →ₗ[𝕜] TangentSpace I'' (g (f x))) hsurj
  have hinj : Function.Injective g' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (g' : TangentSpace I' (f x) →ₗ[𝕜] TangentSpace I'' (g (f x)))) hdim).2 hsurj
  obtain ⟨e, he⟩ := h
  have hcomp (v : TangentSpace I x) : g' (f' v) = e v := by
    rw [← ContinuousLinearEquiv.coe_coe, he, ContinuousLinearMap.comp_apply]
  -- The inverse of `f'` is `e.symm ∘ g'`, so it is continuous without any completeness assumption
  -- on the field.
  obtain ⟨φ, hφ⟩ : f'.IsInvertible := .of_inverse (g := e.symm.toContinuousLinearMap ∘L g')
    (ContinuousLinearMap.ext fun y ↦ hinj (by simp [hcomp]))
    (ContinuousLinearMap.ext fun v ↦ by simp [hcomp])
  -- Then `g' ∘ φ = e`, so `g'` is invertible as well.
  refine ⟨⟨φ, hφ⟩, (ContinuousLinearMap.isInvertible_comp_equiv (e := φ)).1 ?_⟩
  rw [hφ, ← he]
  exact ContinuousLinearMap.isInvertible_equiv

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
