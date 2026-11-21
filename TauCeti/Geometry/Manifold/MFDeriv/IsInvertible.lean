/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Analysis.Normed.Operator.FiniteDimensional
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Invertible manifold derivatives of composites

If `f` has invertible manifold derivative at `x` and `g` has invertible manifold derivative at
`f x`, then `g ∘ f` has invertible manifold derivative at `x`. No differentiability hypothesis is
needed, since an invertible derivative forces differentiability
(`mdifferentiableAt_of_isInvertible_mfderiv`), and no finite-dimensionality or smoothness of the
manifolds is assumed.

If the target is modelled on a finite-dimensional space over a complete field and the source model
has the same `Module.finrank`, a manifold derivative is invertible exactly when it is injective
(`isInvertible_mfderiv_iff_injective`). An infinite-dimensional model has `finrank` zero, so the
rank equality alone does not make the source model finite-dimensional; this follows instead from
injectivity, since an injective derivative embeds the source model into the target model.
Conversely to the first statement, if the middle manifold is modelled on a finite-dimensional
space and the target model has the same `Module.finrank`, and a composite of differentiable maps
has invertible manifold derivative, then so do both factors
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

/-- If the target is modelled on a finite-dimensional space over a complete field and the source
model has the same `Module.finrank`, a manifold derivative is invertible exactly when it is
injective; this is the manifold form of the operator criterion
`ContinuousLinearMap.isInvertible_of_injective_of_finrank_eq`. The source model need not be
assumed finite-dimensional: an infinite-dimensional model has `finrank` zero, and
finite-dimensionality of the source follows from injectivity, which embeds the source model into
the target model, not from the rank equality alone. -/
theorem isInvertible_mfderiv_iff_injective [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E']
    {f : M → M'} {x : M} (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E') :
    (mfderiv I I' f x).IsInvertible ↔ Function.Injective (mfderiv I I' f x) := by
  refine ⟨ContinuousLinearMap.IsInvertible.injective, fun hinj ↦ ?_⟩
  -- Read the derivative on the model spaces, where the operator criterion applies.
  set e := tangentSpaceCastModel I x
  set e' := tangentSpaceCastModel I' (f x)
  set A : E →L[𝕜] E' := (e' : TangentSpace I' (f x) →L[𝕜] E') ∘L mfderiv I I' f x ∘L
    (e.symm : E →L[𝕜] TangentSpace I x)
  have hA : Function.Injective A := by
    simp only [A, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
    exact e'.injective.comp (hinj.comp e.symm.injective)
  have : FiniteDimensional 𝕜 E := .of_injective (A : E →ₗ[𝕜] E') hA
  have hAinv := A.isInvertible_of_injective_of_finrank_eq hdim hA
  rwa [ContinuousLinearMap.isInvertible_equiv_comp,
    ContinuousLinearMap.isInvertible_comp_equiv] at hAinv

/-- Between manifolds whose middle model is finite-dimensional and whose target model has the same
`Module.finrank`, if a composite of differentiable maps has invertible manifold derivative, then so
do both factors. The source and target models need not be assumed finite-dimensional (the target
is a quotient of the middle space), and the field need not be complete. This specialises
`ContinuousLinearMap.isInvertible_comp_iff_of_injective_left`: the rank equality makes the
surjective derivative of `g` injective. -/
theorem isInvertible_mfderiv_of_isInvertible_mfderiv_comp
    [FiniteDimensional 𝕜 E']
    {f : M → M'} {g : M' → M''} {x : M}
    (hdim : Module.finrank 𝕜 E' = Module.finrank 𝕜 E'')
    (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x)
    (h : (mfderiv I I'' (g ∘ f) x).IsInvertible) :
    (mfderiv I I' f x).IsInvertible ∧ (mfderiv I' I'' g (f x)).IsInvertible := by
  rw [mfderiv_comp x hg hf] at h
  set g' := mfderiv I' I'' g (f x)
  -- `g'` is surjective since the composite is bijective, hence injective between tangent spaces
  -- of the same finite dimension.
  have hsurj : Function.Surjective g' := .of_comp h.surjective
  have : FiniteDimensional 𝕜 (TangentSpace I'' (g (f x))) :=
    Module.Finite.of_surjective (g' : TangentSpace I' (f x) →ₗ[𝕜] TangentSpace I'' (g (f x))) hsurj
  have hdim' : Module.finrank 𝕜 (TangentSpace I' (f x)) =
      Module.finrank 𝕜 (TangentSpace I'' (g (f x))) := by
    rw [(tangentSpaceCastModel I' (f x)).toLinearEquiv.finrank_eq,
      (tangentSpaceCastModel I'' (g (f x))).toLinearEquiv.finrank_eq, hdim]
  have hinj : Function.Injective g' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (g' : TangentSpace I' (f x) →ₗ[𝕜] TangentSpace I'' (g (f x)))) hdim').2 hsurj
  exact (ContinuousLinearMap.isInvertible_comp_iff_of_injective_left hinj).1 h

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
