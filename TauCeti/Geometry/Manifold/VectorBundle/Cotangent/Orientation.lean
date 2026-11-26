/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
public import TauCeti.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Orientation.Comap

/-!
# The orientation of the cotangent bundle of an oriented Riemannian manifold

A Riemannian metric on a manifold `M` identifies each cotangent space with the tangent space: the
Riesz isomorphism `T*ₓM ≃ TₓM`, `p ↦ p♯` (`Riemannian.Tensor.rieszDual`), sends a covector to the
vector that represents it for the inner product, and its inverse is the metric dual
`v ↦ v♭ = ⟪v, ·⟫`. Both are continuous on total spaces
(`TauCeti.CotangentBundle.continuous_rieszDual`,
`TauCeti.CotangentBundle.continuous_rieszDual_symm`): the metric dual is the continuous metric
`innerSL ℝ` applied to the vector, and a continuous family of fibrewise linear isomorphisms of
finite rank has a continuous inverse (`TauCeti.continuous_bundle_symm`). So the Riesz isomorphisms
form an isomorphism of vector bundles `T*M ≃ TM`.

An orientation of `M`, that is, of its tangent bundle, therefore transports to an orientation of
the cotangent bundle (`TauCeti.CotangentBundle.orientation`, through
`TauCeti.VectorBundleOrientation.comap`): the cotangent space at `x` is oriented so that `p ↦ p♯`
carries its orientation to that of `TₓM` (`TauCeti.CotangentBundle.map_orientation_apply`). An
oriented cotangent bundle has a Thom class, and so a Thom isomorphism with integral coefficients.

## Main definitions

* `TauCeti.CotangentBundle.orientation`: the orientation of `T*M` transported from an orientation
  of `M` along the Riesz isomorphisms.

## Main results

* `TauCeti.CotangentBundle.continuous_rieszDual`,
  `TauCeti.CotangentBundle.continuous_rieszDual_symm`: the Riesz isomorphisms and their inverses are
  continuous on total spaces.
* `TauCeti.CotangentBundle.map_orientation_apply`: the Riesz isomorphism carries the orientation of
  `T*ₓM` to that of `TₓM`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the musical isomorphisms).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (orientations of vector bundles).
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- **The metric dual is continuous.** The map `v ↦ v♭ = ⟪v, ·⟫` from the tangent bundle to the
cotangent bundle, the inverse of the Riesz isomorphisms, is continuous on total spaces. -/
theorem continuous_rieszDual_symm :
    Continuous fun v : TangentBundle I M ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) v.proj
      ((Riemannian.Tensor.rieszDual (I := I) v.proj).symm.toContinuousLinearEquiv v.snd) := by
  -- The metric dual of `v` is `innerSL ℝ v`, the metric applied to `v`.
  have h (x : M) (v : TangentSpace I x) :
      (Riemannian.Tensor.rieszDual (I := I) x).symm v = innerSL ℝ v := by
    ext w
    rw [innerSL_apply_apply, ← Riemannian.Tensor.inner_rieszDual,
      LinearIsometryEquiv.apply_symm_apply]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, h]
  exact ((IsContMDiffRiemannianBundle.contMDiff_innerSL (I := I) (n := 0)
    (V := fun x : M ↦ TangentSpace I x)).continuous.comp
      (FiberBundle.continuous_proj E (TangentSpace I))).clm_bundle_apply continuous_id

/-- **The Riesz isomorphism is continuous.** The map `p ↦ p♯` from the cotangent bundle to the
tangent bundle, sending a covector to the vector representing it for the metric, is continuous on
total spaces. -/
theorem continuous_rieszDual :
    Continuous fun z : CotangentBundle I M ↦ TotalSpace.mk' E (E := TangentSpace I) z.proj
      ((Riemannian.Tensor.rieszDual (I := I) z.proj).toContinuousLinearEquiv z.snd) := by
  have := continuous_bundle_symm (F₁ := E) (F₂ := E →L[ℝ] ℝ) (E₁ := TangentSpace I)
    (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
    (fun x ↦ (Riemannian.Tensor.rieszDual (I := I) x).symm.toContinuousLinearEquiv)
    continuous_rieszDual_symm
  simpa using this

variable {ι : Type*} [Fintype ι]

variable (I) in
/-- **The orientation of the cotangent bundle of an oriented Riemannian manifold.** An orientation
of the tangent bundle transports along the Riesz isomorphisms `T*ₓM ≃ TₓM`, `p ↦ p♯`, of the metric
to an orientation of the cotangent bundle: the cotangent space at `x` is oriented as the pull-back
of the orientation of `TₓM`. -/
def orientation (hι : Fintype.card ι = finrank ℝ E)
    (o : VectorBundleOrientation E (TangentSpace I : M → Type _) ι) :
    VectorBundleOrientation (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ι :=
  o.comap (g := ContinuousMap.id M)
    (φ := fun x ↦ (Riemannian.Tensor.rieszDual (I := I) x).toContinuousLinearEquiv)
    (by rw [ContinuousLinearMap.dual_finrank_eq, hι]) continuous_rieszDual

/-- The cotangent space at `x` is oriented as the pull-back of the orientation of `TₓM` along the
Riesz isomorphism `p ↦ p♯`. -/
theorem orientation_apply (hι : Fintype.card ι = finrank ℝ E)
    (o : VectorBundleOrientation E (TangentSpace I : M → Type _) ι) (x : M) :
    orientation I hι o x =
      Orientation.map ι (Riemannian.Tensor.rieszDual (I := I) x).symm.toLinearEquiv (o x) :=
  VectorBundleOrientation.comap_apply (g := ContinuousMap.id M)
    (φ := fun x ↦ (Riemannian.Tensor.rieszDual (I := I) x).toContinuousLinearEquiv) _ o
    continuous_rieszDual x

/-- The Riesz isomorphism `p ↦ p♯` carries the orientation of `T*ₓM` to that of `TₓM`. -/
@[simp]
theorem map_orientation_apply (hι : Fintype.card ι = finrank ℝ E)
    (o : VectorBundleOrientation E (TangentSpace I : M → Type _) ι) (x : M) :
    Orientation.map ι (Riemannian.Tensor.rieszDual (I := I) x).toLinearEquiv
      (orientation I hι o x) = o x :=
  VectorBundleOrientation.map_comap_apply (g := ContinuousMap.id M)
    (φ := fun x ↦ (Riemannian.Tensor.rieszDual (I := I) x).toContinuousLinearEquiv) _ o
    continuous_rieszDual x

end CotangentBundle

end TauCeti
