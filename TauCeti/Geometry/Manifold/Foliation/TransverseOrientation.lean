/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Foliation.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Orientation.Transverse

/-!
# Transversely oriented foliations and their Euler classes

A codimension-one foliation `F` of a manifold `M` is *transversely oriented* by a continuous vector
field `ν` that is nowhere tangent to `F`. If `M` is oriented as well, then the tangent field of `F`
is oriented (`TauCeti.Foliation.transverseOrientation`): a basis `v₁, …, vₖ` of `T_x F` is positive
exactly when `ν x, v₁, …, vₖ` is a positive basis of `T_x M`. This is the convention by which a
transverse vector field orients a hypersurface of an oriented manifold. Placing `ν x` last instead
multiplies the orientation by `(-1)ᵏ`, so for foliations of `3`-manifolds (`k = 2`) the two
conventions agree.

An oriented vector bundle has a Thom class
(`TauCeti.VectorBundleOrientation.exists_isThomClass`). So a transversely orientable
codimension-one foliation of an orientable manifold has a Thom class with coefficients in any
commutative ring `K` (`TauCeti.Foliation.exists_isThomClass_of_transverse`), and hence an
Euler class (`TauCeti.Foliation.exists_isEulerClass_of_transverse`). In particular a transversely
orientable codimension-one foliation of a closed orientable `3`-manifold has an Euler class in
`H²(M; K)`, the kind of class that Thurston's Euler class inequality bounds.

The existence results take the manifold, its model space and the coefficient ring in `Type`:
`TauCeti.VectorBundleOrientation.exists_isThomClass` asks for the base and the model fibre
`Fin k → ℝ` of the tangent field to live in the same universe.

## Main definitions

* `TauCeti.Foliation.transverseOrientation`: the orientation of the tangent field of a
  codimension-one foliation induced by an orientation of the manifold and a transverse vector
  field.

## Main results

* `TauCeti.Foliation.transverseOrientation_apply`: on each tangent space of the foliation it is
  the orientation induced by the transverse vector (`Orientation.transverse`).
* `TauCeti.Foliation.exists_isThomClass_of_transverse`: a transversely orientable
  codimension-one foliation of an orientable manifold has a Thom class.
* `TauCeti.Foliation.transverseOrientation_neg`: reversing the orientation of the manifold reverses
  it.
* `TauCeti.Foliation.exists_isEulerClass_of_transverse`: such a foliation has an Euler class.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition
  15.21 (the orientation of a hypersurface induced by a transverse vector field).
* W. P. Thurston, *A norm for the homology of 3-manifolds*, Mem. Amer. Math. Soc. 59 (1986),
  no. 339 (the Euler class of a transversely oriented foliation).
* D. Calegari, *Foliations and the Geometry of 3-Manifolds*, Oxford University Press (2007).
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

namespace Foliation

section Orientation

universe w

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} [IsManifold I (n + 1) M]
  [IsManifold I 1 M] (F : Foliation I n M k)

/-- **The orientation of the tangent field of a transversely oriented foliation.** For a
foliation `F` of codimension one (of rank `k` on a manifold of dimension `k + 1`), an orientation
`o` of the tangent bundle and a continuous vector field `ν` nowhere tangent to `F` orient the
tangent field of `F`: a basis `v₁, …, vₖ` of `T_x F` is positive exactly when `ν x, v₁, …, vₖ` is
a positive basis of `T_x M`. -/
def transverseOrientation (hE : finrank ℝ E = k + 1)
    (o : VectorBundleOrientation E (TangentSpace I : M → Type w) (Fin (k + 1)))
    {ν : ∀ x : M, TangentSpace I x} (hν : Continuous fun x ↦ (⟨x, ν x⟩ : TangentBundle I M))
    (hνF : ∀ x, ν x ∉ F.distribution x) :
    letI := F.isContMDiffDistribution.fiberBundle
    haveI := F.isContMDiffDistribution.vectorBundle
    VectorBundleOrientation (Fin k → ℝ) (fun x ↦ F.distribution x) (Fin k) :=
  letI := F.isContMDiffDistribution.fiberBundle
  haveI := F.isContMDiffDistribution.vectorBundle
  VectorBundleOrientation.transverse hE (finrank_fin_fun ℝ)
    (isEmbedding_totalSpace_subbundle E (Fin k → ℝ) F.distribution).continuous o hν hνF

/-- On each tangent space of the foliation, the transverse orientation is the orientation of
`T_x F` induced by the orientation of `T_x M` and the transverse vector `ν x`. -/
theorem transverseOrientation_apply (hE : finrank ℝ E = k + 1)
    (o : VectorBundleOrientation E (TangentSpace I : M → Type w) (Fin (k + 1)))
    {ν : ∀ x : M, TangentSpace I x} (hν : Continuous fun x ↦ (⟨x, ν x⟩ : TangentBundle I M))
    (hνF : ∀ x, ν x ∉ F.distribution x) (x : M) (hx : finrank ℝ (TangentSpace I x) = k + 1)
    (hFx : finrank ℝ (F.distribution x) = k) :
    F.transverseOrientation hE o hν hνF x = (o x).transverse hx hFx (hνF x) := by
  let := F.isContMDiffDistribution.fiberBundle
  have := F.isContMDiffDistribution.vectorBundle
  exact VectorBundleOrientation.transverse_apply hE (finrank_fin_fun ℝ)
    (isEmbedding_totalSpace_subbundle E (Fin k → ℝ) F.distribution).continuous o hν hνF x hx hFx

/-- Reversing the orientation of the manifold reverses the transverse orientation of the tangent
field. -/
@[simp]
theorem transverseOrientation_neg (hE : finrank ℝ E = k + 1)
    (o : VectorBundleOrientation E (TangentSpace I : M → Type w) (Fin (k + 1)))
    {ν : ∀ x : M, TangentSpace I x} (hν : Continuous fun x ↦ (⟨x, ν x⟩ : TangentBundle I M))
    (hνF : ∀ x, ν x ∉ F.distribution x) :
    F.transverseOrientation hE (-o) hν hνF = -F.transverseOrientation hE o hν hνF := by
  let := F.isContMDiffDistribution.fiberBundle
  have := F.isContMDiffDistribution.vectorBundle
  exact VectorBundleOrientation.transverse_neg hE (finrank_fin_fun ℝ)
    (isEmbedding_totalSpace_subbundle E (Fin k → ℝ) F.distribution).continuous o hν hνF

end Orientation

section Existence

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}
  [IsManifold I (n + 1) M] [IsManifold I 1 M] [Orientable I M] (F : Foliation I n M k)

/-- **A transversely orientable codimension-one foliation of an orientable manifold has a Thom
class.** If `F` has rank `k` on an orientable manifold of dimension `k + 1` and some
continuous vector field is nowhere tangent to `F`, then the tangent field of `F` has a Thom class
`u ∈ Hᵏ(TF, TF₀; K)` with coefficients in any commutative ring `K`. -/
theorem exists_isThomClass_of_transverse (hE : finrank ℝ E = k + 1)
    {ν : ∀ x : M, TangentSpace I x} (hν : Continuous fun x ↦ (⟨x, ν x⟩ : TangentBundle I M))
    (hνF : ∀ x, ν x ∉ F.distribution x) (K : Type) [CommRing K] :
    ∃ u : F.thomPair.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ (Fin k → ℝ)), F.IsThomClass u := by
  obtain ⟨o⟩ := (orientable_iff_nonempty_vectorBundleOrientation (I := I) (M := M)).1 ‹_›
  rw [hE] at o
  let := F.isContMDiffDistribution.fiberBundle
  have := F.isContMDiffDistribution.vectorBundle
  obtain ⟨u, hu⟩ := (F.transverseOrientation hE o hν hνF).exists_isThomClass (by simp) K
  exact ⟨u, F.isThomClass_iff.2 hu⟩

/-- **A transversely orientable codimension-one foliation of an orientable manifold has an
Euler class** `e ∈ Hᵏ(M; K)`, with coefficients in any commutative ring `K`: the Euler class of a
Thom class of its tangent field. -/
theorem exists_isEulerClass_of_transverse (hE : finrank ℝ E = k + 1)
    {ν : ∀ x : M, TangentSpace I x} (hν : Continuous fun x ↦ (⟨x, ν x⟩ : TangentBundle I M))
    (hνF : ∀ x, ν x ∉ F.distribution x) (K : Type) [CommRing K] :
    ∃ e : (TopCat.of M).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) k,
      F.IsEulerClass e := by
  obtain ⟨u, hu⟩ := F.exists_isThomClass_of_transverse hE hν hνF K
  exact ⟨_, isEulerClass_eulerClass hu⟩

end Existence

end Foliation

end TauCeti
