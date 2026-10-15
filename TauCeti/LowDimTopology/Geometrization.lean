/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Incompressible
public import TauCeti.Geometry.Manifold.Irreducible
public import TauCeti.Geometry.Manifold.Orientation
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.FiniteVolume
public import TauCeti.LowDimTopology.SeifertFibration

/-!
# The geometrization conjecture

Thurston's geometrization conjecture (Kirby's problem 3.45), proved by Perelman, describes every
closed orientable irreducible 3-manifold `M`: it can be cut along finitely many disjoint
incompressible tori into pieces each of which is Seifert fibred or hyperbolic of finite volume.
This is the form in which Bessières, Besson, Boileau, Maillot and Porti state it. Thurston's
original formulation instead asks that the pieces carry geometric structures of finite volume
modelled on his eight geometries (`TauCeti.HasGeometricStructure`).

A *geometric torus decomposition* of `M`, `TauCeti.IsGeometricTorusDecomposition T`, is a finite
family of maps `T i : S¹ × S¹ → M` that are

* locally flat embeddings, so that each torus is tame;
* incompressible, that is injective on fundamental groups;
* pairwise disjoint;

such that every connected component of the complement `M \ ⋃ i, T i (S¹ × S¹)` is Seifert fibred
(`TauCeti.IsSeifertFibered`) or carries a complete hyperbolic metric of finite volume
(`TauCeti.IsFiniteVolumeHyperbolic`). The components are the interiors of the pieces of `M` cut
along the tori; they are open subsets of `M`, so they inherit its smooth structure, which is the
one their hyperbolic metrics are smooth for. A family of tori is allowed to be empty: a closed
Seifert-fibred or hyperbolic 3-manifold is its own single piece
(`TauCeti.isGeometricTorusDecomposition_of_isEmpty_of_isSeifertFibered` for the Seifert case).

The decomposition is only asked to exist. The canonical choice, the JSJ decomposition, and the
uniqueness of a minimal family of tori up to isotopy are separate theorems.

`TauCeti.GeometrizationConjecture` asserts that every closed orientable irreducible smooth
3-manifold has a geometric torus decomposition. Irreducibility is the condition
`TauCeti.IsSphereBoundsBall` that every locally flat 2-sphere bounds a ball. A closed orientable
prime 3-manifold is irreducible unless it is `S¹ × S²`, which is Seifert fibred, so this also
covers the prime manifolds. The conjecture is stated, not proved.

## Main definitions

* `TauCeti.IsGeometricTorusDecomposition`: a finite family of disjoint locally flat
  incompressible tori cutting a 3-manifold into Seifert-fibred and finite-volume hyperbolic pieces.
* `TauCeti.GeometrizationConjecture`: every closed orientable irreducible 3-manifold has a
  geometric torus decomposition.

## Main results

* `TauCeti.exists_opens_eq_connectedComponentIn_compl_iUnion_range`: every component of the
  complement of finitely many tori is open, so the condition on the pieces applies to all of them.
* `TauCeti.isGeometricTorusDecomposition_of_isEmpty_of_isSeifertFibered`: a connected
  Seifert-fibred 3-manifold has the empty geometric torus decomposition.
* `TauCeti.GeometrizationConjecture.exists_isGeometricTorusDecomposition`: applying the
  conjecture.

## References

* W. P. Thurston, *Three-dimensional manifolds, Kleinian groups and hyperbolic geometry*, Bull.
  Amer. Math. Soc. (N.S.) 6 (1982), 357–381, Conjecture 1.1.
* L. Bessières, G. Besson, M. Boileau, S. Maillot, J. Porti, *Geometrisation of 3-manifolds*,
  EMS Tracts in Mathematics 13, European Mathematical Society (2010), Introduction.
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), 401–487,
  Section 3.
* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 3.45, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
-/

public section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {ι : Type*}

/-- For finitely many tori in a Hausdorff 3-manifold, every connected component of the complement
of their images is open. -/
theorem exists_opens_eq_connectedComponentIn_compl_iUnion_range [T2Space M] [Finite ι]
    (T : ι → C(Circle × Circle, M)) (x : M) :
    ∃ U : Opens M, (U : Set M) = connectedComponentIn (⋃ i, range (T i))ᶜ x := by
  have := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  have hclosed : IsClosed (⋃ i, range (T i)) :=
    isClosed_iUnion_of_finite fun i ↦ (isCompact_range (T i).continuous).isClosed
  exact ⟨⟨_, hclosed.isOpen_compl.connectedComponentIn⟩, rfl⟩

variable [T3Space M] [SecondCountableTopology M] [IsManifold (𝓡 3) ∞ M]
  {T : ι → C(Circle × Circle, M)}

/-- A family of maps `T i : S¹ × S¹ → M` is a **geometric torus decomposition** of the 3-manifold
`M` when there are finitely many maps, they are disjoint locally flat incompressible embeddings of
the torus, and every connected component of the complement of their images is Seifert fibred or
hyperbolic of finite volume. For finitely many tori the components are open
(`TauCeti.exists_opens_eq_connectedComponentIn_compl_iUnion_range`), so they are 3-manifolds with
the structure inherited from `M`. -/
structure IsGeometricTorusDecomposition (T : ι → C(Circle × Circle, M)) : Prop where
  /-- There are finitely many tori. -/
  finite : Finite ι
  /-- Each torus is locally flat, flattened by charts of `M` onto `ℝ² × {0} ⊆ ℝ² × ℝ`. -/
  isLocallyFlat (i : ι) : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ (T i)
  /-- Each torus is incompressible. -/
  isIncompressible (i : ι) : IsIncompressible (T i)
  /-- The tori are pairwise disjoint. -/
  pairwise_disjoint : Pairwise (Disjoint on fun i ↦ range (T i))
  /-- Each connected component of the complement of the tori is Seifert fibred or hyperbolic of
  finite volume. -/
  isSeifertFibered_or_isFiniteVolumeHyperbolic (x : M) (hx : x ∉ ⋃ i, range (T i)) (U : Opens M)
    (hU : (U : Set M) = connectedComponentIn (⋃ i, range (T i))ᶜ x) :
    haveI : PreconnectedSpace U :=
      Subtype.preconnectedSpace (hU ▸ isPreconnected_connectedComponentIn)
    IsSeifertFibered U ∨ IsFiniteVolumeHyperbolic (𝓡 3) U

/-- A connected Seifert-fibred 3-manifold has a geometric torus decomposition with no tori: it is
its own single piece. -/
theorem isGeometricTorusDecomposition_of_isEmpty_of_isSeifertFibered [IsEmpty ι]
    [ConnectedSpace M] (h : IsSeifertFibered M) : IsGeometricTorusDecomposition T where
  finite := inferInstance
  isLocallyFlat i := isEmptyElim i
  isIncompressible i := isEmptyElim i
  pairwise_disjoint i := isEmptyElim i
  isSeifertFibered_or_isFiniteVolumeHyperbolic x _ U hU := by
    have hU' : (U : Set M) = univ := by
      rw [hU, iUnion_of_empty, compl_empty, connectedComponentIn_univ,
        PreconnectedSpace.connectedComponent_eq_univ]
    exact Or.inl
      (((Homeomorph.setCongr hU').trans (Homeomorph.Set.univ M)).isSeifertFibered_iff.2 h)

/-- The **geometrization conjecture** (Thurston, Kirby's problem 3.45; a theorem of Perelman):
every closed orientable irreducible 3-manifold `M`, that is a compact connected orientable smooth
3-manifold without boundary in which every locally flat 2-sphere bounds a ball, has a geometric
torus decomposition: finitely many disjoint locally flat incompressible tori whose complement has
Seifert-fibred and finite-volume hyperbolic components. -/
def GeometrizationConjecture : Prop :=
  ∀ (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) ∞ M],
    IsSphereBoundsBall M →
      ∃ (n : ℕ) (T : Fin n → C(Circle × Circle, M)), IsGeometricTorusDecomposition T

/-- A proof of the geometrization conjecture gives every closed orientable irreducible
3-manifold a geometric torus decomposition. -/
theorem GeometrizationConjecture.exists_isGeometricTorusDecomposition
    (h : GeometrizationConjecture.{u}) (M : Type u) [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M]
    [ConnectedSpace M] [Orientable (𝓡 3) ∞ M] (hM : IsSphereBoundsBall M) :
    ∃ (n : ℕ) (T : Fin n → C(Circle × Circle, M)), IsGeometricTorusDecomposition T :=
  h M hM

/-- The defining characterization of the geometrization conjecture. -/
theorem geometrizationConjecture_iff :
    GeometrizationConjecture.{u} ↔
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) ∞ M],
        IsSphereBoundsBall M →
          ∃ (n : ℕ) (T : Fin n → C(Circle × Circle, M)), IsGeometricTorusDecomposition T :=
  Iff.rfl

end TauCeti
