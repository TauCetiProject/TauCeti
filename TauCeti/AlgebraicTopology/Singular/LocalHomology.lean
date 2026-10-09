/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# Local homology at a point with a Euclidean chart

Let `M` be a `T₁` space and `x : M` a point in the source of an open partial homeomorphism
`φ : M → E` to a real normed space, such as a chart of a topological manifold modelled on `E`.
The **local homology** of `M` at `x` is the relative singular homology `Hₖ(M, M ∖ {x})`.  This
file computes it: it is the homology of `(E, E ∖ {φ x})`, so it vanishes in degree zero when
`E ≠ 0`, and in degree `k + 1` it is the degree-`k` reduced homology of the unit sphere `S` of `E`.
When `E` has dimension `n`, `Hₖ(M, M ∖ {x})` therefore vanishes for `k ≠ n`, and for `n ≥ 1` it is
one copy of the coefficients in degree `n`.

Local homology is the input to local orientations of manifolds: a local orientation of an
`n`-manifold at `x` is a generator of `Hₙ(M, M ∖ {x}; ℤ)`, and the orientation local system and
fundamental classes are assembled from these groups.

The computation has three steps.

* **Excision.**  For an open set `U` containing a closed set `K`, the inclusion
  `(U, U ∖ K) ⟶ (X, X ∖ K)` induces isomorphisms on relative homology
  (`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`), because the interiors of
  `U` and `X ∖ K` cover `X`.  Applied to the source of `φ` in `M` and to its target in `E`, and
  combined with the homeomorphism of source and target, this identifies `Hₖ(M, M ∖ {x})` with
  `Hₖ(E, E ∖ {φ x})` (`TauCeti.singularHomologyComplSingletonIsoOfChart`).
* **The connecting morphism.**  Since `E` is contractible, the reduced connecting morphism
  from `Hₖ₊₁(E, E ∖ {y})` to the degree-`k` reduced homology of `E ∖ {y}` is an isomorphism.
* **Radial retraction.**  `E ∖ {y}` is homotopy equivalent to the unit sphere of `E`
  (`TauCeti.complSingletonHomotopyEquivSphere`), by radial projection about `y` followed by
  translation.

## Main definitions and results

* `TauCeti.singularHomologyComplSingletonIsoOfChart`: `Hₖ(M, M ∖ {x}) ≅ Hₖ(E, E ∖ {φ x})`.
* `TauCeti.singularHomologyComplSingletonIso`: `Hₖ₊₁(M, M ∖ {x})` is isomorphic to the
  degree-`k` reduced homology of `S`.
* `TauCeti.isZero_singularHomology_complSingleton_zero`: `H₀(M, M ∖ {x}) = 0` when `E ≠ 0`.
* `TauCeti.isZero_singularHomology_complSingleton_of_ne`: `Hₖ(M, M ∖ {x}) = 0` for
  `k ≠ dim E`, for finite-dimensional `E`.
* `TauCeti.singularHomologyComplSingletonIsoOfFinrankEq`: `Hₙ₊₁(M, M ∖ {x}) ≅ R` when
  `dim E = n + 1`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, the local homology groups `Hₙ(M, M ∖ {x})` and
  local orientations, and Section 2.1, Theorem 2.20 (excision).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section Chart

variable {M : Type w} [TopologicalSpace M] [T1Space M] {E : Type w} [TopologicalSpace E]
  [T1Space E] (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source)

/-- The local homology of `M` at a point `x` in the source of an open partial homeomorphism
`φ : M → E` is that of `E` at `φ x`: excision onto the source of `φ`, the homeomorphism of the
source with the target, and excision onto the target give `Hₖ(M, M ∖ {x}) ≅ Hₖ(E, E ∖ {φ x})`
(`TauCeti.singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom`). -/
def singularHomologyComplSingletonIsoOfChart (k : ℕ) :
    (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology R k ≅
      (TopPair.ofSubset ({φ x}ᶜ : Set (TopCat.of E))).singularHomology R k :=
  haveI := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R
    (X := TopCat.of M) φ.open_source isClosed_singleton (Set.singleton_subset_iff.2 hx) k
  haveI := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R
    (X := TopCat.of E) φ.open_target isClosed_singleton
    (Set.singleton_subset_iff.2 (φ.map_source hx)) k
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := TopCat.of M) φ.source {x}ᶜ) R k)).symm ≪≫
    asIso (TopPair.singularHomologyMap (TopPair.ofSubsetIso
      (X := TopCat.of φ.source) (Y := TopCat.of φ.target) φ.toHomeomorphSourceTarget
      (B := Subtype.val ⁻¹' {x}ᶜ) (B' := Subtype.val ⁻¹' {φ x}ᶜ)
      fun z ↦ (φ.injOn.eq_iff z.2 hx).not.symm).hom R k) ≪≫
    asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := TopCat.of E) φ.target {φ x}ᶜ) R k)

/-- The isomorphism `TauCeti.singularHomologyComplSingletonIsoOfChart` commutes with the
excision maps from the source and target of `φ` and the homeomorphism between them. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom
    (k : ℕ) :
    TopPair.singularHomologyMap (TopPair.excisionMap (X := TopCat.of M) φ.source {x}ᶜ) R k ≫
        (singularHomologyComplSingletonIsoOfChart R φ hx k).hom =
      TopPair.singularHomologyMap (TopPair.ofSubsetIso
          (X := TopCat.of φ.source) (Y := TopCat.of φ.target) φ.toHomeomorphSourceTarget
          (B := Subtype.val ⁻¹' {x}ᶜ) (B' := Subtype.val ⁻¹' {φ x}ᶜ)
          fun z ↦ (φ.injOn.eq_iff z.2 hx).not.symm).hom R k ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := TopCat.of E) φ.target {φ x}ᶜ) R k := by
  simp [singularHomologyComplSingletonIsoOfChart]

end Chart

variable {M : Type w} [TopologicalSpace M] [T1Space M] {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source)

/-- **Local homology at a point with a Euclidean chart.** For `x` in the source of an open
partial homeomorphism `φ : M → E`, the local homology `Hₖ₊₁(M, M ∖ {x})` is the degree-`k`
reduced homology of the unit sphere of `E`.  It is
`TauCeti.singularHomologyComplSingletonIsoOfChart`, followed by the reduced connecting morphism
of the pair `(E, E ∖ {φ x})`, an isomorphism since `E` is contractible, and by
`TauCeti.complSingletonHomotopyEquivSphere`. -/
def singularHomologyComplSingletonIso (k : ℕ) :
    (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology R (k + 1) ≅
      (reducedSingularHomologyFunctor R k).obj (TopCat.of (sphere (0 : E) 1)) :=
  haveI : ContractibleSpace (TopPair.ofSubset ({φ x}ᶜ : Set (TopCat.of E))).fst :=
    inferInstanceAs (ContractibleSpace E)
  singularHomologyComplSingletonIsoOfChart R φ hx (k + 1) ≪≫
    asIso ((TopPair.ofSubset ({φ x}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R k) ≪≫
    (complSingletonHomotopyEquivSphere (φ x)).reducedSingularHomologyIso R k

/-- `TauCeti.singularHomologyComplSingletonIso` is the chart isomorphism followed by the reduced
connecting morphism of `(E, E ∖ {φ x})` and the map induced by
`TauCeti.complSingletonHomotopyEquivSphere`. -/
@[simp]
lemma singularHomologyComplSingletonIso_hom (k : ℕ) :
    (singularHomologyComplSingletonIso R φ hx k).hom =
      (singularHomologyComplSingletonIsoOfChart R φ hx (k + 1)).hom ≫
        (TopPair.ofSubset ({φ x}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R k ≫
          (reducedSingularHomologyFunctor R k).map
            (TopCat.ofHom (complSingletonHomotopyEquivSphere (φ x)).toFun) := by
  -- The subspace of the pair `(E, E ∖ {φ x})` and the source of the homotopy equivalence are the
  -- same space presented through `TopCat.of E` and through `E`, so the inner composite is only
  -- type-correct up to unfolding and is rewritten by `Iso.trans_hom` as a term.
  have : ContractibleSpace (TopPair.ofSubset ({φ x}ᶜ : Set (TopCat.of E))).fst :=
    inferInstanceAs (ContractibleSpace E)
  rw [singularHomologyComplSingletonIso, Iso.trans_hom]
  exact congrArg (_ ≫ ·) ((Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (asIso_hom _)
    (ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_hom R _ k)))

include hx in
/-- **Local homology vanishes in degree zero** at a point with a chart to a nonzero real normed
space: `E` is path connected and `E ∖ {φ x}` is nonempty. -/
theorem isZero_singularHomology_complSingleton_zero [Nontrivial E] :
    IsZero ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology R 0) := by
  have : PathConnectedSpace (TopPair.ofSubset ({φ x}ᶜ : Set (TopCat.of E))).fst :=
    inferInstanceAs (PathConnectedSpace E)
  have : Nonempty (TopPair.ofSubset ({φ x}ᶜ : Set (TopCat.of E))).snd :=
    let ⟨z, hz⟩ := exists_ne (φ x)
    ⟨⟨z, hz⟩⟩
  exact (TopPair.isZero_singularHomology_zero _ R).of_iso
    (singularHomologyComplSingletonIsoOfChart R φ hx 0)

include hx in
/-- **Local homology vanishes outside the dimension**: at a point with a chart to a real normed
space `E` of finite dimension `n`, the local homology `Hₖ(M, M ∖ {x})` vanishes for `k ≠ n`. -/
theorem isZero_singularHomology_complSingleton_of_ne [FiniteDimensional ℝ E] {n k : ℕ}
    (h : finrank ℝ E = n) (hk : k ≠ n) :
    IsZero ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology R k) := by
  cases k with
  | zero =>
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (h ▸ Nat.pos_of_ne_zero hk.symm)
    exact isZero_singularHomology_complSingleton_zero R φ hx
  | succ k =>
    refine IsZero.of_iso ?_ (singularHomologyComplSingletonIso R φ hx k)
    cases n with
    | zero =>
      -- A zero-dimensional space is a point, so its unit sphere is empty.
      have : Subsingleton E := Module.finrank_zero_iff.1 h
      have : IsEmpty (sphere (0 : E) 1) :=
        ⟨fun z ↦ by simpa [Subsingleton.elim (z : E) 0] using z.2⟩
      exact isZero_reducedSingularHomologyFunctor_of_isEmpty R _ k
    | succ n =>
      exact (isZero_reducedSingularHomologyFunctor_sphere_of_ne R
        (finrank_euclideanSpace_ulift_fin.{w} (n + 1)) (by lia)).of_iso
        (reducedSingularHomologySphereIsoOfFinrankEq R
          (h.trans (finrank_euclideanSpace_ulift_fin (n + 1)).symm) k)

/-- **Local homology in the top degree**: at a point with a chart to a real normed space of
dimension `n + 1`, the local homology `Hₙ₊₁(M, M ∖ {x})` is one copy of the coefficients.  It is
`TauCeti.singularHomologyComplSingletonIso` followed by the map on reduced homology induced by the
homeomorphism of the unit sphere of `E` with `TopCat.sphere n`
(`TauCeti.sphereHomeomorphOfFinrankEq` and `TauCeti.diskBoundaryHomeomorph`), and by
`TauCeti.reducedSingularHomologyTopCatSphereIso`. -/
def singularHomologyComplSingletonIsoOfFinrankEq {n : ℕ} (h : finrank ℝ E = n + 1) :
    (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology R (n + 1) ≅ R :=
  haveI := Module.finite_of_finrank_eq_succ h
  singularHomologyComplSingletonIso R φ hx n ≪≫
    (reducedSingularHomologyFunctor R n).mapIso (TopCat.isoOfHomeo
      ((sphereHomeomorphOfFinrankEq
          (h.trans (finrank_euclideanSpace_ulift_fin.{w} (n + 1)).symm)).trans
        (diskBoundaryHomeomorph (n + 1)).symm : sphere (0 : E) 1 ≃ₜ TopCat.sphere.{w} n)) ≪≫
    reducedSingularHomologyTopCatSphereIso R n

/-- `TauCeti.singularHomologyComplSingletonIsoOfFinrankEq` is
`TauCeti.singularHomologyComplSingletonIso`, followed by the map on reduced homology induced by the
homeomorphism of the unit sphere of `E` with `TopCat.sphere n`, and by
`TauCeti.reducedSingularHomologyTopCatSphereIso`. -/
@[simp]
lemma singularHomologyComplSingletonIsoOfFinrankEq_hom {n : ℕ} (h : finrank ℝ E = n + 1) :
    haveI := Module.finite_of_finrank_eq_succ h
    (singularHomologyComplSingletonIsoOfFinrankEq R φ hx h).hom =
      (singularHomologyComplSingletonIso R φ hx n).hom ≫
        (reducedSingularHomologyFunctor R n).map (TopCat.ofHom
          (((sphereHomeomorphOfFinrankEq
              (h.trans (finrank_euclideanSpace_ulift_fin.{w} (n + 1)).symm)).trans
            (diskBoundaryHomeomorph (n + 1)).symm : sphere (0 : E) 1 ≃ₜ TopCat.sphere.{w} n) :
            C(sphere (0 : E) 1, TopCat.sphere.{w} n))) ≫
          (reducedSingularHomologyTopCatSphereIso R n).hom :=
  (rfl)

end TauCeti
