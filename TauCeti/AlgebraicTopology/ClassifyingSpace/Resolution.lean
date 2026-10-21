/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Acyclic
public import TauCeti.RepresentationTheory.Augmentation.Basic
public import TauCeti.RepresentationTheory.Rep.OfMulAction
public import TauCeti.AlgebraicTopology.Cellular.Resolution
public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.ClassifyingSpace.WeakContractibility
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction

/-!
# Projective resolutions from Milnor's countable join

A group `G` acts on the simplices of the countable join `indexedJoin fun _ : ℕ => G` by
translating the labels of their vertices, and this action commutes with taking faces
(`TauCeti.face_smul_universalGSpace`). So the ordered simplicial chains of the countable join,
indexed by the cells of `universalGSpace G` and oriented by increasing index as its CW structure
is, form a chain complex of permutation representations of `G`
(`TauCeti.universalGSpaceChainComplex`). Forgetting the action gives back the ordered simplicial
chain complex (`TauCeti.universalGSpaceChainComplexForget₂Iso`).

The action on simplices is free, so each term is a free representation, with basis one simplex
in each orbit (`TauCeti.ofMulActionIsoFree`), and in particular projective. The sum of the
coefficients of a `0`-chain is an augmentation onto the trivial representation
(`TauCeti.universalGSpaceAugmentation`), and it is a quasi-isomorphism because the augmented
ordered chain complex of the countable join is exact
(`TauCeti.quasiIso_orderedSimplicialChainComplexAugmentation_indexedJoin`). Together these make
the ordered chains of the countable join a projective resolution of the trivial representation
(`TauCeti.universalGSpaceResolution`). It is the topological counterpart of Mathlib's standard
resolution `Rep.standardResolution`; on underlying complexes of modules,
`TauCeti.universalGSpaceToStandardComplex` maps the former to the latter.

The cellular chains give a second resolution. The CW structure of the classifying space lifts
along the orbit map to a CW structure on the countable join whose cells `G` permutes freely, and
the countable join has vanishing singular homology in positive degrees
(`TauCeti.isZero_singularHomology_universalGSpace`), since all its homotopy groups vanish. So
its cellular chains are a projective resolution of the trivial representation as well
(`TauCeti.classifyingSpaceCellularResolution`), by the general statement for acyclic free
`G`-CW complexes, `TauCeti.cellularResolution`.

## Main definitions

* `TauCeti.universalGSpaceChainComplex`: the ordered chain complex of the countable join, as a
  chain complex of permutation representations of `G`.
* `TauCeti.universalGSpaceAugmentation`: its augmentation onto the trivial representation.
* `TauCeti.universalGSpaceResolution`: the resulting projective resolution of the trivial
  representation.
* `TauCeti.classifyingSpaceCellularResolution`: the cellular chains of the CW structure lifted
  from the classifying space, as a projective resolution of the trivial representation.

## Main results

* `TauCeti.universalGSpaceChainComplexForget₂Iso`: forgetting the action gives the ordered
  simplicial chain complex of the countable join.
* `TauCeti.quasiIso_universalGSpaceAugmentation`: the augmentation is a quasi-isomorphism.
* `TauCeti.isZero_singularHomology_universalGSpace`: the singular homology of the countable join
  vanishes in positive degrees.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter I, Sections 4 and 5.
-/

public section

noncomputable section

open CategoryTheory Finsupp AbstractSimplicialComplex

namespace TauCeti

universe u

attribute [local instance] universalGSpaceVertexOrder

section ChainComplex

variable (k : Type u) [Ring k] (G : Type u) [Group G]

/-- The ordered simplicial boundary of the countable join commutes with translation. -/
private lemma boundary_comp_lmapDomain_smul (n : ℕ) (g : G) :
    OrderedSimplicialChain.boundary (K := indexedJoin fun _ : ℕ => G) k n ∘ₗ
        lmapDomain k k (g • ·) =
      lmapDomain k k (g • ·) ∘ₗ OrderedSimplicialChain.boundary k n := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp

/-- The ordered simplicial boundary of the countable join, as a morphism between the permutation
representations of `G` on its simplices of consecutive dimensions. -/
def universalGSpaceBoundary (n : ℕ) :
    Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell (n + 1)) ⟶
      Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) :=
  Rep.ofHom
    { toLinearMap := (MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ
        OrderedSimplicialChain.boundary k n ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
      isIntertwining' g := LinearMap.ext fun x ↦ by
        simpa [Representation.ofMulAction_def] using
          congr((MonoidAlgebra.coeffLinearEquiv k).symm
            ($(boundary_comp_lmapDomain_smul k G n g) (MonoidAlgebra.coeffLinearEquiv k x))) }

/-- The boundary of a simplex is the alternating sum of its faces. -/
@[simp]
theorem universalGSpaceBoundary_hom_single {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell (n + 1)) (a : k) :
    (dsimp% only ((universalGSpaceBoundary k G n).hom (MonoidAlgebra.single c a))) =
      ∑ j : Fin (n + 2), (-1 : k) ^ (j : ℕ) • MonoidAlgebra.single (c.face j) a := by
  simp [universalGSpaceBoundary, ← MonoidAlgebra.ofCoeff_single, ← MonoidAlgebra.ofCoeff_smul,
    smul_single]

/-- Read on coefficients, the equivariant boundary is the ordered simplicial boundary. -/
theorem universalGSpaceBoundary_comp_coeff (n : ℕ) :
    (forget₂ (Rep k G) (ModuleCat k)).map (universalGSpaceBoundary k G n) ≫
        (MonoidAlgebra.coeffLinearEquiv k).toModuleIso.hom =
      (MonoidAlgebra.coeffLinearEquiv k).toModuleIso.hom ≫
        ModuleCat.ofHom (OrderedSimplicialChain.boundary k n) := by
  ext x
  simp [universalGSpaceBoundary]

/-- **The ordered chains of the countable join as a complex of representations.** In degree `n`
it is the permutation representation of `G` on the `n`-simplices of the countable join, which
are the `n`-cells of `universalGSpace G`, and its differential is the alternating simplicial
boundary. -/
-- The body is exposed so that its terms are permutation representations by definition, as for
-- Mathlib's `Rep.standardComplex`; the statements below about its differential and augmentation
-- rely on this.
@[expose]
def universalGSpaceChainComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun n ↦ Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n))
    (universalGSpaceBoundary k G) fun n ↦
      Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ by
        simpa [universalGSpaceBoundary] using congr((MonoidAlgebra.coeffLinearEquiv k).symm
          ($(OrderedSimplicialChain.boundary_boundary k n) (MonoidAlgebra.coeffLinearEquiv k x)))

/-- In degree `n` the complex is the permutation representation on the `n`-simplices. -/
@[simp]
theorem universalGSpaceChainComplex_X (n : ℕ) :
    (universalGSpaceChainComplex k G).X n =
      Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) :=
  rfl

/-- The differential of the complex is the equivariant simplicial boundary. -/
@[simp]
theorem universalGSpaceChainComplex_d (n : ℕ) :
    (universalGSpaceChainComplex k G).d (n + 1) n = universalGSpaceBoundary k G n :=
  ChainComplex.of_d
    (fun n ↦ Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n))
    (universalGSpaceBoundary k G) n

/-- **Forgetting the action gives the ordered simplicial chain complex** of the countable join;
in each degree the isomorphism reads a vector of the permutation representation as its
coefficients. -/
def universalGSpaceChainComplexForget₂Iso :
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).obj
        (universalGSpaceChainComplex k G) ≅
      orderedSimplicialChainComplex (indexedJoin fun _ : ℕ => G) k :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (MonoidAlgebra.coeffLinearEquiv k).toModuleIso ≪≫
      eqToIso (orderedSimplicialChainComplex_X k n).symm)
    fun i j (h : j + 1 = i) ↦ by
      subst h
      rw [Functor.mapHomologicalComplex_obj_d, universalGSpaceChainComplex_d,
        orderedSimplicialChainComplex_d]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      exact ((reassoc_of% universalGSpaceBoundary_comp_coeff k G j) _).symm

/-- In each degree the isomorphism reads a vector as its coefficients. -/
@[simp]
theorem universalGSpaceChainComplexForget₂Iso_hom_f (n : ℕ) :
    (universalGSpaceChainComplexForget₂Iso k G).hom.f n =
      (MonoidAlgebra.coeffLinearEquiv k).toModuleIso.hom ≫
        eqToHom (orderedSimplicialChainComplex_X k n).symm :=
  (rfl)

/-- The coefficient sum vanishes on boundaries of `1`-simplices. -/
private lemma universalGSpaceBoundary_comp_permutationAugmentation :
    universalGSpaceBoundary k G 0 ≫ permutationAugmentation k G _ = 0 :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ by
    simpa [universalGSpaceBoundary] using
      congr(ModuleCat.Hom.hom $(forget₂_map_permutationAugmentation k G _)
        ((universalGSpaceBoundary k G 0).hom x)).trans
        (LinearMap.congr_fun (OrderedSimplicialChain.augmentation_comp_boundary k)
          (MonoidAlgebra.coeffLinearEquiv k x))

/-- The **augmentation** of the ordered chains of the countable join: the chain map to the
trivial representation, placed in degree `0`, that sums the coefficients of a `0`-chain. -/
def universalGSpaceAugmentation :
    universalGSpaceChainComplex k G ⟶
      (ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k) :=
  ((universalGSpaceChainComplex k G).toSingle₀Equiv _).symm
    ⟨permutationAugmentation k G _, by
      rw [universalGSpaceChainComplex_d]
      exact universalGSpaceBoundary_comp_permutationAugmentation k G⟩

/-- In degree `0` the augmentation sums the coefficients. -/
@[simp]
theorem universalGSpaceAugmentation_f_zero :
    (universalGSpaceAugmentation k G).f 0 = permutationAugmentation k G _ :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **The augmentation of the countable join is a quasi-isomorphism**: forgetting the action, it
is the augmentation of the ordered simplicial chain complex. -/
instance quasiIso_universalGSpaceAugmentation : QuasiIso (universalGSpaceAugmentation k G) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat k)),
    quasiIso_iff_of_arrow_mk_iso _ (orderedSimplicialChainComplexAugmentation
      (indexedJoin fun _ : ℕ => G) k) ?_]
  · exact quasiIso_orderedSimplicialChainComplexAugmentation_indexedJoin k
  · -- In degree `0` both augmentations sum the coefficients of a `0`-chain.
    refine Arrow.isoMk' _ _ (universalGSpaceChainComplexForget₂Iso k G)
      ((HomologicalComplex.singleMapHomologicalComplex _ _ 0).app _) ?_
    ext : 1
    simpa using (forget₂_map_permutationAugmentation k G _).symm

end ChainComplex

section Resolution

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- **The ordered chains of Milnor's countable join are a projective resolution** of the
trivial representation of `G`: the terms are free over the group ring, because `G` acts freely
on the simplices, and the augmentation is a quasi-isomorphism. -/
-- The body is exposed, as for Mathlib's `standardResolution`, so that the complex of the
-- resolution is the chain complex by definition: even stating `universalGSpaceResolution_π`
-- needs this, its augmentation having source `universalGSpaceChainComplex k G`.
@[expose]
def universalGSpaceResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := universalGSpaceChainComplex k G
  projective n := by
    rw [universalGSpaceChainComplex_X]
    infer_instance
  π := universalGSpaceAugmentation k G

/-- The complex of the resolution is the ordered chain complex of the countable join. -/
@[simp]
theorem universalGSpaceResolution_complex :
    (universalGSpaceResolution k G).complex = universalGSpaceChainComplex k G :=
  (rfl)

/-- The augmentation of the resolution sums the coefficients of a `0`-chain. -/
@[simp]
theorem universalGSpaceResolution_π :
    (universalGSpaceResolution k G).π = universalGSpaceAugmentation k G :=
  (rfl)

end Resolution

section Cellular

/-- **The singular homology of Milnor's countable join vanishes in positive degrees**, since all
its homotopy groups vanish. -/
theorem isZero_singularHomology_universalGSpace (k : Type u) [Ring k] (G : Type u) [Nonempty G]
    (n : ℕ) :
    Limits.IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj
      (ModuleCat.of k k)).obj (TopCat.of (universalGSpace G))) := by
  obtain ⟨x⟩ : Nonempty (universalGSpace G) := inferInstance
  refine isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup (n := n + 2)
    (X := TopCat.of (universalGSpace G)) (x := x) (fun m _ ↦ ?_) k (by lia) (by lia)
  rcases m with _ | m
  · exact HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
  · exact subsingleton_homotopyGroup_universalGSpace G m x

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- **The cellular chains of Milnor's countable join are a projective resolution** of the trivial
representation of `G`, for the CW structure lifted from the classifying space
`TauCeti.instCWComplexClassifyingSpace` along the orbit map, whose cells are permuted freely by
`G`. -/
def classifyingSpaceCellularResolution : ProjectiveResolution (Rep.trivial k G k) :=
  haveI : PathConnectedSpace (classifyingSpaceProj G ⁻¹' (Set.univ : Set (classifyingSpace G))) :=
    isPathConnected_iff_pathConnectedSpace.1 (pathConnectedSpace_iff_univ.1 inferInstance)
  cellularResolution Set.univ (isQuotientCoveringMap_classifyingSpaceProj G) k fun n ↦
    (isZero_singularHomology_universalGSpace k G n).of_iso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) (n + 1)).obj
        (ModuleCat.of k k)).mapIso (TopCat.isoOfHomeo (Homeomorph.Set.univ _)))

end Cellular

end TauCeti
