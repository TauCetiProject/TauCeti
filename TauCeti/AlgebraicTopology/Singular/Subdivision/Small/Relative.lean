/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Restrict
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-!
# The relative small-chain theorem

Let `P` be a topological pair and `U` a family of subsets of its ambient space.  The singular
simplices of the ambient space whose image lies in a member of `U` form a subcomplex
`TopPair.smallSingularSubcomplex P U` of the ambient simplicial set of the singular pair of `P`,
to which the singular pair restricts.  Its preimage in the singular simplicial set of the subspace
is the small subcomplex of the subspace for the pulled-back family
(`TopPair.smallSingularSubcomplex_preimage_hom`), a map of pairs carries the simplices small for
the pulled-back family into the simplices small for the family
(`TopPair.smallSingularSubcomplex_le_preimage`), and a continuous map into a single member of `U`
vanishes in the chains relative to the small subcomplex
(`TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero`).

The main result is the relative form of the small-chain theorem: when `U` is an open cover, the
inclusion of the restricted pair induces isomorphisms on relative singular homology in every degree
(`TopPair.isIso_homologyMap_restrictι_smallSingularSubcomplex`).  It identifies the relative
homology of a topological pair with that of its singular pair restricted to the simplices
subordinate to any open cover of the ambient space, and is the input from the small-chain theorem
to excision for relative singular homology.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  (P : TopPair.{w}) {ι : Type*} (U : ι → Set P.fst)

/-- The singular simplices of the ambient space of a topological pair whose image lies in a member
of the family `U`, as a subcomplex of the ambient simplicial set of the singular pair of `P`.  It is
`TopCat.smallSingularSubcomplex` of the ambient space, typed so that the singular pair can be
restricted to it. -/
def smallSingularSubcomplex : (toSSetPair.obj P).right.Subcomplex :=
  P.fst.smallSingularSubcomplex U

/-- The small subcomplex of a topological pair is the small subcomplex of its ambient space. -/
lemma smallSingularSubcomplex_eq :
    P.smallSingularSubcomplex U = P.fst.smallSingularSubcomplex U := (rfl)

@[simp]
lemma mem_smallSingularSubcomplex_iff {n : SimplexCategoryᵒᵖ}
    (σ : (toSSetPair.obj P).right.obj n) :
    σ ∈ (P.smallSingularSubcomplex U).obj n ↔
      ∃ i, Set.range (P.fst.toSSetObjEquiv n σ) ⊆ U i :=
  TopCat.mem_smallSingularSubcomplex_iff P.fst U σ

/-- The preimage of the small subcomplex of a pair in the singular simplicial set of its subspace
is the small subcomplex of the subspace for the restricted family. -/
lemma smallSingularSubcomplex_preimage_hom :
    (P.smallSingularSubcomplex U).preimage (toSSetPair.obj P).hom =
      P.snd.smallSingularSubcomplex (fun i ↦ P.map ⁻¹' U i) :=
  TopCat.preimage_smallSingularSubcomplex U P.map

variable (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)

include hU hcov in
/-- **The relative small-chain theorem.** Restricting the singular pair of a topological pair to
the simplices subordinate to an open cover of the ambient space does not change relative
homology. -/
theorem isIso_homologyMap_restrictι_smallSingularSubcomplex (n : ℕ) :
    IsIso (SSetPair.homologyMap
      ((toSSetPair.obj P).restrictι (P.smallSingularSubcomplex U)) R n) := by
  refine SSetPair.isIso_homologyMap_restrictι R ?_ ?_ n
  · exact (congrArg (fun T : (toSSetPair.obj P).left.Subcomplex ↦
        QuasiIso (SSet.chainComplexMap T.ι R))
      (P.smallSingularSubcomplex_preimage_hom U)).mpr
      (TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι R (fun i ↦ P.map ⁻¹' U i)
        (fun i ↦ (hU i).preimage P.map.hom.continuous)
        (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ]))
  · exact TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι R U hU hcov

variable {P} {P' : TopPair.{w}} (f : P ⟶ P') (U : ι → Set P'.fst)

/-- A map of pairs carries the simplices small for the pulled-back family into the simplices small
for the family.  This is `TopCat.preimage_smallSingularSubcomplex` at the pair-level types
required to restrict the map of singular pairs (`SSetPair.restrictMap`). -/
lemma smallSingularSubcomplex_le_preimage :
    P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i) ≤
      (P'.smallSingularSubcomplex U).preimage (toSSetPair.map f).right :=
  (TopCat.preimage_smallSingularSubcomplex U (Hom.fst f)).ge

end TopPair

namespace TauCeti

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasCoproducts.{w} A]

/-- A continuous map `f : Z ⟶ W` taking values in a single member `U i` of a family of subsets
induces the zero map into the singular chains of `W` relative to the simplices small for `U`. -/
@[reassoc]
lemma chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero
    {Z W : TopCat.{w}} {ι : Type*} (U : ι → Set W) (f : Z ⟶ W) {i : ι} (hf : ∀ z, f z ∈ U i)
    (T : A) :
    SSet.chainComplexMap (TopCat.toSSet.map f) T ≫
        (W.smallSingularSubcomplex U).pair.chainComplexπ T =
      0 := by
  have hι : SSet.chainComplexMap (W.smallSingularSubcomplex U).ι T ≫
      (W.smallSingularSubcomplex U).pair.chainComplexπ T = 0 :=
    (W.smallSingularSubcomplex U).pair.chainComplex_condition T
  have hmap : SSet.chainComplexMap (TopCat.toSSet.map f) T =
      SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom ⟨fun z ↦ ⟨f z, hf z⟩, f.hom.continuous.subtype_mk hf⟩) ≫
          TopCat.toSmallSingularSubcomplex U (subset_refl (U i))) T ≫
      SSet.chainComplexMap (W.smallSingularSubcomplex U).ι T := by
    refine Eq.trans ?_ (((SSet.chainComplexFunctor A).obj T).map_comp _ _)
    congr 2
    rw [Category.assoc, TopCat.toSmallSingularSubcomplex_ι, ← TopCat.toSSet.map_comp]
    rfl
  exact (eq_whisker hmap _).trans ((Category.assoc _ _ _).trans ((whisker_eq _ hι).trans comp_zero))

end TauCeti
