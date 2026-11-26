/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Restrict
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv
import TauCeti.Data.Set.Lattice
import TauCeti.Topology.Category.TopCat.Subspace

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

For a subspace `A ⊆ U i` of a family `U : ι → Set X`, `TopCat.toSmallPair` gives the map of
singular pairs `(X, A) ⟶ (X, X.smallSingularSubcomplex U)`. For two subsets `U` and `V` of `X`,
`TopCat.smallSingularSubcomplexToUnion` and `TopCat.smallSingularSubcomplexPairToUnion` compare the
singular simplices lying in `U` or in `V` with `U ∪ V` and `(X, U ∪ V)`, naturally along
`TopCat.smallSingularSubcomplexPairMap`.

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

/-- The relative small-chain isomorphism for the pair defined by a subset. -/
lemma isIso_homologyMap_restrictι_smallSingularSubcomplex_ofSubset {X : TopCat.{w}}
    (S : Set X) {κ : Type*} (F : κ → Set X) (hF : ∀ i, IsOpen (F i))
    (hcov : ⋃ i, F i = Set.univ) (n : ℕ) :
    IsIso (SSetPair.homologyMap ((toSSetPair.obj (ofSubset S)).restrictι
      (X.smallSingularSubcomplex F)) R n) := by
  have hi := isIso_homologyMap_restrictι_smallSingularSubcomplex R (ofSubset S) F hF hcov n
  erw [smallSingularSubcomplex_eq (ofSubset S) F] at hi
  exact hi

variable {P} {P' : TopPair.{w}} (f : P ⟶ P') (U : ι → Set P'.fst)

/-- A map of pairs carries the simplices small for the pulled-back family into the simplices small
for the family.  This is `TopCat.preimage_smallSingularSubcomplex` at the pair-level types
required to restrict the map of singular pairs (`SSetPair.restrictMap`). -/
lemma smallSingularSubcomplex_le_preimage :
    P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i) ≤
      (P'.smallSingularSubcomplex U).preimage (toSSetPair.map f).right :=
  (TopCat.preimage_smallSingularSubcomplex U (Hom.fst f)).ge

end TopPair

namespace TopCat

section Union

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X : TopCat.{w}}

/-- The map of singular pairs `(X, A) ⟶ (X, X.smallSingularSubcomplex U)` for `A` contained in
`U i`, with the identity on the singular simplicial set of `X`. -/
def toSmallPair {ι : Type*} (U : ι → Set X) {A : Set X} {i : ι} (h : A ⊆ U i) :
    TopPair.toSSetPair.obj (TopPair.ofSubset A) ⟶ (X.smallSingularSubcomplex U).pair :=
  SSetPair.homMk (toSmallSingularSubcomplex U h) (𝟙 _)
    ((toSmallSingularSubcomplex_ι _ _).trans (Category.comp_id _).symm)

@[simp]
lemma toSmallPair_left {ι : Type*} (U : ι → Set X) {A : Set X} {i : ι} (h : A ⊆ U i) :
    (toSmallPair U h).left = toSmallSingularSubcomplex U h :=
  (rfl)

@[simp]
lemma toSmallPair_right {ι : Type*} (U : ι → Set X) {A : Set X} {i : ι} (h : A ⊆ U i) :
    (toSmallPair U h).right = 𝟙 (toSSet.obj X) :=
  (rfl)

variable (U V : Set X)

/-- The inclusion of the singular simplicial set of `U ∪ V` into that of `X`. -/
private abbrev unionι : toSSet.obj (of ↥(U ∪ V)) ⟶ toSSet.obj X :=
  toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ V)))

private lemma mono_unionι : Mono (unionι U V) := Functor.map_mono _ _

attribute [local instance] mono_unionι

private lemma smallSubcomplex_le_range :
    X.smallSingularSubcomplex ![U, V] ≤ SSet.Subcomplex.range (unionι U V) := by
  intro n σ hσ
  obtain ⟨i, hi⟩ := (mem_smallSingularSubcomplex_iff X ![U, V] σ).1 hσ
  refine (mem_range_toSSet_subtypeVal_iff (U ∪ V) n σ).2 (hi.trans ?_)
  fin_cases i <;> simp

/-- The singular simplices of `X` lying in `U` or in `V` are singular simplices of `U ∪ V`. -/
def smallSingularSubcomplexToUnion :
    (X.smallSingularSubcomplex ![U, V] : SSet) ⟶ toSSet.obj (of ↥(U ∪ V)) :=
  SSet.Subcomplex.homOfLE (smallSubcomplex_le_range U V) ≫
    inv (SSet.Subcomplex.toRange (unionι U V))

/-- Followed by the inclusion of `U ∪ V` into `X`, the map `TopCat.smallSingularSubcomplexToUnion`
is the inclusion of the singular simplices of `X` lying in `U` or in `V`. -/
@[reassoc]
lemma smallSingularSubcomplexToUnion_comp :
    smallSingularSubcomplexToUnion U V ≫ toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ V))) =
      (X.smallSingularSubcomplex ![U, V]).ι := by
  have h : inv (SSet.Subcomplex.toRange (unionι U V)) ≫ unionι U V =
      (SSet.Subcomplex.range (unionι U V)).ι := by
    rw [IsIso.inv_comp_eq, SSet.Subcomplex.toRange_ι]
  rw [smallSingularSubcomplexToUnion, Category.assoc, h, SSet.Subcomplex.homOfLE_ι]

/-- The comparison maps `TopCat.smallSingularSubcomplexToUnion` are natural in maps carrying `U`
into `U'` and `V` into `V'`. -/
@[reassoc]
lemma smallSingularSubcomplexToUnion_comp_restrict {Y : TopCat.{w}} (f : X ⟶ Y) {U' V' : Set Y}
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    smallSingularSubcomplexToUnion U V ≫
        toSSet.map (ofHom ⟨(hfU.union_union hfV).restrict,
          f.hom.continuous.restrict (hfU.union_union hfV)⟩) =
      X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id (Fin.forall_fin_two.2 ⟨hfU, hfV⟩) ≫
        smallSingularSubcomplexToUnion U' V' := by
  rw [← cancel_mono (unionι U' V')]
  simp only [Category.assoc, smallSingularSubcomplexToUnion_comp, smallSingularSubcomplexMap_ι,
    ← Functor.map_comp, ← ofHom_subtypeVal_comp]
  rw [Functor.map_comp, smallSingularSubcomplexToUnion_comp_assoc]

/-- Up to an isomorphism of simplicial sets, `TopCat.smallSingularSubcomplexToUnion U V` is the
inclusion of the singular simplices of `U ∪ V` lying in the trace of `U` or in the trace of `V`:
the singular simplices of `X` lying in `U` or in `V` are exactly the images of those. -/
lemma exists_iso_comp_smallSingularSubcomplexToUnion :
    ∃ e : ((of ↥(U ∪ V)).smallSingularSubcomplex
        (fun i ↦ ofHom (ContinuousMap.subtypeVal (U ∪ V)) ⁻¹' ![U, V] i) : SSet) ≅
        (X.smallSingularSubcomplex ![U, V] : SSet),
      e.hom ≫ smallSingularSubcomplexToUnion U V =
        ((of ↥(U ∪ V)).smallSingularSubcomplex
          (fun i ↦ ofHom (ContinuousMap.subtypeVal (U ∪ V)) ⁻¹' ![U, V] i)).ι := by
  set f := unionι U V
  set D := X.smallSingularSubcomplex ![U, V]
  -- The simplices of `D` all come from `U ∪ V`, so `D` is isomorphic to its preimage under `f`,
  -- which is the subcomplex of simplices of `U ∪ V` small for its cover by `U` and `V`.
  have : IsIso (D.fromPreimage f) := by
    have (n : SimplexCategoryᵒᵖ) : IsIso ((D.fromPreimage f).app n) := by
      have hinj : Function.Injective (f.app n) :=
        (CategoryTheory.mono_iff_injective (f.app n)).1 inferInstance
      refine (isIso_iff_bijective _).2 ⟨fun x y hxy ↦ Subtype.ext ?_, fun y ↦ ?_⟩
      · exact hinj (congrArg Subtype.val hxy)
      · exact (D.mem_range_fromPreimage_app_iff f y).2 (smallSubcomplex_le_range U V n y.property)
    exact NatIso.isIso_of_isIso_app _
  rw [← preimage_smallSingularSubcomplex]
  refine ⟨asIso (D.fromPreimage f), ?_⟩
  rw [asIso_hom, ← cancel_mono f, Category.assoc, smallSingularSubcomplexToUnion_comp,
    SSet.Subcomplex.fromPreimage_ι]

lemma toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion {A : Set X} {i : Fin 2}
    (h : A ⊆ ![U, V] i) (h' : A ⊆ U ∪ V) :
    toSmallSingularSubcomplex ![U, V] h ≫ smallSingularSubcomplexToUnion U V =
      toSSet.map (ofHom (ContinuousMap.inclusion h')) := by
  rw [← cancel_mono (unionι U V), Category.assoc, smallSingularSubcomplexToUnion_comp,
    toSmallSingularSubcomplex_ι, ← Functor.map_comp]
  rfl

/-- The map of singular pairs from `X` relative to its singular simplices lying in `U` or in `V`
to `(X, U ∪ V)`, given by `TopCat.smallSingularSubcomplexToUnion` on subobjects and the identity on
the singular simplicial set of `X`. -/
def smallSingularSubcomplexPairToUnion :
    (X.smallSingularSubcomplex ![U, V]).pair ⟶
      TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)) :=
  SSetPair.homMk (smallSingularSubcomplexToUnion U V) (𝟙 _)
    ((smallSingularSubcomplexToUnion_comp U V).trans (Category.comp_id _).symm)

@[simp]
lemma smallSingularSubcomplexPairToUnion_left :
    (smallSingularSubcomplexPairToUnion U V).left = smallSingularSubcomplexToUnion U V :=
  (rfl)

@[simp]
lemma smallSingularSubcomplexPairToUnion_right :
    (smallSingularSubcomplexPairToUnion U V).right = 𝟙 (toSSet.obj X) :=
  (rfl)

/-- The chain map induced by the ambient component of `TopCat.smallSingularSubcomplexPairToUnion`
is the identity. Not `@[simp]`: `TopCat.smallSingularSubcomplexPairToUnion_right` already
rewrites its left-hand side. -/
lemma chainComplexMap_smallSingularSubcomplexPairToUnion_right :
    SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).right R = 𝟙 _ :=
  (congrArg (SSet.chainComplexMap · R) (smallSingularSubcomplexPairToUnion_right U V)).trans
    (CategoryTheory.Functor.map_id _ _)

/-- The quotient map from the singular chains of `X` to its chains relative to the singular
simplices lying in `U` or in `V`, followed by `TopCat.smallSingularSubcomplexPairToUnion`, is the
quotient map to the relative chains of `(X, U ∪ V)`. -/
@[reassoc]
lemma chainComplexπ_smallSingularSubcomplexPairToUnion :
    (X.smallSingularSubcomplex ![U, V]).pair.chainComplexπ R ≫
        SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) R =
      (TopPair.ofSubset (U ∪ V)).singularChainComplexπ R := by
  rw [← SSetPair.chainComplexπ_naturality, chainComplexMap_smallSingularSubcomplexPairToUnion_right]
  exact Category.id_comp _

lemma toSmallPair_comp_smallSingularSubcomplexPairToUnion {A : Set X} {i : Fin 2}
    (h : A ⊆ ![U, V] i) (h' : A ⊆ U ∪ V) :
    toSmallPair ![U, V] h ≫ smallSingularSubcomplexPairToUnion U V =
      TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h') := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, TopPair.toSSetPair_map_ofSubsetMap_id_left]
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion U V h h'
  · rw [MorphismProperty.Comma.comp_right, TopPair.toSSetPair_map_ofSubsetMap_id_right]
    exact Category.comp_id _

/-- The singular simplices of `X` lying in `U` or in `V` compute the homology of `U ∪ V`, by the
small-chain theorem for the cover of `U ∪ V` by `U` and `V`, which only needs to be open in
`U ∪ V`. -/
lemma quasiIso_chainComplexMap_smallSingularSubcomplexToUnion
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexToUnion U V) R) := by
  obtain ⟨e, he⟩ := exists_iso_comp_smallSingularSubcomplexToUnion U V
  have hq := TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι R
    (fun i ↦ ofHom (ContinuousMap.subtypeVal (U ∪ V)) ⁻¹' ![U, V] i)
    (fun i ↦ by fin_cases i; exacts [hU, hV])
    (by
      rw [← Set.preimage_iUnion, Set.iUnion_vecCons_pair]
      exact Set.eq_univ_of_forall fun x ↦ x.property)
  have hcomp : SSet.chainComplexMap (e.hom ≫ smallSingularSubcomplexToUnion U V) R =
      SSet.chainComplexMap e.hom R ≫ SSet.chainComplexMap (smallSingularSubcomplexToUnion U V) R :=
    Functor.map_comp _ _ _
  rw [← he, hcomp] at hq
  exact quasiIso_of_comp_left (SSet.chainComplexMap e.hom R) _

/-- For `U` and `V` open in `U ∪ V`, the quotient map from the relative chains of `X` modulo its
singular simplices lying in `U` or in `V` to the relative chains of `(X, U ∪ V)` (killing all
singular simplices lying in `U ∪ V`) is a quasi-isomorphism. -/
lemma quasiIso_chainComplexMap_smallSingularSubcomplexPairToUnion
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    QuasiIso (SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) R) := by
  have : QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).left R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplexToUnion R U V hU hV
  have : IsIso (SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).right R) := by
    rw [chainComplexMap_smallSingularSubcomplexPairToUnion_right]
    exact IsIso.id _
  have : QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).right R) :=
    quasiIso_of_isIso _
  exact SSetPair.quasiIso_chainComplexMap _ R

/-- For `U` and `V` open in `U ∪ V`, the comparison map from the relative homology of `X` modulo
its singular simplices lying in `U` or in `V` to `Hₙ(X, U ∪ V; R)` is an isomorphism. -/
lemma isIso_homologyMap_smallSingularSubcomplexPairToUnion
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (n : ℕ) :
    IsIso (SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) R n) := by
  have := quasiIso_chainComplexMap_smallSingularSubcomplexPairToUnion R U V hU hV
  infer_instance

section Naturality

variable {U V} {Y : TopCat.{w}} {U' V' : Set Y} (f : X ⟶ Y)
  (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- The map of singular pairs from `X` relative to its singular simplices lying in `U` or in `V`
to `Y` relative to its singular simplices lying in `U'` or in `V'`, induced by a map `f` carrying
`U` into `U'` and `V` into `V'`. -/
def smallSingularSubcomplexPairMap :
    (X.smallSingularSubcomplex ![U, V]).pair ⟶ (Y.smallSingularSubcomplex ![U', V']).pair :=
  SSetPair.homMk
    (X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id (Fin.forall_fin_two.2 ⟨hfU, hfV⟩))
    (toSSet.map f) (smallSingularSubcomplexMap_ι _ _ _ _ _)

@[simp]
lemma smallSingularSubcomplexPairMap_left :
    (smallSingularSubcomplexPairMap f hfU hfV).left =
      X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id (Fin.forall_fin_two.2 ⟨hfU, hfV⟩) :=
  (rfl)

@[simp]
lemma smallSingularSubcomplexPairMap_right :
    (smallSingularSubcomplexPairMap f hfU hfV).right = toSSet.map f :=
  (rfl)

lemma toSmallPair_comp_smallSingularSubcomplexPairMap {A : Set X} {A' : Set Y} {i : Fin 2}
    (h : A ⊆ ![U, V] i) (h' : A' ⊆ ![U', V'] i) (hA : Set.MapsTo f A A') :
    toSmallPair ![U, V] h ≫ smallSingularSubcomplexPairMap f hfU hfV =
      TopPair.toSSetPair.map (TopPair.ofSubsetMap f hA) ≫ toSmallPair ![U', V'] h' := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      TopPair.toSSetPair_map_ofSubsetMap_left]
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ f id _ h h' hA
  · rw [MorphismProperty.Comma.comp_right, MorphismProperty.Comma.comp_right,
      TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The comparison maps `TopCat.smallSingularSubcomplexPairToUnion` are natural in maps carrying
`U` into `U'` and `V` into `V'`. -/
@[reassoc]
lemma smallSingularSubcomplexPairToUnion_comp_ofSubsetMap :
    smallSingularSubcomplexPairToUnion U V ≫
        TopPair.toSSetPair.map (TopPair.ofSubsetMap f (hfU.union_union hfV)) =
      smallSingularSubcomplexPairMap f hfU hfV ≫ smallSingularSubcomplexPairToUnion U' V' := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      TopPair.toSSetPair_map_ofSubsetMap_left]
    exact smallSingularSubcomplexToUnion_comp_restrict U V f hfU hfV
  · rw [MorphismProperty.Comma.comp_right, MorphismProperty.Comma.comp_right,
      TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end Naturality

end Union

end TopCat

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
      (W.smallSingularSubcomplex U).pair.chainComplexπ T = 0 := by
  have hf' : TopCat.toSSet.map f =
      (TopCat.toSSet.map (TopCat.ofHom ⟨fun z ↦ ⟨f z, hf z⟩, f.hom.continuous.subtype_mk hf⟩) ≫
        TopCat.toSmallSingularSubcomplex U (subset_refl (U i))) ≫
        (W.smallSingularSubcomplex U).ι := by
    rw [Category.assoc, TopCat.toSmallSingularSubcomplex_ι, ← TopCat.toSSet.map_comp]
    exact congrArg TopCat.toSSet.map (TopCat.ext fun _ ↦ rfl)
  exact (eq_whisker ((congrArg (SSet.chainComplexMap · T) hf').trans
      (((SSet.chainComplexFunctor A).obj T).map_comp _ _)) _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ ((W.smallSingularSubcomplex U).pair.chainComplex_condition T)).trans comp_zero

end TauCeti
