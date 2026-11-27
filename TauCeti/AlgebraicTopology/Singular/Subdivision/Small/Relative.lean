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
singular pairs `(X, A) ⟶ (X, X.smallSingularSubcomplex U)`. For an arbitrary family `U : ι → Set X`,
`TopCat.smallSingularSubcomplexToIUnion` and `TopCat.smallSingularSubcomplexPairToIUnion` compare
the singular simplices lying in a member of `U` with `⋃ i, U i` and `(X, ⋃ i, U i)`, naturally
under reindexed covered maps `TopCat.smallSingularSubcomplexPairMap`. When each `U i` is open in
`⋃ i, U i`, `TopCat.smallSingularSubcomplexToIUnionChainHomotopyEquiv` exhibits the induced chain
map as a chain homotopy equivalence. Specializing to `![U, V]` yields the binary union comparison
(`TopCat.smallSingularSubcomplexToUnion`, `TopCat.smallSingularSubcomplexPairToUnion`,
`TopCat.smallSingularSubcomplexToUnionChainHomotopyEquiv`).

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

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] {X : TopCat.{w}}

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

section IUnion

variable {ι : Type*} (U : ι → Set X)

/-- The inclusion of the singular simplicial set of `⋃ i, U i` into that of `X`. -/
private abbrev iUnionι : toSSet.obj (of ↥(⋃ i, U i)) ⟶ toSSet.obj X :=
  toSSet.map (ofHom (ContinuousMap.subtypeVal (⋃ i, U i)))

private lemma mono_iUnionι : Mono (iUnionι U) := Functor.map_mono _ _

attribute [local instance] mono_iUnionι

private lemma smallSubcomplex_le_range :
    X.smallSingularSubcomplex U ≤ SSet.Subcomplex.range (iUnionι U) := by
  intro n σ hσ
  obtain ⟨i, hi⟩ := (mem_smallSingularSubcomplex_iff X U σ).1 hσ
  exact (mem_range_toSSet_subtypeVal_iff (⋃ i, U i) n σ).2 (hi.trans (Set.subset_iUnion U i))

/-- The singular simplices of `X` lying in some member of `U` are singular simplices of
`⋃ i, U i`. -/
def smallSingularSubcomplexToIUnion :
    (X.smallSingularSubcomplex U : SSet) ⟶ toSSet.obj (of ↥(⋃ i, U i)) :=
  SSet.Subcomplex.homOfLE (smallSubcomplex_le_range U) ≫
    inv (SSet.Subcomplex.toRange (iUnionι U))

/-- Followed by the inclusion of `⋃ i, U i` into `X`, `TopCat.smallSingularSubcomplexToIUnion`
is the inclusion of the singular simplices of `X` lying in some member of `U`. -/
@[reassoc]
lemma smallSingularSubcomplexToIUnion_comp :
    smallSingularSubcomplexToIUnion U ≫
        toSSet.map (ofHom (ContinuousMap.subtypeVal (⋃ i, U i))) =
      (X.smallSingularSubcomplex U).ι := by
  have h : inv (SSet.Subcomplex.toRange (iUnionι U)) ≫ iUnionι U =
      (SSet.Subcomplex.range (iUnionι U)).ι := by
    rw [IsIso.inv_comp_eq, SSet.Subcomplex.toRange_ι]
  rw [smallSingularSubcomplexToIUnion, Category.assoc, h, SSet.Subcomplex.homOfLE_ι]

/-- A map `f : X ⟶ Y` carrying each `U i` into `V (r i)` maps `⋃ i, U i` into `⋃ j, V j`. -/
lemma mapsTo_iUnion {κ : Type*} {Y : TopCat.{w}} {V : κ → Set Y} {f : X ⟶ Y}
    (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    Set.MapsTo f (⋃ i, U i) (⋃ j, V j) := by
  rintro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨r i, hf i hi⟩

/-- The comparison maps `TopCat.smallSingularSubcomplexToIUnion` are natural under reindexed
covered maps `f : X ⟶ Y` carrying each `U i` into `V (r i)`. -/
@[reassoc]
lemma smallSingularSubcomplexToIUnion_comp_restrict {κ : Type*} {Y : TopCat.{w}} (V : κ → Set Y)
    (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    smallSingularSubcomplexToIUnion U ≫
        toSSet.map (ofHom ⟨(mapsTo_iUnion U r hf).restrict,
          f.hom.continuous.restrict (mapsTo_iUnion U r hf)⟩) =
      X.smallSingularSubcomplexMap U V f r hf ≫ smallSingularSubcomplexToIUnion V := by
  rw [← cancel_mono (iUnionι V)]
  simp only [Category.assoc, smallSingularSubcomplexToIUnion_comp, smallSingularSubcomplexMap_ι,
    ← Functor.map_comp, ← ofHom_subtypeVal_comp]
  rw [Functor.map_comp, smallSingularSubcomplexToIUnion_comp_assoc]

/-- Up to an isomorphism of simplicial sets, `TopCat.smallSingularSubcomplexToIUnion U` is the
inclusion of the singular simplices of `⋃ i, U i` lying in the trace of some `U i`. -/
lemma exists_iso_comp_smallSingularSubcomplexToIUnion :
    ∃ e : ((of ↥(⋃ i, U i)).smallSingularSubcomplex
        (fun i ↦ ofHom (ContinuousMap.subtypeVal (⋃ j, U j)) ⁻¹' U i) : SSet) ≅
        (X.smallSingularSubcomplex U : SSet),
      e.hom ≫ smallSingularSubcomplexToIUnion U =
        ((of ↥(⋃ i, U i)).smallSingularSubcomplex
          (fun i ↦ ofHom (ContinuousMap.subtypeVal (⋃ j, U j)) ⁻¹' U i)).ι := by
  set f := iUnionι U
  set D := X.smallSingularSubcomplex U
  -- The simplices of `D` all come from `⋃ i, U i`, so `D` is isomorphic to its preimage under `f`,
  -- which is the subcomplex of simplices of `⋃ i, U i` small for the trace family.
  have : IsIso (D.fromPreimage f) := by
    have (n : SimplexCategoryᵒᵖ) : IsIso ((D.fromPreimage f).app n) := by
      have hinj : Function.Injective (f.app n) :=
        (CategoryTheory.mono_iff_injective (f.app n)).1 inferInstance
      refine (isIso_iff_bijective _).2 ⟨fun x y hxy ↦ Subtype.ext ?_, fun y ↦ ?_⟩
      · exact hinj (congrArg Subtype.val hxy)
      · exact (D.mem_range_fromPreimage_app_iff f y).2 (smallSubcomplex_le_range U n y.property)
    exact NatIso.isIso_of_isIso_app _
  rw [← preimage_smallSingularSubcomplex]
  refine ⟨asIso (D.fromPreimage f), ?_⟩
  rw [asIso_hom, ← cancel_mono f, Category.assoc, smallSingularSubcomplexToIUnion_comp,
    SSet.Subcomplex.fromPreimage_ι]

private lemma iUnion_preimage_subtypeVal :
    ⋃ i, ofHom (ContinuousMap.subtypeVal (⋃ j, U j)) ⁻¹' U i = Set.univ := by
  rw [← Set.preimage_iUnion]
  exact Set.eq_univ_of_forall fun x ↦ x.property

lemma toSmallSingularSubcomplex_comp_smallSingularSubcomplexToIUnion {A : Set X} {i : ι}
    (h : A ⊆ U i) (h' : A ⊆ ⋃ j, U j := h.trans (Set.subset_iUnion U i)) :
    toSmallSingularSubcomplex U h ≫ smallSingularSubcomplexToIUnion U =
      toSSet.map (ofHom (ContinuousMap.inclusion h')) := by
  rw [← cancel_mono (iUnionι U), Category.assoc, smallSingularSubcomplexToIUnion_comp,
    toSmallSingularSubcomplex_ι, ← Functor.map_comp]
  rfl

/-- The map of singular pairs from `X` relative to its singular simplices lying in a member of `U`
to `(X, ⋃ i, U i)`, given by `TopCat.smallSingularSubcomplexToIUnion` on subobjects and the
identity on the singular simplicial set of `X`. -/
def smallSingularSubcomplexPairToIUnion :
    (X.smallSingularSubcomplex U).pair ⟶
      TopPair.toSSetPair.obj (TopPair.ofSubset (⋃ i, U i)) :=
  SSetPair.homMk (smallSingularSubcomplexToIUnion U) (𝟙 _)
    ((smallSingularSubcomplexToIUnion_comp U).trans (Category.comp_id _).symm)

@[simp]
lemma smallSingularSubcomplexPairToIUnion_left :
    (smallSingularSubcomplexPairToIUnion U).left = smallSingularSubcomplexToIUnion U :=
  (rfl)

@[simp]
lemma smallSingularSubcomplexPairToIUnion_right :
    (smallSingularSubcomplexPairToIUnion U).right = 𝟙 (toSSet.obj X) :=
  (rfl)

lemma toSmallPair_comp_smallSingularSubcomplexPairToIUnion {A : Set X} {i : ι} (h : A ⊆ U i)
    (h' : A ⊆ ⋃ j, U j := h.trans (Set.subset_iUnion U i)) :
    toSmallPair U h ≫ smallSingularSubcomplexPairToIUnion U =
      TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h') := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, TopPair.toSSetPair_map_ofSubsetMap_id_left]
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexToIUnion U h h'
  · rw [MorphismProperty.Comma.comp_right, TopPair.toSSetPair_map_ofSubsetMap_id_right]
    exact Category.comp_id _

end IUnion

section Preadditive

variable [Preadditive C] (R : C)

omit [HasCoproducts.{w, v, u} C] in
private lemma homotopyEquiv_ofIso_hom {K L : ChainComplex C ℕ} (e : K ≅ L) :
    (_root_.HomotopyEquiv.ofIso e).hom = e.hom :=
  (rfl)

section IUnion

variable {ι : Type*} (U : ι → Set X)

/-- The chain map induced by the ambient component of
`TopCat.smallSingularSubcomplexPairToIUnion` is the identity. Not `@[simp]`:
`TopCat.smallSingularSubcomplexPairToIUnion_right` already rewrites its left-hand side. -/
lemma chainComplexMap_smallSingularSubcomplexPairToIUnion_right :
    SSet.chainComplexMap (smallSingularSubcomplexPairToIUnion U).right R = 𝟙 _ :=
  (congrArg (SSet.chainComplexMap · R) (smallSingularSubcomplexPairToIUnion_right U)).trans
    (CategoryTheory.Functor.map_id _ _)

/-- When each `U i` is open in `⋃ j, U j`, the chain map induced by
`TopCat.smallSingularSubcomplexToIUnion U` is a chain homotopy equivalence. -/
def smallSingularSubcomplexToIUnionChainHomotopyEquiv
    (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set ↥(⋃ j, U j))) :
    _root_.HomotopyEquiv ((X.smallSingularSubcomplex U : SSet).chainComplex R)
      ((toSSet.obj (of ↥(⋃ i, U i))).chainComplex R) :=
  let h := exists_iso_comp_smallSingularSubcomplexToIUnion U
  let e := h.choose
  have he : e.hom ≫ smallSingularSubcomplexToIUnion U = _ := h.choose_spec
  let eChain := ((SSet.chainComplexFunctor C).obj R).mapIso e.symm
  let hU' : ∀ i, IsOpen (ofHom (ContinuousMap.subtypeVal (⋃ j, U j)) ⁻¹' U i) := hU
  let E := (_root_.HomotopyEquiv.ofIso eChain).trans
    (TauCeti.smallSingularChainHomotopyEquiv R
      (fun i ↦ ofHom (ContinuousMap.subtypeVal (⋃ j, U j)) ⁻¹' U i)
      hU' (iUnion_preimage_subtypeVal U))
  have hhom : E.hom = SSet.chainComplexMap (smallSingularSubcomplexToIUnion U) R := by
    rw [_root_.HomotopyEquiv.trans_hom, homotopyEquiv_ofIso_hom, Functor.mapIso_hom, Iso.symm_hom,
      TauCeti.smallSingularChainHomotopyEquiv_hom, ← he,
      ← ((SSet.chainComplexFunctor C).obj R).map_comp]
    simp
  E.copy (_root_.Homotopy.ofEq hhom)

/-- The forward map of `TopCat.smallSingularSubcomplexToIUnionChainHomotopyEquiv` is the chain
map induced by `TopCat.smallSingularSubcomplexToIUnion`. -/
@[simp]
lemma smallSingularSubcomplexToIUnionChainHomotopyEquiv_hom
    (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set ↥(⋃ j, U j))) :
    (smallSingularSubcomplexToIUnionChainHomotopyEquiv R U hU).hom =
      SSet.chainComplexMap (smallSingularSubcomplexToIUnion U) R :=
  (rfl)

end IUnion

end Preadditive

section Abelian

variable [Abelian C] (R : C)

section IUnion

variable {ι : Type*} (U : ι → Set X)

/-- The quotient map from the singular chains of `X` to its chains relative to the singular
simplices lying in a member of `U`, followed by `TopCat.smallSingularSubcomplexPairToIUnion`, is
the quotient map to the relative chains of `(X, ⋃ i, U i)`. -/
@[reassoc]
lemma chainComplexπ_smallSingularSubcomplexPairToIUnion :
    (X.smallSingularSubcomplex U).pair.chainComplexπ R ≫
        SSetPair.chainComplexMap (smallSingularSubcomplexPairToIUnion U) R =
      (TopPair.ofSubset (⋃ i, U i)).singularChainComplexπ R := by
  rw [← SSetPair.chainComplexπ_naturality,
    chainComplexMap_smallSingularSubcomplexPairToIUnion_right]
  exact Category.id_comp _

/-- The singular simplices of `X` lying in a member of `U` compute the homology of `⋃ i, U i`, by
the small-chain theorem for the cover of `⋃ i, U i` by the traces of `U i`. -/
lemma quasiIso_chainComplexMap_smallSingularSubcomplexToIUnion
    (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set ↥(⋃ j, U j))) :
    QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexToIUnion U) R) :=
  (smallSingularSubcomplexToIUnionChainHomotopyEquiv R U hU).quasiIso_hom

/-- When each `U i` is open in `⋃ j, U j`, the quotient map from the relative chains of `X` modulo
its singular simplices lying in a member of `U` to the relative chains of `(X, ⋃ i, U i)` is a
quasi-isomorphism. -/
lemma quasiIso_chainComplexMap_smallSingularSubcomplexPairToIUnion
    (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set ↥(⋃ j, U j))) :
    QuasiIso (SSetPair.chainComplexMap (smallSingularSubcomplexPairToIUnion U) R) := by
  have : QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexPairToIUnion U).left R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplexToIUnion R U hU
  have : IsIso (SSet.chainComplexMap (smallSingularSubcomplexPairToIUnion U).right R) := by
    rw [chainComplexMap_smallSingularSubcomplexPairToIUnion_right]
    exact IsIso.id _
  have : QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexPairToIUnion U).right R) :=
    quasiIso_of_isIso _
  exact SSetPair.quasiIso_chainComplexMap _ R

/-- When each `U i` is open in `⋃ j, U j`, the comparison map from the relative homology of `X`
modulo its singular simplices lying in a member of `U` to `Hₙ(X, ⋃ i, U i; R)` is an
isomorphism. -/
lemma isIso_homologyMap_smallSingularSubcomplexPairToIUnion
    (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set ↥(⋃ j, U j))) (n : ℕ) :
    IsIso (SSetPair.homologyMap (smallSingularSubcomplexPairToIUnion U) R n) := by
  have := quasiIso_chainComplexMap_smallSingularSubcomplexPairToIUnion R U hU
  infer_instance

end IUnion

end Abelian

section Naturality

variable {ι κ : Type*} (U : ι → Set X) {Y : TopCat.{w}} (V : κ → Set Y) (f : X ⟶ Y)
  (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))

/-- The map of singular pairs from `X` relative to its singular simplices lying in a member of `U`
to `Y` relative to its singular simplices lying in a member of `V`, induced by a map `f` carrying
each `U i` into `V (r i)`. -/
def smallSingularSubcomplexPairMap :
    (X.smallSingularSubcomplex U).pair ⟶ (Y.smallSingularSubcomplex V).pair :=
  SSetPair.homMk (X.smallSingularSubcomplexMap U V f r hf) (toSSet.map f)
    (smallSingularSubcomplexMap_ι _ _ _ _ _)

@[simp]
lemma smallSingularSubcomplexPairMap_left :
    (smallSingularSubcomplexPairMap U V f r hf).left =
      X.smallSingularSubcomplexMap U V f r hf :=
  (rfl)

@[simp]
lemma smallSingularSubcomplexPairMap_right :
    (smallSingularSubcomplexPairMap U V f r hf).right = toSSet.map f :=
  (rfl)

lemma toSmallPair_comp_smallSingularSubcomplexPairMap {A : Set X} {A' : Set Y} {i : ι}
    (h : A ⊆ U i) (h' : A' ⊆ V (r i)) (hA : Set.MapsTo f A A') :
    toSmallPair U h ≫ smallSingularSubcomplexPairMap U V f r hf =
      TopPair.toSSetPair.map (TopPair.ofSubsetMap f hA) ≫ toSmallPair V h' := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      TopPair.toSSetPair_map_ofSubsetMap_left]
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ f r hf h h' hA
  · rw [MorphismProperty.Comma.comp_right, MorphismProperty.Comma.comp_right,
      TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The comparison maps `TopCat.smallSingularSubcomplexPairToIUnion` are natural under reindexed
covered maps `f : X ⟶ Y` carrying each `U i` into `V (r i)`. -/
@[reassoc]
lemma smallSingularSubcomplexPairToIUnion_comp_ofSubsetMap :
    smallSingularSubcomplexPairToIUnion U ≫
        TopPair.toSSetPair.map (TopPair.ofSubsetMap f (mapsTo_iUnion U r hf)) =
      smallSingularSubcomplexPairMap U V f r hf ≫ smallSingularSubcomplexPairToIUnion V := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      TopPair.toSSetPair_map_ofSubsetMap_left]
    exact smallSingularSubcomplexToIUnion_comp_restrict U V f r hf
  · rw [MorphismProperty.Comma.comp_right, MorphismProperty.Comma.comp_right,
      TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end Naturality

section Union

/-- The homeomorphism `↥(⋃ i, ![U, V] i) ≅ ↥(U ∪ V)` as an isomorphism in `TopCat`. -/
private def iUnionPairIso (U V : Set X) :
    of ↥(⋃ i, ![U, V] i) ≅ of ↥(U ∪ V) :=
  TopCat.isoOfHomeo (Homeomorph.setCongr (Set.iUnion_vecCons_pair U V))

private lemma isOpen_preimage_subtypeVal_iUnion_pair (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V)))
    (i : Fin 2) :
    IsOpen ((↑) ⁻¹' ![U, V] i : Set ↥(⋃ j, ![U, V] j)) := by
  have h : ((↑) ⁻¹' ![U, V] i : Set ↥(⋃ j, ![U, V] j)) =
      (iUnionPairIso U V).hom ⁻¹' ((↑) ⁻¹' ![U, V] i : Set ↥(U ∪ V)) :=
    rfl
  rw [h]
  refine IsOpen.preimage (iUnionPairIso U V).hom.hom.continuous ?_
  fin_cases i
  exacts [hU, hV]

/-- The singular simplices of `X` lying in `U` or in `V` are singular simplices of `U ∪ V`,
obtained from `TopCat.smallSingularSubcomplexToIUnion` for `![U, V]`. -/
def smallSingularSubcomplexToUnion (U V : Set X) :
    (X.smallSingularSubcomplex ![U, V] : SSet) ⟶ toSSet.obj (of ↥(U ∪ V)) :=
  smallSingularSubcomplexToIUnion ![U, V] ≫ toSSet.map (iUnionPairIso U V).hom

/-- Followed by the inclusion of `U ∪ V` into `X`, `TopCat.smallSingularSubcomplexToUnion`
is the inclusion of the singular simplices of `X` lying in `U` or in `V`. -/
@[reassoc]
lemma smallSingularSubcomplexToUnion_comp (U V : Set X) :
    smallSingularSubcomplexToUnion U V ≫ toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ V))) =
      (X.smallSingularSubcomplex ![U, V]).ι := by
  rw [smallSingularSubcomplexToUnion, Category.assoc, ← Functor.map_comp]
  exact smallSingularSubcomplexToIUnion_comp ![U, V]

/-- The comparison maps `TopCat.smallSingularSubcomplexToUnion` are natural in maps carrying `U`
into `U'` and `V` into `V'`. -/
@[reassoc]
lemma smallSingularSubcomplexToUnion_comp_restrict (U V : Set X) {Y : TopCat.{w}} (f : X ⟶ Y)
    {U' V' : Set Y} (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    smallSingularSubcomplexToUnion U V ≫
        toSSet.map (ofHom ⟨(hfU.union_union hfV).restrict,
          f.hom.continuous.restrict (hfU.union_union hfV)⟩) =
      X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id (Fin.forall_fin_two.2 ⟨hfU, hfV⟩) ≫
        smallSingularSubcomplexToUnion U' V' := by
  rw [smallSingularSubcomplexToUnion, smallSingularSubcomplexToUnion, Category.assoc,
    ← Functor.map_comp]
  have h : (iUnionPairIso U V).hom ≫
      ofHom ⟨(hfU.union_union hfV).restrict, f.hom.continuous.restrict (hfU.union_union hfV)⟩ =
      ofHom ⟨(mapsTo_iUnion ![U, V] id (Fin.forall_fin_two.2 ⟨hfU, hfV⟩)).restrict,
        f.hom.continuous.restrict _⟩ ≫ (iUnionPairIso U' V').hom :=
    TopCat.ext fun _ ↦ rfl
  rw [h, Functor.map_comp, smallSingularSubcomplexToIUnion_comp_restrict_assoc]

lemma toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion (U V : Set X) {A : Set X}
    {i : Fin 2} (h : A ⊆ ![U, V] i) (h' : A ⊆ U ∪ V) :
    toSmallSingularSubcomplex ![U, V] h ≫ smallSingularSubcomplexToUnion U V =
      toSSet.map (ofHom (ContinuousMap.inclusion h')) := by
  rw [smallSingularSubcomplexToUnion, ← Category.assoc,
    toSmallSingularSubcomplex_comp_smallSingularSubcomplexToIUnion ![U, V] h, ← Functor.map_comp]
  exact congrArg toSSet.map (TopCat.ext fun _ ↦ rfl)

/-- The map of singular pairs from `X` relative to its singular simplices lying in `U` or in `V`
to `(X, U ∪ V)`, given by `TopCat.smallSingularSubcomplexToUnion` on subobjects and the
identity on the singular simplicial set of `X`. -/
def smallSingularSubcomplexPairToUnion (U V : Set X) :
    (X.smallSingularSubcomplex ![U, V]).pair ⟶
      TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)) :=
  SSetPair.homMk (smallSingularSubcomplexToUnion U V) (𝟙 _)
    ((smallSingularSubcomplexToUnion_comp U V).trans (Category.comp_id _).symm)

@[simp]
lemma smallSingularSubcomplexPairToUnion_left (U V : Set X) :
    (smallSingularSubcomplexPairToUnion U V).left = smallSingularSubcomplexToUnion U V :=
  (rfl)

@[simp]
lemma smallSingularSubcomplexPairToUnion_right (U V : Set X) :
    (smallSingularSubcomplexPairToUnion U V).right = 𝟙 (toSSet.obj X) :=
  (rfl)

lemma toSmallPair_comp_smallSingularSubcomplexPairToUnion (U V : Set X) {A : Set X} {i : Fin 2}
    (h : A ⊆ ![U, V] i) (h' : A ⊆ U ∪ V) :
    toSmallPair ![U, V] h ≫ smallSingularSubcomplexPairToUnion U V =
      TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h') := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, smallSingularSubcomplexPairToUnion_left,
      toSmallPair_left, TopPair.toSSetPair_map_ofSubsetMap_id_left]
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion U V h h'
  · rw [MorphismProperty.Comma.comp_right, smallSingularSubcomplexPairToUnion_right,
      toSmallPair_right, TopPair.toSSetPair_map_ofSubsetMap_id_right]
    exact Category.comp_id _

section Preadditive

variable [Preadditive C] (R : C)

/-- The chain map induced by the ambient component of `TopCat.smallSingularSubcomplexPairToUnion`
is the identity. Not `@[simp]`: `TopCat.smallSingularSubcomplexPairToUnion_right` already
rewrites its left-hand side. -/
lemma chainComplexMap_smallSingularSubcomplexPairToUnion_right (U V : Set X) :
    SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).right R = 𝟙 _ :=
  (congrArg (SSet.chainComplexMap · R) (smallSingularSubcomplexPairToUnion_right U V)).trans
    (CategoryTheory.Functor.map_id _ _)

/-- When `U` and `V` are open in `U ∪ V`, the chain map induced by
`TopCat.smallSingularSubcomplexToUnion U V` is a chain homotopy equivalence, derived from
`TopCat.smallSingularSubcomplexToIUnionChainHomotopyEquiv`. -/
def smallSingularSubcomplexToUnionChainHomotopyEquiv (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    _root_.HomotopyEquiv ((X.smallSingularSubcomplex ![U, V] : SSet).chainComplex R)
      ((toSSet.obj (of ↥(U ∪ V))).chainComplex R) :=
  let eIso : ((toSSet.obj (of ↥(⋃ i, ![U, V] i))).chainComplex R) ≅
      ((toSSet.obj (of ↥(U ∪ V))).chainComplex R) :=
    ((SSet.chainComplexFunctor C).obj R).mapIso (toSSet.mapIso (iUnionPairIso U V))
  let E := (smallSingularSubcomplexToIUnionChainHomotopyEquiv R ![U, V]
    (isOpen_preimage_subtypeVal_iUnion_pair U V hU hV)).trans (_root_.HomotopyEquiv.ofIso eIso)
  have hhom : E.hom = SSet.chainComplexMap (smallSingularSubcomplexToUnion U V) R := by
    rw [_root_.HomotopyEquiv.trans_hom, smallSingularSubcomplexToIUnionChainHomotopyEquiv_hom,
      homotopyEquiv_ofIso_hom, Functor.mapIso_hom, Functor.mapIso_hom,
      ← ((SSet.chainComplexFunctor C).obj R).map_comp]
    rfl
  E.copy (_root_.Homotopy.ofEq hhom)

/-- The forward map of `TopCat.smallSingularSubcomplexToUnionChainHomotopyEquiv` is the chain map
induced by `TopCat.smallSingularSubcomplexToUnion`. -/
@[simp]
lemma smallSingularSubcomplexToUnionChainHomotopyEquiv_hom (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    (smallSingularSubcomplexToUnionChainHomotopyEquiv R U V hU hV).hom =
      SSet.chainComplexMap (smallSingularSubcomplexToUnion U V) R :=
  (rfl)

end Preadditive

section Abelian

variable [Abelian C] (R : C)

/-- The quotient map from the singular chains of `X` to its chains relative to the singular
simplices lying in `U` or in `V`, followed by `TopCat.smallSingularSubcomplexPairToUnion`, is the
quotient map to the relative chains of `(X, U ∪ V)`. -/
@[reassoc]
lemma chainComplexπ_smallSingularSubcomplexPairToUnion (U V : Set X) :
    (X.smallSingularSubcomplex ![U, V]).pair.chainComplexπ R ≫
        SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) R =
      (TopPair.ofSubset (U ∪ V)).singularChainComplexπ R := by
  rw [← SSetPair.chainComplexπ_naturality, chainComplexMap_smallSingularSubcomplexPairToUnion_right]
  exact Category.id_comp _

/-- The singular simplices of `X` lying in `U` or in `V` compute the homology of `U ∪ V`, by
`TopCat.smallSingularSubcomplexToIUnionChainHomotopyEquiv` for `![U, V]`. -/
lemma quasiIso_chainComplexMap_smallSingularSubcomplexToUnion (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexToUnion U V) R) :=
  (smallSingularSubcomplexToUnionChainHomotopyEquiv R U V hU hV).quasiIso_hom

/-- For `U` and `V` open in `U ∪ V`, the quotient map from the relative chains of `X` modulo its
singular simplices lying in `U` or in `V` to the relative chains of `(X, U ∪ V)` is a
quasi-isomorphism. -/
lemma quasiIso_chainComplexMap_smallSingularSubcomplexPairToUnion (U V : Set X)
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
lemma isIso_homologyMap_smallSingularSubcomplexPairToUnion (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (n : ℕ) :
    IsIso (SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) R n) := by
  have := quasiIso_chainComplexMap_smallSingularSubcomplexPairToUnion R U V hU hV
  infer_instance

end Abelian

/-- The comparison maps `TopCat.smallSingularSubcomplexPairToUnion` are natural in maps carrying
`U` into `U'` and `V` into `V'`. -/
@[reassoc]
lemma smallSingularSubcomplexPairToUnion_comp_ofSubsetMap {U V : Set X} {Y : TopCat.{w}}
    {U' V' : Set Y} (f : X ⟶ Y) (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    smallSingularSubcomplexPairToUnion U V ≫
        TopPair.toSSetPair.map (TopPair.ofSubsetMap f (hfU.union_union hfV)) =
      smallSingularSubcomplexPairMap ![U, V] ![U', V'] f id (Fin.forall_fin_two.2 ⟨hfU, hfV⟩) ≫
        smallSingularSubcomplexPairToUnion U' V' := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      smallSingularSubcomplexPairToUnion_left, smallSingularSubcomplexPairToUnion_left,
      smallSingularSubcomplexPairMap_left, TopPair.toSSetPair_map_ofSubsetMap_left]
    exact smallSingularSubcomplexToUnion_comp_restrict U V f hfU hfV
  · rw [MorphismProperty.Comma.comp_right, MorphismProperty.Comma.comp_right,
      smallSingularSubcomplexPairToUnion_right, smallSingularSubcomplexPairToUnion_right,
      smallSingularSubcomplexPairMap_right, TopPair.toSSetPair_map_right,
      TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

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
