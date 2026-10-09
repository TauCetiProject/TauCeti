/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# The Mayer–Vietoris sequence in singular cohomology

Let `U` and `V` be open subsets of a topological space `X` with `U ∪ V = X`, let `R` and `M` be
objects of a `k`-linear abelian category with coproducts, and write `Hⁿ(-)` for singular
cohomology `Hⁿ(-; R, M)`, the cohomology of `Hom(C(-; R), M)`. This file constructs the
Mayer–Vietoris long exact sequence
`⋯ ⟶ Hⁿ(X) ⟶ Hⁿ(U) ⊞ Hⁿ(V) ⟶ Hⁿ(U ∩ V) ⟶ Hⁿ⁺¹(X) ⟶ ⋯`,
whose first map is `(j_U^*, j_V^*)` and whose second map is `i_U^* - i_V^*`, the `i` and `j`
being the inclusions. These are the maps dual to the maps `j_U + j_V` and `(i_U, -i_V)` of the
Mayer–Vietoris sequence in singular homology. The connecting morphism is natural in maps of
covered spaces.

The construction dualizes the one in homology. For a pushout square of simplicial sets whose top
map is a monomorphism, the Mayer–Vietoris short exact sequence of chain complexes is split in each
degree, so applying `Hom(-, M)` keeps it short exact
(`SSet.shortExact_mayerVietorisCochainShortComplex`). For the singular simplicial sets of
`U ∩ V`, `U`, `V` and the subcomplex of singular simplices of `X` lying in `U` or in `V`, the
small-chain theorem identifies the cohomology of that subcomplex with the singular cohomology of
`X` (`TauCeti.smallSingularCohomologyIso`).

## Main definitions and results

* `SSet.cochainComplexMap`: the map of cochain complexes `Hom(C(Y; R), M) ⟶ Hom(C(X; R), M)`
  induced by a map of simplicial sets `X ⟶ Y`.
* `SSet.shortExact_mayerVietorisCochainShortComplex`: the cochain Mayer–Vietoris sequence of a
  pushout square of simplicial sets is short exact.
* `TauCeti.smallSingularCohomologyIso`: restricting cochains to the chains subordinate to an open
  cover is an isomorphism on cohomology.
* `TopCat.singularCohomologyMayerVietorisToBiprod` and
  `TopCat.singularCohomologyMayerVietorisFromBiprod`: the maps `Hⁿ(X) ⟶ Hⁿ(U) ⊞ Hⁿ(V)` and
  `Hⁿ(U) ⊞ Hⁿ(V) ⟶ Hⁿ(U ∩ V)`.
* `TopCat.singularCohomologyMayerVietorisδ`: the connecting morphism `Hⁿ(U ∩ V) ⟶ Hᵐ(X)`,
  `n + 1 = m`, characterized by `TopCat.singularCohomologyMayerVietorisδ_comp_homologyMap`.
* `TopCat.singularCohomologyMayerVietoris_exact₁`, `TopCat.singularCohomologyMayerVietoris_exact₂`,
  `TopCat.singularCohomologyMayerVietoris_exact₃`: exactness at `Hᵐ(X)`, at `Hⁿ(U) ⊞ Hⁿ(V)` and at
  `Hⁿ(U ∩ V)`.
* `TopCat.mono_singularCohomologyMayerVietorisToBiprod_zero`: injectivity at the degree-zero
  endpoint.
* `TopCat.singularCohomologyMayerVietorisδ_naturality`: naturality of the connecting morphism.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, the Mayer–Vietoris sequences in cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti.ChainComplex

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

variable {R k M} in
/-- The map of cochain complexes `Hom(C(Y; R), M) ⟶ Hom(C(X; R), M)` induced by a map
`f : X ⟶ Y` of simplicial sets: precomposition with the chain map induced by `f`. -/
def cochainComplexMap {X Y : SSet.{w}} (f : X ⟶ Y) :
    (Y.chainComplex R).linearYonedaObj k M ⟶ (X.chainComplex R).linearYonedaObj k M :=
  (linearYonedaFunctor k M).map (chainComplexMap f R).op

variable {R k M} in
/-- The degree-`n` component of the cochain map induced by `f` acts by precomposition with the
degree-`n` component of the induced chain map. -/
@[simp]
lemma cochainComplexMap_f_apply {X Y : SSet.{w}} (f : X ⟶ Y) (n : ℕ)
    (g : ((Y.chainComplex R).linearYonedaObj k M).X n) :
    (cochainComplexMap (R := R) (k := k) (M := M) f).f n g = (chainComplexMap f R).f n ≫ g :=
  (rfl)

variable {R k M} in
@[simp]
lemma cochainComplexMap_id (X : SSet.{w}) :
    cochainComplexMap (R := R) (k := k) (M := M) (𝟙 X) = 𝟙 _ := by
  simp [cochainComplexMap]

variable {R k M} in
@[reassoc]
lemma cochainComplexMap_comp {X Y Z : SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cochainComplexMap (R := R) (k := k) (M := M) (f ≫ g) =
      cochainComplexMap g ≫ cochainComplexMap f := by
  simp [cochainComplexMap]

variable {R k M} in
/-- The cochain map induced by a continuous map is the one induced by its singular simplicial
map. -/
@[simp]
lemma cochainComplexMap_toSSet_map {X Y : TopCat.{w}} (f : X ⟶ Y) :
    cochainComplexMap (R := R) (k := k) (M := M) (TopCat.toSSet.map f) =
      TopCat.singularCochainComplexMap f := (rfl)

variable {X₁ X₂ X₃ X₄ : SSet.{w}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/- The cochain Mayer–Vietoris sequence with its terms written as `(linearYonedaFunctor k M).obj`,
the form in which `Hom(-, M)` is applied to the chain Mayer–Vietoris sequence. It is
definitionally `SSet.mayerVietorisCochainShortComplex`, whose terms are written as the singular
cochain complexes. -/
private def cochainShortComplex (sq : CommSq t l r b) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk
    (biprod.lift ((linearYonedaFunctor k M).map (chainComplexMap r R).op)
      ((linearYonedaFunctor k M).map (chainComplexMap b R).op))
    (biprod.desc ((linearYonedaFunctor k M).map (chainComplexMap t R).op)
      (-(linearYonedaFunctor k M).map (chainComplexMap l R).op))
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← Functor.map_comp, ← Functor.map_comp,
        ← op_comp, ← op_comp, ← Functor.map_comp, ← Functor.map_comp, sq.w, add_neg_cancel])

private lemma shortExact_cochainShortComplex (sq : IsPushout t l r b) [Mono t] :
    (cochainShortComplex R k M sq.toCommSq).ShortExact := by
  let S : ShortComplex (ChainComplex C ℕ) :=
    ShortComplex.mk (biprod.lift (chainComplexMap t R) (-chainComplexMap l R))
      (biprod.desc (chainComplexMap r R) (chainComplexMap b R))
      (by rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
        sq.w, add_neg_cancel])
  have hS : S.ShortExact := shortExact_mayerVietorisShortComplex R sq
  -- `SSetPair.of t` has `t` as its structure map, so this is the split monomorphism instance for
  -- the chains of a pair of simplicial sets.
  have ht (i : ℕ) : IsSplitMono ((chainComplexMap t R).f i) :=
    inferInstanceAs (IsSplitMono ((chainComplexMap (SSetPair.of t).hom R).f i))
  have (i : ℕ) : IsSplitMono (S.f.f i) :=
    IsSplitMono.mk'
      { retraction := (biprod.fst : X₂.chainComplex R ⊞ X₃.chainComplex R ⟶ _).f i ≫
          @retraction _ _ _ _ ((chainComplexMap t R).f i) (ht i)
        id := by rw [← Category.assoc, ← HomologicalComplex.comp_f, biprod.lift_fst,
          IsSplitMono.id] }
  have he : ((linearYonedaFunctor k M).mapIso (biprod.opIso _ _) ≪≫
      (linearYonedaFunctor k M).mapBiprod _ _).inv =
        biprod.desc ((linearYonedaFunctor k M).map
          (biprod.fst : X₂.chainComplex R ⊞ X₃.chainComplex R ⟶ _).op)
          ((linearYonedaFunctor k M).map biprod.snd.op) := by
    rw [Iso.trans_inv, Functor.mapIso_inv, Functor.mapBiprod_inv]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, ← Functor.map_comp, biprod.inl_opIso_inv, biprod.inl_desc]
    · rw [biprod.inr_desc_assoc, ← Functor.map_comp, biprod.inr_opIso_inv, biprod.inr_desc]
  -- `Hom(-, M)` keeps the degreewise split chain sequence short exact; it remains to identify
  -- `Hom(C(X₂) ⊞ C(X₃), M)` with `Hom(C(X₂), M) ⊞ Hom(C(X₃), M)` compatibly with the maps.
  refine ShortComplex.shortExact_of_iso (Iso.symm ?_) (shortExact_map_linearYonedaFunctor k M hS)
  refine ShortComplex.isoMk (Iso.refl ((linearYonedaFunctor k M).obj (op (X₄.chainComplex R))))
    (((linearYonedaFunctor k M).mapIso (biprod.opIso _ _) ≪≫
      (linearYonedaFunctor k M).mapBiprod _ _).symm)
    (Iso.refl ((linearYonedaFunctor k M).obj (op (X₁.chainComplex R)))) ?_ ?_
  · rw [Iso.symm_hom, he]
    dsimp [S, cochainShortComplex, ShortComplex.op, -linearYonedaFunctor_obj]
    simp [biprod.desc_eq, ← Functor.map_comp, ← op_comp, -linearYonedaFunctor_obj]
  · rw [Iso.symm_hom, he]
    dsimp [S, cochainShortComplex, ShortComplex.op, -linearYonedaFunctor_obj]
    apply biprod.hom_ext' <;>
      simp [← Functor.map_comp, ← op_comp, -linearYonedaFunctor_obj]

/-- The cochain Mayer–Vietoris sequence `Hom(C(X₄), M) ⟶ Hom(C(X₂), M) ⊞ Hom(C(X₃), M) ⟶
Hom(C(X₁), M)` of a commutative square of simplicial sets, with first map `(r^*, b^*)` and second
map `t^* - l^*`. It is the image under `Hom(-, M)` of the chain Mayer–Vietoris sequence, once
`Hom(C(X₂) ⊞ C(X₃), M)` is identified with `Hom(C(X₂), M) ⊞ Hom(C(X₃), M)`. -/
abbrev mayerVietorisCochainShortComplex (sq : CommSq t l r b) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk
    (biprod.lift (cochainComplexMap (R := R) (k := k) (M := M) r) (cochainComplexMap b))
    (biprod.desc (cochainComplexMap t) (-cochainComplexMap l))
    (by simp [← cochainComplexMap_comp, sq.w])

/-- **The cochain Mayer–Vietoris short exact sequence.** For a pushout square of simplicial sets
whose top map is a monomorphism, the cochain Mayer–Vietoris sequence is short exact. -/
lemma shortExact_mayerVietorisCochainShortComplex (sq : IsPushout t l r b) [Mono t] :
    (mayerVietorisCochainShortComplex R k M sq.toCommSq).ShortExact :=
  -- The two short complexes agree definitionally; see `cochainShortComplex`.
  shortExact_cochainShortComplex R k M sq

end SSet

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
  (hcov : ⋃ i, U i = Set.univ)

/-- The isomorphism on singular cohomology induced by restricting cochains to the chains
subordinate to an open cover. It is dual to `TauCeti.smallSingularHomologyIso`. -/
def smallSingularCohomologyIso (n : ℕ) :
    X.singularCohomology R k M n ≅
      (((X.smallSingularSubcomplex U : SSet).chainComplex R).linearYonedaObj k M).homology n :=
  ((smallSingularChainHomotopyEquiv R U hU hcov).linearYonedaFunctorMap k M).toHomologyIso n

/-- The small-chain cohomology isomorphism is the map induced by the inclusion of the singular
simplices subordinate to the cover. -/
@[simp]
lemma smallSingularCohomologyIso_hom (n : ℕ) :
    (smallSingularCohomologyIso R k M U hU hcov n).hom =
      HomologicalComplex.homologyMap (SSet.cochainComplexMap (X.smallSingularSubcomplex U).ι)
        n := by
  simp [smallSingularCohomologyIso, HomotopyEquiv.toHomologyIso, SSet.cochainComplexMap]

end TauCeti

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {X : TopCat.{w}}

section Maps

variable (U V : Set X)

/-- The first map `Hⁿ(X) ⟶ Hⁿ(U) ⊞ Hⁿ(V)` of the Mayer–Vietoris sequence in singular cohomology,
with components the restrictions `j_U^*` and `j_V^*` along the inclusions. -/
def singularCohomologyMayerVietorisToBiprod (n : ℕ) :
    X.singularCohomology R k M n ⟶
      (of U).singularCohomology R k M n ⊞ (of V).singularCohomology R k M n :=
  biprod.lift (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) n)
    (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) n)

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisToBiprod_fst (n : ℕ) :
    singularCohomologyMayerVietorisToBiprod R k M U V n ≫ biprod.fst =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisToBiprod_snd (n : ℕ) :
    singularCohomologyMayerVietorisToBiprod R k M U V n ≫ biprod.snd =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) n :=
  biprod.lift_snd _ _

/-- The second map `Hⁿ(U) ⊞ Hⁿ(V) ⟶ Hⁿ(U ∩ V)` of the Mayer–Vietoris sequence in singular
cohomology, the difference `i_U^* - i_V^*` of the restrictions along the inclusions of `U ∩ V`.
It is dual to the map `(i_U, -i_V)` of the homology sequence. -/
def singularCohomologyMayerVietorisFromBiprod (n : ℕ) :
    (of U).singularCohomology R k M n ⊞ (of V).singularCohomology R k M n ⟶
      (of ↥(U ∩ V)).singularCohomology R k M n :=
  biprod.desc
    (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_left)) n)
    (-TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_right)) n)

@[reassoc (attr := simp)]
lemma inl_singularCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ singularCohomologyMayerVietorisFromBiprod R k M U V n =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_left)) n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_singularCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ singularCohomologyMayerVietorisFromBiprod R k M U V n =
      -TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_right)) n :=
  biprod.inr_desc _ _

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    singularCohomologyMayerVietorisToBiprod R k M U V n ≫
      singularCohomologyMayerVietorisFromBiprod R k M U V n = 0 := by
  simp [singularCohomologyMayerVietorisToBiprod, singularCohomologyMayerVietorisFromBiprod,
    ← singularCohomologyMap_comp, (commSq_ofHom_inter U V).w]

end Maps

/-! ### The long exact sequence of an open cover by two sets -/

section Sequence

variable {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- The cochain Mayer–Vietoris sequence of the pushout square of singular simplicial sets of
`U ∩ V`, `U`, `V` and the simplices of `X` lying in `U` or in `V`. -/
private abbrev cochainSequence (U V : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  SSet.mayerVietorisCochainShortComplex R k M
    (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq

private lemma shortExact_cochainSequence (U V : Set X) :
    (cochainSequence R k M U V).ShortExact :=
  SSet.shortExact_mayerVietorisCochainShortComplex R k M
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)

/-- The restriction of cochains to the simplices lying in `U` or in `V`, on cohomology. -/
private abbrev smallIso (n : ℕ) :
    X.singularCohomology R k M n ≅ (cochainSequence R k M U V).X₁.homology n :=
  TauCeti.smallSingularCohomologyIso R k M ![U, V] (by simp [Fin.forall_fin_two, hU, hV])
    (by rw [← hUV]; ext; simp [Fin.exists_fin_two]) n

private lemma smallIso_hom (n : ℕ) :
    (smallIso R k M hU hV hUV n).hom =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (X.smallSingularSubcomplex ![U, V]).ι) n :=
  TauCeti.smallSingularCohomologyIso_hom ..

/-- Cohomology commutes with the biproduct in the middle of the cochain sequence. -/
private abbrev homologyBiprodIso (n : ℕ) :
    (cochainSequence R k M U V).X₂.homology n ≅
      (of U).singularCohomology R k M n ⊞ (of V).singularCohomology R k M n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapBiprod _ _

private lemma homologyMap_f_comp_homologyBiprodIso_hom (n : ℕ) :
    HomologicalComplex.homologyMap (cochainSequence R k M U V).f n ≫
        (homologyBiprodIso R k M n).hom =
      biprod.lift
        (HomologicalComplex.homologyMap (SSet.cochainComplexMap
          (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset)) n)
        (HomologicalComplex.homologyMap (SSet.cochainComplexMap
          (toSmallSingularSubcomplex ![U, V]
            ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset)) n) :=
  -- The homology functor applied to a cochain map is its map on cohomology by definition.
  biprod.map_lift_mapBiprod (HomologicalComplex.homologyFunctor _ _ n) _ _ _ _

private lemma smallIso_hom_comp_homologyMap_f (n : ℕ) :
    (smallIso R k M hU hV hUV n).hom ≫
        HomologicalComplex.homologyMap (cochainSequence R k M U V).f n ≫
          (homologyBiprodIso R k M n).hom =
      singularCohomologyMayerVietorisToBiprod R k M U V n := by
  rw [homologyMap_f_comp_homologyBiprodIso_hom]
  apply biprod.hom_ext <;>
    simp [← HomologicalComplex.homologyMap_comp, ← SSet.cochainComplexMap_comp,
      toSmallSingularSubcomplex_ι]

@[reassoc]
private lemma homologyBiprodIso_hom_comp_fromBiprod (n : ℕ) :
    (homologyBiprodIso R k M (U := U) (V := V) n).hom ≫
        singularCohomologyMayerVietorisFromBiprod R k M U V n =
      HomologicalComplex.homologyMap (cochainSequence R k M U V).g n := by
  have h := biprod.mapBiprod_hom_desc (HomologicalComplex.homologyFunctor (ModuleCat.{v} k) _ n)
    ((of U).singularCochainComplex R k M) ((of V).singularCochainComplex R k M)
    (singularCochainComplexMap (ofHom (ContinuousMap.inclusion Set.inter_subset_left)))
    (-singularCochainComplexMap (ofHom (ContinuousMap.inclusion Set.inter_subset_right)))
  rw [Functor.map_neg] at h
  -- `h` is the claim, up to the definitional identifications of the homology functor applied to a
  -- cochain map with its map on cohomology, and of `singularCochainComplexMap` of an inclusion
  -- with `SSet.cochainComplexMap` of the induced map of singular simplicial sets.
  exact h

/-- The Mayer–Vietoris connecting morphism `Hⁿ(U ∩ V) ⟶ Hᵐ(X)` in singular cohomology, where
`n + 1 = m`, for an open cover of `X` by `U` and `V`. It is the connecting morphism of the cochain
Mayer–Vietoris sequence of the singular simplices lying in `U`, in `V` and in `U` or `V`, followed
by the inverse of the restriction isomorphism from the cohomology of `X`. -/
def singularCohomologyMayerVietorisδ (n m : ℕ) (h : n + 1 = m := by lia) :
    (of ↥(U ∩ V)).singularCohomology R k M n ⟶ X.singularCohomology R k M m :=
  (shortExact_cochainSequence R k M U V).δ n m (by simpa) ≫ (smallIso R k M hU hV hUV m).inv

/-- Followed by restriction to the singular simplices lying in `U` or in `V`, the Mayer–Vietoris
connecting morphism is the connecting morphism of the cochain Mayer–Vietoris sequence of those
simplices. Since that restriction is an isomorphism on cohomology, this characterizes it. -/
@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisδ_comp_homologyMap (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyMayerVietorisδ R k M hU hV hUV n m h ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (X.smallSingularSubcomplex ![U, V]).ι) m =
      (SSet.shortExact_mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V)).δ n m (by simpa) := by
  rw [singularCohomologyMayerVietorisδ, Category.assoc,
    ← smallIso_hom R k M hU hV hUV, Iso.inv_hom_id, Category.comp_id]

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisδ_toBiprod (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyMayerVietorisδ R k M hU hV hUV n m h ≫
      singularCohomologyMayerVietorisToBiprod R k M U V m = 0 := by
  rw [← smallIso_hom_comp_homologyMap_f R k M hU hV hUV, singularCohomologyMayerVietorisδ,
    Category.assoc, Iso.inv_hom_id_assoc,
    (shortExact_cochainSequence R k M U V).δ_comp_assoc, zero_comp]

@[reassoc (attr := simp)]
lemma singularCohomologyMayerVietorisFromBiprod_δ (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyMayerVietorisFromBiprod R k M U V n ≫
      singularCohomologyMayerVietorisδ R k M hU hV hUV n m h = 0 := by
  rw [← cancel_epi (homologyBiprodIso R k M n).hom, comp_zero,
    homologyBiprodIso_hom_comp_fromBiprod_assoc, singularCohomologyMayerVietorisδ,
    (shortExact_cochainSequence R k M U V).comp_δ_assoc, zero_comp]

/-- **Exactness of the Mayer–Vietoris sequence at `Hᵐ(X)`.** -/
lemma singularCohomologyMayerVietoris_exact₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (singularCohomologyMayerVietorisδ_toBiprod R k M hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_cochainSequence R k M U V).homology_exact₁ n m (by simpa))
  refine ShortComplex.isoMk (Iso.refl _) (smallIso R k M hU hV hUV m).symm
    (homologyBiprodIso R k M m) ?_ ?_
  · simp [singularCohomologyMayerVietorisδ]
  · dsimp only
    rw [Iso.symm_hom, ← smallIso_hom_comp_homologyMap_f R k M hU hV hUV, Iso.inv_hom_id_assoc]

include hU hV hUV in
/-- **Exactness of the Mayer–Vietoris sequence at `Hⁿ(U) ⊞ Hⁿ(V)`.** -/
lemma singularCohomologyMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _
      (singularCohomologyMayerVietorisToBiprod_fromBiprod R k M U V n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_cochainSequence R k M U V).homology_exact₂ n)
  refine ShortComplex.isoMk (smallIso R k M hU hV hUV n).symm (homologyBiprodIso R k M n)
    (Iso.refl _) ?_ ?_
  · dsimp only
    rw [Iso.symm_hom, ← smallIso_hom_comp_homologyMap_f R k M hU hV hUV, Iso.inv_hom_id_assoc]
  · dsimp only
    rw [Iso.refl_hom, Category.comp_id, homologyBiprodIso_hom_comp_fromBiprod]

/-- **Exactness of the Mayer–Vietoris sequence at `Hⁿ(U ∩ V)`.** -/
lemma singularCohomologyMayerVietoris_exact₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (singularCohomologyMayerVietorisFromBiprod_δ R k M hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_cochainSequence R k M U V).homology_exact₃ n m (by simpa))
  refine ShortComplex.isoMk (homologyBiprodIso R k M n) (Iso.refl _)
    (smallIso R k M hU hV hUV m).symm ?_ ?_
  · dsimp only
    rw [Iso.refl_hom, Category.comp_id, homologyBiprodIso_hom_comp_fromBiprod]
  · simp [singularCohomologyMayerVietorisδ]

include hU hV hUV in
/-- The map `H⁰(X) ⟶ H⁰(U) ⊞ H⁰(V)` at the start of the Mayer–Vietoris sequence is a
monomorphism. -/
lemma mono_singularCohomologyMayerVietorisToBiprod_zero :
    Mono (singularCohomologyMayerVietorisToBiprod R k M U V 0) := by
  have := (shortExact_cochainSequence R k M U V).mono_f
  have : Mono (HomologicalComplex.homologyMap (cochainSequence R k M U V).f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 fun i h ↦ by
      rw [ComplexShape.up_Rel] at h
      omega
  rw [← smallIso_hom_comp_homologyMap_f R k M hU hV hUV]
  infer_instance

variable {Y : TopCat.{w}} {U' V' : Set Y} (hU' : IsOpen U') (hV' : IsOpen V')
  (hUV' : U' ∪ V' = Set.univ) (f : X ⟶ Y) (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- The morphism of cochain Mayer–Vietoris sequences induced by a map of covered spaces. -/
private def cochainSequenceMap :
    cochainSequence R k M U' V' ⟶ cochainSequence R k M U V where
  τ₁ := SSet.cochainComplexMap (X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id
    (by simp [Fin.forall_fin_two, hfU, hfV]))
  τ₂ := biprod.map
    (singularCochainComplexMap (ofHom ⟨hfU.restrict, f.hom.continuous.restrict hfU⟩))
    (singularCochainComplexMap (ofHom ⟨hfV.restrict, f.hom.continuous.restrict hfV⟩))
  τ₃ := singularCochainComplexMap (ofHom ⟨(hfU.inter_inter hfV).restrict,
    f.hom.continuous.restrict (hfU.inter_inter hfV)⟩)
  -- Each square of cochain maps comes from a square of maps of singular simplicial sets. Those
  -- through the small subcomplexes are checked after the inclusion into the singular simplicial
  -- set of `Y`; all of them then commute because the underlying squares of continuous maps do,
  -- pointwise by definition.
  comm₁₂ := by
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, biprod.map_fst, biprod.map_snd,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, ← SSet.cochainComplexMap_comp,
        ← SSet.cochainComplexMap_toSSet_map] <;>
      congr 1 <;>
      rw [← cancel_mono (Y.smallSingularSubcomplex ![U', V']).ι, Category.assoc, Category.assoc,
        smallSingularSubcomplexMap_ι, toSmallSingularSubcomplex_ι_assoc,
        toSmallSingularSubcomplex_ι, ← Functor.map_comp, ← Functor.map_comp] <;>
      rfl
  comm₂₃ := by
    apply biprod.hom_ext' <;>
      simp [← singularCochainComplexMap_comp] <;>
      rfl

private lemma cochainSequenceMap_τ₃ :
    (cochainSequenceMap R k M f hfU hfV).τ₃ = singularCochainComplexMap (ofHom
      ⟨(hfU.inter_inter hfV).restrict, f.hom.continuous.restrict (hfU.inter_inter hfV)⟩) := rfl

/-- **Naturality of the Mayer–Vietoris connecting morphism.** A map `f : X ⟶ Y` carrying `U` into
`U'` and `V` into `V'` commutes with the connecting morphisms, where `U ∩ V ⟶ U' ∩ V'` is the
restriction of `f`. -/
@[reassoc]
lemma singularCohomologyMayerVietorisδ_naturality (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyMayerVietorisδ R k M hU' hV' hUV' n m h ≫ TopCat.singularCohomologyMap f m =
      TopCat.singularCohomologyMap (ofHom ⟨(hfU.inter_inter hfV).restrict,
          f.hom.continuous.restrict (hfU.inter_inter hfV)⟩) n ≫
        singularCohomologyMayerVietorisδ R k M hU hV hUV n m h := by
  have hsmall : (smallIso R k M hU' hV' hUV' m).inv ≫ TopCat.singularCohomologyMap f m =
      HomologicalComplex.homologyMap (cochainSequenceMap R k M f hfU hfV).τ₁ m ≫
        (smallIso R k M hU hV hUV m).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, smallIso_hom, smallIso_hom]
    simp only [TopCat.singularCohomologyMap, ← SSet.cochainComplexMap_toSSet_map,
      cochainSequenceMap, ← HomologicalComplex.homologyMap_comp, ← SSet.cochainComplexMap_comp,
      smallSingularSubcomplexMap_ι]
  rw [singularCohomologyMayerVietorisδ, singularCohomologyMayerVietorisδ, Category.assoc, hsmall,
    ← Category.assoc, HomologicalComplex.HomologySequence.δ_naturality
      (cochainSequenceMap R k M f hfU hfV) (shortExact_cochainSequence R k M U' V')
      (shortExact_cochainSequence R k M U V), Category.assoc, cochainSequenceMap_τ₃]

end Sequence

end TopCat
