/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.MayerVietoris
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.Topology.Category.TopPair

/-!
# The relative Mayer–Vietoris sequence of two open sets

Let `U` and `V` be open subsets of a topological space `X`, and let `R` be an object of an abelian
category with coproducts. This file constructs the relative Mayer–Vietoris long exact sequence of
relative singular homology with coefficients in `R`,
`⋯ ⟶ Hₙ(X, U ∩ V) ⟶ Hₙ(X, U) ⊞ Hₙ(X, V) ⟶ Hₙ(X, U ∪ V) ⟶ Hₙ₋₁(X, U ∩ V) ⟶ ⋯`,
whose first map is `(i_U, -i_V)` and whose second map is `j_U + j_V`, the `i` and `j` being the
maps induced by the inclusions of pairs with the identity of `X`. Unlike the absolute sequence,
`U` and `V` need not cover `X`.

For the complements `U = X ∖ A` and `V = X ∖ B` of closed sets this is the sequence
`⋯ ⟶ Hₙ(X, X ∖ (A ∪ B)) ⟶ Hₙ(X, X ∖ A) ⊞ Hₙ(X, X ∖ B) ⟶ Hₙ(X, X ∖ (A ∩ B)) ⟶ ⋯`
through which the homology of a manifold relative to the complement of a compact set is computed
by induction on the number of convex pieces in charts, which is the route to fundamental classes
and to Poincaré duality.

The construction applies the relative Mayer–Vietoris sequence of a square of pairs of simplicial
sets (`SSetPair.shortExact_mayerVietoris`) to the pairs formed by the singular simplicial set of
`X` and the singular simplicial sets of `U ∩ V`, `U` and `V`, together with the subcomplex of
singular simplices of `X` lying in `U` or in `V`. The ambient square consists of identities and
the square of subobjects is the pushout square of the absolute Mayer–Vietoris sequence
(`TopCat.isPushout_toSSet_inter_smallSingularSubcomplex`). Since `U` and `V` are open, the
small-chain theorem for the cover of `U ∪ V` by `U` and `V` identifies the relative homology of
`X` modulo that subcomplex with `Hₙ(X, U ∪ V)`.

## Main definitions and results

* `TopCat.relativeMayerVietorisToBiprod`, `TopCat.relativeMayerVietorisFromBiprod`: the maps
  `Hₙ(X, U ∩ V) ⟶ Hₙ(X, U) ⊞ Hₙ(X, V)` and `Hₙ(X, U) ⊞ Hₙ(X, V) ⟶ Hₙ(X, U ∪ V)`.
* `TopCat.relativeMayerVietorisδ`: the connecting morphism `Hₙ(X, U ∪ V) ⟶ Hₘ(X, U ∩ V)`,
  `m + 1 = n`.
* `TopCat.relativeMayerVietoris_exact₁`, `TopCat.relativeMayerVietoris_exact₂`,
  `TopCat.relativeMayerVietoris_exact₃`: exactness at `Hₘ(X, U ∩ V)`, at
  `Hₙ(X, U) ⊞ Hₙ(X, V)` and at `Hₙ(X, U ∪ V)`.
* `TopCat.epi_relativeMayerVietorisFromBiprod_zero`: surjectivity at the degree-zero endpoint.
* `TopCat.relativeMayerVietorisToBiprod_naturality`,
  `TopCat.relativeMayerVietorisFromBiprod_naturality`, `TopCat.relativeMayerVietorisδ_naturality`:
  the maps of the sequence are natural in maps `f : X ⟶ Y` carrying `U` into `U'` and `V` into
  `V'`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the relative Mayer–Vietoris sequence, and
  Lemma 3.27 for its use on complements of compact sets in a manifold.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X : TopCat.{w}} (U V : Set X)

/-! ### The maps of the sequence -/

/-- The first map `Hₙ(X, U ∩ V) ⟶ Hₙ(X, U) ⊞ Hₙ(X, V)` of the relative Mayer–Vietoris sequence,
with components `i_U` and `-i_V` induced by the identity of `X`. -/
def relativeMayerVietorisToBiprod (n : ℕ) :
    (TopPair.ofSubset (U ∩ V)).singularHomology R n ⟶
      (TopPair.ofSubset U).singularHomology R n ⊞ (TopPair.ofSubset V).singularHomology R n :=
  biprod.lift (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_left) R n)
    (-TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_right) R n)

@[reassoc (attr := simp)]
lemma relativeMayerVietorisToBiprod_fst (n : ℕ) :
    relativeMayerVietorisToBiprod R U V n ≫ biprod.fst =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_left) R n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma relativeMayerVietorisToBiprod_snd (n : ℕ) :
    relativeMayerVietorisToBiprod R U V n ≫ biprod.snd =
      -TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_right) R n :=
  biprod.lift_snd _ _

/-- The second map `Hₙ(X, U) ⊞ Hₙ(X, V) ⟶ Hₙ(X, U ∪ V)` of the relative Mayer–Vietoris sequence,
the sum of the maps `j_U` and `j_V` induced by the identity of `X`. -/
def relativeMayerVietorisFromBiprod (n : ℕ) :
    (TopPair.ofSubset U).singularHomology R n ⊞ (TopPair.ofSubset V).singularHomology R n ⟶
      (TopPair.ofSubset (U ∪ V)).singularHomology R n :=
  biprod.desc (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) Set.subset_union_left) R n)
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) Set.subset_union_right) R n)

@[reassoc (attr := simp)]
lemma inl_relativeMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ relativeMayerVietorisFromBiprod R U V n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) Set.subset_union_left) R n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_relativeMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ relativeMayerVietorisFromBiprod R U V n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) Set.subset_union_right) R n :=
  biprod.inr_desc _ _

/-! ### The square of singular pairs -/

/-- The singular simplices of `X` lying in `U` or in `V`. -/
private abbrev smallSubcomplex : (toSSet.obj X).Subcomplex :=
  X.smallSingularSubcomplex ![U, V]

/-- The map of singular pairs `(X, A) ⟶ (X, smallSubcomplex U V)` for `A` contained in `U` or in
`V`, with the identity on the singular simplicial set of `X`. -/
private abbrev toSmallPair {A : Set X} {i : Fin 2} (h : A ⊆ ![U, V] i) :
    TopPair.toSSetPair.obj (TopPair.ofSubset A) ⟶ (smallSubcomplex U V).pair :=
  SSetPair.homMk (toSmallSingularSubcomplex ![U, V] h) (𝟙 _)
    ((toSmallSingularSubcomplex_ι _ _).trans (Category.comp_id _).symm)

/-- On singular simplicial sets of subspaces, the map of pairs induced by the identity of `X` is
the map induced by the inclusion of subspaces. -/
private lemma toSSetPair_map_ofSubsetMap_left {A B : Set X} (h : A ⊆ B) :
    (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h)).left =
      toSSet.map (ofHom (ContinuousMap.inclusion h)) := by
  rw [TopPair.toSSetPair_map_left]
  congr 1
  ext x
  exact Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ x)

/-- On the singular simplicial set of `X`, the map of pairs induced by the identity of `X` is the
identity. -/
private lemma toSSetPair_map_ofSubsetMap_right {A B : Set X} (h : A ⊆ B) :
    (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h)).right = 𝟙 (toSSet.obj X) :=
  (congrArg toSSet.map (TopPair.ofSubsetMap_fst (𝟙 X) h)).trans (toSSet.map_id X)

private lemma mono_toSSetPair_map_ofSubsetMap_left {A B : Set X} (h : A ⊆ B) :
    Mono (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h)).left := by
  rw [toSSetPair_map_ofSubsetMap_left]
  exact Functor.map_mono _ _

private lemma mono_toSSetPair_map_ofSubsetMap_right {A B : Set X} (h : A ⊆ B) :
    Mono (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h)).right := by
  refine ⟨fun g g' hgh ↦ ?_⟩
  rw [toSSetPair_map_ofSubsetMap_right] at hgh
  exact (Category.comp_id g).symm.trans (hgh.trans (Category.comp_id g'))

attribute [local instance] mono_toSSetPair_map_ofSubsetMap_left
  mono_toSSetPair_map_ofSubsetMap_right

private lemma isPushout_left :
    IsPushout (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_left)).left
      (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_right)).left
      (toSmallPair U V (i := 0) (Matrix.cons_val_zero U ![V]).superset).left
      (toSmallPair U V (i := 1)
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset).left := by
  rw [toSSetPair_map_ofSubsetMap_left, toSSetPair_map_ofSubsetMap_left]
  exact isPushout_toSSet_inter_smallSingularSubcomplex U V

private lemma isPushout_right :
    IsPushout (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_left)).right
      (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_right)).right
      (toSmallPair U V (i := 0) (Matrix.cons_val_zero U ![V]).superset).right
      (toSmallPair U V (i := 1)
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset).right := by
  rw [toSSetPair_map_ofSubsetMap_right, toSSetPair_map_ofSubsetMap_right]
  exact IsPushout.of_id_fst

/-! ### Comparison with the pair `(X, U ∪ V)` -/

/-- The inclusion of the singular simplicial set of `U ∪ V` into that of `X`. -/
private abbrev unionι : toSSet.obj (of ↥(U ∪ V)) ⟶ toSSet.obj X :=
  toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ V)))

private lemma mono_unionι : Mono (unionι U V) := Functor.map_mono _ _

attribute [local instance] mono_unionι

private lemma smallSubcomplex_le_range :
    smallSubcomplex U V ≤ SSet.Subcomplex.range (unionι U V) := by
  intro n σ hσ
  obtain ⟨i, hi⟩ := (mem_smallSingularSubcomplex_iff X ![U, V] σ).1 hσ
  refine (mem_range_toSSet_subtypeVal_iff (U ∪ V) n σ).2 (hi.trans ?_)
  fin_cases i <;> simp

/-- The singular simplices of `X` lying in `U` or in `V` are singular simplices of `U ∪ V`. -/
private def smallSubcomplexToUnion : (smallSubcomplex U V : SSet) ⟶ toSSet.obj (of ↥(U ∪ V)) :=
  SSet.Subcomplex.homOfLE (smallSubcomplex_le_range U V) ≫
    inv (SSet.Subcomplex.toRange (unionι U V))

@[reassoc]
private lemma smallSubcomplexToUnion_comp :
    smallSubcomplexToUnion U V ≫ unionι U V = (smallSubcomplex U V).ι := by
  have h : inv (SSet.Subcomplex.toRange (unionι U V)) ≫ unionι U V =
      (SSet.Subcomplex.range (unionι U V)).ι := by
    rw [IsIso.inv_comp_eq, SSet.Subcomplex.toRange_ι]
  rw [smallSubcomplexToUnion, Category.assoc, h, SSet.Subcomplex.homOfLE_ι]

private lemma toSmallSingularSubcomplex_comp_smallSubcomplexToUnion {A : Set X} {i : Fin 2}
    (h : A ⊆ ![U, V] i) (h' : A ⊆ U ∪ V) :
    toSmallSingularSubcomplex ![U, V] h ≫ smallSubcomplexToUnion U V =
      toSSet.map (ofHom (ContinuousMap.inclusion h')) := by
  rw [← cancel_mono (unionι U V), Category.assoc, smallSubcomplexToUnion_comp,
    toSmallSingularSubcomplex_ι, ← Functor.map_comp]
  rfl

/-- The map of singular pairs `(X, smallSubcomplex U V) ⟶ (X, U ∪ V)`, with the identity on the
singular simplicial set of `X`. -/
private abbrev smallPairToUnion :
    (smallSubcomplex U V).pair ⟶ TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)) :=
  SSetPair.homMk (smallSubcomplexToUnion U V) (𝟙 _)
    ((smallSubcomplexToUnion_comp U V).trans (Category.comp_id _).symm)

private lemma toSmallPair_comp_smallPairToUnion {A : Set X} {i : Fin 2} (h : A ⊆ ![U, V] i)
    (h' : A ⊆ U ∪ V) :
    toSmallPair U V h ≫ smallPairToUnion U V =
      TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h') := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, toSSetPair_map_ofSubsetMap_left]
    exact toSmallSingularSubcomplex_comp_smallSubcomplexToUnion U V h h'
  · rw [MorphismProperty.Comma.comp_right, toSSetPair_map_ofSubsetMap_right]
    exact Category.comp_id _

/-- The singular simplices of `X` lying in `U` or in `V` compute the homology of `U ∪ V`, by the
small-chain theorem for the open cover of `U ∪ V` by `U` and `V`. -/
private lemma quasiIso_chainComplexMap_smallSubcomplexToUnion (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso (SSet.chainComplexMap (smallSubcomplexToUnion U V) R) := by
  set f := unionι U V
  set D := smallSubcomplex U V
  -- The simplices of `D` all come from `U ∪ V`, so `D` is isomorphic to its preimage under `f`.
  have : IsIso (D.fromPreimage f) := by
    have (n : SimplexCategoryᵒᵖ) : IsIso ((D.fromPreimage f).app n) := by
      have hinj : Function.Injective (f.app n) :=
        (CategoryTheory.mono_iff_injective (f.app n)).1 inferInstance
      refine (isIso_iff_bijective _).2 ⟨fun x y hxy ↦ Subtype.ext ?_, fun y ↦ ?_⟩
      · exact hinj (congrArg Subtype.val hxy)
      · exact (D.mem_range_fromPreimage_app_iff f y).2 (smallSubcomplex_le_range U V n y.2)
    exact NatIso.isIso_of_isIso_app _
  have hfac : D.fromPreimage f ≫ smallSubcomplexToUnion U V = (D.preimage f).ι := by
    rw [← cancel_mono f, Category.assoc, smallSubcomplexToUnion_comp,
      SSet.Subcomplex.fromPreimage_ι]
  -- The preimage of `D` is the subcomplex of simplices of `U ∪ V` small for its cover by `U`
  -- and `V`, whose inclusion is a quasi-isomorphism.
  have hq := TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι R
    (fun i ↦ ofHom (ContinuousMap.subtypeVal (U ∪ V)) ⁻¹' ![U, V] i)
    (fun i ↦ (TauCeti.isOpen_vecCons hU hV i).preimage continuous_subtype_val)
    (by
      rw [← Set.preimage_iUnion, TauCeti.iUnion_vecCons]
      exact Set.eq_univ_of_forall fun x ↦ x.2)
  rw [← preimage_smallSingularSubcomplex] at hq
  have hcomp : SSet.chainComplexMap (D.preimage f).ι R =
      SSet.chainComplexMap (D.fromPreimage f) R ≫
        SSet.chainComplexMap (smallSubcomplexToUnion U V) R := by
    rw [← hfac]
    exact Functor.map_comp _ _ _
  rw [hcomp] at hq
  exact quasiIso_of_comp_left (SSet.chainComplexMap (D.fromPreimage f) R) _

private lemma isIso_homologyMap_smallPairToUnion (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    IsIso (SSetPair.homologyMap (smallPairToUnion U V) R n) := by
  have : QuasiIso (SSet.chainComplexMap (smallPairToUnion U V).left R) :=
    quasiIso_chainComplexMap_smallSubcomplexToUnion R U V hU hV
  -- The ambient component is the identity of the singular simplicial set of `X`, seen between
  -- two syntactically different presentations of it, so the instance is supplied by hand.
  have : IsIso (SSet.chainComplexMap (smallPairToUnion U V).right R) := by
    rw [show SSet.chainComplexMap (smallPairToUnion U V).right R = 𝟙 _ from
      CategoryTheory.Functor.map_id _ _]
    exact IsIso.id _
  have : QuasiIso (SSet.chainComplexMap (smallPairToUnion U V).right R) := quasiIso_of_isIso _
  exact SSetPair.isIso_homologyMap_of_quasiIso _ R n

private lemma relativeMayerVietorisToBiprod_eq (n : ℕ) :
    relativeMayerVietorisToBiprod R U V n =
      SSetPair.mayerVietorisToBiprod R
        (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_left))
        (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) Set.inter_subset_right)) n := by
  ext <;> simp [relativeMayerVietorisToBiprod]

private lemma mayerVietorisFromBiprod_comp_homologyMap_smallPairToUnion (n : ℕ) :
    SSetPair.mayerVietorisFromBiprod R
        (toSmallPair U V (i := 0) (Matrix.cons_val_zero U ![V]).superset)
        (toSmallPair U V (i := 1)
          ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) n ≫
      SSetPair.homologyMap (smallPairToUnion U V) R n =
    relativeMayerVietorisFromBiprod R U V n := by
  apply biprod.hom_ext'
  · rw [SSetPair.inl_mayerVietorisFromBiprod_assoc, ← SSetPair.homologyMap_comp,
      toSmallPair_comp_smallPairToUnion _ _ _ Set.subset_union_left,
      inl_relativeMayerVietorisFromBiprod]
  · rw [SSetPair.inr_mayerVietorisFromBiprod_assoc, ← SSetPair.homologyMap_comp,
      toSmallPair_comp_smallPairToUnion _ _ _ Set.subset_union_right,
      inr_relativeMayerVietorisFromBiprod]

/-! ### The long exact sequence -/

/-- The first two maps of the relative Mayer–Vietoris sequence compose to zero. -/
@[reassoc (attr := simp)]
lemma relativeMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    relativeMayerVietorisToBiprod R U V n ≫ relativeMayerVietorisFromBiprod R U V n = 0 := by
  rw [relativeMayerVietorisToBiprod_eq, ← mayerVietorisFromBiprod_comp_homologyMap_smallPairToUnion,
    SSetPair.mayerVietorisToBiprod_fromBiprod_assoc R
      (MorphismProperty.Arrow.Hom.ext (isPushout_left U V).w (isPushout_right U V).w), zero_comp]

variable {U V} (hU : IsOpen U) (hV : IsOpen V)

/-- The relative Mayer–Vietoris connecting morphism `Hₙ(X, U ∪ V) ⟶ Hₘ(X, U ∩ V)`, where
`m + 1 = n`, for open sets `U` and `V`. It is the connecting morphism of the relative
Mayer–Vietoris sequence of the singular pairs of `X` modulo `U ∩ V`, `U`, `V` and the singular
simplices lying in `U` or in `V`, precomposed with the inverse of the small-chain isomorphism
identifying the last of these with `Hₙ(X, U ∪ V)`. -/
def relativeMayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (TopPair.ofSubset (U ∪ V)).singularHomology R n ⟶
      (TopPair.ofSubset (U ∩ V)).singularHomology R m :=
  have := isIso_homologyMap_smallPairToUnion R U V hU hV n
  inv (SSetPair.homologyMap (smallPairToUnion U V) R n) ≫
    SSetPair.mayerVietorisδ R (isPushout_left U V) (isPushout_right U V) n m h

private lemma homologyMap_smallPairToUnion_comp_relativeMayerVietorisδ (n m : ℕ)
    (h : m + 1 = n := by lia) :
    SSetPair.homologyMap (smallPairToUnion U V) R n ≫ relativeMayerVietorisδ R hU hV n m h =
      SSetPair.mayerVietorisδ R (isPushout_left U V) (isPushout_right U V)
        n m h := by
  have := isIso_homologyMap_smallPairToUnion R U V hU hV n
  rw [relativeMayerVietorisδ, IsIso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma relativeMayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    relativeMayerVietorisδ R hU hV n m h ≫ relativeMayerVietorisToBiprod R U V m = 0 := by
  rw [relativeMayerVietorisδ, Category.assoc, relativeMayerVietorisToBiprod_eq,
    SSetPair.mayerVietorisδ_toBiprod R _ _ n m h, comp_zero]

@[reassoc (attr := simp)]
lemma relativeMayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    relativeMayerVietorisFromBiprod R U V n ≫ relativeMayerVietorisδ R hU hV n m h = 0 := by
  rw [← mayerVietorisFromBiprod_comp_homologyMap_smallPairToUnion, Category.assoc,
    homologyMap_smallPairToUnion_comp_relativeMayerVietorisδ R hU hV n m h,
    SSetPair.mayerVietorisFromBiprod_δ R _ _ n m h]

/-- **Exactness of the relative Mayer–Vietoris sequence at `Hₘ(X, U ∩ V)`.** -/
lemma relativeMayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (relativeMayerVietorisδ_toBiprod R hU hV n m h)).Exact := by
  have := isIso_homologyMap_smallPairToUnion R U V hU hV n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietoris_exact₁ R (isPushout_left U V) (isPushout_right U V) n m h)
  refine ShortComplex.isoMk (asIso (SSetPair.homologyMap (smallPairToUnion U V) R n))
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [homologyMap_smallPairToUnion_comp_relativeMayerVietorisδ R hU hV n m h]
  · simp [relativeMayerVietorisToBiprod_eq]

include hU hV in
/-- **Exactness of the relative Mayer–Vietoris sequence at `Hₙ(X, U) ⊞ Hₙ(X, V)`.** -/
lemma relativeMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (relativeMayerVietorisToBiprod_fromBiprod R U V n)).Exact := by
  have := isIso_homologyMap_smallPairToUnion R U V hU hV n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietoris_exact₂ R (isPushout_left U V) (isPushout_right U V)
      n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (asIso (SSetPair.homologyMap (smallPairToUnion U V) R n)) ?_ ?_
  · simp [relativeMayerVietorisToBiprod_eq]
  · simp [mayerVietorisFromBiprod_comp_homologyMap_smallPairToUnion]

/-- **Exactness of the relative Mayer–Vietoris sequence at `Hₙ(X, U ∪ V)`.** -/
lemma relativeMayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (relativeMayerVietorisFromBiprod_δ R hU hV n m h)).Exact := by
  have := isIso_homologyMap_smallPairToUnion R U V hU hV n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietoris_exact₃ R (isPushout_left U V) (isPushout_right U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _)
    (asIso (SSetPair.homologyMap (smallPairToUnion U V) R n)) (Iso.refl _) ?_ ?_
  · simp [mayerVietorisFromBiprod_comp_homologyMap_smallPairToUnion]
  · simp [homologyMap_smallPairToUnion_comp_relativeMayerVietorisδ R hU hV n m h]

include hU hV in
/-- The map `H₀(X, U) ⊞ H₀(X, V) ⟶ H₀(X, U ∪ V)` at the end of the relative Mayer–Vietoris
sequence is an epimorphism. -/
lemma epi_relativeMayerVietorisFromBiprod_zero : Epi (relativeMayerVietorisFromBiprod R U V 0) := by
  have := isIso_homologyMap_smallPairToUnion R U V hU hV 0
  have := SSetPair.epi_mayerVietorisFromBiprod_zero R (isPushout_left U V) (isPushout_right U V)
  rw [← mayerVietorisFromBiprod_comp_homologyMap_smallPairToUnion]
  exact epi_comp _ _

/-! ### Naturality -/

variable {Y : TopCat.{w}} {U' V' : Set Y} (hU' : IsOpen U') (hV' : IsOpen V') (f : X ⟶ Y)
  (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- The maps of pairs induced by the identities of `X` and `Y` commute with those induced by
`f`. -/
private lemma ofSubsetMap_id_comp_ofSubsetMap {A B : Set X} {A' B' : Set Y}
    (hAB : Set.MapsTo (𝟙 X) A B) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B')
    (hAB' : Set.MapsTo (𝟙 Y) A' B') :
    TopPair.ofSubsetMap (𝟙 X) hAB ≫ TopPair.ofSubsetMap f hB =
      TopPair.ofSubsetMap f hA ≫ TopPair.ofSubsetMap (𝟙 Y) hAB' :=
  TopPair.hom_ext_of_fst _ (by
    simp only [TopPair.Hom.fst_comp, TopPair.ofSubsetMap_fst]
    exact (Category.id_comp f).trans (Category.comp_id f).symm)

/-- The first map of the relative Mayer–Vietoris sequence is natural in maps `f : X ⟶ Y` carrying
`U` into `U'` and `V` into `V'`. -/
@[reassoc]
lemma relativeMayerVietorisToBiprod_naturality (n : ℕ) :
    relativeMayerVietorisToBiprod R U V n ≫
        biprod.map (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfU) R n)
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfV) R n) =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap f (hfU.inter_inter hfV)) R n ≫
        relativeMayerVietorisToBiprod R U' V' n := by
  ext <;> simp only [Category.assoc, biprod.map_fst, biprod.map_snd,
      relativeMayerVietorisToBiprod_fst, relativeMayerVietorisToBiprod_fst_assoc,
      relativeMayerVietorisToBiprod_snd, relativeMayerVietorisToBiprod_snd_assoc,
      Preadditive.neg_comp, Preadditive.comp_neg, neg_inj,
      ← TopPair.singularHomologyMap_comp] <;>
    exact congrArg (TopPair.singularHomologyMap · R n) (ofSubsetMap_id_comp_ofSubsetMap f _ _ _ _)

/-- The second map of the relative Mayer–Vietoris sequence is natural in maps `f : X ⟶ Y`
carrying `U` into `U'` and `V` into `V'`. -/
@[reassoc]
lemma relativeMayerVietorisFromBiprod_naturality (n : ℕ) :
    relativeMayerVietorisFromBiprod R U V n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap f (hfU.union_union hfV)) R n =
      biprod.map (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfU) R n)
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfV) R n) ≫
        relativeMayerVietorisFromBiprod R U' V' n := by
  ext <;> simp only [biprod.inl_map_assoc, biprod.inr_map_assoc,
      inl_relativeMayerVietorisFromBiprod_assoc, inr_relativeMayerVietorisFromBiprod_assoc,
      inl_relativeMayerVietorisFromBiprod, inr_relativeMayerVietorisFromBiprod,
      ← TopPair.singularHomologyMap_comp] <;>
    exact congrArg (TopPair.singularHomologyMap · R n) (ofSubsetMap_id_comp_ofSubsetMap f _ _ _ _)

/-- On singular simplicial sets of subspaces, the map of pairs induced by `f` is the map induced by
the restriction of `f`. -/
private lemma toSSetPair_map_ofSubsetMap_left_restrict {A : Set X} {A' : Set Y}
    (hA : Set.MapsTo f A A') :
    (TopPair.toSSetPair.map (TopPair.ofSubsetMap f hA)).left =
      toSSet.map (ofHom ⟨hA.restrict, f.hom.continuous.restrict hA⟩) := by
  rw [TopPair.toSSetPair_map_left]
  congr 1
  ext x
  exact Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ x)

include hfU hfV in
private lemma mapsTo_vecCons : ∀ i, Set.MapsTo f (![U, V] i) (![U', V'] (id i)) := by
  simp [Fin.forall_fin_two, hfU, hfV]

/-- The map of singular pairs `(X, smallSubcomplex U V) ⟶ (Y, smallSubcomplex U' V')` induced
by `f`. -/
private abbrev smallPairMap : (smallSubcomplex U V).pair ⟶ (smallSubcomplex U' V').pair :=
  SSetPair.homMk (X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id (mapsTo_vecCons f hfU hfV))
    (toSSet.map f) (smallSingularSubcomplexMap_ι _ _ _ _ _)

private lemma toSmallPair_comp_smallPairMap {A : Set X} {A' : Set Y} {i : Fin 2}
    (h : A ⊆ ![U, V] i) (h' : A' ⊆ ![U', V'] i) (hA : Set.MapsTo f A A') :
    toSmallPair U V h ≫ smallPairMap f hfU hfV =
      TopPair.toSSetPair.map (TopPair.ofSubsetMap f hA) ≫ toSmallPair U' V' h' := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      toSSetPair_map_ofSubsetMap_left_restrict]
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ f id _ h h' hA
  · rw [MorphismProperty.Comma.comp_right, MorphismProperty.Comma.comp_right,
      TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

private lemma smallPairToUnion_comp_ofSubsetMap :
    smallPairToUnion U V ≫ TopPair.toSSetPair.map (TopPair.ofSubsetMap f (hfU.union_union hfV)) =
      smallPairMap f hfU hfV ≫ smallPairToUnion U' V' := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      toSSetPair_map_ofSubsetMap_left_restrict]
    -- After the rewrite, the composite's middle object is `toSSet.obj ↧(U ∪ V)` on one side but
    -- `(TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V))).left` on the other, which agree only
    -- after unfolding `TopPair.toSSetPair`. The goal is thus not type-correct at the transparency
    -- `rw` uses, so `dsimp`-unfolding the `SSetPair.homMk` components still leaves `rw` stuck;
    -- `change` re-elaborates the goal with the `left` components of `smallPairToUnion` and
    -- `smallPairMap` written out.
    change smallSubcomplexToUnion U V ≫ _ =
      X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id _ ≫ smallSubcomplexToUnion U' V'
    rw [← cancel_mono (unionι U' V'), Category.assoc, Category.assoc, smallSubcomplexToUnion_comp,
      ← Functor.map_comp, ← ofHom_subtypeVal_comp, Functor.map_comp,
      smallSubcomplexToUnion_comp_assoc, smallSingularSubcomplexMap_ι]
  · rw [MorphismProperty.Comma.comp_right, MorphismProperty.Comma.comp_right,
      TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- **Naturality of the relative Mayer–Vietoris connecting morphism.** A map `f : X ⟶ Y` carrying
`U` into `U'` and `V` into `V'` commutes with the connecting morphisms. -/
@[reassoc]
lemma relativeMayerVietorisδ_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    relativeMayerVietorisδ R hU hV n m h ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap f (hfU.inter_inter hfV)) R m =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap f (hfU.union_union hfV)) R n ≫
        relativeMayerVietorisδ R hU' hV' n m h := by
  have := isIso_homologyMap_smallPairToUnion R U V hU hV n
  have := isIso_homologyMap_smallPairToUnion R U' V' hU' hV' n
  have hnat := SSetPair.mayerVietorisδ_naturality R
    (TopPair.toSSetPair.map (TopPair.ofSubsetMap f (hfU.inter_inter hfV)))
    (TopPair.toSSetPair.map (TopPair.ofSubsetMap f hfU))
    (TopPair.toSSetPair.map (TopPair.ofSubsetMap f hfV)) (smallPairMap f hfU hfV)
    (isPushout_left U V) (isPushout_right U V) (isPushout_left U' V') (isPushout_right U' V')
    ?_ ?_ ?_ ?_ n m h
  · rw [relativeMayerVietorisδ, relativeMayerVietorisδ, Category.assoc, hnat, ← Category.assoc,
      ← Category.assoc]
    congr 1
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, ← SSetPair.homologyMap_comp,
      ← SSetPair.homologyMap_comp, smallPairToUnion_comp_ofSubsetMap]
  · simp only [← Functor.map_comp]
    exact congrArg _ (ofSubsetMap_id_comp_ofSubsetMap f _ _ _ _)
  · simp only [← Functor.map_comp]
    exact congrArg _ (ofSubsetMap_id_comp_ofSubsetMap f _ _ _ _)
  · exact toSmallPair_comp_smallPairMap f hfU hfV _ _ hfU
  · exact toSmallPair_comp_smallPairMap f hfU hfV _ _ hfV

end TopCat
