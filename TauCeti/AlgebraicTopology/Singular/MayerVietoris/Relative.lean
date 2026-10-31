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
# Relative Mayer–Vietoris sequences

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

The second sequence is the Mayer–Vietoris sequence of two pairs. For subsets `C ⊆ A` and
`D ⊆ B` of `X`, with `A` and `B` open in `A ∪ B` and `C` and `D` open in `C ∪ D`, it is
`⋯ ⟶ Hₙ(A ∩ B, C ∩ D) ⟶ Hₙ(A, C) ⊞ Hₙ(B, D) ⟶ Hₙ(A ∪ B, C ∪ D) ⟶ Hₙ₋₁(A ∩ B, C ∩ D) ⟶ ⋯`,
again with first map `(i_A, -i_B)` and second map `j_A + j_B`, now induced by the inclusions of
the subspaces. For the restrictions `(E|U, E₀|U)` and `(E|V, E₀|V)` of a pair over two open sets
of a base, such as the Thom pair of a vector bundle over a union of two trivializing open sets,
this is the sequence that assembles the relative homology of the pair over `U ∪ V` from its pieces.
Here the ambient square of singular simplicial sets is the pushout square of `A ∩ B`, `A`, `B`
and the singular simplices of `X` lying in `A` or in `B`, the square of subobjects is the
corresponding square for `C` and `D`, and the small-chain theorem for both covers identifies the
corner pair with `(A ∪ B, C ∪ D)`.

## Main definitions and results

* `TopCat.relativeMayerVietorisToBiprod`, `TopCat.relativeMayerVietorisFromBiprod`: the maps
  `Hₙ(X, U ∩ V) ⟶ Hₙ(X, U) ⊞ Hₙ(X, V)` and `Hₙ(X, U) ⊞ Hₙ(X, V) ⟶ Hₙ(X, U ∪ V)`.
* `TopCat.relativeMayerVietorisδ`: the connecting morphism `Hₙ(X, U ∪ V) ⟶ Hₘ(X, U ∩ V)`,
  `m + 1 = n`.
* `TopCat.relativeMayerVietoris_exact₁`, `TopCat.relativeMayerVietoris_exact₂`,
  `TopCat.relativeMayerVietoris_exact₃`: exactness at `Hₘ(X, U ∩ V)`, at
  `Hₙ(X, U) ⊞ Hₙ(X, V)` and at `Hₙ(X, U ∪ V)`.
* `TopCat.epi_relativeMayerVietorisFromBiprod_zero`: surjectivity at the degree-zero endpoint.
* `TopCat.mono_relativeMayerVietorisToBiprod`: injectivity of the first map when
  `Hₖ₊₁(X, U ∪ V)` vanishes.
* `TopCat.relativeMayerVietorisToBiprod_naturality`,
  `TopCat.relativeMayerVietorisFromBiprod_naturality`, `TopCat.relativeMayerVietorisδ_naturality`:
  the maps of the sequence are natural in maps `f : X ⟶ Y` carrying `U` into `U'` and `V` into
  `V'`.
* `TopCat.pairMayerVietorisToBiprod`, `TopCat.pairMayerVietorisFromBiprod`: the maps
  `Hₙ(A ∩ B, C ∩ D) ⟶ Hₙ(A, C) ⊞ Hₙ(B, D)` and `Hₙ(A, C) ⊞ Hₙ(B, D) ⟶ Hₙ(A ∪ B, C ∪ D)`.
* `TopCat.pairMayerVietorisδ`: the connecting morphism
  `Hₙ(A ∪ B, C ∪ D) ⟶ Hₘ(A ∩ B, C ∩ D)`, `m + 1 = n`.
* `TopCat.pairMayerVietoris_exact₁`, `TopCat.pairMayerVietoris_exact₂`,
  `TopCat.pairMayerVietoris_exact₃`: exactness at `Hₘ(A ∩ B, C ∩ D)`, at
  `Hₙ(A, C) ⊞ Hₙ(B, D)` and at `Hₙ(A ∪ B, C ∪ D)`.
* `TopCat.smallSingularPair`, `TopCat.toSmallSingularPair` and `TopCat.smallSingularPairToUnion`:
  the square of singular pairs underlying the sequence of two pairs and its comparison with
  `(A ∪ B, C ∪ D)`, through `TopCat.smallSingularSubcomplexToUnion`; they are shared with the
  sequence in cohomology.
* `TopCat.epi_pairMayerVietorisFromBiprod_zero` and `TopCat.mono_pairMayerVietorisToBiprod`:
  surjectivity at the degree-zero endpoint, and injectivity of the first map when
  `Hₖ₊₁(A ∪ B, C ∪ D)` vanishes.
* `TopCat.isZero_singularHomology_ofInclusion_union`: `Hₙ(A ∪ B, C ∪ D)` vanishes when `Hₙ(A, C)`,
  `Hₙ(B, D)` and `Hₙ₋₁(A ∩ B, C ∩ D)` do.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the relative Mayer–Vietoris sequence, both for
  `(X, U ∩ V)`, `(X, U)`, `(X, V)` and for pairs `(A ∪ B, C ∪ D)` with `C ⊆ A` and `D ⊆ B`, and
  Lemma 3.27 for its use on complements of compact sets in a manifold.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, where the cohomological sequence of two pairs over open sets of a base
  is used to construct the Thom class.
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
  set D := smallSubcomplex U V
  -- The simplices of `D` all come from `U ∪ V`, so `D` is isomorphic to its preimage under `f`,
  -- which is the subcomplex of simplices of `U ∪ V` small for its cover by `U` and `V`.
  have : IsIso (D.fromPreimage f) := by
    have (n : SimplexCategoryᵒᵖ) : IsIso ((D.fromPreimage f).app n) := by
      have hinj : Function.Injective (f.app n) :=
        (CategoryTheory.mono_iff_injective (f.app n)).1 inferInstance
      refine (isIso_iff_bijective _).2 ⟨fun x y hxy ↦ Subtype.ext ?_, fun y ↦ ?_⟩
      · exact hinj (congrArg Subtype.val hxy)
      · exact (D.mem_range_fromPreimage_app_iff f y).2 (smallSubcomplex_le_range U V n y.2)
    exact NatIso.isIso_of_isIso_app _
  rw [← preimage_smallSingularSubcomplex]
  refine ⟨asIso (D.fromPreimage f), ?_⟩
  rw [asIso_hom, ← cancel_mono f, Category.assoc, smallSingularSubcomplexToUnion_comp,
    SSet.Subcomplex.fromPreimage_ι]

private lemma toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion {A : Set X} {i : Fin 2}
    (h : A ⊆ ![U, V] i) (h' : A ⊆ U ∪ V) :
    toSmallSingularSubcomplex ![U, V] h ≫ smallSingularSubcomplexToUnion U V =
      toSSet.map (ofHom (ContinuousMap.inclusion h')) := by
  rw [← cancel_mono (unionι U V), Category.assoc, smallSingularSubcomplexToUnion_comp,
    toSmallSingularSubcomplex_ι, ← Functor.map_comp]
  rfl

/-- The map of singular pairs `(X, smallSubcomplex U V) ⟶ (X, U ∪ V)`, with the identity on the
singular simplicial set of `X`. -/
private abbrev smallPairToUnion :
    (smallSubcomplex U V).pair ⟶ TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)) :=
  SSetPair.homMk (smallSingularSubcomplexToUnion U V) (𝟙 _)
    ((smallSingularSubcomplexToUnion_comp U V).trans (Category.comp_id _).symm)

private lemma toSmallPair_comp_smallPairToUnion {A : Set X} {i : Fin 2} (h : A ⊆ ![U, V] i)
    (h' : A ⊆ U ∪ V) :
    toSmallPair U V h ≫ smallPairToUnion U V =
      TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) h') := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left, toSSetPair_map_ofSubsetMap_left]
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion U V h h'
  · rw [MorphismProperty.Comma.comp_right, toSSetPair_map_ofSubsetMap_right]
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
      rw [← Set.preimage_iUnion, TauCeti.iUnion_vecCons]
      exact Set.eq_univ_of_forall fun x ↦ x.2)
  have hcomp : SSet.chainComplexMap (e.hom ≫ smallSingularSubcomplexToUnion U V) R =
      SSet.chainComplexMap e.hom R ≫ SSet.chainComplexMap (smallSingularSubcomplexToUnion U V) R :=
    Functor.map_comp _ _ _
  rw [← he, hcomp] at hq
  exact quasiIso_of_comp_left (SSet.chainComplexMap e.hom R) _

private lemma isIso_homologyMap_smallPairToUnion (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    IsIso (SSetPair.homologyMap (smallPairToUnion U V) R n) := by
  have : QuasiIso (SSet.chainComplexMap (smallPairToUnion U V).left R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplexToUnion R U V
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
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
/-- If `Hₖ₊₁(X, U ∪ V)` vanishes, the first map `Hₖ(X, U ∩ V) ⟶ Hₖ(X, U) ⊞ Hₖ(X, V)` of the
relative Mayer–Vietoris sequence is a monomorphism. -/
lemma mono_relativeMayerVietorisToBiprod {k : ℕ}
    (h : IsZero ((TopPair.ofSubset (U ∪ V)).singularHomology R (k + 1))) :
    Mono (relativeMayerVietorisToBiprod R U V k) :=
  (relativeMayerVietoris_exact₁ R hU hV (k + 1) k).mono_g (h.eq_of_src _ _)

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
    change smallSingularSubcomplexToUnion U V ≫ _ =
      X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id _ ≫ smallSingularSubcomplexToUnion U' V'
    rw [← cancel_mono (unionι U' V'), Category.assoc, Category.assoc,
      smallSingularSubcomplexToUnion_comp, ← Functor.map_comp, ← ofHom_subtypeVal_comp,
      Functor.map_comp, smallSingularSubcomplexToUnion_comp_assoc, smallSingularSubcomplexMap_ι]
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

/-! ### The Mayer–Vietoris sequence of two pairs -/

section Pair

variable {A B C D : Set X} (hCA : C ⊆ A) (hDB : D ⊆ B)

/-- The first map `Hₙ(A ∩ B, C ∩ D) ⟶ Hₙ(A, C) ⊞ Hₙ(B, D)` of the Mayer–Vietoris sequence of the
pairs `(A, C)` and `(B, D)`, with components `i_A` and `-i_B` induced by the inclusions. -/
def pairMayerVietorisToBiprod (n : ℕ) :
    (TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).singularHomology R n ⟶
      (TopPair.ofInclusion hCA).singularHomology R n ⊞
        (TopPair.ofInclusion hDB).singularHomology R n :=
  biprod.lift
    (TopPair.singularHomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
      (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx) R n)
    (-TopPair.singularHomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
      (ContinuousMap.inclusion Set.inter_subset_right) fun _ hx ↦ Set.inter_subset_right hx) R n)

@[reassoc (attr := simp)]
lemma pairMayerVietorisToBiprod_fst (n : ℕ) :
    pairMayerVietorisToBiprod R hCA hDB n ≫ biprod.fst =
      TopPair.singularHomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
        (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx) R n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma pairMayerVietorisToBiprod_snd (n : ℕ) :
    pairMayerVietorisToBiprod R hCA hDB n ≫ biprod.snd =
      -TopPair.singularHomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
        (ContinuousMap.inclusion Set.inter_subset_right)
          fun _ hx ↦ Set.inter_subset_right hx) R n :=
  biprod.lift_snd _ _

/-- The second map `Hₙ(A, C) ⊞ Hₙ(B, D) ⟶ Hₙ(A ∪ B, C ∪ D)` of the Mayer–Vietoris sequence of the
pairs `(A, C)` and `(B, D)`, the sum of the maps `j_A` and `j_B` induced by the inclusions. -/
def pairMayerVietorisFromBiprod (n : ℕ) :
    (TopPair.ofInclusion hCA).singularHomology R n ⊞
        (TopPair.ofInclusion hDB).singularHomology R n ⟶
      (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularHomology R n :=
  biprod.desc
    (TopPair.singularHomologyMap (TopPair.ofInclusionMap hCA (Set.union_subset_union hCA hDB)
      (ContinuousMap.inclusion Set.subset_union_left) fun _ hx ↦ Set.subset_union_left hx) R n)
    (TopPair.singularHomologyMap (TopPair.ofInclusionMap hDB (Set.union_subset_union hCA hDB)
      (ContinuousMap.inclusion Set.subset_union_right) fun _ hx ↦ Set.subset_union_right hx) R n)

@[reassoc (attr := simp)]
lemma inl_pairMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ pairMayerVietorisFromBiprod R hCA hDB n =
      TopPair.singularHomologyMap (TopPair.ofInclusionMap hCA (Set.union_subset_union hCA hDB)
        (ContinuousMap.inclusion Set.subset_union_left) fun _ hx ↦ Set.subset_union_left hx) R n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_pairMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ pairMayerVietorisFromBiprod R hCA hDB n =
      TopPair.singularHomologyMap (TopPair.ofInclusionMap hDB (Set.union_subset_union hCA hDB)
        (ContinuousMap.inclusion Set.subset_union_right)
          fun _ hx ↦ Set.subset_union_right hx) R n :=
  biprod.inr_desc _ _

/-! #### The square of singular pairs -/

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_left
  TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

/-- The pair formed by the singular simplices of `X` lying in `A` or in `B` and those lying in `C`
or in `D`. For `A` and `B` open in `A ∪ B` and `C` and `D` open in `C ∪ D`, the small-chain theorem
shows that its comparison map `TopCat.smallSingularPairToUnion` to the singular pair of
`(A ∪ B, C ∪ D)` induces an isomorphism on relative homology. -/
abbrev smallSingularPair : SSetPair.{w} :=
  SSetPair.of (SSet.Subcomplex.homOfLE (smallSingularSubcomplex_mono X
    (U := ![C, D]) (U' := ![A, B]) (Fin.forall_fin_two.2 ⟨hCA, hDB⟩)))

/-- The map of singular pairs `(A₁, C₁) ⟶ TopCat.smallSingularPair hCA hDB` for `A₁` and `C₁` lying
in matching members of the covers `![A, B]` and `![C, D]`. -/
abbrev toSmallSingularPair {A₁ C₁ : Set X} (h₁ : C₁ ⊆ A₁) {i : Fin 2}
    (hA : A₁ ⊆ ![A, B] i) (hC : C₁ ⊆ ![C, D] i) :
    TopPair.toSSetPair.obj (TopPair.ofInclusion h₁) ⟶ smallSingularPair hCA hDB :=
  SSetPair.homMk (toSmallSingularSubcomplex ![C, D] hC) (toSmallSingularSubcomplex ![A, B] hA) (by
    -- Stated with the components written out, so that it typechecks without unfolding the pairs.
    have h : toSmallSingularSubcomplex ![C, D] hC ≫
        SSet.Subcomplex.homOfLE (smallSingularSubcomplex_mono X
          (U := ![C, D]) (U' := ![A, B]) (Fin.forall_fin_two.2 ⟨hCA, hDB⟩)) =
          toSSet.map (ofHom (ContinuousMap.inclusion h₁)) ≫
            toSmallSingularSubcomplex ![A, B] hA := by
      refine (cancel_mono (X.smallSingularSubcomplex ![A, B]).ι).1 ?_
      rw [Category.assoc, Category.assoc, SSet.Subcomplex.homOfLE_ι, toSmallSingularSubcomplex_ι,
        toSmallSingularSubcomplex_ι, ← Functor.map_comp, ← TopCat.ofHom_comp,
        ContinuousMap.subtypeVal_comp_inclusion]
    exact h)

/-- On subobjects, the square of singular pairs `(A ∩ B, C ∩ D)`, `(A, C)`, `(B, D)` and
`TopCat.smallSingularPair hCA hDB` is the pushout square of the singular simplicial sets of `C ∩ D`,
`C` and `D` and of the singular simplices lying in `C` or in `D`. -/
lemma isPushout_toSmallSingularPair_left :
    IsPushout
      (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
        (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx)).left
      (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
        (ContinuousMap.inclusion Set.inter_subset_right) fun _ hx ↦ Set.inter_subset_right hx)).left
      (toSmallSingularPair hCA hDB hCA (i := 0) (Matrix.cons_val_zero A ![B]).superset
        (Matrix.cons_val_zero C ![D]).superset).left
      (toSmallSingularPair hCA hDB hDB (i := 1)
        ((Matrix.cons_val_one A ![B]).trans (Matrix.cons_val_zero B ![])).superset
        ((Matrix.cons_val_one C ![D]).trans (Matrix.cons_val_zero D ![])).superset).left := by
  rw [TopPair.toSSetPair_map_ofInclusionMap_inclusion_left _ _ _ _ Set.inter_subset_left,
    TopPair.toSSetPair_map_ofInclusionMap_inclusion_left _ _ _ _ Set.inter_subset_right]
  exact isPushout_toSSet_inter_smallSingularSubcomplex C D

/-- On ambient simplicial sets, the square of singular pairs `(A ∩ B, C ∩ D)`, `(A, C)`, `(B, D)`
and `TopCat.smallSingularPair hCA hDB` is the pushout square of the singular simplicial sets of
`A ∩ B`, `A` and `B` and of the singular simplices lying in `A` or in `B`. -/
lemma isPushout_toSmallSingularPair_right :
    IsPushout
      (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
        (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx)).right
      (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
        (ContinuousMap.inclusion Set.inter_subset_right)
          fun _ hx ↦ Set.inter_subset_right hx)).right
      (toSmallSingularPair hCA hDB hCA (i := 0) (Matrix.cons_val_zero A ![B]).superset
        (Matrix.cons_val_zero C ![D]).superset).right
      (toSmallSingularPair hCA hDB hDB (i := 1)
        ((Matrix.cons_val_one A ![B]).trans (Matrix.cons_val_zero B ![])).superset
        ((Matrix.cons_val_one C ![D]).trans (Matrix.cons_val_zero D ![])).superset).right := by
  rw [TopPair.toSSetPair_map_ofInclusionMap_inclusion_right,
    TopPair.toSSetPair_map_ofInclusionMap_inclusion_right]
  exact isPushout_toSSet_inter_smallSingularSubcomplex A B

/-! #### Comparison with the pair `(A ∪ B, C ∪ D)` -/

/-- The map of singular pairs `TopCat.smallSingularPair hCA hDB ⟶ (A ∪ B, C ∪ D)`, given by
`TopCat.smallSingularSubcomplexToUnion` on both components. -/
abbrev smallSingularPairToUnion :
    smallSingularPair hCA hDB ⟶
      TopPair.toSSetPair.obj (TopPair.ofInclusion (Set.union_subset_union hCA hDB)) :=
  SSetPair.homMk (smallSingularSubcomplexToUnion C D) (smallSingularSubcomplexToUnion A B) (by
    -- Stated with the components written out, so that it typechecks without unfolding the pairs.
    have h : smallSingularSubcomplexToUnion C D ≫
        toSSet.map (ofHom (ContinuousMap.inclusion (Set.union_subset_union hCA hDB))) =
          SSet.Subcomplex.homOfLE (smallSingularSubcomplex_mono X
              (U := ![C, D]) (U' := ![A, B]) (Fin.forall_fin_two.2 ⟨hCA, hDB⟩)) ≫
            smallSingularSubcomplexToUnion A B := by
      refine (cancel_mono (toSSet.map (ofHom (ContinuousMap.subtypeVal (A ∪ B))))).1 ?_
      rw [Category.assoc, Category.assoc, smallSingularSubcomplexToUnion_comp,
        SSet.Subcomplex.homOfLE_ι, ← Functor.map_comp, ← TopCat.ofHom_comp,
        ContinuousMap.subtypeVal_comp_inclusion]
      exact smallSingularSubcomplexToUnion_comp C D
    exact h)

/-- Followed by `TopCat.smallSingularPairToUnion`, the map `TopCat.toSmallSingularPair` is the map
of singular pairs induced by the inclusion `(A₁, C₁) ⟶ (A ∪ B, C ∪ D)`. -/
lemma toSmallSingularPair_comp_smallSingularPairToUnion {A₁ C₁ : Set X} (h₁ : C₁ ⊆ A₁)
    {i : Fin 2} (hA : A₁ ⊆ ![A, B] i) (hC : C₁ ⊆ ![C, D] i) (hA' : A₁ ⊆ A ∪ B)
    (hC' : C₁ ⊆ C ∪ D) :
    toSmallSingularPair hCA hDB h₁ hA hC ≫ smallSingularPairToUnion hCA hDB =
      TopPair.toSSetPair.map (TopPair.ofInclusionMap h₁ (Set.union_subset_union hCA hDB)
        (ContinuousMap.inclusion hA') fun _ hx ↦ hC' hx) := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · rw [MorphismProperty.Comma.comp_left,
      TopPair.toSSetPair_map_ofInclusionMap_inclusion_left _ _ _ _ hC']
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion C D hC hC'
  · rw [MorphismProperty.Comma.comp_right, TopPair.toSSetPair_map_ofInclusionMap_inclusion_right]
    exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexToUnion A B hA hA'

variable (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B)))
  (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B))) (hC : IsOpen ((↑) ⁻¹' C : Set ↥(C ∪ D)))
  (hD : IsOpen ((↑) ⁻¹' D : Set ↥(C ∪ D)))

include hA hB hC hD in
/-- The relative homology of `TopCat.smallSingularPair hCA hDB` is identified with that of
`(A ∪ B, C ∪ D)` by `TopCat.smallSingularPairToUnion`. -/
lemma isIso_homologyMap_smallSingularPairToUnion (n : ℕ) :
    IsIso (SSetPair.homologyMap (smallSingularPairToUnion hCA hDB) R n) := by
  have : QuasiIso (SSet.chainComplexMap (smallSingularPairToUnion hCA hDB).left R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplexToUnion R C D hC hD
  have : QuasiIso (SSet.chainComplexMap (smallSingularPairToUnion hCA hDB).right R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplexToUnion R A B hA hB
  exact SSetPair.isIso_homologyMap_of_quasiIso _ R n

private lemma pairMayerVietorisToBiprod_eq (n : ℕ) :
    pairMayerVietorisToBiprod R hCA hDB n =
      SSetPair.mayerVietorisToBiprod R
        (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
          (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx))
        (TopPair.toSSetPair.map (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
          (ContinuousMap.inclusion Set.inter_subset_right)
            fun _ hx ↦ Set.inter_subset_right hx)) n := by
  ext <;> simp [pairMayerVietorisToBiprod]

private lemma mayerVietorisFromBiprod_comp_homologyMap_smallSingularPairToUnion (n : ℕ) :
    SSetPair.mayerVietorisFromBiprod R
        (toSmallSingularPair hCA hDB hCA (i := 0) (Matrix.cons_val_zero A ![B]).superset
          (Matrix.cons_val_zero C ![D]).superset)
        (toSmallSingularPair hCA hDB hDB (i := 1)
          ((Matrix.cons_val_one A ![B]).trans (Matrix.cons_val_zero B ![])).superset
          ((Matrix.cons_val_one C ![D]).trans (Matrix.cons_val_zero D ![])).superset) n ≫
      SSetPair.homologyMap (smallSingularPairToUnion hCA hDB) R n =
    pairMayerVietorisFromBiprod R hCA hDB n := by
  apply biprod.hom_ext'
  · rw [SSetPair.inl_mayerVietorisFromBiprod_assoc, ← SSetPair.homologyMap_comp,
      toSmallSingularPair_comp_smallSingularPairToUnion _ _ _ _ _ Set.subset_union_left
        Set.subset_union_left,
      inl_pairMayerVietorisFromBiprod]
  · rw [SSetPair.inr_mayerVietorisFromBiprod_assoc, ← SSetPair.homologyMap_comp,
      toSmallSingularPair_comp_smallSingularPairToUnion _ _ _ _ _ Set.subset_union_right
        Set.subset_union_right,
      inr_pairMayerVietorisFromBiprod]

/-! #### The long exact sequence -/

/-- The first two maps of the Mayer–Vietoris sequence of two pairs compose to zero. -/
@[reassoc (attr := simp)]
lemma pairMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    pairMayerVietorisToBiprod R hCA hDB n ≫ pairMayerVietorisFromBiprod R hCA hDB n = 0 := by
  rw [pairMayerVietorisToBiprod_eq,
    ← mayerVietorisFromBiprod_comp_homologyMap_smallSingularPairToUnion,
    SSetPair.mayerVietorisToBiprod_fromBiprod_assoc R
      (MorphismProperty.Arrow.Hom.ext (isPushout_toSmallSingularPair_left hCA hDB).w
        (isPushout_toSmallSingularPair_right hCA hDB).w), zero_comp]

/-- The connecting morphism `Hₙ(A ∪ B, C ∪ D) ⟶ Hₘ(A ∩ B, C ∩ D)`, `m + 1 = n`, of the
Mayer–Vietoris sequence of the pairs `(A, C)` and `(B, D)`, for `A` and `B` open in `A ∪ B` and
`C` and `D` open in `C ∪ D`. It is the connecting morphism of the Mayer–Vietoris sequence of the
singular pairs of `A ∩ B`, `A`, `B` and of the singular simplices of `X` lying in `A` or in `B`
(relative to those lying in `C` or in `D`), precomposed with the inverse of the small-chain
isomorphism identifying the last of these with `Hₙ(A ∪ B, C ∪ D)`. -/
def pairMayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularHomology R n ⟶
      (TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).singularHomology R m :=
  have := isIso_homologyMap_smallSingularPairToUnion R hCA hDB hA hB hC hD n
  inv (SSetPair.homologyMap (smallSingularPairToUnion hCA hDB) R n) ≫
    SSetPair.mayerVietorisδ R (isPushout_toSmallSingularPair_left hCA hDB)
      (isPushout_toSmallSingularPair_right hCA hDB) n m h

private lemma homologyMap_smallSingularPairToUnion_comp_pairMayerVietorisδ (n m : ℕ)
    (h : m + 1 = n := by lia) :
    SSetPair.homologyMap (smallSingularPairToUnion hCA hDB) R n ≫
        pairMayerVietorisδ R hCA hDB hA hB hC hD n m h =
      SSetPair.mayerVietorisδ R (isPushout_toSmallSingularPair_left hCA hDB)
        (isPushout_toSmallSingularPair_right hCA hDB) n m h := by
  have := isIso_homologyMap_smallSingularPairToUnion R hCA hDB hA hB hC hD n
  rw [pairMayerVietorisδ, IsIso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma pairMayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    pairMayerVietorisδ R hCA hDB hA hB hC hD n m h ≫ pairMayerVietorisToBiprod R hCA hDB m = 0 := by
  rw [pairMayerVietorisδ, Category.assoc, pairMayerVietorisToBiprod_eq,
    SSetPair.mayerVietorisδ_toBiprod R _ _ n m h, comp_zero]

@[reassoc (attr := simp)]
lemma pairMayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    pairMayerVietorisFromBiprod R hCA hDB n ≫
      pairMayerVietorisδ R hCA hDB hA hB hC hD n m h = 0 := by
  rw [← mayerVietorisFromBiprod_comp_homologyMap_smallSingularPairToUnion, Category.assoc,
    homologyMap_smallSingularPairToUnion_comp_pairMayerVietorisδ R hCA hDB hA hB hC hD n m h,
    SSetPair.mayerVietorisFromBiprod_δ R _ _ n m h]

/-- **Exactness of the Mayer–Vietoris sequence of two pairs at `Hₘ(A ∩ B, C ∩ D)`.** -/
lemma pairMayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (pairMayerVietorisδ_toBiprod R hCA hDB hA hB hC hD n m h)).Exact := by
  have := isIso_homologyMap_smallSingularPairToUnion R hCA hDB hA hB hC hD n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietoris_exact₁ R (isPushout_toSmallSingularPair_left hCA hDB)
      (isPushout_toSmallSingularPair_right hCA hDB) n m h)
  refine ShortComplex.isoMk (asIso (SSetPair.homologyMap (smallSingularPairToUnion hCA hDB) R n))
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [homologyMap_smallSingularPairToUnion_comp_pairMayerVietorisδ R hCA hDB hA hB hC hD n m h]
  · simp [pairMayerVietorisToBiprod_eq]

include hA hB hC hD in
/-- **Exactness of the Mayer–Vietoris sequence of two pairs at `Hₙ(A, C) ⊞ Hₙ(B, D)`.** -/
lemma pairMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (pairMayerVietorisToBiprod_fromBiprod R hCA hDB n)).Exact := by
  have := isIso_homologyMap_smallSingularPairToUnion R hCA hDB hA hB hC hD n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietoris_exact₂ R (isPushout_toSmallSingularPair_left hCA hDB)
      (isPushout_toSmallSingularPair_right hCA hDB) n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (asIso (SSetPair.homologyMap (smallSingularPairToUnion hCA hDB) R n)) ?_ ?_
  · simp [pairMayerVietorisToBiprod_eq]
  · simp [mayerVietorisFromBiprod_comp_homologyMap_smallSingularPairToUnion]

/-- **Exactness of the Mayer–Vietoris sequence of two pairs at `Hₙ(A ∪ B, C ∪ D)`.** -/
lemma pairMayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (pairMayerVietorisFromBiprod_δ R hCA hDB hA hB hC hD n m h)).Exact := by
  have := isIso_homologyMap_smallSingularPairToUnion R hCA hDB hA hB hC hD n
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSetPair.mayerVietoris_exact₃ R (isPushout_toSmallSingularPair_left hCA hDB)
      (isPushout_toSmallSingularPair_right hCA hDB) n m h)
  refine ShortComplex.isoMk (Iso.refl _)
    (asIso (SSetPair.homologyMap (smallSingularPairToUnion hCA hDB) R n)) (Iso.refl _) ?_ ?_
  · simp [mayerVietorisFromBiprod_comp_homologyMap_smallSingularPairToUnion]
  · simp [homologyMap_smallSingularPairToUnion_comp_pairMayerVietorisδ R hCA hDB hA hB hC hD n m h]

include hA hB hC hD in
/-- If `Hₖ₊₁(A ∪ B, C ∪ D)` vanishes, the first map `Hₖ(A ∩ B, C ∩ D) ⟶ Hₖ(A, C) ⊞ Hₖ(B, D)` of
the Mayer–Vietoris sequence of two pairs is a monomorphism. -/
lemma mono_pairMayerVietorisToBiprod {k : ℕ}
    (h : IsZero ((TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularHomology R
      (k + 1))) :
    Mono (pairMayerVietorisToBiprod R hCA hDB k) :=
  (pairMayerVietoris_exact₁ R hCA hDB hA hB hC hD (k + 1) k).mono_g (h.eq_of_src _ _)

include hA hB hC hD in
/-- The map `H₀(A, C) ⊞ H₀(B, D) ⟶ H₀(A ∪ B, C ∪ D)` at the end of the Mayer–Vietoris sequence of
two pairs is an epimorphism. -/
lemma epi_pairMayerVietorisFromBiprod_zero : Epi (pairMayerVietorisFromBiprod R hCA hDB 0) := by
  have := isIso_homologyMap_smallSingularPairToUnion R hCA hDB hA hB hC hD 0
  have := SSetPair.epi_mayerVietorisFromBiprod_zero R (isPushout_toSmallSingularPair_left hCA hDB)
    (isPushout_toSmallSingularPair_right hCA hDB)
  rw [← mayerVietorisFromBiprod_comp_homologyMap_smallSingularPairToUnion]
  exact epi_comp _ _

include hA hB hC hD in
/-- **Vanishing propagates along the Mayer–Vietoris sequence of two pairs**: if `Hₙ(A, C)` and
`Hₙ(B, D)` vanish, and so does `Hₙ₋₁(A ∩ B, C ∩ D)` when `n` is positive, then `Hₙ(A ∪ B, C ∪ D)`
vanishes. -/
lemma isZero_singularHomology_ofInclusion_union {n : ℕ}
    (hAC : IsZero ((TopPair.ofInclusion hCA).singularHomology R n))
    (hBD : IsZero ((TopPair.ofInclusion hDB).singularHomology R n))
    (hABCD : ∀ m, m + 1 = n →
      IsZero ((TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).singularHomology R m)) :
    IsZero ((TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularHomology R n) := by
  have hbiprod : IsZero ((TopPair.ofInclusion hCA).singularHomology R n ⊞
      (TopPair.ofInclusion hDB).singularHomology R n) := (biprod_isZero_iff _ _).2 ⟨hAC, hBD⟩
  cases n with
  | zero =>
    have := epi_pairMayerVietorisFromBiprod_zero R hCA hDB hA hB hC hD
    exact IsZero.of_epi_eq_zero (pairMayerVietorisFromBiprod R hCA hDB 0) (hbiprod.eq_of_src _ _)
  | succ m =>
    exact (pairMayerVietoris_exact₃ R hCA hDB hA hB hC hD (m + 1) m).isZero_of_both_isZero hbiprod
      (hABCD m rfl)

end Pair

end TopCat
