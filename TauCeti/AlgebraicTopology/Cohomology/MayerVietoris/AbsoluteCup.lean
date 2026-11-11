/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Cup
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair

/-!
# The absolute Mayer–Vietoris connecting morphism and cup products

Let `U` and `V` be open subsets of a space `X` with `U ∪ V = X`. This file proves that cupping
with a class `b ∈ H^q(X)` intertwines the connecting morphism `δ : Hᵖ(U ∩ V) ⟶ Hᵖ⁺¹(X)` of the
Mayer–Vietoris sequence of the cover `{U, V}` (`TopCat.singularCohomologyMayerVietorisδ`) with
itself: for `a ∈ Hᵖ(U ∩ V)`,

`δ (a ⌣ b|_{U ∩ V}) = δ a ⌣ b`

(`TopCat.singularCohomologyMayerVietorisδ_singularCup`). There is no sign, since `a` stands to the
left of `b`. For a map `p : E ⟶ B` and an open cover `{U, V}` of `B`, this is the compatibility of
the Leray–Hirsch map `a ↦ p^*a ⌣ e` with the Mayer–Vietoris sequences of `{U, V}` and of
`{p⁻¹ U, p⁻¹ V}`, which the proof that it is bijective by induction over open sets uses.

The proof deduces it from the corresponding statement for the Mayer–Vietoris sequence of two
pairs, `TopCat.singularCohomologyPairMayerVietorisδ_singularCup`, applied to the pairs `(U, ∅)` and
`(V, ∅)`. For this, the connecting morphism of two pairs `(U, A)` and `(V, B)` is compared with the
absolute one: the maps `Hⁿ(-, -) ⟶ Hⁿ(-)` from relative to absolute cohomology carry the first to
the second (`TopCat.singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ`). At the level of
simplicial sets, the quotient maps from ambient to relative chains form a morphism from the relative
cochain Mayer–Vietoris short exact sequence of a square of pairs to the absolute one of its square
of ambient simplicial sets, so the connecting morphisms commute with them
(`SSetPair.mayerVietorisCochainδ_comp_homologyMap_chainComplexπ`).

## Main results

* `SSetPair.mayerVietorisCochainδ_comp_homologyMap_chainComplexπ`: the relative cochain
  Mayer–Vietoris connecting morphism of a square of pairs of simplicial sets is carried to the
  absolute one of its square of ambient simplicial sets.
* `TopCat.singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ`: the connecting morphism
  of the Mayer–Vietoris sequence of two pairs is carried to the absolute one.
* `TopCat.singularCohomologyMayerVietorisδ_singularCup`: `δ (a ⌣ b|_{U ∩ V}) = δ a ⌣ b`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (the Mayer–Vietoris sequences in cohomology) and Section 4.D (the Leray–Hirsch
  theorem).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite TauCeti.ChainComplex

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {P₁ P₂ P₃ P₄ : SSetPair.{w}} {t : P₁ ⟶ P₂} {l : P₁ ⟶ P₃} {r : P₂ ⟶ P₄} {b : P₃ ⟶ P₄}
  (sqL : IsPushout t.left l.left r.left b.left) [Mono t.left]
  (sqR : IsPushout t.right l.right r.right b.right) [Mono t.right]

/-- The map `Hom(C(P), M) ⟶ Hom(C(P.right), M)` from relative to ambient cochains of a pair of
simplicial sets: precomposition with the quotient map from ambient to relative chains. -/
abbrev cochainComplexπ (P : SSetPair.{w}) :
    (P.chainComplex R).linearYonedaObj k M ⟶ (P.right.chainComplex R).linearYonedaObj k M :=
  (linearYonedaFunctor k M).map (P.chainComplexπ R).op

/-- **The relative and absolute cochain Mayer–Vietoris connecting morphisms.** For a square of
pairs of simplicial sets whose squares of subobjects and of ambient simplicial sets are pushouts
with monomorphic top maps, the maps from relative to absolute cohomology induced by the quotient
maps from ambient to relative chains carry the relative connecting morphism `Hⁿ(P₁) ⟶ Hᵐ(P₄)` to
the absolute one of the square of ambient simplicial sets. -/
@[reassoc]
lemma mayerVietorisCochainδ_comp_homologyMap_chainComplexπ (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainδ R k M sqL sqR n m h ≫
        HomologicalComplex.homologyMap (cochainComplexπ R k M P₄) m =
      HomologicalComplex.homologyMap (cochainComplexπ R k M P₁) n ≫
        SSet.mayerVietorisCochainδ R k M sqR n m h := by
  -- The quotient maps from ambient to relative chains, on cochains.
  have hπ {P Q : SSetPair.{w}} (f : P ⟶ Q) :
      cochainComplexπ R k M Q ≫ SSet.cochainComplexMap f.right =
        cochainComplexMap f ≫ cochainComplexπ R k M P := by
    have h := congrArg (fun φ ↦ (linearYonedaFunctor k M).map φ.op)
      (chainComplexπ_naturality R f)
    simp only [op_comp, Functor.map_comp] at h
    exact h
  let ψ : mayerVietorisCochainShortComplex R k M (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w) ⟶
      SSet.mayerVietorisCochainShortComplex R k M sqR.toCommSq :=
    { τ₁ := cochainComplexπ R k M P₄
      τ₂ := biprod.map (cochainComplexπ R k M P₂) (cochainComplexπ R k M P₃)
      τ₃ := cochainComplexπ R k M P₁
      comm₁₂ := by
        apply biprod.hom_ext
        · erw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst,
            biprod.lift_fst_assoc]
          exact hπ r
        · erw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd,
            biprod.lift_snd_assoc]
          exact hπ b
      comm₂₃ := by
        apply biprod.hom_ext'
        · erw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
          exact hπ t
        · erw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, Preadditive.neg_comp,
            Preadditive.comp_neg]
          exact congrArg Neg.neg (hπ l) }
  rw [mayerVietorisCochainδ_def R k M sqL sqR n m h, SSet.mayerVietorisCochainδ_def R k M sqR n m h]
  exact HomologicalComplex.HomologySequence.δ_naturality ψ _ _ n m (by simpa)

end SSetPair

namespace TopCat

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_left
  TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

section Comparison

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {X : TopCat.{w}}
  {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
  {A B : Set X} (hAU : A ⊆ U) (hBV : B ⊆ V)
  (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B))) (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B)))

/-- The absolute cochain Mayer–Vietoris connecting morphism of a pushout square of simplicial sets
only depends on its maps. -/
private lemma mayerVietorisCochainδ_congr {X₁ X₂ X₃ X₄ : SSet.{w}} {t t' : X₁ ⟶ X₂}
    {l l' : X₁ ⟶ X₃} {r r' : X₂ ⟶ X₄} {b b' : X₃ ⟶ X₄} (sq : IsPushout t l r b) [Mono t]
    (sq' : IsPushout t' l' r' b') (ht : t = t') (hl : l = l') (hr : r = r')
    (hb : b = b') (n m : ℕ) (h : n + 1 = m) :
    SSet.mayerVietorisCochainδ R k M sq n m h =
      haveI : Mono t' := ht ▸ inferInstance
      SSet.mayerVietorisCochainδ R k M sq' n m h := by
  subst ht hl hr hb
  rfl

/-- **The connecting morphism of two pairs and the absolute one.** For an open cover of `X` by `U`
and `V` and subsets `A ⊆ U` and `B ⊆ V` open in `A ∪ B`, the maps from relative to absolute
cohomology carry the connecting morphism `Hⁿ(U ∩ V, A ∩ B) ⟶ Hᵐ(U ∪ V, A ∪ B)` of the
Mayer–Vietoris sequence of the pairs `(U, A)` and `(V, B)` to the connecting morphism
`Hⁿ(U ∩ V) ⟶ Hᵐ(X)` of the cover `{U, V}`, followed by the restriction to `U ∪ V`. -/
@[reassoc]
lemma singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ (n m : ℕ)
    (h : n + 1 = m := by lia) :
    singularCohomologyPairMayerVietorisδ R k M hAU hBV (hU.preimage continuous_subtype_val)
        (hV.preimage continuous_subtype_val) hA hB n m h ≫
      (TopPair.ofInclusion (Set.union_subset_union hAU hBV)).singularCohomologyπ R k M m =
    (TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)).singularCohomologyπ R k M n ≫
      singularCohomologyMayerVietorisδ R k M hU hV hUV n m h ≫
        TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (U ∪ V))) m := by
  -- Both sides are compared after restriction to the singular simplices lying in `U` or in `V`,
  -- which is an isomorphism from the cohomology of `U ∪ V`.
  have := quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion R k M U V
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
  refine (cancel_mono (HomologicalComplex.homologyMap (SSet.cochainComplexMap (R := R) (k := k)
    (M := M) (smallSingularSubcomplexToUnion U V)) m)).1 ?_
  -- The left side: naturality of the quotient map from ambient to relative chains.
  have hπ : (TopPair.ofInclusion (Set.union_subset_union hAU hBV)).singularCohomologyπ R k M m ≫
      HomologicalComplex.homologyMap (SSet.cochainComplexMap (R := R) (k := k) (M := M)
        (smallSingularSubcomplexToUnion U V)) m =
      HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
          (smallSingularPairToUnion hAU hBV)) m ≫
        HomologicalComplex.homologyMap (SSetPair.cochainComplexπ R k M
          (smallSingularPair hAU hBV)) m := by
    have hc : ((TopPair.ofInclusion
        (Set.union_subset_union hAU hBV)).singularCochainComplexShortComplex R k M).f ≫
        SSet.cochainComplexMap (R := R) (k := k) (M := M)
          (smallSingularSubcomplexToUnion U V) =
        SSetPair.cochainComplexMap (R := R) (k := k) (M := M) (smallSingularPairToUnion hAU hBV) ≫
          SSetPair.cochainComplexπ R k M (smallSingularPair hAU hBV) := by
      have h := congrArg (fun φ ↦ (linearYonedaFunctor k M).map φ.op)
        (SSetPair.chainComplexπ_naturality R (smallSingularPairToUnion hAU hBV))
      simp only [op_comp, Functor.map_comp] at h
      rw [TopPair.singularCochainComplexShortComplex_f_eq]
      exact h
    exact (HomologicalComplex.homologyMap_comp _ _ m).symm.trans
      ((congrArg (HomologicalComplex.homologyMap · m) hc).trans
        (HomologicalComplex.homologyMap_comp _ _ m))
  -- The right side: restricting from `X` to `U ∪ V` and then to the small simplices is restricting
  -- from `X` to the small simplices.
  have hres : TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofHom (ContinuousMap.subtypeVal (U ∪ V))) m ≫
      HomologicalComplex.homologyMap (SSet.cochainComplexMap (R := R) (k := k) (M := M)
        (smallSingularSubcomplexToUnion U V)) m =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (X.smallSingularSubcomplex ![U, V]).ι) m := by
    rw [TopCat.singularCohomologyMap, ← HomologicalComplex.homologyMap_comp,
      ← SSet.cochainComplexMap_comp, smallSingularSubcomplexToUnion_comp]
  have h₁ := singularCohomologyPairMayerVietorisδ_comp_homologyMap R k M hAU hBV
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) hA hB n m h
  have h₂ := SSetPair.mayerVietorisCochainδ_comp_homologyMap_chainComplexπ R k M
    (isPushout_toSmallSingularPair_left hAU hBV) (isPushout_toSmallSingularPair_right hAU hBV) n m h
  have h₃ : SSet.mayerVietorisCochainδ R k M (isPushout_toSmallSingularPair_right hAU hBV) n m h =
      SSet.mayerVietorisCochainδ R k M (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h :=
    mayerVietorisCochainδ_congr R k M (isPushout_toSmallSingularPair_right hAU hBV)
      (isPushout_toSSet_inter_smallSingularSubcomplex U V)
      (TopPair.toSSetPair_map_ofInclusionMap_inclusion_right _ _ _ _)
      (TopPair.toSSetPair_map_ofInclusionMap_inclusion_right _ _ _ _) rfl rfl n m h
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hπ).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h₁).trans ?_
  refine h₂.trans ?_
  refine (congrArg (_ ≫ ·) h₃).trans ?_
  refine (congrArg (_ ≫ ·)
    (singularCohomologyMayerVietorisδ_comp_homologyMap R k M hU hV hUV n m h).symm).trans ?_
  refine (congrArg (fun φ ↦ _ ≫ _ ≫ φ) hres.symm).trans ?_
  simp only [Category.assoc]
  rfl

end Comparison

/-! ### The connecting morphism and the cup product -/

section Cup

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C}
  (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C] {X : TopCat.{w}}
  {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- The empty subspace of `∅ ∪ ∅` is open. -/
private lemma isOpen_preimage_empty : IsOpen ((↑) ⁻¹' (∅ : Set X) : Set ↥((∅ : Set X) ∪ ∅)) := by
  rw [Set.preimage_empty]
  exact isOpen_empty

private instance isEmpty_snd_ofInclusion_empty_union :
    IsEmpty (TopPair.ofInclusion (Set.union_subset_union (Set.empty_subset U)
      (Set.empty_subset V))).snd :=
  ⟨fun x ↦ by simpa using x.2⟩

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
include hUV in
/-- For `U ∪ V = X`, restriction from `X` to `U ∪ V` is injective on cohomology. -/
private lemma injective_singularCohomologyMap_subtypeVal_union {R M : C} (n : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofHom (ContinuousMap.subtypeVal (U ∪ V))) n) := by
  let σ : X ⟶ of ↥(U ∪ V) := ofHom ⟨fun x ↦ ⟨x, hUV ▸ Set.mem_univ x⟩, by fun_prop⟩
  have hσ : σ ≫ ofHom (ContinuousMap.subtypeVal (U ∪ V)) = 𝟙 X := rfl
  refine Function.LeftInverse.injective (g := TopCat.singularCohomologyMap σ n) fun x ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hσ,
    TopCat.singularCohomologyMap_id]
  rfl

/-- **The Mayer–Vietoris connecting morphism and the cup product.** Let `U` and `V` be open
subsets covering `X`. For `a ∈ Hᵖ(U ∩ V)` and `b ∈ H^q(X)`, the connecting morphism of the
Mayer–Vietoris sequence of the cover `{U, V}` sends `a ⌣ b|_{U ∩ V}` to `δ a ⌣ b`. -/
theorem singularCohomologyMayerVietorisδ_singularCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    {p q n p' m : ℕ} (h : p + q = n) (hp : p + 1 = p') (hm : n + 1 = m) (h' : p' + q = m)
    (a : (of ↥(U ∩ V)).singularCohomology R k M p) (b : X.singularCohomology S k N q) :
    singularCohomologyMayerVietorisδ T k L hU hV hUV n m hm
        ((of ↥(U ∩ V)).singularCup k u μ p q n h a
          (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (U ∩ V))) q b)) =
      X.singularCup k u μ p' q m h'
        (singularCohomologyMayerVietorisδ R k M hU hV hUV p p' hp a) b := by
  -- Work with the pairs `(U, ∅)` and `(V, ∅)`, whose relative cohomology is absolute cohomology.
  have hAU : (∅ : Set X) ⊆ U := Set.empty_subset U
  have hBV : (∅ : Set X) ⊆ V := Set.empty_subset V
  let j : of ↥(U ∪ V) ⟶ X := ofHom (ContinuousMap.subtypeVal (U ∪ V))
  let πU := (TopPair.ofInclusion (Set.union_subset_union hAU hBV)).singularCohomologyπ S k N q
  let ι := interToUnionMap hAU hBV
  -- The class `b` restricted to `U ∪ V`, as a class of the pair `(U ∪ V, ∅)`.
  let b' := inv πU (TopCat.singularCohomologyMap j q b)
  have hb' : πU b' = TopCat.singularCohomologyMap j q b :=
    (ConcreteCategory.comp_apply (inv πU) πU _).symm.trans
      (by rw [IsIso.inv_hom_id]; rfl)
  have hfst : TopPair.Hom.fst ι ≫ j = ofHom (ContinuousMap.subtypeVal (U ∩ V)) := by
    ext x
    exact congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)
  -- Its restriction to `(U ∩ V, ∅)` maps to the restriction of `b` to `U ∩ V`.
  have hι : (TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)).singularCohomologyπ S k N q
      (TopPair.singularCohomologyMap ι q b') =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (U ∩ V))) q b :=
    (ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality ι q) b').symm.trans <|
      (congrArg (TopCat.singularCohomologyMap (TopPair.Hom.fst ι) q) hb').trans <|
        (ConcreteCategory.comp_apply _ _ _).symm.trans
          (ConcreteCategory.congr_hom
            ((TopCat.singularCohomologyMap_comp (TopPair.Hom.fst ι) j q).symm.trans
              (congrArg (TopCat.singularCohomologyMap · q) hfst)) b)
  apply injective_singularCohomologyMap_subtypeVal_union k hUV
  -- Both sides are the images of the two sides of the corresponding identity for the pairs.
  have hpair := singularCohomologyPairMayerVietorisδ_singularCup (A := ∅) (B := ∅) k hU hV hUV
    hAU hBV
    isOpen_preimage_empty isOpen_preimage_empty u μ h hp hm h' a b'
  have hcomp := ConcreteCategory.congr_hom
    (singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ (A := ∅) (B := ∅) T k L hU hV
      hUV hAU hBV
      isOpen_preimage_empty isOpen_preimage_empty n m hm)
    ((TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)).singularCup k u μ p q n h a
      (TopPair.singularCohomologyMap ι q b'))
  refine (congrArg (fun z ↦ TopCat.singularCohomologyMap j m
    (singularCohomologyMayerVietorisδ T k L hU hV hUV n m hm
      ((of ↥(U ∩ V)).singularCup k u μ p q n h a z))) hι.symm).trans ?_
  refine (congrArg (fun z ↦ TopCat.singularCohomologyMap j m
    (singularCohomologyMayerVietorisδ T k L hU hV hUV n m hm z))
    (TopPair.singularCohomologyπ_singularCup k
      (TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)) u μ p q n h a
      (TopPair.singularCohomologyMap ι q b')).symm).trans ?_
  refine hcomp.symm.trans ?_
  refine (congrArg _ hpair).trans ?_
  refine (TopPair.singularCohomologyπ_singularCup k
    (TopPair.ofInclusion (Set.union_subset_union hAU hBV)) u μ p' q m h'
    (TopCat.singularCohomologyMap j p' (singularCohomologyMayerVietorisδ R k M hU hV hUV p p' hp a))
    b').trans ?_
  refine (congrArg _ hb').trans ?_
  exact singularCup_naturality j k u μ p' q m h' _ _

end Cup

end TopCat
