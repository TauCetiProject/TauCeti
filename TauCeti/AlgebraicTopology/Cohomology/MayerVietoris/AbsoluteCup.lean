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
`(V, ∅)`, using that the maps `Hⁿ(-, -) ⟶ Hⁿ(-)` from relative to absolute cohomology carry the
connecting morphism of two pairs to the absolute one
(`TopCat.singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ`).

## Main results

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

namespace TopCat

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
    (singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ T k L hAU hBV
      isOpen_preimage_empty isOpen_preimage_empty hU hV hUV n m hm)
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
