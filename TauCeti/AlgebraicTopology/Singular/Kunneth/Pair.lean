/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Relative

/-!
# The shuffle map of a product of two pairs

Let `A ⊆ X` and `B ⊆ Y` be subsets of topological spaces, and write `A × Y` and `X × B` for the
preimages of `A` and `B` under the projections of `X × Y`. The shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` (`TopCat.shuffle`) carries `C(A; R) ⊗ C(Y; S)` into the chains
of `A × Y` and `C(X; R) ⊗ C(B; S)` into the chains of `X × B`. So it descends to the **shuffle map
of the product of the pairs** `(X, A)` and `(Y, B)` (`TopCat.shufflePair`)

`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)`,

characterized by `(π ⊗ π) ≫ shufflePair = shuffle ≫ π`
(`TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair`). It is built from the
relative shuffle map `TopCat.shuffleRel` of `(X, A)` and `Y`: tensoring on the left with
`C(X, A; R)` preserves the short exact sequence `C(B) ⟶ C(Y) ⟶ C(Y, B)`, since the inclusion of
the singular chains of `B` splits in each degree, and the relative shuffle map followed by the
quotient modulo the chains of `A × Y ∪ X × B` vanishes on `C(X, A; R) ⊗ C(B; S)`.

It is natural in maps of pairs (`TopCat.shufflePair_naturality`). When `A` and `B` are open it is a
quasi-isomorphism (`TopCat.quasiIso_shufflePair`): this is the **relative Eilenberg–Zilber
theorem for a product of open pairs**. The tensored sequence maps to the singular chain sequence of
the triple `(X × Y, A × Y ∪ X × B, A × Y)`, by the relative shuffle maps of `(X, A)` with `B` and
with `Y` on the first two terms and by `shufflePair` on the third. The relative shuffle maps are
quasi-isomorphisms (`TopCat.quasiIso_shuffleRel`), and the first is followed by the inclusion of
pairs `(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)`, an excision since `A × Y` and `X × B` are open sets
covering the union, the first the subspace and the second the image. The five lemma concludes.
Openness is used only through this excision.

The map lives on simplicial singular chains, the chain model of the shuffle and
Alexander–Whitney maps (`TopCat.shuffle`, `TopCat.alexanderWhitney`). The relative homology of
`(X × Y, A × Y ∪ X × B)` is also reached through cubical chains, by the comparison
`TauCeti.cubicalChainComplexProdToSingular` behind `TauCeti.singularHomologyKunnethPair`; the two
chain-level constructions are not compared here.

## Main definitions

* `TopCat.shufflePair`: the shuffle map
  `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)` of a product of two pairs.

## Main results

* `TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair`: the shuffle map of a
  product of pairs is induced by the absolute shuffle map.
* `TopCat.shufflePair_naturality`: naturality in maps of both pairs.
* `TopCat.quasiIso_shufflePair`: the relative Eilenberg–Zilber theorem for a product of open
  pairs.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product `Hₚ(X, A) ⊗ H_q(Y, B) ⟶ Hₙ(X × Y, A × Y ∪ X × B)`.
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 3, excisive couples and the relative
  Eilenberg–Zilber theorem.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits
  AlgebraicTopology

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

section Construction

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- Tensoring on the left with `C(X, A; R)` preserves the short exact sequence
`C(B; S) ⟶ C(Y; S) ⟶ C(Y, B; S)` of singular chains of the pair `(Y, B)`, since the inclusion of
the singular chains of `B` splits in each degree. -/
theorem shortExact_tensorLeftShortComplex_singularChainComplexShortComplex :
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).ShortExact :=
  shortExact_tensorLeftShortComplex _
    ((TopPair.ofSubset B).shortExact_singularChainComplexShortComplex S)

/-- The inclusion of pairs `(X × Y, A × Y) ⟶ (X × Y, A × Y ∪ X × B)`, given by the identity of
`X × Y`. -/
abbrev preimageFstToUnion :
    TopPair.ofSubset (fst X Y ⁻¹' A) ⟶ TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) :=
  TopPair.ofSubsetMap (𝟙 _) fun _ hz ↦ Or.inl hz

omit [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- A map into `X × Y` with values in `A × Y ∪ X × B` induces the zero map into the relative
chains of `(X × Y, A × Y ∪ X × B)`. -/
private theorem chainComplexMap_comp_singularChainComplexπ_of_mem {Z : TopCat.{w}}
    (g : Z ⟶ X ⊗ Y) (hg : ∀ z, g z ∈ fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (M : C) :
    SSet.chainComplexMap (toSSet.map g) M ≫
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ M = 0 := by
  let P := TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
  let ℓ : Z ⟶ P.snd := TopCat.ofHom ⟨fun z ↦ ⟨g z, hg z⟩, by fun_prop⟩
  have h : SSet.chainComplexMap (toSSet.map g) M =
      SSet.chainComplexMap (toSSet.map ℓ) M ≫ SSet.chainComplexMap (toSSet.map P.map) M := by
    -- `g` is `ℓ` followed by the inclusion of the subspace, by definition of `ℓ`.
    exact (toSSet ⋙ (SSet.chainComplexFunctor C).obj M).map_comp ℓ P.map
  rw [h]
  -- `rw [Category.assoc]` does not apply: the ambient chains of the pair appear both as those of
  -- `P.fst` and as those of `X ⊗ Y`, which agree only up to unfolding `TopPair.ofSubset`.
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (TopPair.chainComplexMap_comp_singularChainComplexπ P M)).trans comp_zero)

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The projection `C(X; R) ⟶ C(X, A; R)` and the inclusion `C(B; S) ⟶ C(Y; S)`, tensored in the
two variables, commute. -/
private theorem singularChainComplexπ_tensorHom_comp_tensorHom_chainComplexMap :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)) ≫
      (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) =
    (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) ≫
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) := by
  -- This is the naturality of the map of fixed-left totalizations induced by the projection.
  have h := ((curriedTensor C).mapBifunctorLeftMap (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    ((TopPair.ofSubset A).singularChainComplexπ R)).naturality
      (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S)
  rw [Functor.mapBifunctorLeftMap_app, Functor.mapBifunctorLeftMap_app,
    Functor.mapBifunctorLeft_map, Functor.mapBifunctorLeft_map] at h
  exact h.symm

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The projection `C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S)` is the projection in the first
variable followed by the projection in the second. -/
private theorem singularChainComplexπ_tensorHom_singularChainComplexπ_eq :
    (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
  (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _).symm (Category.id_comp _).symm).trans
    (mapBifunctorMap_comp _ _ _ _ _ _)

omit [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The quotient map `(X × Y, A × Y) ⟶ (X × Y, A × Y ∪ X × B)` turns the projection to the
relative chains of `(X × Y, A × Y)` into the projection to those of `(X × Y, A × Y ∪ X × B)`. -/
@[reassoc]
private theorem singularChainComplexπ_preimageFstToUnion (M : C) :
    (TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplexπ M ≫
        TopPair.singularChainComplexMap (preimageFstToUnion X Y A B) M =
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ M := by
  have h₀ : TopPair.Hom.fst (preimageFstToUnion X Y A B) = 𝟙 (X ⊗ Y) :=
    TopPair.ofSubsetMap_fst _ _
  have h := TopPair.singularChainComplexπ_pair_naturality (preimageFstToUnion X Y A B) M
  simp only [h₀] at h
  have h₁ : SSet.chainComplexMap (toSSet.map (𝟙 (X ⊗ Y))) M = 𝟙 _ :=
    (toSSet ⋙ (SSet.chainComplexFunctor C).obj M).map_id (X ⊗ Y)
  exact h.symm.trans ((congrArg (· ≫ _) h₁).trans (Category.id_comp _))

/-- On `C(X; R) ⊗ C(Y; S)`, the relative shuffle map of `(X, A)` and `Y` followed by the quotient
modulo the chains of `A × Y ∪ X × B` is the shuffle map followed by the projection to the relative
chains of `(X × Y, A × Y ∪ X × B)`. -/
private theorem shuffleRel_preimageFstToUnion :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffleRel X Y A R S ≫
          TopPair.singularChainComplexMap (preimageFstToUnion X Y A B) (R ⊗ S) =
      shuffle X Y R S ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) :=
  (singularChainComplexπ_tensorHom_id_shuffleRel_assoc X Y A R S _).trans
    ((Category.assoc _ _ _).trans (congrArg (shuffle X Y R S ≫ ·)
      (singularChainComplexπ_preimageFstToUnion X Y A B (R ⊗ S))))

/-- The relative shuffle map of `(X, A)` and `Y`, followed by the quotient modulo the chains of
`A × Y ∪ X × B`, vanishes on `C(X, A; R) ⊗ C(B; S)`, which it carries into the chains of
`X × B`. -/
private theorem shuffleRel_cokernel_condition :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) ≫
      shuffleRel X Y A R S ≫ TopPair.singularChainComplexMap (preimageFstToUnion X Y A B) (R ⊗ S) =
        0 := by
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X
    (TopPair.ofSubset B).snd A R S
  have : Epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)) := hS.epi_g
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S))).1 ?_
  have h₂ := shuffle_naturality (𝟙 X) ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y)
    R S
  simp only [CategoryTheory.Functor.map_id] at h₂
  have hx := singularChainComplexπ_tensorHom_comp_tensorHom_chainComplexMap X Y A B R S
  have e₂ := shuffleRel_preimageFstToUnion X Y A B R S
  have e₃ := chainComplexMap_comp_singularChainComplexπ_of_mem X Y A B
    (𝟙 X ⊗ₘ ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y))
    (fun z ↦ Or.inr (Subtype.prop (z.2 : (TopPair.ofSubset B).snd))) (R ⊗ S)
  -- Move the projection past the inclusion of `C(B)` (`hx`), apply the relative shuffle map
  -- (`e₂`), and use naturality of the shuffle map (`h₂`) to factor through the chains of
  -- `X × B ⊆ A × Y ∪ X × B` (`e₃`). The chain complexes of `X` and `Y` appear in several forms
  -- that agree only up to unfolding, so the composites are reassociated by hand.
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₃).trans
          (comp_zero.trans comp_zero.symm)))))))

/-- **The shuffle map of a product of two pairs**,
`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)`, induced by the shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` on the quotients. It is characterized by
`TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair`, and is a
quasi-isomorphism when `A` and `B` are open (`TopCat.quasiIso_shufflePair`). -/
def shufflePair :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S) :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc (CokernelCofork.ofπ _ (shuffleRel_cokernel_condition X Y A B R S))

/-- On `C(X, A; R) ⊗ C(Y; S)` the shuffle map of the product of pairs is the relative shuffle map
of `(X, A)` and `Y`, followed by the quotient modulo the chains of `A × Y ∪ X × B`. -/
@[reassoc (attr := simp)]
theorem tensorHom_singularChainComplexπ_shufflePair :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shufflePair X Y A B R S =
      shuffleRel X Y A R S ≫
        TopPair.singularChainComplexMap (preimageFstToUnion X Y A B) (R ⊗ S) :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- **The shuffle map of a product of pairs is induced by the shuffle map**: on
`C(X; R) ⊗ C(Y; S)` it is the shuffle map followed by the projection to the relative chains of
`(X × Y, A × Y ∪ X × B)`. -/
@[reassoc (attr := simp)]
theorem singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shufflePair X Y A B R S =
      shuffle X Y R S ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) := by
  have h := singularChainComplexπ_tensorHom_singularChainComplexπ_eq X Y A B R S
  -- `rw [Category.assoc]` does not apply: the chains of `Y` appear both as those of `Y` and as the
  -- ambient chains of the pair `(Y, B)`, which agree only up to unfolding `TopPair.ofSubset`.
  exact (congrArg (· ≫ shufflePair X Y A B R S) h).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (tensorHom_singularChainComplexπ_shufflePair X Y A B R S)).trans
      (shuffleRel_preimageFstToUnion X Y A B R S)))

end Construction

section Naturality

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The projection `C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S)` is an epimorphism. -/
private theorem epi_singularChainComplexπ_tensorHom_singularChainComplexπ :
    Epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S) := by
  have h₁ := (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S).epi_g
  have h₂ := (shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S).epi_g
  have h := singularChainComplexπ_tensorHom_singularChainComplexπ_eq X Y A B R S
  rw [h]
  exact epi_comp' h₁ h₂

/-- **Naturality of the shuffle map of a product of pairs** in maps of pairs `(X, A) ⟶ (X', A')`
and `(Y, B) ⟶ (Y', B')`. -/
@[reassoc]
theorem shufflePair_naturality {X' Y' : TopCat.{w}} {A' : Set X'} {B' : Set Y'} (f : X ⟶ X')
    (hf : Set.MapsTo f A A') (g : Y ⟶ Y') (hg : Set.MapsTo g B B') :
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) ≫
          shufflePair X' Y' A' B' R S =
      shufflePair X Y A B R S ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S) := by
  have := epi_singularChainComplexπ_tensorHom_singularChainComplexπ X Y A B R S
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)).1 ?_
  have hπf := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  have hπg := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap g hg) S
  simp only [TopPair.ofSubsetMap_fst] at hπf hπg
  have h₁ : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫
          (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
            TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) =
      (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        ((TopPair.ofSubset A').singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B').singularChainComplexπ S) :=
    (mapBifunctorMap_comp _ _ _ _ _ _).symm.trans <|
      (congrArg₂ (· ⊗ₘ ·) hπf.symm hπg.symm).trans (mapBifunctorMap_comp _ _ _ _ _ _)
  have h₂ := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S)
  have hfst := TopPair.ofSubsetMap_fst (B := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (B' := fst X' Y' ⁻¹' A' ∪ snd X' Y' ⁻¹' B') (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)
  -- Both sides are the shuffle map followed by the map of pairs induced by `f × g`. The chain
  -- complexes of the pairs appear both as relative chains and as the chains of their ambient
  -- spaces, which agree only up to unfolding, so the composites are reassociated by `calc`.
  calc _ = (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        ((TopPair.ofSubset A').singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B').singularChainComplexπ S) ≫ shufflePair X' Y' A' B' R S :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans (Category.assoc _ _ _))
    _ = shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) ≫
        (TopPair.ofSubset (fst X' Y' ⁻¹' A' ∪ snd X' Y' ⁻¹' B')).singularChainComplexπ (R ⊗ S) :=
        (congrArg (_ ≫ ·)
          (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X' Y' A' B' R S)).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
            (shuffle_naturality f g R S)).trans (Category.assoc _ _ _)))
    _ = _ := (congrArg (fun φ ↦ shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map φ) (R ⊗ S) ≫
        (TopPair.ofSubset (fst X' Y' ⁻¹' A' ∪ snd X' Y' ⁻¹' B')).singularChainComplexπ (R ⊗ S))
          hfst.symm).trans <|
      (congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _)
          (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S).symm
            ).trans (Category.assoc _ _ _)))

end Naturality

section QuasiIso

open Topology

/-- The triple `(X × Y, A × Y ∪ X × B, A × Y)`, with `A × Y` and `X × B` the preimages of `A` and
`B` under the projections. -/
private abbrev prodUnionFstTriple : TauCeti.TopTriple.{w} :=
  TauCeti.TopTriple.ofSubset (X := X ⊗ Y) (A := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (B := fst X Y ⁻¹' A)
    Set.subset_union_left

/-- The pair `(X × Y, A × Y)` is the total pair of the triple `(X × Y, A × Y ∪ X × B, A × Y)`. -/
private abbrev prodUnionFstTotalPairIso :
    TopPair.ofSubset (fst X Y ⁻¹' A) ≅
      TauCeti.TopTriple.totalPair.obj (prodUnionFstTriple X Y A B) :=
  TauCeti.TopTriple.ofSubsetTotalPairIso (X := X ⊗ Y) Set.subset_union_left

/-- The inclusion of pairs `(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)`, an excision when `A` and `B`
are open. -/
private def prodExcisionFst :
    TopPair.ofSubset (fst X (TopPair.ofSubset B).snd ⁻¹' A) ⟶
      TauCeti.TopTriple.innerPair.obj (prodUnionFstTriple X Y A B) :=
  TopPair.ofHom (TopCat.ofHom ⟨fun p ↦ ⟨(p.1, p.2.1), Or.inr p.2.2⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun p ↦ ⟨(fst X _ p.1, (snd X (TopPair.ofSubset B).snd p.1).1), p.2⟩,
      by fun_prop⟩) (by ext; rfl)

/-- The excision map, followed by the inclusion of pairs `(A × Y ∪ X × B, A × Y) ⟶ (X × Y, A × Y)`,
is the product of the identity of `X` with the inclusion of `B` on ambient spaces. -/
private theorem fst_prodExcisionFst_comp_innerToTotal :
    TopPair.Hom.fst (prodExcisionFst X Y A B ≫
        TauCeti.TopTriple.innerToTotal.app (prodUnionFstTriple X Y A B)) =
      𝟙 X ⊗ₘ ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y) := by
  ext; rfl

omit [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
variable {A B} in
/-- **Excision onto `X × B`**: for open `A` and `B`, the inclusion of pairs
`(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)` induces isomorphisms on relative singular homology. The
open sets `A × Y` and `X × B` cover `A × Y ∪ X × B`; the first is the subspace and the second is the
image of the inclusion. -/
private theorem isIso_singularHomologyMap_prodExcisionFst (hA : IsOpen A) (hB : IsOpen B)
    (M : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (prodExcisionFst X Y A B) M n) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover M (prodExcisionFst X Y A B) ?_ ?_
    (![(↑) ⁻¹' (fst X Y ⁻¹' A), (↑) ⁻¹' (snd X Y ⁻¹' B)] :
      Fin 2 → Set ↥(fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)) ?_ ?_ ?_ n
  · refine ⟨IsEmbedding.subtypeVal.isInducing.of_comp_iff.1
      (IsEmbedding.id.prodMap IsEmbedding.subtypeVal).isInducing, fun x y h ↦ ?_⟩
    have h' : (x.1, (x.2.1 : Y)) = (y.1, (y.2.1 : Y)) := congrArg Subtype.val h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h'
    exact Prod.ext h₁ (Subtype.ext h₂)
  · rintro x ⟨a, ha⟩
    have hx : fst X Y a.1 = fst X (TopPair.ofSubset B).snd x :=
      congrArg (fun w : ↥(fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ↦ fst X Y w.1) ha
    exact ⟨⟨x, (hx ▸ (a.2 : fst X Y a.1 ∈ A) : fst X (TopPair.ofSubset B).snd x ∈ A)⟩, rfl⟩
  · simp only [Fin.forall_fin_two]
    exact ⟨TopCat.isOpen_subtypeVal_preimage_preimage_fst_union hA,
      TopCat.isOpen_subtypeVal_preimage_preimage_snd_union hB⟩
  · ext w
    simp only [Set.mem_iUnion, Fin.exists_fin_two, Set.mem_univ, iff_true]
    exact w.2
  · simp only [Fin.forall_fin_two]
    refine ⟨Or.inl fun w hw ↦ ⟨⟨w.1, hw⟩, rfl⟩, Or.inr fun w hw ↦ ⟨(w.1.1, ⟨w.1.2, hw⟩), rfl⟩⟩

/-- The comparison on the first terms: the relative shuffle map of `(X, A)` and `B`, followed by
the excision map. -/
private def shufflePairτ₁ :
    (TopPair.ofSubset A).singularChainComplex R ⊗
        (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶
      (TauCeti.TopTriple.innerPair.obj (prodUnionFstTriple X Y A B)).singularChainComplex (R ⊗ S) :=
  shuffleRel X (TopPair.ofSubset B).snd A R S ≫
    TopPair.singularChainComplexMap (prodExcisionFst X Y A B) (R ⊗ S)

/-- The comparison on the middle terms: the relative shuffle map of `(X, A)` and `Y`, read in the
total pair of the triple. -/
private def shufflePairτ₂ :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      (TauCeti.TopTriple.totalPair.obj (prodUnionFstTriple X Y A B)).singularChainComplex (R ⊗ S) :=
  shuffleRel X Y A R S ≫
    TopPair.singularChainComplexMap (prodUnionFstTotalPairIso X Y A B).hom (R ⊗ S)

omit [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- Reading the relative chains of `(X × Y, A × Y)` in the total pair of the triple turns the
projection to them into the projection to the relative chains of the total pair. -/
private theorem singularChainComplexπ_ofSubsetTotalPairIso (M : C) :
    (TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplexπ M ≫ TopPair.singularChainComplexMap
        (prodUnionFstTotalPairIso X Y A B).hom M =
      (TauCeti.TopTriple.totalPair.obj (prodUnionFstTriple X Y A B)).singularChainComplexπ M := by
  have h := TopPair.singularChainComplexπ_pair_naturality
    (prodUnionFstTotalPairIso X Y A B).hom M
  simp only [TauCeti.TopTriple.ofSubsetTotalPairIso_hom_fst] at h
  have h₁ : SSet.chainComplexMap (toSSet.map (𝟙 (X ⊗ Y))) M = 𝟙 _ :=
    (toSSet ⋙ (SSet.chainComplexFunctor C).obj M).map_id (X ⊗ Y)
  exact h.symm.trans ((congrArg (· ≫ _) h₁).trans (Category.id_comp _))

omit [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The excision map followed by the inclusion into the total pair of the triple is induced on
ambient chains by the product of the identity of `X` with the inclusion of `B`. -/
private theorem singularChainComplexπ_prodExcisionFst_innerToTotal (M : C) :
    (TopPair.ofSubset (fst X (TopPair.ofSubset B).snd ⁻¹' A)).singularChainComplexπ M ≫
        TopPair.singularChainComplexMap (prodExcisionFst X Y A B) M ≫
          TopPair.singularChainComplexMap
            (TauCeti.TopTriple.innerToTotal.app (prodUnionFstTriple X Y A B)) M =
      SSet.chainComplexMap
          (toSSet.map (𝟙 X ⊗ₘ ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y))) M ≫
        (TauCeti.TopTriple.totalPair.obj (prodUnionFstTriple X Y A B)).singularChainComplexπ M := by
  have h := TopPair.singularChainComplexπ_pair_naturality (prodExcisionFst X Y A B ≫
    TauCeti.TopTriple.innerToTotal.app (prodUnionFstTriple X Y A B)) M
  rw [fst_prodExcisionFst_comp_innerToTotal, TopPair.singularChainComplexMap_comp] at h
  exact h.symm

/-- The comparison maps commute with the maps of the sequences on the first two terms. -/
private theorem shufflePair_comm₁₂ :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) ≫
        shufflePairτ₂ X Y A B R S =
      shufflePairτ₁ X Y A B R S ≫ TopPair.singularChainComplexMap
        (TauCeti.TopTriple.innerToTotal.app (prodUnionFstTriple X Y A B)) (R ⊗ S) := by
  have := (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X
    (TopPair.ofSubset B).snd A R S).epi_g
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S))).1 ?_
  have h₂ := shuffle_naturality (𝟙 X) ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y)
    R S
  simp only [CategoryTheory.Functor.map_id] at h₂
  have hx := singularChainComplexπ_tensorHom_comp_tensorHom_chainComplexMap X Y A B R S
  have e₂ := (singularChainComplexπ_tensorHom_id_shuffleRel_assoc X Y A R S _).trans
    ((Category.assoc _ _ _).trans (congrArg (shuffle X Y R S ≫ ·)
      (singularChainComplexπ_ofSubsetTotalPairIso X Y A B (R ⊗ S))))
  have e₁ := (singularChainComplexπ_tensorHom_id_shuffleRel_assoc X (TopPair.ofSubset B).snd A R S
    _).trans ((Category.assoc _ _ _).trans (congrArg (shuffle X (TopPair.ofSubset B).snd R S ≫ ·)
      (singularChainComplexπ_prodExcisionFst_innerToTotal X Y A B (R ⊗ S))))
  -- Both sides are the shuffle map of `X` and `B`, followed by the map induced by `X × B ⟶ X × Y`
  -- and the projection to the relative chains of `(X × Y, A × Y)`. The chain complexes appear in
  -- several forms that agree only up to unfolding, so the composites are reassociated by hand.
  exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hx).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans
        (Category.assoc _ _ _))))))).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans e₁).symm

/-- The comparison maps commute with the maps of the sequences on the last two terms. -/
private theorem shufflePair_comm₂₃ :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shufflePair X Y A B R S =
      shufflePairτ₂ X Y A B R S ≫ TopPair.singularChainComplexMap
        (TauCeti.TopTriple.totalToOuter.app (prodUnionFstTriple X Y A B)) (R ⊗ S) := by
  have h : (prodUnionFstTotalPairIso X Y A B).hom ≫
        TauCeti.TopTriple.totalToOuter.app (prodUnionFstTriple X Y A B) =
      preimageFstToUnion X Y A B :=
    TopPair.hom_ext_of_fst _ (by
      rw [TopPair.Hom.fst_comp, TauCeti.TopTriple.ofSubsetTotalPairIso_hom_fst,
        TauCeti.TopTriple.totalToOuter_app_fst]
      exact (Category.comp_id _).trans (TopPair.ofSubsetMap_fst _ _).symm)
  exact (tensorHom_singularChainComplexπ_shufflePair X Y A B R S).trans
    ((congrArg (shuffleRel X Y A R S ≫ ·)
      ((congrArg (TopPair.singularChainComplexMap · (R ⊗ S)) h.symm).trans
        (TopPair.singularChainComplexMap_comp _ _ _))).trans (Category.assoc _ _ _).symm)

/-- The morphism from the sequence `C(X, A) ⊗ (C(B) ⟶ C(Y) ⟶ C(Y, B))` to the singular chain
sequence of the triple `(X × Y, A × Y ∪ X × B, A × Y)` given by the relative shuffle maps and the
shuffle map of the product of pairs. -/
private def shufflePairShortComplexMap :
    tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplexShortComplex S) ⟶
      (prodUnionFstTriple X Y A B).singularChainComplexShortComplex (R ⊗ S) where
  τ₁ := shufflePairτ₁ X Y A B R S
  τ₂ := shufflePairτ₂ X Y A B R S
  τ₃ := shufflePair X Y A B R S
  comm₁₂ := (shufflePair_comm₁₂ X Y A B R S).symm
  comm₂₃ := (shufflePair_comm₂₃ X Y A B R S).symm

variable {A B}

/-- **The relative Eilenberg–Zilber theorem for a product of open pairs**: for open `A ⊆ X` and
`B ⊆ Y`, the shuffle map `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)` is a
quasi-isomorphism. -/
theorem quasiIso_shufflePair (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (shufflePair X Y A B R S) := by
  have : QuasiIso (TopPair.singularChainComplexMap (prodExcisionFst X Y A B) (R ⊗ S)) :=
    (quasiIso_iff _).2 fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2
      (isIso_singularHomologyMap_prodExcisionFst X Y hA hB (R ⊗ S) n)
  have : QuasiIso (shufflePairτ₁ X Y A B R S) := by
    rw [shufflePairτ₁]
    infer_instance
  have : QuasiIso (shufflePairτ₂ X Y A B R S) := by
    rw [shufflePairτ₂]
    infer_instance
  exact HomologySequence.quasiIso_τ₃ (shufflePairShortComplexMap X Y A B R S)
    (shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S)
    ((prodUnionFstTriple X Y A B).shortExact_singularChainComplexShortComplex (R ⊗ S)) ‹_› ‹_›

end QuasiIso

end TopCat
