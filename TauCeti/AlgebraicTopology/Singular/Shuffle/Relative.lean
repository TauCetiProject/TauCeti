/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.Shuffle.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Relative
import TauCeti.CategoryTheory.Monoidal.Category

/-!
# Relative shuffle maps on singular chains

Let `X` and `Y` be topological spaces with subsets `A ⊆ X` and `B ⊆ Y`, and let `R` and `S` be
coefficient objects in an abelian monoidal preadditive category `C` with `w`-indexed coproducts
whose tensor functors `tensorLeft` and `tensorRight` preserve `w`-indexed discrete colimits. This
file descends the singular shuffle map
`TopCat.shuffle X Y R S : C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` to the three relative settings:

* `TopCat.shuffleRel`: the relative shuffle map
  `C(X, A; R) ⊗ C(Y; S) ⟶ C(X × Y, fst⁻¹(A); R ⊗ S)`, with one factor relative, characterized by
  `TopCat.singularChainComplexπ_tensorHom_id_shuffleRel` and natural via
  `TopCat.shuffleRel_naturality`.
* `TopCat.relativeShuffleToSmallChains`: the small-chain relative shuffle map
  `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; fst⁻¹(A) + snd⁻¹(B); R ⊗ S)` into the quotient by singular
  simplices lying in `A × Y` or `X × B`, characterized by
  `TopCat.singularChainComplexπ_tensorHom_relativeShuffleToSmallChains` and natural in both pairs
  (`TopCat.relativeShuffleToSmallChains_naturality`) and coefficients
  (`TopCat.relativeShuffleToSmallChains_coefficient_naturality`).
* `TopCat.shufflePair`: the relative shuffle map of a product of two pairs
  `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)`, obtained by postcomposing
  `TopCat.relativeShuffleToSmallChains` with `TopCat.smallSingularSubcomplexPairToUnion`
  (`TopCat.relativeShuffleToSmallChains_comp_smallSingularSubcomplexPairToUnion`), characterized by
  `TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair` and
  `TopCat.id_tensorHom_singularChainComplexπ_shufflePair`, and natural in pairs
  (`TopCat.shufflePair_naturality`) and coefficients (`TopCat.shufflePair_coefficient_naturality`).
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

section Splitting

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

/-- Tensoring on the right with `C(Y; S)` preserves the short exact sequence
`C(A; R) ⟶ C(X; R) ⟶ C(X, A; R)` of singular chains of the pair `(X, A)`, since the inclusion of
the singular chains of `A` splits in each degree. -/
theorem shortExact_tensorRightShortComplex_singularChainComplexShortComplex :
    (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
      ((TopPair.ofSubset A).singularChainComplexShortComplex R)).ShortExact :=
  shortExact_tensorRightShortComplex _ _
    ((TopPair.ofSubset A).shortExact_singularChainComplexShortComplex R)

/-- Tensoring on the left with `C(X, A; R)` preserves the short exact sequence
`C(B; S) ⟶ C(Y; S) ⟶ C(Y, B; S)` of singular chains of the pair `(Y, B)`, since the inclusion of
the singular chains of `B` splits in each degree. -/
theorem shortExact_tensorLeftShortComplex_singularChainComplexShortComplex :
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).ShortExact :=
  shortExact_tensorLeftShortComplex _
    ((TopPair.ofSubset B).shortExact_singularChainComplexShortComplex S)

/-- The projection `C(X; R) ⟶ C(X, A; R)` and the subspace inclusion `C(B; S) ⟶ C(Y; S)`,
tensored in the two variables, commute. -/
lemma singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)) ≫
      (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶
            (toSSet.obj Y).chainComplex S)) =
      (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
          (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
            (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶
              (toSSet.obj Y).chainComplex S)) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  rw [TopPair.toSSetPair_obj_hom]
  exact (tensor_id_comp_id_tensor _ _).trans (id_tensor_comp_tensor_id _ _).symm

/-- The projection `C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S)` is the projection in the first
variable followed by the projection in the second. -/
lemma singularChainComplexπ_tensorHom_singularChainComplexπ_eq :
    (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
  (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _).symm (Category.id_comp _).symm).trans
    (mapBifunctorMap_comp _ _ _ _ _ _)

end Splitting

variable [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

section ShuffleRel

variable (X Y : TopCat.{w}) (B : Set X) (R S : C)

/-- On `C(B; R) ⊗ C(Y; S)` the shuffle map is the shuffle map of `B` and `Y` followed by the map
induced by `B × Y ≅ fst⁻¹(B)` and the inclusion of `fst⁻¹(B)` into `X × Y`. -/
@[reassoc]
theorem chainComplexMap_tensorHom_id_shuffle :
    (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffle X Y R S =
      shuffle (TopPair.ofSubset B).snd Y R S ≫
        SSet.chainComplexMap (toSSet.map (prodPreimageFstIso X Y B).hom) (R ⊗ S) ≫
          SSet.chainComplexMap
            (toSSet.map (TopPair.ofSubset (fst X Y ⁻¹' B)).map) (R ⊗ S) := by
  have h := shuffle_naturality (TopPair.ofSubset B).map (𝟙 Y) R S
  simp only [CategoryTheory.Functor.map_id] at h
  refine h.trans (congrArg (_ ≫ ·) ?_)
  simp only [← CategoryTheory.Functor.map_comp, prodPreimageFstIso_hom_comp_map]
  rfl

/-- The shuffle map carries `C(B; R) ⊗ C(Y; S)` into the chains of `fst⁻¹(B)`, which vanish in
the relative chains of `(X × Y, fst⁻¹(B))`. -/
private theorem shuffle_cokernel_condition :
    (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffle X Y R S ≫
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) = 0 := by
  -- The composite factors through the singular chains of `fst⁻¹(B)`, which `π` kills. The
  -- composites are reassociated by hand: the singular chains of `X × Y` appear both as those of
  -- the ambient space of the pair and as `(toSSet.obj (X ⊗ Y)).chainComplex`, which agree only up
  -- to unfolding `TopPair.ofSubset`, so `rw [Category.assoc]` does not apply.
  refine (Category.assoc _ _ _).symm.trans
    ((chainComplexMap_tensorHom_id_shuffle X Y B R S =≫ _).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (TopPair.chainComplexMap_comp_singularChainComplexπ _ _)).trans
        comp_zero))).trans comp_zero)))

/-- **The relative shuffle map** `C(X, B; R) ⊗ C(Y; S) ⟶ C(X × Y, fst⁻¹(B); R ⊗ S)`, induced by
the shuffle map `C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` on the cokernels; it is characterized by
`TopCat.singularChainComplexπ_tensorHom_id_shuffleRel`. -/
def shuffleRel :
    (TopPair.ofSubset B).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplex (R ⊗ S) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc (CokernelCofork.ofπ _ (shuffle_cokernel_condition X Y B R S))

/-- The relative shuffle map is induced by the shuffle map: on `C(X; R) ⊗ C(Y; S)` it is the
shuffle map followed by the projection to the relative chains of `(X × Y, fst⁻¹(B))`. -/
@[reassoc (attr := simp)]
theorem singularChainComplexπ_tensorHom_id_shuffleRel :
    ((TopPair.ofSubset B).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffleRel X Y B R S =
      shuffle X Y R S ≫
        (TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- **Naturality of the relative shuffle map** in maps of pairs `(X, B) ⟶ (X', B')` and in maps
`Y ⟶ Y'`. -/
@[reassoc]
theorem shuffleRel_naturality {X' Y' : TopCat.{w}} {B' : Set X'} (f : X ⟶ X')
    (hf : Set.MapsTo f B B') (g : Y ⟶ Y') :
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
        SSet.chainComplexMap (toSSet.map g) S) ≫ shuffleRel X' Y' B' R S =
      shuffleRel X Y B R S ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_fst f g hf)) (R ⊗ S) := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S
  have : Epi ((TopPair.ofSubset B).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj Y).chainComplex S)) := hS.epi_g
  have hπ := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  rw [TopPair.ofSubsetMap_fst] at hπ
  have h₂ := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_fst f g hf)) (R ⊗ S)
  rw [TopPair.ofSubsetMap_fst] at h₂
  exact TauCeti.tensorHom_comp_eq_of_epi_tensorHom hπ.symm
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    (singularChainComplexπ_tensorHom_id_shuffleRel X Y B R S)
    (singularChainComplexπ_tensorHom_id_shuffleRel X' Y' B' R S)
    (shuffle_naturality f g R S) h₂

end ShuffleRel

section RelativeShuffle

section Fixed

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

private def leftRelativeShuffleToSmallChains :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  shuffleRel X Y A R S ≫
    SSetPair.chainComplexMap
      (toSmallPair ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] (i := 0) (Matrix.cons_val_zero _ _).superset)
      (R ⊗ S)

@[reassoc]
private lemma singularChainComplexπ_tensorHom_id_leftRelativeShuffleToSmallChains :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        leftRelativeShuffleToSmallChains X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) := by
  have hπ' :
      (TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplexπ (R ⊗ S) ≫
          SSetPair.chainComplexMap
            (toSmallPair ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] (i := 0)
              (Matrix.cons_val_zero _ _).superset) (R ⊗ S) =
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) := by
    have h := (SSetPair.chainComplexπ_naturality (R ⊗ S)
      (toSmallPair ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] (i := 0)
        (Matrix.cons_val_zero _ _).superset)).symm
    rw [toSmallPair_right] at h
    exact h.trans ((congrArg (· ≫ _) (SSet.chainComplexMap_id _ _)).trans (Category.id_comp _))
  rw [leftRelativeShuffleToSmallChains, ← Category.assoc,
    singularChainComplexπ_tensorHom_id_shuffleRel]
  exact (Category.assoc _ _ _).trans (whisker_eq _ hπ')

private lemma id_tensorHom_chainComplexMap_comp_leftRelativeShuffleToSmallChains :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        SSet.chainComplexMap (TopPair.toSSetPair.obj (TopPair.ofSubset B)).hom S) ≫
      leftRelativeShuffleToSmallChains X Y A B R S = 0 := by
  let pA := (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    𝟙 ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.chainComplex S)
  rw [← cancel_epi pA, comp_zero]
  have hcomm := singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap X Y A B R S
  have hnat := shuffle_naturality (𝟙 X) (TopPair.ofSubset B).map R S
  simp only [CategoryTheory.Functor.map_id] at hnat
  have hf (z) : (𝟙 X ⊗ₘ (TopPair.ofSubset B).map) z ∈ ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 1 :=
    Set.mem_preimage.2 ((ConcreteCategory.congr_hom
      (tensorHom_snd (𝟙 X) (TopPair.ofSubset B).map) z).symm ▸ (snd X (of ↥B) z).property)
  calc _ = (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
            SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
          ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
          leftRelativeShuffleToSmallChains X Y A B R S :=
        (Category.assoc _ _ _).symm.trans <| (eq_whisker hcomm _).trans (Category.assoc _ _ _)
    _ = (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
            SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
          shuffle X Y R S ≫
          ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
            (R ⊗ S) :=
        whisker_eq _
          (singularChainComplexπ_tensorHom_id_leftRelativeShuffleToSmallChains X Y A B R S)
    _ = 0 :=
        (Category.assoc _ _ _).symm.trans <| (eq_whisker hnat _).trans <|
          (Category.assoc _ _ _).trans <|
            (whisker_eq _
              (TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero
                _ _ hf (R ⊗ S))).trans comp_zero

/-- **The relative shuffle map to small chains**
`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; fst⁻¹(A) + snd⁻¹(B); R ⊗ S)`, descending
`TopCat.shuffle X Y R S` to chains relative to `fst⁻¹(A)` and `snd⁻¹(B)`. -/
def relativeShuffleToSmallChains :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  (CokernelCofork.IsColimit.desc' hS.gIsCokernel
    (leftRelativeShuffleToSmallChains X Y A B R S)
    (id_tensorHom_chainComplexMap_comp_leftRelativeShuffleToSmallChains X Y A B R S)).val

@[reassoc]
private lemma id_tensorHom_singularChainComplexπ_relativeShuffleToSmallChains :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ relativeShuffleToSmallChains X Y A B R S =
      leftRelativeShuffleToSmallChains X Y A B R S :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  (CokernelCofork.IsColimit.desc' hS.gIsCokernel _
    (id_tensorHom_chainComplexMap_comp_leftRelativeShuffleToSmallChains X Y A B R S)).property

/-- `relativeShuffleToSmallChains` is characterized by precomposing with `π_A ⊗ π_B`. -/
@[reassoc (attr := simp)]
lemma singularChainComplexπ_tensorHom_relativeShuffleToSmallChains :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫
        relativeShuffleToSmallChains X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) :=
  (congrArg (· ≫ relativeShuffleToSmallChains X Y A B R S)
    (singularChainComplexπ_tensorHom_singularChainComplexπ_eq X Y A B R S)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·)
          (id_tensorHom_singularChainComplexπ_relativeShuffleToSmallChains X Y A B R S)).trans
        (singularChainComplexπ_tensorHom_id_leftRelativeShuffleToSmallChains X Y A B R S)))

end Fixed

/-- **Naturality of `relativeShuffleToSmallChains`** in maps carrying `A` into `A'` and `B` into
`B'`. -/
@[reassoc]
lemma relativeShuffleToSmallChains_naturality {X Y X' Y' : TopCat.{w}} {A : Set X} {B : Set Y}
    {A' : Set X'} {B' : Set Y'} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') (R S : C) :
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) ≫
        relativeShuffleToSmallChains X' Y' A' B' R S =
      relativeShuffleToSmallChains X Y A B R S ≫
        SSetPair.chainComplexMap
          (smallSingularSubcomplexPairMap ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]
            ![fst X' Y' ⁻¹' A', snd X' Y' ⁻¹' B'] (f ⊗ₘ g) id
            (Fin.forall_fin_two.2 ⟨mapsTo_tensorHom_preimage_fst f g hf,
              mapsTo_tensorHom_preimage_snd f g hg⟩))
          (R ⊗ S) := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have hπ := SSetPair.chainComplexπ_naturality (R ⊗ S)
    (smallSingularSubcomplexPairMap ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]
      ![fst X' Y' ⁻¹' A', snd X' Y' ⁻¹' B'] (f ⊗ₘ g) id
      (Fin.forall_fin_two.2 ⟨mapsTo_tensorHom_preimage_fst f g hf,
        mapsTo_tensorHom_preimage_snd f g hg⟩))
  have hA := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  have hB := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap g hg) S
  rw [smallSingularSubcomplexPairMap_right] at hπ
  rw [TopPair.ofSubsetMap_fst] at hA hB
  exact TauCeti.tensorHom_comp_eq_of_epi_tensorHom hA.symm hB.symm
    (singularChainComplexπ_tensorHom_relativeShuffleToSmallChains X Y A B R S)
    (singularChainComplexπ_tensorHom_relativeShuffleToSmallChains X' Y' A' B' R S)
    (shuffle_naturality f g R S) hπ

/-- **Naturality of the relative shuffle map to small chains** in both coefficient objects. -/
@[reassoc]
lemma relativeShuffleToSmallChains_coefficient_naturality (X Y : TopCat.{w}) (A : Set X)
    (B : Set Y) {R S R' S' : C} (φ : R ⟶ R') (ψ : S ⟶ S') :
    ((TopPair.ofSubset A).singularChainComplexCoefficientMap φ ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexCoefficientMap ψ) ≫
        relativeShuffleToSmallChains X Y A B R' S' =
      relativeShuffleToSmallChains X Y A B R S ≫
        ((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app
          ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have hπ := NatTrans.congr_app ((SSetPair.chainComplexFunctorπ C).naturality (φ ⊗ₘ ψ))
    ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair
  have hA := (TopPair.ofSubset A).singularChainComplexπ_comp_singularChainComplexCoefficientMap φ
  have hB := (TopPair.ofSubset B).singularChainComplexπ_comp_singularChainComplexCoefficientMap ψ
  exact TauCeti.tensorHom_comp_eq_of_epi_tensorHom hA hB
    (singularChainComplexπ_tensorHom_relativeShuffleToSmallChains X Y A B R S)
    (singularChainComplexπ_tensorHom_relativeShuffleToSmallChains X Y A B R' S')
    (shuffle_coefficient_naturality X Y φ ψ) hπ

end RelativeShuffle

section ShufflePair

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

/-- **The shuffle map of a product of two pairs**,
`C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y, A × Y ∪ X × B; R ⊗ S)`, obtained by postcomposing
`TopCat.relativeShuffleToSmallChains` with `TopCat.smallSingularSubcomplexPairToUnion`. It is
characterized by `TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair` and
`TopCat.id_tensorHom_singularChainComplexπ_shufflePair`. -/
def shufflePair :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S) :=
  relativeShuffleToSmallChains X Y A B R S ≫
    SSetPair.chainComplexMap
      (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S)

/-- `relativeShuffleToSmallChains` followed by `smallSingularSubcomplexPairToUnion` is
`TopCat.shufflePair`. -/
@[reassoc]
lemma relativeShuffleToSmallChains_comp_smallSingularSubcomplexPairToUnion :
    relativeShuffleToSmallChains X Y A B R S ≫
      SSetPair.chainComplexMap
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S) =
      shufflePair X Y A B R S :=
  (rfl)

/-- On `C(X, A; R) ⊗ C(Y; S)` the shuffle map of the product of pairs is the relative shuffle map
of `(X, A)` and `Y`, followed by the quotient modulo the chains of `A × Y ∪ X × B`. -/
@[reassoc (attr := simp)]
theorem id_tensorHom_singularChainComplexπ_shufflePair :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shufflePair X Y A B R S =
      shuffleRel X Y A R S ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap (𝟙 _) fun _ hz ↦ Or.inl hz) (R ⊗ S) :=
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _)
      (id_tensorHom_singularChainComplexπ_relativeShuffleToSmallChains X Y A B R S)).trans <|
      (Category.assoc _ _ _).trans <| whisker_eq _ <|
        (((SSetPair.chainComplexFunctor C).obj (R ⊗ S)).map_comp _ _).symm.trans <|
          congrArg (SSetPair.chainComplexMap · (R ⊗ S))
            (toSmallPair_comp_smallSingularSubcomplexPairToUnion _ _ _ _)

/-- **The shuffle map of a product of pairs is induced by the shuffle map**: on
`C(X; R) ⊗ C(Y; S)` it is the shuffle map followed by the projection to the relative chains of
`(X × Y, A × Y ∪ X × B)`. -/
@[reassoc (attr := simp)]
theorem singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shufflePair X Y A B R S =
      shuffle X Y R S ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) :=
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _)
      (singularChainComplexπ_tensorHom_relativeShuffleToSmallChains X Y A B R S)).trans <|
      (Category.assoc _ _ _).trans <| whisker_eq _ <|
        chainComplexπ_smallSingularSubcomplexPairToUnion (R ⊗ S)
          (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)

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
  refine (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (relativeShuffleToSmallChains_naturality f g hf hg R S)).trans <|
      (Category.assoc _ _ _).trans <|
        (whisker_eq _ ?_).trans (Category.assoc _ _ _).symm
  rw [← ((SSetPair.chainComplexFunctor C).obj (R ⊗ S)).map_comp,
    ← ((SSetPair.chainComplexFunctor C).obj (R ⊗ S)).map_comp]
  congr 1
  exact (smallSingularSubcomplexPairToUnion_comp_ofSubsetMap (f ⊗ₘ g)
    (mapsTo_tensorHom_preimage_fst f g hf) (mapsTo_tensorHom_preimage_snd f g hg)).symm

/-- **Naturality of the shuffle map of a product of pairs** in both coefficient objects. -/
@[reassoc]
lemma shufflePair_coefficient_naturality {R S R' S' : C} (φ : R ⟶ R') (ψ : S ⟶ S') :
    ((TopPair.ofSubset A).singularChainComplexCoefficientMap φ ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexCoefficientMap ψ) ≫
        shufflePair X Y A B R' S' =
      shufflePair X Y A B R S ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexCoefficientMap
          (φ ⊗ₘ ψ) := by
  rw [shufflePair, shufflePair, relativeShuffleToSmallChains_coefficient_naturality_assoc,
    Category.assoc]
  exact whisker_eq _ (((SSetPair.chainComplexFunctor C).map (φ ⊗ₘ ψ)).naturality
    (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B))).symm

end ShufflePair

end TopCat
