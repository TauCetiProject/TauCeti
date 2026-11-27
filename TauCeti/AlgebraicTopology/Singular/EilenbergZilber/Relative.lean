/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber.Basic
public import TauCeti.AlgebraicTopology.Singular.Shuffle.Relative
import TauCeti.CategoryTheory.Monoidal.Category

/-!
# The relative Eilenberg–Zilber theorem for singular chains

For topological spaces `X` and `Y`, subsets `A ⊆ X` and `B ⊆ Y`, and coefficient objects `R` and
`S` in an abelian monoidal preadditive category `C` with `w`-indexed coproducts whose tensor
functors `tensorLeft` and `tensorRight` preserve `w`-indexed discrete colimits, let
`C(X × Y; fst⁻¹(A) + snd⁻¹(B); R ⊗ S)` denote the quotient of `C(X × Y; R ⊗ S)` modulo singular
simplices lying wholly in `A × Y` or wholly in `X × B` (the relative chain complex of the pair
`((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair`). The relative
Alexander–Whitney map
* `TopCat.relativeAlexanderWhitneySmallChains X Y A B R S :
  C(X × Y; fst⁻¹(A) + snd⁻¹(B); R ⊗ S) ⟶ C(X, A; R) ⊗ C(Y, B; S)`
and the relative shuffle map `TopCat.relativeShuffleToSmallChains X Y A B R S` form a chain
homotopy equivalence `TopCat.relativeEilenbergZilberSmallChainsHomotopyEquiv`.

Because `0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0` splits in each degree, tensoring with any chain
complex preserves short exactness via `HomologicalComplex.shortExact_tensorLeftShortComplex`
and `HomologicalComplex.shortExact_tensorRightShortComplex`, so both Eilenberg–Zilber
homotopies descend to relative chains via `Homotopy.descCokernel`, giving
`TopCat.relativeShuffleAlexanderWhitneySmallChainsHomotopy` and
`TopCat.relativeAlexanderWhitneyShuffleSmallChainsHomotopy` without openness, flatness, or Künneth
assumptions (passing to `C(X × Y, A × Y ∪ X × B; R ⊗ S)` when `A` and `B` are open is
`TopCat.quasiIso_shufflePair_of_isOpen`).

## Main definitions and results

* `TopCat.relativeShuffleAlexanderWhitneySmallChainsHomotopy`: the chain homotopy
  `AW ∘ shuffle ≃ id` on `C(X, A; R) ⊗ C(Y, B; S)`, characterized on quotient chains by
  `TopCat.singularChainComplexπ_tensorHom_f_relativeShuffleAlexanderWhitneySmallChainsHomotopy_hom`.
* `TopCat.relativeAlexanderWhitneyShuffleSmallChainsHomotopy`: the chain homotopy
  `shuffle ∘ AW ≃ id` on `C(X × Y; fst⁻¹(A) + snd⁻¹(B); R ⊗ S)`, characterized on quotient chains
  by `TopCat.chainComplexπ_f_relativeAlexanderWhitneyShuffleSmallChainsHomotopy_hom`.
* `TopCat.relativeEilenbergZilberSmallChainsHomotopyEquiv`: the resulting chain homotopy
  equivalence.
* `TopCat.quasiIso_relativeShuffleToSmallChains`: `TopCat.relativeShuffleToSmallChains` is a
  quasi-isomorphism.
* Inverse laws on homology (in `TopCat`):
  `homologyMap_relativeShuffleToSmallChains_comp_homologyMap_relativeAlexanderWhitneySmallChains`,
  `homologyMap_relativeAlexanderWhitneySmallChains_comp_homologyMap_relativeShuffleToSmallChains`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Section 3.B.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology
  HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

private lemma comp_homotopy_hom_comp_eq_zero {K' K Z : ChainComplex C ℕ}
    {f : K' ⟶ K} {π : K ⟶ Z} {φ₁ ψ₁ : K' ⟶ K'} {φ₂ ψ₂ : K ⟶ K}
    {H₁ : _root_.Homotopy φ₁ ψ₁} {H₂ : _root_.Homotopy φ₂ ψ₂} {i j : ℕ}
    (hnat : f.f i ≫ H₂.hom i j = H₁.hom i j ≫ f.f j) (hp : f ≫ π = 0) :
    f.f i ≫ H₂.hom i j ≫ π.f j = 0 := by
  rw [← Category.assoc, hnat, Category.assoc, ← HomologicalComplex.comp_f, hp,
    HomologicalComplex.zero_f, comp_zero]

end

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

private lemma tensorHom_f_comp_shuffleAlexanderWhitneyHomotopy_hom_comp_eq_zero
    {K' K L' L : SSet.{w}} (f : K' ⟶ K) (g : L' ⟶ L) {Z : ChainComplex C ℕ}
    (p : K.chainComplex R ⊗ L.chainComplex S ⟶ Z)
    (hp : (SSet.chainComplexMap f R ⊗ₘ SSet.chainComplexMap g S) ≫ p = 0) (i j : ℕ) :
    (SSet.chainComplexMap f R ⊗ₘ SSet.chainComplexMap g S).f i ≫
        (SSet.shuffleAlexanderWhitneyHomotopy K L R S).hom i j ≫ p.f j = 0 :=
  comp_homotopy_hom_comp_eq_zero
    (SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality R S f g i j) hp

private lemma chainComplexMap_tensorHom_id_comp_shuffleAlexanderWhitneyHomotopy_hom_comp
    (i j : ℕ) :
    (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ
          𝟙 ((toSSet.obj Y).chainComplex S)).f i ≫
        (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j = 0 := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have h := tensorHom_f_comp_shuffleAlexanderWhitneyHomotopy_hom_comp_eq_zero R S
    (toSSet.map (TopPair.ofSubset A).map) (𝟙 (toSSet.obj Y))
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)
    ((tensorHom_comp_tensorHom _ _ _ _).trans <| by
      rw [TopPair.chainComplexMap_comp_singularChainComplexπ]
      exact zero_tensorHom _) i j
  simp only [CategoryTheory.Functor.map_id] at h
  exact h

private lemma id_tensorHom_chainComplexMap_comp_shuffleAlexanderWhitneyHomotopy_hom_comp
    (i j : ℕ) :
    (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
          SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S).f i ≫
        (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j = 0 := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have h := tensorHom_f_comp_shuffleAlexanderWhitneyHomotopy_hom_comp_eq_zero R S
    (𝟙 (toSSet.obj X)) (toSSet.map (TopPair.ofSubset B).map)
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)
    ((tensorHom_comp_tensorHom _ _ _ _).trans <| by
      rw [TopPair.chainComplexMap_comp_singularChainComplexπ]
      exact tensorHom_zero _) i j
  simp only [CategoryTheory.Functor.map_id] at h
  exact h

private def leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy :
    _root_.Homotopy
      ((tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g ≫
        (relativeShuffleToSmallChains X Y A B R S ≫
          relativeAlexanderWhitneySmallChains X Y A B R S))
      (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g := by
  let S₁ := tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
    ((TopPair.ofSubset A).singularChainComplexShortComplex R)
  have hfac : S₁.g ≫ (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) := by
    let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
    exact tensor_id_comp_id_tensor ((TopPair.ofSubset B).singularChainComplexπ S)
      ((TopPair.ofSubset A).singularChainComplexπ R)
  refine _root_.Homotopy.descCokernel
    (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S) S₁.f S₁.g
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S)
    (fun i ↦ (comp_f _ _ i).symm.trans ((congr_hom S₁.zero i).trans (zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₁).1
      (shortExact_tensorRightShortComplex ((toSSet.obj Y).chainComplex S) _
        ((TopPair.ofSubset A).shortExact_singularChainComplexShortComplex R)) i).gIsCokernel)
    (chainComplexMap_tensorHom_id_comp_shuffleAlexanderWhitneyHomotopy_hom_comp X Y A B R S)
    ?_ (hfac.trans (Category.id_comp _).symm)
  exact (Category.assoc _ _ _).symm.trans <| (eq_whisker hfac _).trans <|
    (singularChainComplexπ_tensorHom_relativeShuffleToSmallChains_assoc X Y A B R S _).trans <|
      (Category.assoc _ _ _).trans <|
        (whisker_eq _ (chainComplexπ_relativeAlexanderWhitneySmallChains X Y A B R S)).trans <|
          (Category.assoc _ _ _).symm.trans <| eq_whisker (shuffle_alexanderWhitney X Y R S) _

private lemma π_leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy_hom (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)).f i ≫
        (leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy X Y A B R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j := by
  unfold leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy
  exact _root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j

/-- **The relative Eilenberg–Zilber chain homotopy** `AW ∘ shuffle ≃ id` on
`C(X, A; R) ⊗ C(Y, B; S)`. -/
def relativeShuffleAlexanderWhitneySmallChainsHomotopy :
    _root_.Homotopy
      (relativeShuffleToSmallChains X Y A B R S ≫ relativeAlexanderWhitneySmallChains X Y A B R S)
      (𝟙 _) :=
  let S₂ := tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
    ((TopPair.ofSubset B).singularChainComplexShortComplex S)
  _root_.Homotopy.descCokernel
    (leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy X Y A B R S) S₂.f S₂.g (𝟙 _)
    (fun i ↦ (comp_f _ _ i).symm.trans ((congr_hom S₂.zero i).trans (zero_f _ _ i)))
    (fun i ↦ ((shortExact_iff_degreewise_shortExact S₂).1
      (shortExact_tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).shortExact_singularChainComplexShortComplex S)) i).gIsCokernel)
    (fun i j ↦ by
      let pA := (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)
      have hcomm : pA ≫ S₂.f =
          (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
            SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
            ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
              𝟙 ((toSSet.obj Y).chainComplex S)) := by
        rw [tensorLeftShortComplex_f]
        exact singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap X Y A B R S
      rw [HomologicalComplex.id_f, Category.comp_id]
      have hcomm_i := congrArg (HomologicalComplex.Hom.f · i) hcomm
      have hpA : pA.f i ≫ S₂.f.f i ≫
          (leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy X Y A B R S).hom i j = 0 :=
        (Category.assoc _ _ _).symm.trans <| (eq_whisker hcomm_i _).trans <|
          (Category.assoc _ _ _).trans <|
            (whisker_eq _
              (π_leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy_hom
                X Y A B R S i j)).trans
              (id_tensorHom_chainComplexMap_comp_shuffleAlexanderWhitneyHomotopy_hom_comp
                X Y A B R S i j)
      exact (cancel_epi (pA.f i)).1 (hpA.trans comp_zero.symm))
    (Category.comp_id _).symm rfl

/-- Precomposing `(relativeShuffleAlexanderWhitneySmallChainsHomotopy ...).hom i j` with `π_A ⊗ π_B`
intertwines it with `SSet.shuffleAlexanderWhitneyHomotopy`. -/
@[reassoc (attr := simp)]
lemma singularChainComplexπ_tensorHom_f_relativeShuffleAlexanderWhitneySmallChainsHomotopy_hom
    (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S).f i ≫
      (relativeShuffleAlexanderWhitneySmallChainsHomotopy X Y A B R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S).f j := by
  let : MonoidalCategory (ChainComplex C ℕ) := monoidalCategory C (ComplexShape.down ℕ)
  have hdesc : (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S).f i ≫
      (relativeShuffleAlexanderWhitneySmallChainsHomotopy X Y A B R S).hom i j =
      (leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy X Y A B R S).hom i j := by
    unfold relativeShuffleAlexanderWhitneySmallChainsHomotopy
    exact (_root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j).trans (Category.comp_id _)
  conv_lhs =>
    rw [← tensor_id_comp_id_tensor ((TopPair.ofSubset B).singularChainComplexπ S)
        ((TopPair.ofSubset A).singularChainComplexπ R),
      HomologicalComplex.comp_f, Category.assoc, hdesc]
  exact π_leftRelativeShuffleAlexanderWhitneySmallChainsHomotopy_hom X Y A B R S i j

private lemma chainComplexMap_smallSingularSubcomplex_ι_comp_ambientHomotopy_hom_comp
    (i j : ℕ) :
    (SSet.chainComplexMap ((X ⊗ Y).smallSingularSubcomplex
        ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).ι (R ⊗ S)).f i ≫
      (alexanderWhitneyShuffleHomotopy X Y R S).hom i j ≫
      (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
        (R ⊗ S)).f j = 0 := by
  let π := ((X ⊗ Y).smallSingularSubcomplex
    ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S)
  refine chainComplexMap_f_smallSingularSubcomplex_ι_comp_eq_zero ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]
    i ((alexanderWhitneyShuffleHomotopy X Y R S).hom i j ≫ π.f j) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · let iA : of ↥A ⟶ X := ofHom (ContinuousMap.subtypeVal A)
    let g₀ : of ↥(![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 0) ⟶ of ↥A ⊗ Y :=
      (prodPreimageFstIso X Y A).inv
    have hfac : SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal
        (![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 0)))) (R ⊗ S) =
        SSet.chainComplexMap (toSSet.map g₀) (R ⊗ S) ≫
          SSet.chainComplexMap (toSSet.map (iA ⊗ₘ 𝟙 Y)) (R ⊗ S) := by
      have hg₀ : g₀ ≫ (iA ⊗ₘ 𝟙 Y) =
          ofHom (ContinuousMap.subtypeVal (![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 0)) :=
        prodPreimageFstIso_inv_comp_whiskerRight X Y A
      rw [← hg₀, Functor.map_comp]
      exact ((SSet.chainComplexFunctor C).obj (R ⊗ S)).map_comp _ _
    have hzero := TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero
      ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] (iA ⊗ₘ 𝟙 Y) (i := 0)
      (fun z ↦ mapsTo_tensorHom_preimage_fst (A := Set.univ) iA (𝟙 Y)
        (fun w _ ↦ w.property) (Set.mem_preimage.2 (Set.mem_univ _))) (R ⊗ S)
    rw [hfac, HomologicalComplex.comp_f, Category.assoc,
      comp_homotopy_hom_comp_eq_zero
        (alexanderWhitneyShuffleHomotopy_hom_naturality iA (𝟙 Y) R S i j) hzero,
      comp_zero]
  · let iB : of ↥B ⟶ Y := ofHom (ContinuousMap.subtypeVal B)
    let g₁ : of ↥(![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 1) ⟶ X ⊗ of ↥B :=
      ofHom ⟨fun x ↦ (fst X Y x.val, ⟨snd X Y x.val, x.property⟩),
        ((fst X Y).hom.continuous.comp continuous_subtypeVal).prodMk
          (((snd X Y).hom.continuous.comp continuous_subtypeVal).subtype_mk fun x ↦ x.property)⟩
    have hfac : SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal
        (![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 1)))) (R ⊗ S) =
        SSet.chainComplexMap (toSSet.map g₁) (R ⊗ S) ≫
          SSet.chainComplexMap (toSSet.map (𝟙 X ⊗ₘ iB)) (R ⊗ S) := by
      have hg₁ : g₁ ≫ (𝟙 X ⊗ₘ iB) =
          ofHom (ContinuousMap.subtypeVal (![fst X Y ⁻¹' A, snd X Y ⁻¹' B] 1)) :=
        TopCat.ext fun _ ↦ rfl
      rw [← hg₁, Functor.map_comp]
      exact ((SSet.chainComplexFunctor C).obj (R ⊗ S)).map_comp _ _
    have hzero := TauCeti.chainComplexMap_comp_smallSingularSubcomplex_chainComplexπ_eq_zero
      ![fst X Y ⁻¹' A, snd X Y ⁻¹' B] (𝟙 X ⊗ₘ iB) (i := 1)
      (fun z ↦ mapsTo_tensorHom_preimage_snd (B := Set.univ) (𝟙 X) iB
        (fun w _ ↦ w.property) (Set.mem_preimage.2 (Set.mem_univ _))) (R ⊗ S)
    rw [hfac, HomologicalComplex.comp_f, Category.assoc,
      comp_homotopy_hom_comp_eq_zero
        (alexanderWhitneyShuffleHomotopy_hom_naturality (𝟙 X) iB R S i j) hzero,
      comp_zero]

/-- **The relative Eilenberg–Zilber chain homotopy** `shuffle ∘ AW ≃ id` on
`C(X × Y; fst⁻¹(A) + snd⁻¹(B); R ⊗ S)`. -/
def relativeAlexanderWhitneyShuffleSmallChainsHomotopy :
    _root_.Homotopy
      (relativeAlexanderWhitneySmallChains X Y A B R S ≫ relativeShuffleToSmallChains X Y A B R S)
      (𝟙 _) :=
  _root_.Homotopy.descCokernel
    (alexanderWhitneyShuffleHomotopy X Y R S)
    (SSet.chainComplexMap
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.hom (R ⊗ S))
    (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))
    (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S))
    (fun i ↦ ((X ⊗ Y).smallSingularSubcomplex
      ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex_condition_f (R ⊗ S) i)
    (fun i ↦ ((X ⊗ Y).smallSingularSubcomplex
      ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.isColimitCokernelCoforkChainComplexX (R ⊗ S) i)
    (chainComplexMap_smallSingularSubcomplex_ι_comp_ambientHomotopy_hom_comp X Y A B R S)
    ((Category.assoc _ _ _).symm.trans <|
      (eq_whisker (chainComplexπ_relativeAlexanderWhitneySmallChains X Y A B R S) _).trans <|
      (Category.assoc _ _ _).trans <|
      (whisker_eq _
        (singularChainComplexπ_tensorHom_relativeShuffleToSmallChains X Y A B R S)).trans
      (Category.assoc _ _ _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Precomposing `(relativeAlexanderWhitneyShuffleSmallChainsHomotopy ...).hom i j` with the
small-chain quotient map intertwines it with `alexanderWhitneyShuffleHomotopy`. -/
@[reassoc (attr := simp)]
lemma chainComplexπ_f_relativeAlexanderWhitneyShuffleSmallChainsHomotopy_hom (i j : ℕ) :
    (((X ⊗ Y).smallSingularSubcomplex
        ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S)).f i ≫
      (relativeAlexanderWhitneyShuffleSmallChainsHomotopy X Y A B R S).hom i j =
      (alexanderWhitneyShuffleHomotopy X Y R S).hom i j ≫
        (((X ⊗ Y).smallSingularSubcomplex
          ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ (R ⊗ S)).f j := by
  unfold relativeAlexanderWhitneyShuffleSmallChainsHomotopy
  exact _root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j

/-- **The relative Eilenberg–Zilber theorem**: `TopCat.relativeAlexanderWhitneySmallChains` and
`TopCat.relativeShuffleToSmallChains` form a chain homotopy equivalence between
`C(X × Y; fst⁻¹(A) + snd⁻¹(B); R ⊗ S)` and `C(X, A; R) ⊗ C(Y, B; S)`. -/
def relativeEilenbergZilberSmallChainsHomotopyEquiv :
    _root_.HomotopyEquiv
      (((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex (R ⊗ S))
      ((TopPair.ofSubset A).singularChainComplex R ⊗
        (TopPair.ofSubset B).singularChainComplex S) where
  hom := relativeAlexanderWhitneySmallChains X Y A B R S
  inv := relativeShuffleToSmallChains X Y A B R S
  homotopyHomInvId := relativeAlexanderWhitneyShuffleSmallChainsHomotopy X Y A B R S
  homotopyInvHomId := relativeShuffleAlexanderWhitneySmallChainsHomotopy X Y A B R S

@[simp]
lemma relativeEilenbergZilberSmallChainsHomotopyEquiv_hom :
    (relativeEilenbergZilberSmallChainsHomotopyEquiv X Y A B R S).hom =
      relativeAlexanderWhitneySmallChains X Y A B R S :=
  (rfl)

@[simp]
lemma relativeEilenbergZilberSmallChainsHomotopyEquiv_inv :
    (relativeEilenbergZilberSmallChainsHomotopyEquiv X Y A B R S).inv =
      relativeShuffleToSmallChains X Y A B R S :=
  (rfl)

/-- `TopCat.relativeShuffleToSmallChains` is a quasi-isomorphism, being the homotopy inverse of
`TopCat.relativeAlexanderWhitneySmallChains` in
`TopCat.relativeEilenbergZilberSmallChainsHomotopyEquiv`. -/
instance quasiIso_relativeShuffleToSmallChains :
    QuasiIso (relativeShuffleToSmallChains X Y A B R S) := by
  rw [← relativeEilenbergZilberSmallChainsHomotopyEquiv_inv]
  infer_instance

/-- On homology, `relativeShuffleToSmallChains` followed by `relativeAlexanderWhitneySmallChains` is
the identity. -/
@[reassoc (attr := simp)]
lemma homologyMap_relativeShuffleToSmallChains_comp_homologyMap_relativeAlexanderWhitneySmallChains
    (n : ℕ) :
    homologyMap (relativeShuffleToSmallChains X Y A B R S) n ≫
        homologyMap (relativeAlexanderWhitneySmallChains X Y A B R S) n = 𝟙 _ :=
  ((relativeEilenbergZilberSmallChainsHomotopyEquiv X Y A B R S).toHomologyIso n).inv_hom_id

/-- On homology, `relativeAlexanderWhitneySmallChains` followed by `relativeShuffleToSmallChains` is
the identity. -/
@[reassoc (attr := simp)]
lemma homologyMap_relativeAlexanderWhitneySmallChains_comp_homologyMap_relativeShuffleToSmallChains
    (n : ℕ) :
    homologyMap (relativeAlexanderWhitneySmallChains X Y A B R S) n ≫
        homologyMap (relativeShuffleToSmallChains X Y A B R S) n = 𝟙 _ :=
  ((relativeEilenbergZilberSmallChainsHomotopyEquiv X Y A B R S).toHomologyIso n).hom_inv_id

end TopCat
