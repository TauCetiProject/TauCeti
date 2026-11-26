/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.CrossProduct.Basic
public import TauCeti.AlgebraicTopology.Singular.Shuffle.Relative

/-!
# The relative cross product in singular homology

For subsets `A ⊆ X` and `B ⊆ Y` and coefficient objects `R` and `S` in an abelian monoidal
preadditive category `C` with `w`-indexed coproducts whose tensor functors `tensorLeft` and
`tensorRight` preserve `w`-indexed discrete colimits, `TopCat.singularRelativeHomologyCross` is the
relative homology cross product

`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` (`p + q = n`),

obtained by composing the algebraic cross product `HomologicalComplex.homologyCross` with the
shuffle map of a product of pairs `TopCat.shufflePair`.

This relative homology cross product feeds the Kronecker duality formulas for relative cross and
cup products in `TauCeti.AlgebraicTopology.Cohomology.Cup.Kronecker` and the local homology cross
product in `TauCeti.AlgebraicTopology.Singular.LocalHomology.Cross`, which in turn establish
generator preservation and reflection for local cohomology cross products and Thom classes over
arbitrary commutative rings without flatness or Künneth hypotheses.

`TopCat.singularRelativeHomologyCross` and
`TopCat.homologyπ_tensorHom_singularRelativeHomologyCross` assume `WalkingParallelPair` colimit
preservation for `tensorLeft` of `Hₚ(X, A; R)` and `tensorRight` of `Z_q(Y, B; S)` and
`C_{q+1}(Y, B; S)`; the compatibility and naturality results also require the corresponding
`WalkingParallelPair` instances on the ambient chains, target pairs, or target coefficients.

## Main definitions and results

* `TopCat.singularRelativeHomologyCross`: the relative homology cross product, with cycle
  evaluation (`TopCat.homologyπ_tensorHom_singularRelativeHomologyCross`), compatibility with the
  absolute cross product (`TopCat.singularHomologyπ_tensorHom_singularRelativeHomologyCross`), and
  naturality in pairs (`TopCat.singularRelativeHomologyCross_naturality`) and coefficients
  (`TopCat.singularRelativeHomologyCross_coefficient_naturality`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Section 3.B.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology
  HomologicalComplex

universe w v u

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

namespace TopCat

section Basic

variable (X Y : TopCat.{w}) (R S : C) (A : Set X) (B : Set Y) (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The relative homology cross product**
`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` (`p + q = n`). -/
def singularRelativeHomologyCross :
    (TopPair.ofSubset A).singularHomology R p ⊗ (TopPair.ofSubset B).singularHomology S q ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  homologyCross ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
    homologyMap (shufflePair X Y A B R S) n

/-- Definitional unfolding of `TopCat.singularRelativeHomologyCross`. -/
lemma singularRelativeHomologyCross_def :
    singularRelativeHomologyCross X Y R S A B p q n h =
      homologyCross ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
        homologyMap (shufflePair X Y A B R S) n :=
  (rfl)

/-- Cycle evaluation of `TopCat.singularRelativeHomologyCross` in `(X × Y, A × Y ∪ X × B)`. -/
@[reassoc (attr := simp)]
lemma homologyπ_tensorHom_singularRelativeHomologyCross :
    (((TopPair.ofSubset A).singularChainComplex R).homologyπ p ⊗ₘ
        ((TopPair.ofSubset B).singularChainComplex S).homologyπ q) ≫
        singularRelativeHomologyCross X Y R S A B p q n h =
      cyclesCross ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
        cyclesMap (shufflePair X Y A B R S) n ≫
          ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex
            (R ⊗ S)).homologyπ n :=
  (homologyπ_tensorHom_homologyCross_assoc _ _ p q n h _).trans
    (cyclesCross _ _ p q n h ≫= homologyπ_naturality (shufflePair X Y A B R S) n)

/-- **Compatibility with the absolute homology cross product** along `singularHomologyπ`. -/
@[reassoc (attr := simp)]
lemma singularHomologyπ_tensorHom_singularRelativeHomologyCross
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    ((TopPair.ofSubset A).singularHomologyπ R p ⊗ₘ (TopPair.ofSubset B).singularHomologyπ S q) ≫
        singularRelativeHomologyCross X Y R S A B p q n h =
      singularHomologyCross X Y R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomologyπ (R ⊗ S) n := by
  rw [singularRelativeHomologyCross_def]
  exact (homologyCross_comp_homologyMap_naturality
    (K := (toSSet.obj X).chainComplex R) (L := (toSSet.obj Y).chainComplex S)
    ((TopPair.ofSubset A).singularChainComplexπ R) ((TopPair.ofSubset B).singularChainComplexπ S)
    p q n h (shufflePair X Y A B R S) (shuffle X Y R S)
    ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S))
    (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S)).trans
    ((Category.assoc _ _ _).symm.trans
      (eq_whisker (singularHomologyCross_def X Y R S p q n h).symm _))

end Basic

/-- **Naturality of `singularRelativeHomologyCross`** in pair maps `(f, g)`. -/
@[reassoc]
lemma singularRelativeHomologyCross_naturality
    {X Y X' Y' : TopCat.{w}} {A : Set X} {B : Set Y} {A' : Set X'} {B' : Set Y'}
    (f : X ⟶ X') (g : Y ⟶ Y') (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A').singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B').singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B').singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hf) R p ⊗ₘ
        TopPair.singularHomologyMap (TopPair.ofSubsetMap g hg) S q) ≫
        singularRelativeHomologyCross X' Y' R S A' B' p q n h =
      singularRelativeHomologyCross X Y R S A B p q n h ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S) n := by
  rw [singularRelativeHomologyCross_def, singularRelativeHomologyCross_def]
  exact (homologyCross_comp_homologyMap_naturality
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R)
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) p q n h
    (shufflePair X' Y' A' B' R S) (shufflePair X Y A B R S)
    (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S))
    (shufflePair_naturality X Y A B R S f hf g hg)).trans (Category.assoc _ _ _).symm

/-- **Naturality of `singularRelativeHomologyCross`** in both coefficient objects. -/
@[reassoc]
lemma singularRelativeHomologyCross_coefficient_naturality
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) {R S R' S' : C} (φ : R ⟶ R') (ψ : S ⟶ S')
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset A).singularChainComplex R').homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S').cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopPair.ofSubset B).singularChainComplex S').X ((ComplexShape.down ℕ).prev q)))] :
    ((TopPair.ofSubset A).singularHomologyCoefficientMap φ p ⊗ₘ
        (TopPair.ofSubset B).singularHomologyCoefficientMap ψ q) ≫
        singularRelativeHomologyCross X Y R' S' A B p q n h =
      singularRelativeHomologyCross X Y R S A B p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomologyCoefficientMap
          (φ ⊗ₘ ψ) n := by
  rw [singularRelativeHomologyCross_def, singularRelativeHomologyCross_def]
  exact (homologyCross_comp_homologyMap_naturality
    ((TopPair.ofSubset A).singularChainComplexCoefficientMap φ)
    ((TopPair.ofSubset B).singularChainComplexCoefficientMap ψ)
    p q n h (shufflePair X Y A B R' S') (shufflePair X Y A B R S)
    ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexCoefficientMap
      (φ ⊗ₘ ψ))
    (shufflePair_coefficient_naturality X Y A B φ ψ)).trans (Category.assoc _ _ _).symm

end TopCat
