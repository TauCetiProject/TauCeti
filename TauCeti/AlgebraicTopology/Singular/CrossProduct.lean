/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber

/-!
# The cross product in singular homology

For topological spaces `X` and `Y` and coefficient objects `R` and `S`, the homology cross
product is the morphism

`Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)`, for `p + q = n`.

It is the cross product `HomologicalComplex.homologyCross` of the singular chain complexes,
`Hₚ(C(X; R)) ⊗ H_q(C(Y; S)) ⟶ Hₙ(C(X; R) ⊗ C(Y; S))`, followed by the map on homology induced
by the Eilenberg–Mac Lane shuffle map `C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)`.  On classes of
cycles `a` and `b` it is the class of the shuffle product `a × b`.  It is natural in both spaces
and in both coefficient objects.  As for `HomologicalComplex.homologyCross`, each declaration
only assumes that tensoring preserves cokernels for the three objects the construction uses:
`tensorLeft` of `Hₚ(C(X; R))`, and `tensorRight` of the cycles `Z_q(C(Y; S))` and of the chains
`C_{q+1}(Y; S)`.  For `ModuleCat` these are found by instance search.

By the Eilenberg–Zilber theorem the shuffle map is a chain homotopy equivalence with homotopy
inverse the Alexander–Whitney map, so the map induced by Alexander–Whitney on homology recovers
the algebraic cross product (`TopCat.singularHomologyCross_comp_homologyMap_alexanderWhitney`).
So the Künneth theorem over a field, that the direct sum over all `p + q = n` of the homology
cross products `Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₙ(X × Y; k)` is an isomorphism, reduces to the
corresponding statement for the direct sum of the algebraic cross products of the singular chain
complexes.

## Main definitions and results

* `TopCat.singularHomologyCross`: the homology cross product.
* `TopCat.homologyπ_tensorHom_singularHomologyCross`: its value on classes of cycles.
* `TopCat.singularHomologyCross_naturality` and
  `TopCat.singularHomologyCross_coefficient_naturality`: naturality in the spaces and in the
  coefficients.
* `TopCat.singularHomologyCross_comp_homologyMap_alexanderWhitney`: under the Eilenberg–Zilber
  isomorphism, the homology cross product is the cross product of the singular chain complexes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the cross product in homology.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- **The homology cross product** `Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)` for `p + q = n`:
the cross product of the singular chain complexes followed by the shuffle map. -/
def singularHomologyCross (X Y : TopCat.{w}) (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    ((singularHomologyFunctor C p).obj R).obj X ⊗ ((singularHomologyFunctor C q).obj S).obj Y ⟶
      ((singularHomologyFunctor C n).obj (R ⊗ S)).obj (X ⊗ Y) :=
  homologyCross ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p q n h ≫
    homologyMap (shuffle X Y R S) n

/-- The homology cross product is the cross product of the singular chain complexes followed by
the map induced by the shuffle map. -/
lemma singularHomologyCross_def (X Y : TopCat.{w}) (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    singularHomologyCross X Y R S p q n h =
      homologyCross ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p q n h ≫
        homologyMap (shuffle X Y R S) n :=
  (rfl)

/-- The cross product of the classes of two singular cycles is the class of their shuffle
product. -/
@[simp, reassoc]
lemma homologyπ_tensorHom_singularHomologyCross (X Y : TopCat.{w}) (R S : C) (p q n : ℕ)
    (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    (((toSSet.obj X).chainComplex R).homologyπ p ⊗ₘ ((toSSet.obj Y).chainComplex S).homologyπ q) ≫
        singularHomologyCross X Y R S p q n h =
      cyclesCross ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p q n h ≫
        cyclesMap (shuffle X Y R S) n ≫
          ((toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S)).homologyπ n :=
  (homologyπ_tensorHom_homologyCross_assoc _ _ p q n h _).trans
    (cyclesCross _ _ p q n h ≫= homologyπ_naturality (shuffle X Y R S) n)

/-- **Naturality of the homology cross product** in both spaces:
`f_* a × g_* b = (f × g)_* (a × b)`. -/
@[reassoc]
lemma singularHomologyCross_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X').chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    (((singularHomologyFunctor C p).obj R).map f ⊗ₘ ((singularHomologyFunctor C q).obj S).map g) ≫
        singularHomologyCross X' Y' R S p q n h =
      singularHomologyCross X Y R S p q n h ≫
        ((singularHomologyFunctor C n).obj (R ⊗ S)).map (f ⊗ₘ g) := by
  -- `Hₙ(f)` is by definition the homology of the induced chain map, so the statement is the
  -- naturality of the algebraic cross product followed by that of the shuffle map.
  have hsh : HomologicalComplex.tensorHom (SSet.chainComplexMap (toSSet.map f) R)
      (SSet.chainComplexMap (toSSet.map g) S) ≫ shuffle X' Y' R S =
        shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) :=
    shuffle_naturality f g R S
  have := homologyCross_naturality_assoc (SSet.chainComplexMap (toSSet.map f) R)
    (SSet.chainComplexMap (toSSet.map g) S) p q n h (homologyMap (shuffle X' Y' R S) n)
  rw [← homologyMap_comp, hsh, homologyMap_comp] at this
  exact this.trans (Category.assoc _ _ _).symm

/-- **Naturality of the homology cross product** in both coefficient objects. -/
@[reassoc]
lemma singularHomologyCross_coefficient_naturality (X Y : TopCat.{w}) {R S R' S' : C}
    (φ : R ⟶ R') (ψ : S ⟶ S') (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R').homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S').cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S').X ((ComplexShape.down ℕ).prev q)))] :
    (((singularHomologyFunctor C p).map φ).app X ⊗ₘ ((singularHomologyFunctor C q).map ψ).app Y) ≫
        singularHomologyCross X Y R' S' p q n h =
      singularHomologyCross X Y R S p q n h ≫
        ((singularHomologyFunctor C n).map (φ ⊗ₘ ψ)).app (X ⊗ Y) := by
  -- `Hₙ(-; φ)` is by definition the homology of the induced chain map, so the statement is the
  -- naturality of the algebraic cross product followed by that of the shuffle map.
  have hsh : HomologicalComplex.tensorHom (((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X))
      (((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y)) ≫ shuffle X Y R' S' =
        shuffle X Y R S ≫ ((SSet.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app (toSSet.obj (X ⊗ Y)) :=
    shuffle_coefficient_naturality X Y φ ψ
  have := homologyCross_naturality_assoc (((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X))
    (((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y)) p q n h
    (homologyMap (shuffle X Y R' S') n)
  rw [← homologyMap_comp, hsh, homologyMap_comp] at this
  exact this.trans (Category.assoc _ _ _).symm

/-- **The homology cross product under Eilenberg–Zilber**: following the homology cross product
by the map induced by the Alexander–Whitney map gives the cross product of the singular chain
complexes.  Since the Alexander–Whitney map is a chain homotopy equivalence, this identifies the
homology cross product with the algebraic one. -/
@[simp, reassoc]
lemma singularHomologyCross_comp_homologyMap_alexanderWhitney (X Y : TopCat.{w}) (R S : C)
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    singularHomologyCross X Y R S p q n h ≫ homologyMap (alexanderWhitney X Y R S) n =
      homologyCross ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p q n h :=
  (Category.assoc _ _ _).trans <| (homologyCross _ _ p q n h ≫=
    ((homologyMap_comp _ _ n).symm.trans
      (((shuffleAlexanderWhitneyHomotopy X Y R S).homologyMap_eq n).trans
        (homologyMap_id _ n)))).trans (Category.comp_id _)

end TopCat
