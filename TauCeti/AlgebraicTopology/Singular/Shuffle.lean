/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Shuffle
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney

/-!
# The shuffle map on singular chains

For topological spaces `X` and `Y`, `TopCat.shuffle X Y R S` is the Eilenberg--Mac Lane shuffle
map from the tensor product of the singular chains of `X` and `Y` to the singular chains of
`X × Y`.  It is the simplicial shuffle map followed by the chain map induced by the canonical
isomorphism
`Sing X × Sing Y ≅ Sing (X × Y)`.  The construction is natural in both spaces and both
coefficient objects.

The comparison with the simplicial shuffle map is recorded in both directions.  In particular,
composing with the map induced by the two projections recovers the simplicial shuffle map.  This
places the singular shuffle and Alexander--Whitney maps in the same product comparison and is the
input for their Eilenberg--Zilber chain homotopies.

## Main definitions and results

* `TopCat.shuffle`: the shuffle map on singular chains.
* `TopCat.shuffle_def`: its factorization through the simplicial shuffle map.
* `TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f`: its value on a pair of singular
  simplices.
* `TopCat.shuffle_naturality`: naturality in both spaces.
* `TopCat.shuffle_coefficient_naturality`: naturality in both coefficient objects.
* `TopCat.shuffle_comp_chainComplexMap_prodComparison`: projecting a shuffled singular chain
  recovers the simplicial shuffle map.
* `TopCat.shuffle_alexanderWhitney` and `TopCat.alexanderWhitney_shuffle`: the two singular
  composites expressed through the corresponding simplicial composites.

## References

* S. Eilenberg and S. Mac Lane, *On the groups `H(Π, n)`, I*, Ann. of Math. 58 (1953).
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial
  HomologicalComplex
open scoped Simplicial
open Functor.LaxMonoidal Functor.Monoidal Functor.OplaxMonoidal
open TauCeti.SSet (chainComplexMap_f_comp)

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- The Eilenberg--Mac Lane shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` on singular chains: the simplicial shuffle map,
followed by the map induced by the monoidal comparison
`Sing X × Sing Y ⟶ Sing (X × Y)`. -/
def shuffle (X Y : TopCat.{w}) (R S : C) :
    (toSSet.obj X).chainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      (toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S) :=
  SSet.shuffle (toSSet.obj X) (toSSet.obj Y) R S ≫
    SSet.chainComplexMap (Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S)

/-- The singular shuffle map is the simplicial shuffle map followed by the chain map induced by
the monoidal product comparison `Sing X × Sing Y ⟶ Sing (X × Y)`. -/
lemma shuffle_def (X Y : TopCat.{w}) (R S : C) :
    shuffle X Y R S = SSet.shuffle (toSSet.obj X) (toSSet.obj Y) R S ≫
      SSet.chainComplexMap (Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S) :=
  (rfl)

/-- The singular shuffle map on the summand of a `p`-simplex `x` of `X` and a `q`-simplex `y`
of `Y` is the image of the shuffle chain under the map to `Sing (X × Y)` classified by
`(x, y)`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_tensorHom_ιChainComplex_shuffle_f {X Y : TopCat.{w}} (R S : C)
    {p q n : ℕ} (x : (toSSet.obj X) _⦋p⦌) (y : (toSSet.obj Y) _⦋q⦌) (h : p + q = n) :
    ((toSSet.obj X).ιChainComplex x ⊗ₘ (toSSet.obj Y).ιChainComplex y) ≫
        ιTensorObj _ _ p q n h ≫ (shuffle X Y R S).f n =
      SSet.shuffleChain (R ⊗ S) p q n h ≫
        (SSet.chainComplexMap
          ((SSet.yonedaEquiv.symm x ⊗ₘ SSet.yonedaEquiv.symm y) ≫
            Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S)).f n := by
  rw [shuffle, HomologicalComplex.comp_f,
    SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_assoc,
    chainComplexMap_f_comp]

/-- In degree zero, the singular shuffle map sends a pair of singular vertices to the
corresponding vertex of the product. -/
lemma ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero {X Y : TopCat.{w}} (R S : C)
    (x : (toSSet.obj X) _⦋0⦌) (y : (toSSet.obj Y) _⦋0⦌) :
    ((toSSet.obj X).ιChainComplex x ⊗ₘ (toSSet.obj Y).ιChainComplex y) ≫
        ιTensorObj _ _ 0 0 0 rfl ≫ (shuffle X Y R S).f 0 =
      (toSSet.obj (X ⊗ Y)).ιChainComplex
        ((Functor.LaxMonoidal.μ toSSet X Y).app _
          ((x, y) : (toSSet.obj X ⊗ toSSet.obj Y) _⦋0⦌)) := by
  let z : (toSSet.obj X ⊗ toSSet.obj Y) _⦋0⦌ := (x, y)
  calc
    _ = (toSSet.obj X ⊗ toSSet.obj Y).ιChainComplex (R := R ⊗ S) z ≫
        (SSet.chainComplexMap (Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S)).f 0 := by
      simpa only [shuffle, HomologicalComplex.comp_f, ← Category.assoc] using
        congrArg (· ≫ (SSet.chainComplexMap
          (Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S)).f 0)
          (SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero
            (toSSet.obj X) (toSSet.obj Y) R S x y)
    _ = _ := SSet.ι_chainComplexMap_f (toSSet.obj X ⊗ toSSet.obj Y)
      (toSSet.obj (X ⊗ Y)) (Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S) z

/-- The shuffle map on singular chains is natural in both spaces. -/
@[reassoc]
lemma shuffle_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (R S : C) :
    (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        shuffle X' Y' R S =
      shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) := by
  rw [shuffle, shuffle, Category.assoc, SSet.shuffle_naturality_assoc,
    ← Functor.map_comp, Functor.LaxMonoidal.μ_natural, Functor.map_comp]

/-- The shuffle map on singular chains is natural in both coefficient objects. -/
@[reassoc]
lemma shuffle_coefficient_naturality (X Y : TopCat.{w}) {R S R' S' : C}
    (f : R ⟶ R') (g : S ⟶ S') :
    (((SSet.chainComplexFunctor C).map f).app (toSSet.obj X) ⊗ₘ
        ((SSet.chainComplexFunctor C).map g).app (toSSet.obj Y)) ≫ shuffle X Y R' S' =
      shuffle X Y R S ≫
        ((SSet.chainComplexFunctor C).map (f ⊗ₘ g)).app (toSSet.obj (X ⊗ Y)) := by
  rw [shuffle, shuffle, Category.assoc, SSet.shuffle_coefficient_naturality_assoc,
    ← ((SSet.chainComplexFunctor C).map (f ⊗ₘ g)).naturality]

/-- Projecting a shuffled singular chain to the product of the two singular simplicial sets
recovers the simplicial shuffle map. -/
@[reassoc]
lemma shuffle_comp_chainComplexMap_prodComparison (X Y : TopCat.{w}) (R S : C) :
    shuffle X Y R S ≫
        SSet.chainComplexMap (CartesianMonoidalCategory.prodComparison toSSet X Y) (R ⊗ S) =
      SSet.shuffle (toSSet.obj X) (toSSet.obj Y) R S := by
  simp only [shuffle, Category.assoc, ← Functor.map_comp, ← δ_of_cartesianMonoidalCategory,
    Functor.Monoidal.μ_δ]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The singular composite `shuffle ≫ alexanderWhitney` is the corresponding simplicial
composite, under the canonical identification `Sing (X × Y) ≅ Sing X × Sing Y`. -/
@[reassoc]
lemma shuffle_alexanderWhitney (X Y : TopCat.{w}) (R S : C) :
    shuffle X Y R S ≫ alexanderWhitney X Y R S =
      SSet.shuffle (toSSet.obj X) (toSSet.obj Y) R S ≫
        SSet.alexanderWhitney (toSSet.obj X) (toSSet.obj Y) R S := by
  rw [alexanderWhitney_def, ← Category.assoc,
    shuffle_comp_chainComplexMap_prodComparison]

/-- The singular composite `alexanderWhitney ≫ shuffle` is the simplicial composite conjugated
by the canonical product comparison `Sing (X × Y) ≅ Sing X × Sing Y`. -/
@[reassoc]
lemma alexanderWhitney_shuffle (X Y : TopCat.{w}) (R S : C) :
    alexanderWhitney X Y R S ≫ shuffle X Y R S =
      SSet.chainComplexMap (CartesianMonoidalCategory.prodComparison toSSet X Y) (R ⊗ S) ≫
        (SSet.alexanderWhitney (toSSet.obj X) (toSSet.obj Y) R S ≫
          SSet.shuffle (toSSet.obj X) (toSSet.obj Y) R S) ≫
        SSet.chainComplexMap (Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S) := by
  rw [alexanderWhitney_def, shuffle_def]
  simp only [Category.assoc]

end TopCat
