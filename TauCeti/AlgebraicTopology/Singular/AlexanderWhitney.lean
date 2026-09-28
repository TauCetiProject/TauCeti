/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialSet.AlexanderWhitney

/-!
# The Alexander–Whitney map on singular chains

For topological spaces `X` and `Y`, `TopCat.alexanderWhitney X Y R S` is the Alexander–Whitney
chain map from the singular chains of `X × Y` with coefficients in `R ⊗ S` to the tensor product of
the singular chains of `X` and of `Y`.  A singular simplex `σ` of `X × Y` is sent to
`∑_{p + q = n} (pr₁ ∘ σ)|[0, …, p] ⊗ (pr₂ ∘ σ)|[p, …, n]`: it is the simplicial Alexander–Whitney
map `SSet.alexanderWhitney` precomposed with the map `Sing(X × Y) ⟶ Sing X × Sing Y` induced by the
two projections.  It is natural in both spaces.

## Main definitions and results

* `TopCat.alexanderWhitney`: the Alexander–Whitney map on singular chains.
* `TopCat.ιChainComplex_alexanderWhitney_f`: its value on a singular simplex.
* `TopCat.alexanderWhitney_naturality`: it is natural in both spaces.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, for the front and back faces of a singular simplex.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]

/-- The Alexander–Whitney map `C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` on singular chains: the
simplicial Alexander–Whitney map of `Sing X` and `Sing Y`, precomposed with the map induced by the
two projections of `X × Y`. -/
def alexanderWhitney (X Y : TopCat.{w}) (R S : C) :
    (toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S) ⟶
      (toSSet.obj X).chainComplex R ⊗ (toSSet.obj Y).chainComplex S :=
  SSet.chainComplexMap (lift (toSSet.map (fst X Y)) (toSSet.map (snd X Y))) (R ⊗ S) ≫
    SSet.alexanderWhitney _ _ R S

/-- The Alexander–Whitney map on the summand of a singular simplex `σ` of `X × Y` is the
simplicial Alexander–Whitney map on the pair of its projections to `X` and `Y`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_alexanderWhitney_f {X Y : TopCat.{w}} (R S : C) {n : ℕ}
    (σ : (toSSet.obj (X ⊗ Y)) _⦋n⦌) :
    (toSSet.obj (X ⊗ Y)).ιChainComplex σ ≫ (alexanderWhitney X Y R S).f n =
      (toSSet.obj X ⊗ toSSet.obj Y).ιChainComplex
          ((toSSet.map (fst X Y)).app _ σ, (toSSet.map (snd X Y)).app _ σ) ≫
        (SSet.alexanderWhitney _ _ R S).f n := by
  simp only [alexanderWhitney, HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc]
  -- the components of `lift f g` on simplices are, by definition, the pairs of components
  rfl

/-- The Alexander–Whitney map on singular chains is natural in both spaces. -/
@[reassoc]
lemma alexanderWhitney_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (R S : C) :
    SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) ≫ alexanderWhitney X' Y' R S =
      alexanderWhitney X Y R S ≫
        (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) := by
  have h : toSSet.map (f ⊗ₘ g) ≫ lift (toSSet.map (fst X' Y')) (toSSet.map (snd X' Y')) =
      lift (toSSet.map (fst X Y)) (toSSet.map (snd X Y)) ≫ (toSSet.map f ⊗ₘ toSSet.map g) := by
    ext1 <;> simp [← Functor.map_comp]
  rw [alexanderWhitney, alexanderWhitney, ← Category.assoc, ← Functor.map_comp, h,
    Functor.map_comp, Category.assoc, SSet.alexanderWhitney_naturality, Category.assoc]

end TopCat
