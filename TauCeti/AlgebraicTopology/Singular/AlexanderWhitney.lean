/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Algebra.Homology.Monoidal.TensorCochain
public import TauCeti.AlgebraicTopology.SimplicialSet.AlexanderWhitney

/-!
# The Alexander–Whitney map on singular chains

For topological spaces `X` and `Y`, `TopCat.alexanderWhitney X Y R S` is the Alexander–Whitney
chain map from the singular chains of `X × Y` with coefficients in `R ⊗ S` to the tensor product of
the singular chains of `X` and of `Y`.  A singular simplex `σ` of `X × Y` is sent to
`∑_{p + q = n} (pr₁ ∘ σ)|[0, …, p] ⊗ (pr₂ ∘ σ)|[p, …, n]`: it is the simplicial Alexander–Whitney
map `SSet.alexanderWhitney` precomposed with the map `Sing(X × Y) ⟶ Sing X × Sing Y` induced by the
two projections (`CartesianMonoidalCategory.prodComparison`).  It is natural in both spaces.

For a single space `X` and a coefficient morphism `u : T ⟶ R ⊗ S`, the Alexander–Whitney diagonal
`X.alexanderWhitneyDiagonal u : C(X; T) ⟶ C(X; R) ⊗ C(X; S)` is `u`, followed by the chain map
induced by the diagonal `X ⟶ X × X` and by `TopCat.alexanderWhitney X X R S`.  It sends a singular
simplex `σ` to `∑_{p + q = n} σ|[0, …, p] ⊗ σ|[p, …, n]`, and is natural in `X`.  Cup products
of singular cochains and cap products of singular chains with singular cochains are taken along it.

## Main definitions and results

* `TopCat.alexanderWhitney`: the Alexander–Whitney map on singular chains.
* `TopCat.ιChainComplex_alexanderWhitney_f`: its value on a singular simplex.
* `TopCat.alexanderWhitney_naturality`: it is natural in both spaces.
* `TopCat.alexanderWhitney_coefficient_naturality`: it is natural in both coefficient objects.
* `TopCat.alexanderWhitneyDiagonal`: the Alexander–Whitney diagonal of a space, with
  `TopCat.ιChainComplex_alexanderWhitneyDiagonal_f` its value on a singular simplex and
  `TopCat.alexanderWhitneyDiagonal_naturality` its naturality.
* `TopCat.ιChainComplex_alexanderWhitneyDiagonal_f_tensorCochain`: the tensor product of two
  cochains, precomposed with the Alexander–Whitney diagonal, on a singular simplex.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, for the front and back faces of a singular simplex.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]

/-- The Alexander–Whitney map `C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` on singular chains: the
simplicial Alexander–Whitney map of `Sing X` and `Sing Y`, precomposed with the comparison map
`Sing(X × Y) ⟶ Sing X × Sing Y` induced by the two projections of `X × Y`. -/
def alexanderWhitney (X Y : TopCat.{w}) (R S : C) :
    (toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S) ⟶
      (toSSet.obj X).chainComplex R ⊗ (toSSet.obj Y).chainComplex S :=
  SSet.chainComplexMap (CartesianMonoidalCategory.prodComparison toSSet X Y) (R ⊗ S) ≫
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
  -- `prodComparison` is the `lift` of the two projections, whose components on simplices are, by
  -- definition, the pairs of components
  rfl

/-- The Alexander–Whitney map on singular chains is natural in both spaces. -/
@[reassoc]
lemma alexanderWhitney_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (R S : C) :
    SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) ≫ alexanderWhitney X' Y' R S =
      alexanderWhitney X Y R S ≫
        (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) := by
  rw [alexanderWhitney, alexanderWhitney, ← Category.assoc, ← Functor.map_comp,
    CartesianMonoidalCategory.prodComparison_natural,
    Functor.map_comp, Category.assoc, SSet.alexanderWhitney_naturality, Category.assoc]

/-- The Alexander–Whitney map on singular chains is natural in both coefficient objects. -/
@[reassoc]
lemma alexanderWhitney_coefficient_naturality (X Y : TopCat.{w}) {R S R' S' : C}
    (f : R ⟶ R') (g : S ⟶ S') :
    ((SSet.chainComplexFunctor C).map (f ⊗ₘ g)).app (toSSet.obj (X ⊗ Y)) ≫
        alexanderWhitney X Y R' S' =
      alexanderWhitney X Y R S ≫
        (((SSet.chainComplexFunctor C).map f).app (toSSet.obj X) ⊗ₘ
          ((SSet.chainComplexFunctor C).map g).app (toSSet.obj Y)) := by
  rw [alexanderWhitney, alexanderWhitney, ← Category.assoc,
    ← ((SSet.chainComplexFunctor C).map (f ⊗ₘ g)).naturality
      (CartesianMonoidalCategory.prodComparison toSSet X Y),
    Category.assoc, SSet.alexanderWhitney_coefficient_naturality, Category.assoc]

section AlexanderWhitneyDiagonal

open HomologicalComplex

variable {R S T : C}

/-- **The Alexander–Whitney diagonal** `C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of a space `X`: the
coefficient morphism `u : T ⟶ R ⊗ S`, followed by the chain map induced by the diagonal
`X ⟶ X × X` and by the Alexander–Whitney map `TopCat.alexanderWhitney X X R S`. -/
def alexanderWhitneyDiagonal (X : TopCat.{w}) (u : T ⟶ R ⊗ S) :
    (toSSet.obj X).chainComplex T ⟶ (toSSet.obj X).chainComplex R ⊗ (toSSet.obj X).chainComplex S :=
  ((SSet.chainComplexFunctor C).map u).app _ ≫
    SSet.chainComplexMap (toSSet.map (lift (𝟙 X) (𝟙 X))) (R ⊗ S) ≫ alexanderWhitney X X R S

/-- The Alexander–Whitney diagonal sends a singular `n`-simplex `σ` to
`∑_{p + q = n} σ|[0, …, p] ⊗ σ|[p, …, n]`, after the coefficient morphism `u`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_alexanderWhitneyDiagonal_f (X : TopCat.{w}) (u : T ⟶ R ⊗ S) {n : ℕ}
    (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫ (X.alexanderWhitneyDiagonal u).f n =
      u ≫ ∑ p : Fin (n + 1),
        ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ⊗ₘ
          (toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval p (n - p) (by omega)).op σ)) ≫
          ιTensorObj _ _ (p : ℕ) (n - p) n (by omega) := by
  have hfst : (toSSet.map (fst X X)).app _ ((toSSet.map (lift (𝟙 X) (𝟙 X))).app _ σ) = σ := by
    rw [← NatTrans.comp_app_apply, ← CategoryTheory.Functor.map_comp, lift_fst,
      CategoryTheory.Functor.map_id]
    rfl
  have hsnd : (toSSet.map (snd X X)).app _ ((toSSet.map (lift (𝟙 X) (𝟙 X))).app _ σ) = σ := by
    rw [← NatTrans.comp_app_apply, ← CategoryTheory.Functor.map_comp, lift_snd,
      CategoryTheory.Functor.map_id]
    rfl
  simp only [alexanderWhitneyDiagonal, comp_f,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc, SSet.ι_chainComplexMap_f_assoc,
    ιChainComplex_alexanderWhitney_f, hfst, hsnd]
  -- the simplex of `Sing X ⊗ Sing X` is the pair `(σ, σ)`
  exact congrArg (u ≫ ·) (SSet.ιChainComplex_alexanderWhitney_f (toSSet.obj X) (toSSet.obj X) R S
    (n := n) (σ, σ))

/-- The tensor product of cochains `φ` of degree `p` and `ψ` of degree `q`
(`TauCeti.ChainComplex.tensorCochain`), precomposed with the Alexander–Whitney diagonal, sends a
singular `(p + q)`-simplex `σ` to `φ` of the front `p`-face of `σ` tensored with `ψ` of its back
`q`-face, followed by `μ`, after the coefficient morphism `u`.  This evaluates both the cup and the
cap product of singular cochains on a simplex. -/
lemma ιChainComplex_alexanderWhitneyDiagonal_f_tensorCochain (X : TopCat.{w}) (u : T ⟶ R ⊗ S)
    {M N P : C} (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n)
    (φ : ((toSSet.obj X).chainComplex R).X p ⟶ M) (ψ : ((toSSet.obj X).chainComplex S).X q ⟶ N)
    (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫ (X.alexanderWhitneyDiagonal u).f n ≫
        TauCeti.ChainComplex.tensorCochain μ φ ψ n =
      u ≫ (((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
          ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ ψ)) ≫ μ := by
  subst h
  -- the summand of bidegree `(p, j)` for `j = q`, stated for any such `j`
  have key : ∀ (j : ℕ) (hj : j = q) (hj' : p + j ≤ p + q) (hj'' : p + j = p + q),
      ((toSSet.obj X).ιChainComplex
          ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ⊗ₘ
        (toSSet.obj X).ιChainComplex (R := S)
          ((toSSet.obj X).map (SimplexCategory.subinterval p j hj').op σ)) ≫
        ιTensorObj _ _ p j (p + q) hj'' ≫ TauCeti.ChainComplex.tensorCochain μ φ ψ (p + q) =
      (((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
          ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ ψ)) ≫ μ := by
    rintro _ rfl _ _
    rw [TauCeti.ChainComplex.ιTensorObj_tensorCochain, tensorHom_comp_tensorHom_assoc]
  rw [ιChainComplex_alexanderWhitneyDiagonal_f_assoc, Preadditive.sum_comp,
    Finset.sum_eq_single ⟨p, by omega⟩]
  · simp only [Category.assoc]
    exact congrArg (u ≫ ·) (key (p + q - p) (by omega) _ _)
  · rintro i - hi
    rw [Category.assoc, TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne_left _ _ _ _
      (fun h ↦ hi (Fin.ext h)), comp_zero]
  · simp

/-- The Alexander–Whitney diagonal is natural in the space. -/
@[reassoc]
lemma alexanderWhitneyDiagonal_naturality {X Y : TopCat.{w}} (f : X ⟶ Y)
    (u : T ⟶ R ⊗ S) :
    SSet.chainComplexMap (toSSet.map f) T ≫ Y.alexanderWhitneyDiagonal u =
      X.alexanderWhitneyDiagonal u ≫
        (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map f) S) := by
  have hdiag : f ≫ lift (𝟙 Y) (𝟙 Y) = lift (𝟙 X) (𝟙 X) ≫ (f ⊗ₘ f) := by
    ext <;> simp
  rw [alexanderWhitneyDiagonal, alexanderWhitneyDiagonal, Category.assoc, Category.assoc,
    ((SSet.chainComplexFunctor C).map u).naturality_assoc,
    ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp, hdiag, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp_assoc, alexanderWhitney_naturality]

end AlexanderWhitneyDiagonal

end TopCat
