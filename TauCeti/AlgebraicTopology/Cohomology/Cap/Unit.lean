/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.CategoryTheory.Monoidal.Limits

/-!
# The unit law for the singular cap product

Capping with a constant degree-zero cochain leaves each simplex unchanged and applies the
resulting coefficient morphism. The same formula holds in homology for the class of the constant
cocycle. In particular, the class of the constant cocycle with value the identity of the tensor
unit acts as the identity on singular homology with any coefficient object.

Both coefficient formulas require a linear monoidal category with coproducts indexed by types
in the space's universe, and `tensorLeft M` must preserve these coproducts. The homology formula
also requires an abelian category. In the unit specialization, preservation follows from the
left unitor, which identifies tensoring on the left with the tensor unit with the identity
functor. For modules over a commutative ring, the tensor unit is the ring itself, so the last
formula is `x ⌢ 1 = x`. It is the unit law for the cap product of A. Hatcher,
*Algebraic Topology*, Section 3.3.

For explicit rewriting, use `TauCeti.capChain_constCochain (X := X)` and
`TauCeti.singularCap_constSingularCocycle (X := X)`. The space is otherwise inferred from the goal.
Both coefficient formulas are available to `simp` without opening the `TauCeti` namespace.
The direct unit identities are `TauCeti.capChain_unit` and `TauCeti.singularCap_unit`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Simplicial HomologicalComplex

universe w v u

namespace TauCeti

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- Capping with a constant degree-zero cochain is the map on chains induced by the coefficient
morphism `u ≫ e ▷ S ≫ μ`. -/
-- Simplify the application before `capChain_apply` unfolds the cap-chain map.
@[simp↓]
lemma capChain_constCochain {X : TopCat.{w}} (k : Type*) [Semiring k] [Linear k C]
    [MonoidalLinear k C] {R S T M P : C}
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P) (e : R ⟶ M) (n : ℕ) :
    ChainComplex.capChain k (X.alexanderWhitneyDiagonal u)
        ((TopCat.toSSet.obj X).chainComplexPairing μ) 0 n n (Nat.zero_add n)
        ((TopCat.toSSet.obj X).constCochain e) =
      (((_root_.SSet.chainComplexFunctor C).map (u ≫ e ▷ S ≫ μ)).app
        (TopCat.toSSet.obj X)).f n := by
  apply _root_.SSet.chainComplex_hom_ext
  intro σ
  simp only [TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal,
    _root_.SSet.ιChainComplex_constCochain, SimplexCategory.subinterval_zero_eq_id,
    op_id, Functor.map_id_apply, SSet.ιChainComplex_chainComplexFunctor_map_app_f,
    Category.assoc]

/-- Capping with the constant unit cochain is the identity, with arbitrary chain coefficients. -/
lemma capChain_unit {X : TopCat.{w}} (k : Type*) [Semiring k] [Linear k C]
    [MonoidalLinear k C] (S : C) (n : ℕ) :
    ChainComplex.capChain k (X.alexanderWhitneyDiagonal (λ_ S).inv)
        ((TopCat.toSSet.obj X).chainComplexPairing (λ_ S).hom) 0 n n (Nat.zero_add n)
        ((TopCat.toSSet.obj X).constCochain (𝟙 (𝟙_ C))) =
      𝟙 (((TopCat.toSSet.obj X).chainComplex S).X n) := by
  simp

end Chain

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- Capping with the class of a constant degree-zero cocycle is the map on singular homology
induced by the coefficient morphism `u ≫ e ▷ S ≫ μ`. -/
@[simp]
lemma singularCap_constSingularCocycle {X : TopCat.{w}} (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] {R S T M P : C}
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P) (e : R ⟶ M) (n : ℕ) :
    X.singularCap k u μ 0 n n (Nat.zero_add n)
        ((X.singularCochainComplex R k M).homologyπ 0 (X.constSingularCocycle k e)) =
      ((singularHomologyFunctor C n).map (u ≫ e ▷ S ≫ μ)).app X := by
  let f := ((_root_.SSet.chainComplexFunctor C).map (u ≫ e ▷ S ≫ μ)).app
    (TopCat.toSSet.obj X)
  have hc : ChainComplex.capCycles k (X.alexanderWhitneyDiagonal u)
      ((TopCat.toSSet.obj X).chainComplexPairing μ) 0 n n (Nat.zero_add n)
      (X.constSingularCocycle k e) = cyclesMap f n := by
    apply (cancel_mono (((TopCat.toSSet.obj X).chainComplex P).iCycles n)).1
    rw [ChainComplex.capCycles_i, cyclesMap_i, TopCat.iCycles_constSingularCocycle,
      capChain_constCochain]
  apply (cancel_epi (((TopCat.toSSet.obj X).chainComplex T).homologyπ n)).1
  rw [TopCat.singularCap_homologyπ, hc]
  -- The coefficient map of `singularHomologyFunctor` is definitionally `homologyMap f n`,
  -- since this functor is obtained by postcomposing singular chains with `homologyFunctor`.
  exact (homologyπ_naturality f n).symm

/-- Capping with the class of the constant unit cocycle is the identity on singular homology,
including degree zero, with arbitrary coefficients. -/
lemma singularCap_unit {X : TopCat.{w}} (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (S : C) (n : ℕ) :
    X.singularCap k (λ_ S).inv (λ_ S).hom 0 n n (Nat.zero_add n)
        ((X.singularCochainComplex (𝟙_ C) k (𝟙_ C)).homologyπ 0
          (X.constSingularCocycle k (𝟙 (𝟙_ C)))) =
      𝟙 (((singularHomologyFunctor C n).obj S).obj X) := by
  simp

end Homology

end TauCeti
