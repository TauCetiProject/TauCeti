/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cup
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney

/-!
# The cup product in singular cohomology

Let `C` be a `k`-linear preadditive monoidal category with coproducts.  For a space `X`, the
cup product of singular cochains is the cup product of cochains
(`TauCeti.ChainComplex.cupCochain`) along the Alexander–Whitney diagonal
`X.alexanderWhitneyDiagonal u : C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of a coefficient morphism
`u : T ⟶ R ⊗ S` (`TopCat.alexanderWhitneyDiagonal`), for a pairing `μ : M ⊗ N ⟶ P` of
coefficient objects: a cochain `φ` of degree `p` with values in `M` and a cochain `ψ` of degree
`q` with values in `N` give the cochain of degree `n = p + q` with values in `P` whose value on a
singular simplex `σ` is `μ (φ (σ|[0, …, p]) ⊗ ψ (σ|[p, …, n]))`, precomposed with `u`
(`TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal`).  It satisfies the Leibniz rule
`TauCeti.ChainComplex.d_comp_cupCochain`, and so, when `C` is moreover abelian, descends to the
`k`-bilinear cup product `TopCat.singularCup` on singular cohomology, which is natural in `X`.

For the cohomology of `X` with coefficients in modules over a commutative ring `k`, take
`C := ModuleCat k`, `R = S = T = 𝟙_ (ModuleCat k)` (the module `k`) and `u = (λ_ _).inv`; then
`φ ⌣ ψ` evaluates `σ` to `μ (φ (σ|[0, …, p]) ⊗ ψ (σ|[p, …, n]))`, the cup product of Hatcher,
Section 3.2.

## Main definitions and results

* `TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal`: the cup product of singular
  cochains on a singular simplex.
* `TopCat.singularCup`: the cup product on singular cohomology, with `TopCat.singularCup_homologyπ`
  computing it on classes of cocycles and `TopCat.singularCup_naturality` its naturality.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial
  HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {k : Type*} [CommSemiring k] [Linear k C] [MonoidalLinear k C]
  {R S T M N P : C}

/-- **The cup product of singular cochains on a simplex**: for cochains `φ` of degree `p` and `ψ`
of degree `q`, the value of `φ ⌣ ψ` on a singular `(p + q)`-simplex `σ` is `φ` of the front
`p`-face of `σ` tensored with `ψ` of its back `q`-face, followed by `μ`, after the coefficient
morphism `u`. -/
lemma ιChainComplex_cupCochain_alexanderWhitneyDiagonal (X : TopCat.{w}) (u : T ⟶ R ⊗ S)
    (μ : M ⊗ N ⟶ P) (p q n : ℕ)
    (h : p + q = n) (φ : ((toSSet.obj X).chainComplex R).X p ⟶ M)
    (ψ : ((toSSet.obj X).chainComplex S).X q ⟶ N) (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫
        TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal u) μ p q n h φ ψ =
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
  rw [TauCeti.ChainComplex.cupCochain_apply, ιChainComplex_alexanderWhitneyDiagonal_f_assoc,
    Preadditive.sum_comp, Finset.sum_eq_single ⟨p, by omega⟩]
  · simp only [Category.assoc]
    exact congrArg (u ≫ ·) (key (p + q - p) (by omega) _ _)
  · rintro i - hi
    rw [Category.assoc, TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne _ _ _ _
      (fun h ↦ hi (Fin.ext h)), comp_zero]
  · simp

end Cochain

section Cohomology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N P : C}

/-- **The cup product on singular cohomology**,
`Hᵖ(X; R, M) × H^q(X; S, N) ⟶ Hⁿ(X; T, P)` for `p + q = n`: the cup product of cohomology classes
along the Alexander–Whitney diagonal `X.alexanderWhitneyDiagonal u` and the pairing
`μ : M ⊗ N ⟶ P`, `k`-bilinear and natural in `X` (`TopCat.singularCup_naturality`). -/
def singularCup (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n) :
    X.singularCohomology R k M p →ₗ[k] X.singularCohomology S k N q →ₗ[k]
      X.singularCohomology T k P n :=
  TauCeti.ChainComplex.cup k (X.alexanderWhitneyDiagonal u) μ p q n h

/-- The cup product of the classes of two singular cocycles is the class of their cup product. -/
@[simp]
lemma singularCup_homologyπ (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n)
    (a : (X.singularCochainComplex R k M).cycles p)
    (b : (X.singularCochainComplex S k N).cycles q) :
    X.singularCup k u μ p q n h ((X.singularCochainComplex R k M).homologyπ p a)
        ((X.singularCochainComplex S k N).homologyπ q b) =
      (X.singularCochainComplex T k P).homologyπ n
        (TauCeti.ChainComplex.cupCycles k (X.alexanderWhitneyDiagonal u) μ p q n h a b) :=
  TauCeti.ChainComplex.cup_homologyπ _ _ _ _ _ _ _ _

/-- **Naturality of the cup product**: for a continuous map `f : X ⟶ Y`, pulling back two
cohomology classes of `Y` along `f` and cupping them is pulling back their cup product. -/
lemma singularCup_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : p + q = n)
    (α : Y.singularCohomology R k M p) (β : Y.singularCohomology S k N q) :
    X.singularCup k u μ p q n h (TopCat.singularCohomologyMap f p α)
        (TopCat.singularCohomologyMap f q β) =
      TopCat.singularCohomologyMap f n (Y.singularCup k u μ p q n h α β) :=
  TauCeti.ChainComplex.cup_naturality _ μ _ _ _ _ (alexanderWhitneyDiagonal_naturality f u)
    p q n h α β

end Cohomology

end TopCat
