/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.Relative

/-!
# The cap product of relative cohomology with relative homology

For a topological pair `(X, A)`, a relative cochain `φ` of degree `p` vanishes on the singular
simplices of `A`. Capping a singular `n`-simplex `σ` of `X` with `φ` gives `φ(σ|[0, …, p])` times
the back face `σ|[p, …, n]`, so it vanishes as soon as `σ` lies in `A`: capping with a relative
cochain descends to relative chains, with values in the chains of `X`. On homology this is the
relative cap product

`Hᵖ(X, A; M) ⊗ Hₙ(X, A) ⟶ H_q(X)`,  `p + q = n`,

which is the cap product used in Poincaré and Lefschetz duality: capping relative cohomology
classes `Hᵖ(M, M ∖ K)` with the fundamental classes `Hₙ(M, M ∖ K)` of compact subsets of a
manifold `M`.

The construction descends the Alexander–Whitney diagonal `C(X) ⟶ C(X) ⊗ C(X)`, followed by the
quotient map on the first factor, to a chain map `C(X, A) ⟶ C(X, A) ⊗ C(X)`
(`TopPair.alexanderWhitneyDiagonal`, in
`TauCeti/AlgebraicTopology/Singular/AlexanderWhitney/Relative.lean`), and applies the cap product
of chains and cochains along a diagonal, `TauCeti.ChainComplex.cap`. The coefficients are as for
the absolute cap product `TopCat.singularCap`: a coefficient morphism `u : T ⟶ R ⊗ S` and a
pairing `μ : M ⊗ S ⟶ N` in an abelian monoidal category.

## Main definitions and results

* `TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal`: the relative
  cap product of the image of a singular simplex and a relative cochain.
* `TopPair.singularCap`: the relative cap product `Hᵖ(X, A; R, M) ⟶ (Hₙ(X, A; T) ⟶ H_q(X; N))`,
  with `TopPair.singularCap_homologyπ` computing it on classes of relative cycles and cocycles.
* `TopPair.singularCap_singularCohomologyπ`: compatibility with the absolute cap product,
  `x ⌢ j^*α = j_*x ⌢ α` for `j^* : Hᵖ(X, A) ⟶ Hᵖ(X)` and `j_* : Hₙ(X) ⟶ Hₙ(X, A)`.
* `TopPair.singularCap_naturality`: naturality in maps of pairs, the projection formula
  `f_*(x ⌢ f^*α) = f_*x ⌢ α`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the relative cap product `Hₙ(X, A) × Hᵖ(X, A) ⟶ H_{n - p}(X)`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial

universe w v u

namespace TopPair

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- Capping the image of a singular chain of `X` in the relative chains of `(X, A)` with a
relative cochain is capping the chain with the cochain of `X` it restricts to. -/
@[reassoc]
lemma singularChainComplexπ_capChain_alexanderWhitneyDiagonal (P : TopPair.{w}) (k : Type*)
    [Semiring k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N)
    (p q n : ℕ) (h : p + q = n) (φ : (P.singularChainComplex R).X p ⟶ M) :
    (P.singularChainComplexπ T).f n ≫
        TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p q n h φ =
      TauCeti.ChainComplex.capChain k (P.fst.alexanderWhitneyDiagonal u)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p q n h
        ((P.singularChainComplexπ R).f p ≫ φ) := by
  have := TauCeti.ChainComplex.capChain_naturality (k := k) (P.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (P.fst.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (P.singularChainComplexπ T)
    (P.singularChainComplexπ R) (𝟙 _) (𝟙 _)
    (singularChainComplexπ_alexanderWhitneyDiagonal P u) (by simp) p q n h φ
  rw [HomologicalComplex.id_f, Category.comp_id] at this
  exact this.symm

/-- **The relative cap product of a singular simplex and a relative cochain**: for a relative
cochain `φ` of degree `p`, capping the image in the relative chains of `(X, A)` of a singular
`(p + q)`-simplex `σ` of `X` with `φ` gives the back `q`-face of `σ`, with coefficient `φ` of the
image of the front `p`-face of `σ` paired with `S` through `μ`, after the coefficient morphism
`u`. -/
lemma ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal (P : TopPair.{w})
    (k : Type*) [Semiring k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N)
    (p q n : ℕ) (h : p + q = n) (φ : (P.singularChainComplex R).X p ⟶ M)
    (σ : (TopCat.toSSet.obj P.fst) _⦋n⦌) :
    (TopCat.toSSet.obj P.fst).ιChainComplex σ ≫ (P.singularChainComplexπ T).f n ≫
        TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p q n h φ =
      u ≫ (((TopCat.toSSet.obj P.fst).ιChainComplex
            ((TopCat.toSSet.obj P.fst).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
              (P.singularChainComplexπ R).f p ≫ φ) ▷ S) ≫
          μ ≫ (TopCat.toSSet.obj P.fst).ιChainComplex
            ((TopCat.toSSet.obj P.fst).map (SimplexCategory.subinterval p q (by omega)).op σ) :=
  (congrArg (_ ≫ ·)
    (singularChainComplexπ_capChain_alexanderWhitneyDiagonal P k u μ p q n h φ)).trans
      (TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal _ _ _ _ _ _ _ _ _)

end Chain

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The relative cap product** `Hᵖ(X, A; R, M) ⟶ (Hₙ(X, A; T) ⟶ H_q(X; N))` for `p + q = n`:
the cap product of relative homology and relative cohomology classes along the relative
Alexander–Whitney diagonal `P.alexanderWhitneyDiagonal u` and the chain map induced by the pairing
`μ : M ⊗ S ⟶ N`, `k`-linear in the cohomology class. -/
def singularCap (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n) :
    P.singularCohomology R k M p →ₗ[k]
      (P.singularHomology T n ⟶
        ((AlgebraicTopology.singularHomologyFunctor C q).obj N).obj P.fst) :=
  TauCeti.ChainComplex.cap k (P.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p q n h

/-- The relative cap product is the cap product of chains and cochains along the relative
Alexander–Whitney diagonal and the chain map induced by the coefficient pairing. -/
lemma singularCap_def (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n) :
    P.singularCap k u μ p q n h =
      TauCeti.ChainComplex.cap k (P.alexanderWhitneyDiagonal u)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p q n h :=
  (rfl)

/-- The relative cap product of the class of a relative cycle with the class of a relative cocycle
is the class of their cap product. -/
@[reassoc (attr := simp)]
lemma singularCap_homologyπ (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n)
    (φ : (P.singularCochainComplex R k M).cycles p) :
    (P.singularChainComplex T).homologyπ n ≫
        P.singularCap k u μ p q n h ((P.singularCochainComplex R k M).homologyπ p φ) =
      TauCeti.ChainComplex.capCycles k (P.alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p q n h φ ≫
        ((TopCat.toSSet.obj P.fst).chainComplex N).homologyπ q :=
  TauCeti.ChainComplex.cap_homologyπ _ _ _ _ _ _ _

/-- **Compatibility of the relative and absolute cap products**: for a class `α` of `Hᵖ(X, A)`
with image `j^*α` in `Hᵖ(X)`, and a class `x` of `Hₙ(X)` with image `j_*x` in `Hₙ(X, A)`,
`x ⌢ j^*α = j_*x ⌢ α`. -/
lemma singularCap_singularCohomologyπ (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n)
    (α : P.singularCohomology R k M p) :
    P.fst.singularCap k u μ p q n h (P.singularCohomologyπ R k M p α) =
      P.singularHomologyπ T n ≫ P.singularCap k u μ p q n h α := by
  have := TauCeti.ChainComplex.cap_naturality (k := k) (P.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (P.fst.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (P.singularChainComplexπ T)
    (P.singularChainComplexπ R) (𝟙 _) (𝟙 _)
    (singularChainComplexπ_alexanderWhitneyDiagonal P u) (by simp) p q n h α
  rw [HomologicalComplex.homologyMap_id, Category.comp_id] at this
  rw [TopCat.singularCap_def, singularCap_def]
  exact this

/-- **Naturality of the relative cap product**, the projection formula `f_*(x ⌢ f^*α) = f_*x ⌢ α`:
for a map of pairs `f : (X, A) ⟶ (Y, B)`, capping with the pull-back of a relative cohomology
class of `(Y, B)` and pushing forward along `f` is pushing forward along `f` and capping with the
class. -/
lemma singularCap_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (k : Type*) [Ring k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ)
    (h : p + q = n) (α : P'.singularCohomology R k M p) :
    P.singularCap k u μ p q n h (TopPair.singularCohomologyMap f p α) ≫
        ((AlgebraicTopology.singularHomologyFunctor C q).obj N).map (Hom.fst f) =
      TopPair.singularHomologyMap f T n ≫ P'.singularCap k u μ p q n h α :=
  TauCeti.ChainComplex.cap_naturality _ _ _ _ _ _ _ _
    (alexanderWhitneyDiagonal_naturality f u)
    (SSet.chainComplexPairing_naturality (TopCat.toSSet.map (Hom.fst f)) μ).symm p q n h α

end Homology

end TopPair
