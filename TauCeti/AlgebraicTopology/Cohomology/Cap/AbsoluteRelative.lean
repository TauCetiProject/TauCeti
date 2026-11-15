/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.Connecting
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup

/-!
# The cap product of absolute cohomology with relative homology

For a topological pair `(X, A)`, capping a singular `n`-simplex `σ` of `X` with a cochain `φ` of
`X` of degree `p` gives `φ(σ|[0, …, p])` times the back face `σ|[p, …, n]`.  If `σ` lies in `A`,
so does its back face: capping with an absolute cochain sends the chains of `A` to chains of `A`,
and descends to relative chains, with values in relative chains.  On homology this is the cap
product

`Hᵖ(X; M) ⊗ Hₙ(X, A) ⟶ H_q(X, A)`,  `p + q = n`,

the second of the two same-pair cap products, next to `Hᵖ(X, A) ⊗ Hₙ(X, A) ⟶ H_q(X)` of
`TopPair.singularCap`.  It is the cap product of Poincaré–Lefschetz duality: for a compact
`R`-oriented `m`-manifold `M` with boundary, capping with the relative fundamental class
`[M] ∈ Hₘ(M, ∂M; R)` is an isomorphism `Hᵖ(M; R) ≅ H_{m - p}(M, ∂M; R)`.

The construction caps along the descent `C(X, A) ⟶ C(X) ⊗ C(X, A)` of the Alexander–Whitney
diagonal, followed by the quotient map on the second factor
(`TopPair.rightAlexanderWhitneyDiagonal`, in
`TauCeti/AlgebraicTopology/Singular/AlexanderWhitney/RelativeCup.lean`), and lets the coefficients
act on relative chains through the descent `M ⊗ C(X, A; S) ⟶ C(X, A; N)` of the coefficient
pairing (`SSetPair.chainComplexPairing`).  The coefficients are as for the absolute cap product
`TopCat.singularCap`: a coefficient morphism `u : T ⟶ R ⊗ S` and a pairing `μ : M ⊗ S ⟶ N` in an
abelian monoidal category.

## Main definitions and results

* `TopPair.absoluteSingularCap`: the cap product `Hᵖ(X; R, M) ⟶ (Hₙ(X, A; T) ⟶ H_q(X, A; N))`,
  with `TopPair.absoluteSingularCap_homologyπ` computing it on classes of relative cycles and
  absolute cocycles.
* `TopPair.singularHomologyπ_comp_absoluteSingularCap`: compatibility with the absolute cap product,
  `j_*(x ⌢ α) = j_*x ⌢ α` for `j_* : Hₙ(X) ⟶ Hₙ(X, A)`.
* `TopPair.absoluteSingularCap_naturality`: naturality in maps of pairs, the projection formula
  `f_*(x ⌢ f^*α) = f_*x ⌢ α`.
* `TopPair.absoluteSingularCap_comp_singularHomologyδ`: compatibility with the connecting morphism
  `∂` of the pair, `∂(x ⌢ α) = (-1)^p ∂x ⌢ α|_A`.

With the absolute cap product on `X` and on `A`, capping with `α` therefore commutes, up to the
sign `(-1)^p` at the connecting morphisms, with the maps of the long exact sequence of the pair:
with `i_*` by `TopCat.singularCap_naturality`, with `j_*` by
`TopPair.singularHomologyπ_comp_absoluteSingularCap`, and with `∂` by
`TopPair.absoluteSingularCap_comp_singularHomologyδ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the relative cap product `Hₙ(X, A) × Hᵖ(X) ⟶ H_{n - p}(X, A)` and its
  compatibility with the long exact sequences of pairs used for Lefschetz duality.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TopPair

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The cap product of absolute cohomology with relative homology**,
`Hᵖ(X; R, M) ⟶ (Hₙ(X, A; T) ⟶ H_q(X, A; N))` for `p + q = n`: the cap product of relative
homology classes and absolute cohomology classes along the right relative Alexander–Whitney
diagonal `P.rightAlexanderWhitneyDiagonal u` and the chain map on relative chains induced by the
pairing `μ : M ⊗ S ⟶ N`, `k`-linear in the cohomology class. -/
def absoluteSingularCap (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n) :
    P.fst.singularCohomology R k M p →ₗ[k] (P.singularHomology T n ⟶ P.singularHomology N q) :=
  TauCeti.ChainComplex.cap k (P.rightAlexanderWhitneyDiagonal u)
    ((toSSetPair.obj P).chainComplexPairing μ) p q n h

/-- The cap product of absolute cohomology with relative homology is the cap product of chains and
cochains along the right relative Alexander–Whitney diagonal and the chain map on relative chains
induced by the coefficient pairing. -/
lemma absoluteSingularCap_def (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n) :
    P.absoluteSingularCap k u μ p q n h =
      TauCeti.ChainComplex.cap k (P.rightAlexanderWhitneyDiagonal u)
        ((toSSetPair.obj P).chainComplexPairing μ) p q n h :=
  (rfl)

/-- The cap product of the class of a relative cycle with the class of an absolute cocycle is the
class of their cap product. -/
@[reassoc (attr := simp)]
lemma absoluteSingularCap_homologyπ (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n)
    (φ : (P.fst.singularCochainComplex R k M).cycles p) :
    (P.singularChainComplex T).homologyπ n ≫
        P.absoluteSingularCap k u μ p q n h
          ((P.fst.singularCochainComplex R k M).homologyπ p φ) =
      TauCeti.ChainComplex.capCycles k (P.rightAlexanderWhitneyDiagonal u)
          ((toSSetPair.obj P).chainComplexPairing μ) p q n h φ ≫
        (P.singularChainComplex N).homologyπ q :=
  TauCeti.ChainComplex.cap_homologyπ _ _ _ _ _ _ _

/-- **Compatibility of the absolute and relative cap products**: for a class `x` of `Hₙ(X)` with
image `j_*x` in `Hₙ(X, A)` and a class `α` of `Hᵖ(X)`, `j_*(x ⌢ α) = j_*x ⌢ α`. -/
lemma singularHomologyπ_comp_absoluteSingularCap (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ) (h : p + q = n)
    (α : P.fst.singularCohomology R k M p) :
    P.singularHomologyπ T n ≫ P.absoluteSingularCap k u μ p q n h α =
      P.fst.singularCap k u μ p q n h α ≫ P.singularHomologyπ N q := by
  have := TauCeti.ChainComplex.cap_naturality (k := k) (P.rightAlexanderWhitneyDiagonal u)
    ((toSSetPair.obj P).chainComplexPairing μ) (P.fst.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (P.singularChainComplexπ T) (𝟙 _)
    (P.singularChainComplexπ S) (P.singularChainComplexπ N)
    (singularChainComplexπ_rightAlexanderWhitneyDiagonal P u)
    (SSetPair.chainComplexπ_chainComplexPairing (toSSetPair.obj P) μ).symm p q n h α
  -- `cap_naturality` types this map between `linearYonedaObj` complexes, so state it that way
  -- for `rw` to find it; the identity morphism's type is matched only up to unfolding
  -- `linearYonedaFunctor`, which `exact` performs.
  have hid : HomologicalComplex.homologyMap
      (K := ((TopCat.toSSet.obj P.fst).chainComplex R).linearYonedaObj k M)
      (L := ((TopCat.toSSet.obj P.fst).chainComplex R).linearYonedaObj k M)
      ((TauCeti.ChainComplex.linearYonedaFunctor k M).map (𝟙 _).op) p = 𝟙 _ := by
    rw [op_id, CategoryTheory.Functor.map_id]
    exact HomologicalComplex.homologyMap_id _ _
  rw [hid, ModuleCat.id_apply] at this
  rw [TopCat.singularCap_def, absoluteSingularCap_def]
  exact this.symm

/-- **Naturality of the cap product of absolute cohomology with relative homology**, the
projection formula `f_*(x ⌢ f^*α) = f_*x ⌢ α`: for a map of pairs `f : (X, A) ⟶ (Y, B)`, capping
with the pull-back of a cohomology class of `Y` and pushing forward along `f` is pushing forward
along `f` and capping with the class. -/
lemma absoluteSingularCap_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (k : Type*) [Ring k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n : ℕ)
    (h : p + q = n) (α : P'.fst.singularCohomology R k M p) :
    P.absoluteSingularCap k u μ p q n h (TopCat.singularCohomologyMap (Hom.fst f) p α) ≫
        TopPair.singularHomologyMap f N q =
      TopPair.singularHomologyMap f T n ≫ P'.absoluteSingularCap k u μ p q n h α :=
  TauCeti.ChainComplex.cap_naturality _ _ _ _ _ _ _ _
    (rightAlexanderWhitneyDiagonal_naturality f u)
    (SSetPair.chainComplexPairing_naturality (toSSetPair.map f) μ).symm p q n h α

/-- **The cap product with an absolute class commutes with the connecting morphism of a pair**, up
to the sign `(-1)^p`: for a class `x` of `H_{n'}(X, A)` and a class `α` of `Hᵖ(X)`, the connecting
morphism `∂ : H_{q'}(X, A) ⟶ H_q(A)` sends `x ⌢ α` to `(-1)^p ∂x ⌢ α|_A`, where `α|_A` is the
restriction of `α` to the subspace, `p + q = n`, `q + 1 = q'` and `n + 1 = n'`. -/
theorem absoluteSingularCap_comp_singularHomologyδ (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q n q' n' : ℕ)
    (h : p + q = n) (h' : p + q' = n') (α : P.fst.singularCohomology R k M p)
    (hq : q + 1 = q' := by lia) (hn : n + 1 = n' := by lia) :
    P.absoluteSingularCap k u μ p q' n' h' α ≫ P.singularHomologyδ N q' q hq =
      ((-1 : ℤ) ^ p) • (P.singularHomologyδ T n' n hn ≫
        P.snd.singularCap k u μ p q n h (TopCat.singularCohomologyMap P.map p α)) := by
  rw [absoluteSingularCap_def, TopCat.singularCap_def]
  exact TauCeti.ChainComplex.cap_comp_δ (P.shortExact_singularChainComplexShortComplex T)
    (P.shortExact_singularChainComplexShortComplex N) (P.snd.alexanderWhitneyDiagonal u)
    (P.fst.alexanderWhitneyDiagonal u) (P.rightAlexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.snd).chainComplexPairing μ)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) ((toSSetPair.obj P).chainComplexPairing μ)
    (SSet.chainComplexMap (TopCat.toSSet.map P.map) R)
    (SSet.chainComplexMap (TopCat.toSSet.map P.map) S) (P.singularChainComplexπ S)
    (TopCat.alexanderWhitneyDiagonal_naturality P.map u)
    (SSet.chainComplexPairing_naturality (TopCat.toSSet.map P.map) μ).symm
    (singularChainComplexπ_rightAlexanderWhitneyDiagonal P u)
    (SSetPair.chainComplexπ_chainComplexPairing (toSSetPair.obj P) μ).symm p q n q' n' h h' α hq hn

end TopPair
