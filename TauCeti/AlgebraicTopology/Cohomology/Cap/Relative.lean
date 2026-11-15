/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.Relative
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic

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
* `TopPair.singularCap_singularCohomologyδ`: compatibility with the connecting morphisms of the
  pair, `x ⌢ δβ = i_*(∂x ⌢ β)` for `β ∈ Hᵖ(A)`, `x ∈ Hₙ(X, A)` and `i : A ⟶ X` the inclusion.

The proof of the last identity is a cochain computation. Lift `β` to a cochain `b` of `X` whose
coboundary represents `δβ`, and lift a relative cycle to a chain `z` of `X` by the degreewise
splitting of `0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0`, so that `∂z` is a cycle of `A` representing `∂x`.
The boundary formula for the cap product gives `z ⌢ δb = ∂z ⌢ b - (-1)ᵖ ∂(z ⌢ b)`, and `∂z ⌢ b`
is the image of `∂z ⌢ β` under `i`.

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

section Connecting

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- The chain-level form of `TopPair.singularCap_singularCohomologyδ`. Let `x₂` be a cochain of `X`
whose coboundary is the pull-back of a relative cocycle `ζ` and whose restriction to `A` is a
cocycle `z₃`, and let `s` be a section of the quotient map `C(X) ⟶ C(X, A)` and `r` a retraction
onto `C(A)` as in `SSetPair.chainComplexXSplitting`. Then on relative cycles, capping with `ζ`
agrees with taking the retracted boundary of the lift, capping with `z₃` and including into `X`,
up to the boundary of `x ↦ -(-1)ᵖ s(x) ⌢ x₂`. -/
-- `s` and `r` are variables, typed with the chains of `P.fst` and `P.snd`, so that their composites
-- with the cap products are type-correct without unfolding `toSSetPair`.
private lemma capCycles_eq_add (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q m : ℕ) (h : p + q = m)
    (ζ : (P.singularCochainComplex R k M).cycles (p + 1))
    (x₂ : ((TopCat.toSSet.obj P.fst).chainComplex R).X p ⟶ M)
    (z₃ : (P.snd.singularCochainComplex R k M).cycles p)
    (hd : ((TopCat.toSSet.obj P.fst).chainComplex R).d (p + 1) p ≫ x₂ =
      (P.singularChainComplexπ R).f (p + 1) ≫ (P.singularCochainComplex R k M).iCycles (p + 1) ζ)
    (hg : (SSet.chainComplexMap (TopCat.toSSet.map P.map) R).f p ≫ x₂ =
      (P.snd.singularCochainComplex R k M).iCycles p z₃)
    (s : (P.singularChainComplex T).X (m + 1) ⟶
      ((TopCat.toSSet.obj P.fst).chainComplex T).X (m + 1))
    (r : ((TopCat.toSSet.obj P.fst).chainComplex T).X m ⟶
      ((TopCat.toSSet.obj P.snd).chainComplex T).X m)
    (hs : s ≫ (P.singularChainComplexπ T).f (m + 1) = 𝟙 _)
    (hr : ((P.singularChainComplex T).iCycles (m + 1) ≫ s ≫
        ((TopCat.toSSet.obj P.fst).chainComplex T).d (m + 1) m ≫ r) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map P.map) T).f m =
      (P.singularChainComplex T).iCycles (m + 1) ≫ s ≫
        ((TopCat.toSSet.obj P.fst).chainComplex T).d (m + 1) m)
    (hcyc : ((P.singularChainComplex T).iCycles (m + 1) ≫ s ≫
        ((TopCat.toSSet.obj P.fst).chainComplex T).d (m + 1) m ≫ r) ≫
        ((TopCat.toSSet.obj P.snd).chainComplex T).d m ((ComplexShape.down ℕ).next m) = 0) :
    TauCeti.ChainComplex.capCycles k (P.alexanderWhitneyDiagonal u)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (p + 1) q (m + 1) (by omega) ζ =
      ((TopCat.toSSet.obj P.snd).chainComplex T).liftCycles
          ((P.singularChainComplex T).iCycles (m + 1) ≫ s ≫
            ((TopCat.toSSet.obj P.fst).chainComplex T).d (m + 1) m ≫ r) _ rfl hcyc ≫
        TauCeti.ChainComplex.capCycles k (P.snd.alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj P.snd).chainComplexPairing μ) p q m h z₃ ≫
          HomologicalComplex.cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map P.map) N) q +
      (-((-1 : ℤ) ^ p) • ((P.singularChainComplex T).iCycles (m + 1) ≫ s ≫
          TauCeti.ChainComplex.capChain k (P.fst.alexanderWhitneyDiagonal u)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p (q + 1) (m + 1) (by omega) x₂)) ≫
        ((TopCat.toSSet.obj P.fst).chainComplex N).toCycles (q + 1) q := by
  -- Compare the underlying chains. The capped lift `x ⌢ ζ = s(x) ⌢ δx₂` (`hL`), the capped
  -- retracted boundary `∂s(x) ⌢ x₂` (`hF3`, `hr`) and the boundary formula (`hF5`) remain.
  rw [← cancel_mono (((TopCat.toSSet.obj P.fst).chainComplex N).iCycles q)]
  simp only [Preadditive.add_comp, Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.toCycles_i, TauCeti.ChainComplex.capCycles_i,
    TauCeti.ChainComplex.capCycles_i_assoc, HomologicalComplex.liftCycles_i_assoc]
  have hF1 := (singularChainComplexπ_capChain_alexanderWhitneyDiagonal P k u μ (p + 1) q (m + 1)
    (by omega) ((P.singularCochainComplex R k M).iCycles (p + 1) ζ)).trans
      (congrArg (TauCeti.ChainComplex.capChain k (P.fst.alexanderWhitneyDiagonal u)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (p + 1) q (m + 1) (by omega)) hd.symm)
  have hF3 := TauCeti.ChainComplex.capChain_naturality (k := k) (P.fst.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (P.snd.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.snd).chainComplexPairing μ)
    (SSet.chainComplexMap (TopCat.toSSet.map P.map) T)
    (SSet.chainComplexMap (TopCat.toSSet.map P.map) R)
    (SSet.chainComplexMap (TopCat.toSSet.map P.map) S)
    (SSet.chainComplexMap (TopCat.toSSet.map P.map) N)
    (TopCat.alexanderWhitneyDiagonal_naturality P.map u)
    (SSet.chainComplexPairing_naturality (TopCat.toSSet.map P.map) μ).symm p q m h x₂
  rw [show (SSet.chainComplexMap (TopCat.toSSet.map P.map) R).f p ≫ x₂ = _ from hg] at hF3
  have hF5 := TauCeti.ChainComplex.capChain_comp_d (k := k) (P.fst.alexanderWhitneyDiagonal u)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p q m h x₂
  have hc : -(-1 : ℤ) ^ p * (-1) ^ p = -1 := by rw [neg_mul, ← mul_pow]; norm_num
  -- Name the two cocycles as morphisms of `C`: as elements of the cochain modules they make the
  -- composites below type-correct only up to unfolding `ModuleCat.of`, which blocks `rw`.
  obtain ⟨φ, hφ⟩ : ∃ φ : (P.singularChainComplex R).X (p + 1) ⟶ M,
      φ = (P.singularCochainComplex R k M).iCycles (p + 1) ζ := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ((TopCat.toSSet.obj P.snd).chainComplex R).X p ⟶ M,
      ψ = (P.snd.singularCochainComplex R k M).iCycles p z₃ := ⟨_, rfl⟩
  rw [← hφ] at hF1 ⊢
  rw [← hψ] at hF3 ⊢
  have hL : (P.singularChainComplex T).iCycles (m + 1) ≫
      TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal u)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (p + 1) q (m + 1) (by omega) φ =
      (P.singularChainComplex T).iCycles (m + 1) ≫ s ≫
        TauCeti.ChainComplex.capChain k (P.fst.alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) (p + 1) q (m + 1) (by omega)
          (((TopCat.toSSet.obj P.fst).chainComplex R).d (p + 1) p ≫ x₂) := by
    refine Eq.trans ?_
      (congrArg (fun t ↦ (P.singularChainComplex T).iCycles (m + 1) ≫ s ≫ t) hF1)
    exact congrArg (_ ≫ ·) ((Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) hs.symm).trans (Category.assoc _ _ _)))
  rw [hL, hF3, reassoc_of% hr, Preadditive.zsmul_comp, Category.assoc, Category.assoc, hF5,
    Preadditive.comp_zsmul, Preadditive.comp_zsmul, smul_smul, hc, neg_one_zsmul,
    Preadditive.comp_sub, Preadditive.comp_sub]
  abel

/-- **Compatibility of the relative cap product with the connecting morphisms**: for a class `β` of
`Hᵖ(A)` with image `δβ` in `Hᵖ⁺¹(X, A)`, and a class `x` of `Hₘ₊₁(X, A)` with image `∂x` in
`Hₘ(A)`, `x ⌢ δβ = i_*(∂x ⌢ β)` in `H_q(X)`, where `i : A ⟶ X` is the inclusion and
`p + q = m`. There is no sign. -/
theorem singularCap_singularCohomologyδ (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (p q m : ℕ) (h : p + q = m)
    (β : P.snd.singularCohomology R k M p) :
    P.singularCap k u μ (p + 1) q (m + 1) (by omega)
        (P.singularCohomologyδ R k M p (p + 1) rfl β) =
      P.singularHomologyδ T (m + 1) m ≫ P.snd.singularCap k u μ p q m h β ≫
        ((AlgebraicTopology.singularHomologyFunctor C q).obj N).map P.map := by
  -- Represent `δβ` by a relative cocycle `ζ`, and `β` by a cocycle `z₃` of `A` which lifts to a
  -- cochain `x₂` of `X` with coboundary exactly the pull-back of `ζ`.
  obtain ⟨ζ, hζ⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (p + 1)
    (P.singularCohomologyδ R k M p (p + 1) rfl β)
  obtain ⟨x₂, z₃, hd, hg, rfl⟩ :=
    (P.shortExact_singularCochainComplexShortComplex R k M).moduleCat_exists_d_eq_of_δ_eq p
      (p + 1) rfl β ζ hζ.symm
  rw [← hζ, ← cancel_epi ((P.singularChainComplex T).homologyπ (m + 1)), singularCap_homologyπ,
    SSetPair.homologyπ_homologyδ_assoc (toSSetPair.obj P) T m]
  -- The subspace of `toSSetPair.obj P` is `TopCat.toSSet.obj P.snd` only up to definitional
  -- unfolding (`toSSetPair_obj_left`), so the cap product on `A` is computed on cycles by
  -- `TopCat.singularCap_homologyπ` in a `have` and substituted with `Eq.trans` rather than `rw`.
  have hcap : ((toSSetPair.obj P).left.chainComplex T).homologyπ m ≫
      P.snd.singularCap k u μ p q m h
          (((P.snd.singularCochainComplex R k M).homologyπ p).hom z₃) =
        TauCeti.ChainComplex.capCycles k (P.snd.alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj P.snd).chainComplexPairing μ) p q m h z₃ ≫
        ((TopCat.toSSet.obj P.snd).chainComplex N).homologyπ q :=
    TopCat.singularCap_homologyπ P.snd k u μ p q m h z₃
  have hcap' := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫
    ((AlgebraicTopology.singularHomologyFunctor C q).obj N).map P.map) hcap).trans
      (Category.assoc _ _ _))
  refine Eq.trans ?_ (congrArg (_ ≫ ·) hcap').symm
  rw [TauCeti.singularHomologyFunctor_obj_map, SSet.homologyMap]
  -- `erw`: for the same reason the two homology objects of `A` differ syntactically here.
  erw [HomologicalComplex.homologyπ_naturality]
  rw [capCycles_eq_add P k u μ p q m h ζ x₂ z₃ hd hg
    (SSetPair.chainComplexXSplitting T (toSSetPair.obj P) (m + 1)).s
    (SSetPair.chainComplexXSplitting T (toSSetPair.obj P) m).r
    (SSetPair.chainComplexXSplitting T (toSSetPair.obj P) (m + 1)).s_g
    (SSetPair.chainComplexXSplitting_s_d_r_comp (toSSetPair.obj P) T m)
    (SSetPair.chainComplexXSplitting_s_d_r_comp_d (toSSetPair.obj P) T m _)]
  simp only [Preadditive.add_comp, Category.assoc, HomologicalComplex.toCycles_comp_homologyπ,
    comp_zero, add_zero]
  -- The two sides differ only by `toSSetPair_obj_left` and `toSSetPair_obj_right`.
  rfl

end Connecting

end TopPair
