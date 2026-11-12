/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import TauCeti.Algebra.Homology.Monoidal.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Zero

/-!
# The Kronecker pairing of singular cap and cup products

For a space `X`, a coefficient morphism `u : T ⟶ R ⊗ S`, a singular cohomology class
`α ∈ Hᵖ(X; R, 𝟙)` with values in the tensor unit and a class `β ∈ H^q(X; S, N)`, the cap product
`x ⌢ α ∈ H_q(X; S)` of a class `x ∈ Hₙ(X; T)`, `n = p + q`, taken along the left unitor
`𝟙 ⊗ S ⟶ S`, satisfies

`⟨β, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`,

where the cup product is taken along `u` and the left unitor `𝟙 ⊗ N ⟶ N`
(`TopCat.singularCap_comp_singularKronecker`).  There is no sign: with the front-face convention
of the Alexander–Whitney diagonal both sides evaluate `α` on the front `p`-face and `β` on the back
`q`-face of each singular simplex.  For modules over a commutative ring `k`, with all coefficients
the module `k` and `u` the inverse left unitor, this is the identity
`⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ, x⟩` of Hatcher, Section 3.3, which makes the cap product the adjoint of
the cup product under the Kronecker pairing.

The key chain-level input is `SSet.chainComplexPairing_leftUnitor_hom_f`, from
`TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing`: the action of the tensor unit on
singular chains is the left unitor.

Capping into degree zero is the Kronecker pairing up to the augmentation: for a topological pair
`(X, A)`, a relative class `α ∈ Hⁿ(X, A; R, M)` and a relative class `x ∈ Hₙ(X, A; R)`, the cap
product `x ⌢ α ∈ H₀(X; M)` taken along the right unitors `R ⟶ R ⊗ 𝟙` and `M ⊗ 𝟙 ⟶ M` has
augmentation `ε (x ⌢ α) = ⟨α, x⟩` (`TopPair.singularCap_comp_singularHomology₀ε`).  On chains,
the back `0`-face of each singular `n`-simplex is a vertex, whose augmentation is the identity.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

open Simplicial

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T N : C}

/-- **The Kronecker pairing of a singular cap product**, `⟨β, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: for a class
`α` of degree `p` with values in the tensor unit and a class `β` of degree `q` with values in `N`,
capping a class of degree `n = p + q` with `α` along `u` and the left unitor, and then evaluating
`β`, is evaluating the cup product of `α` and `β` along `u` and the left unitor of `N`. -/
theorem singularCap_comp_singularKronecker (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (p q n : ℕ) (h : p + q = n)
    (α : X.singularCohomology R k (𝟙_ C) p) (β : X.singularCohomology S k N q) :
    X.singularCap k u (λ_ S).hom p q n h α ≫ X.singularKronecker k q β =
      X.singularKronecker k n (X.singularCup k u (λ_ N).hom p q n h α β) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  rw [singularCap_def, singularKronecker_def, singularKronecker_def, TauCeti.singularCup_def]
  refine TauCeti.ChainComplex.cap_comp_kronecker _ _ _ p q n h φ ψ ψ ?_
  rw [SSet.chainComplexPairing_leftUnitor_hom_f]
  exact (leftUnitor_naturality _).symm

end TopCat

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R M : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- On chains, capping a chain of degree `n` with a cochain of degree `n` along the right unitors
and taking the augmentation of the resulting degree-zero chain is evaluating the cochain. -/
lemma capChain_comp_homology₀ε (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (n : ℕ) (h : n + 0 = n)
    (φ : ((toSSet.obj X).chainComplex R).X n ⟶ M) :
    TauCeti.ChainComplex.capChain k (X.alexanderWhitneyDiagonal (ρ_ R).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ M).hom) n 0 n h φ ≫
      ((toSSet.obj X).chainComplex M).cycles₀Iso.inv ≫
        ((toSSet.obj X).chainComplex M).homologyπ 0 ≫ (toSSet.obj X).homology₀ε M =
      φ := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  -- The front `n`-face of an `n`-simplex is the simplex itself, and its back `0`-face is a vertex,
  -- whose augmentation is the identity.
  rw [reassoc_of% (ιChainComplex_capChain_alexanderWhitneyDiagonal X (k := k) (ρ_ R).inv
      (ρ_ M).hom n 0 n h φ σ), SSet.ιChainComplex_cycles₀Iso_inv_homologyπ_assoc,
    SSet.ιHomology₀_homology₀ε]
  simp [TauCeti.SimplexCategory.subinterval_zero_eq_id]

end TopCat

namespace TopPair

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R M : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- On chains, capping a relative chain of degree `n` with a relative cochain of degree `n` along
the right unitors and taking the augmentation of the resulting degree-zero chain is evaluating the
cochain. -/
lemma capChain_comp_homology₀ε (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] [MonoidalLinear k C] (n : ℕ) (h : n + 0 = n)
    (φ : (P.singularChainComplex R).X n ⟶ M) :
    TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (ρ_ R).inv)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing (ρ_ M).hom) n 0 n h φ ≫
      ((TopCat.toSSet.obj P.fst).chainComplex M).cycles₀Iso.inv ≫
        ((TopCat.toSSet.obj P.fst).chainComplex M).homologyπ 0 ≫
          (TopCat.toSSet.obj P.fst).homology₀ε M =
      φ := by
  have : Epi ((P.singularChainComplexπ R).f n) :=
    inferInstanceAs (Epi (((TopPair.toSSetPair.obj P).chainComplexπ R).f n))
  refine (cancel_epi ((P.singularChainComplexπ R).f n)).1 ?_
  rw [singularChainComplexπ_capChain_alexanderWhitneyDiagonal_assoc]
  exact TopCat.capChain_comp_homology₀ε P.fst k n h _

/-- **The augmentation of a relative cap product into degree zero**, `ε (x ⌢ α) = ⟨α, x⟩`: capping
a relative class `x ∈ Hₙ(X, A; R)` with a relative class `α ∈ Hⁿ(X, A; R, M)`, along the right
unitors `R ⟶ R ⊗ 𝟙` and `M ⊗ 𝟙 ⟶ M`, and then applying the augmentation `H₀(X; M) ⟶ M` is the
Kronecker pairing of `α` with `x`. -/
theorem singularCap_comp_singularHomology₀ε (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (n : ℕ) (h : n + 0 = n) (α : P.singularCohomology R k M n) :
    P.singularCap k (ρ_ R).inv (ρ_ M).hom n 0 n h α ≫ P.fst.singularHomology₀ε M =
      P.singularKronecker k n α := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n α
  refine (cancel_epi ((P.singularChainComplex R).homologyπ n)).1 ?_
  rw [singularCap_homologyπ_assoc, singularKronecker_homologyπ,
    ← capChain_comp_homology₀ε P k n h ((P.singularCochainComplex R k M).iCycles n φ),
    ← TauCeti.ChainComplex.capCycles_i_assoc]
  -- In degree zero every chain is a cycle.
  simp only [HomologicalComplex.iCyclesIso_hom_inv_id_assoc]
  exact Category.assoc _ _ _

end TopPair
