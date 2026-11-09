/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.CategoryTheory.Monoidal.Limits

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

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

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
