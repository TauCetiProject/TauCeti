/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup
public import TauCeti.AlgebraicTopology.Singular.KoszulBraiding

/-!
# Graded commutativity of the cup product in singular cohomology

For classes `a ∈ Hᵖ(X; R, M)` and `b ∈ H^q(X; S, N)`, the cup product `b ⌣ a` along a coefficient
morphism `u' : T ⟶ S ⊗ R` and a pairing `μ' : N ⊗ M ⟶ P` is `(-1)^(p * q)` times `a ⌣ b` along
`u` and `μ`, whenever `u` and `μ` agree with `u'` and `μ'` up to the braidings of `C`
(`TopCat.singularCup_gradedComm`).  For coefficients in an object `M` with a commutative pairing,
taken along the left unitor of the unit object, this is `b ⌣ a = (-1)^(p * q) a ⌣ b`
(`TopCat.singularCup_gradedComm_tensorUnit`); with `C := ModuleCat k` and `M` a commutative
`k`-algebra, it is Hatcher, Theorem 3.11.

The cup product is computed along the Alexander–Whitney diagonal, which is not symmetric on the
nose.  The proof compares it with its transpose by the chain homotopy
`TopCat.alexanderWhitneyDiagonalKoszulBraidingHomotopy`, and then evaluates the cup product along
the transposed diagonal by `TauCeti.NatChainComplex.cup_koszulBraidingHom`.

## Main results

* `TopCat.singularCup_gradedComm`: graded commutativity for braided coefficient data.
* `TopCat.singularCup_gradedComm_tensorUnit`: graded commutativity for a commutative pairing on
  cohomology with unit coefficient object.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Theorem 3.11.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  {R S T M N P : C}

/-- **Graded commutativity of the cup product on singular cohomology**: for `a` of degree `p`
and `b` of degree `q`, `b ⌣ a = (-1)^(p * q) a ⌣ b`, where `b ⌣ a` is formed along the coefficient
morphism `u'` and the pairing `μ'`, and `a ⌣ b` along `u` and `μ`, which agree with `u'` and `μ'`
up to the braidings (`hu` and `hμ`).  When `R = S`, `M = N`, `u = u'` and `μ = μ'`, these say that
`u` is cocommutative and `μ` commutative. -/
theorem singularCup_gradedComm (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C]
    [MonoidalLinear k C] {u : T ⟶ R ⊗ S} {u' : T ⟶ S ⊗ R} (hu : u ≫ (β_ R S).hom = u')
    {μ : M ⊗ N ⟶ P} {μ' : N ⊗ M ⟶ P} (hμ : (β_ M N).hom ≫ μ' = μ) {p q n : ℕ} (h : p + q = n)
    (a : X.singularCohomology R k M p) (b : X.singularCohomology S k N q) :
    X.singularCup k u' μ' q p n (by omega) b a =
      ((-1 : ℤ) ^ (p * q)) • X.singularCup k u μ p q n h a b := by
  subst hu hμ
  rw [TauCeti.singularCup_def, TauCeti.singularCup_def,
    ← TauCeti.ChainComplex.cup_eq_of_homotopy
      (H := alexanderWhitneyDiagonalKoszulBraidingHomotopy X u),
    TauCeti.NatChainComplex.cup_koszulBraidingHom]

/-- **Graded commutativity of the cup product with commutative coefficients**: for coefficients in
an object `M` with a commutative pairing `μ : M ⊗ M ⟶ M`, such as a commutative `k`-algebra in
`ModuleCat k`, the cup product `Hᵖ(X; M) × H^q(X; M) ⟶ Hⁿ(X; M)` along the left unitor of the unit
object satisfies `b ⌣ a = (-1)^(p * q) a ⌣ b`. -/
theorem singularCup_gradedComm_tensorUnit (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C]
    [MonoidalLinear k C] {μ : M ⊗ M ⟶ M} (hμ : (β_ M M).hom ≫ μ = μ) {p q n : ℕ}
    (h : p + q = n) (a : X.singularCohomology (𝟙_ C) k M p)
    (b : X.singularCohomology (𝟙_ C) k M q) :
    X.singularCup k (λ_ _).inv μ q p n (by omega) b a =
      ((-1 : ℤ) ^ (p * q)) • X.singularCup k (λ_ _).inv μ p q n h a b :=
  singularCup_gradedComm X k (by
    rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal]) hμ h a b

end TopCat
