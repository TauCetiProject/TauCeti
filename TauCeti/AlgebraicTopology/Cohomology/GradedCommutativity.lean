/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
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
* `TopCat.singularCup_left_comm_tensorUnit`: `b ⌣ (a ⌣ c) = (-1)^(p * q) a ⌣ (b ⌣ c)` for a
  commutative and associative pairing, combining graded commutativity with associativity.

* `TopCat.two_smul_singularCup_self_eq_zero_of_odd` and
  `TopCat.singularCup_self_eq_zero_of_odd`: for cocommutative `u` and commutative `μ`,
  `2 • (a ⌣ a) = 0` for `a` of odd degree, so `a ⌣ a = 0` when `2` is invertible in `k`.

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

/-- **Left commutativity of the cup product with commutative coefficients**: for coefficients in an
object `M` with a commutative and associative pairing `μ : M ⊗ M ⟶ M`, the cup product along the
left unitor of the unit object satisfies `b ⌣ (a ⌣ c) = (-1)^(p * q) a ⌣ (b ⌣ c)` for `a` of
degree `p` and `b` of degree `q`. -/
theorem singularCup_left_comm_tensorUnit (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C]
    [MonoidalLinear k C] {μ : M ⊗ M ⟶ M} (hμ : (β_ M M).hom ≫ μ = μ)
    (hμ' : μ ▷ M ≫ μ = (α_ M M M).hom ≫ M ◁ μ ≫ μ) {p q r m m' n : ℕ} (hm : q + r = m)
    (hn : p + m = n) (hm' : p + r = m') (hn' : q + m' = n) (a : X.singularCohomology (𝟙_ C) k M p)
    (b : X.singularCohomology (𝟙_ C) k M q) (c : X.singularCohomology (𝟙_ C) k M r) :
    X.singularCup k (λ_ _).inv μ q m' n hn' b (X.singularCup k (λ_ _).inv μ p r m' hm' a c) =
      ((-1 : ℤ) ^ (p * q)) •
        X.singularCup k (λ_ _).inv μ p m n hn a (X.singularCup k (λ_ _).inv μ q r m hm b c) := by
  rw [← singularCup_assoc_tensorUnit X k hμ' rfl (by omega) hm' hn',
    singularCup_gradedComm_tensorUnit X k hμ (add_comm p q), map_zsmul, LinearMap.smul_apply,
    singularCup_assoc_tensorUnit X k hμ' (add_comm p q) (by omega) hm hn]

/-- **Twice an odd cup square vanishes**: for a cocommutative coefficient morphism
`u : T ⟶ R ⊗ R` and a commutative pairing `μ : M ⊗ M ⟶ P`, graded commutativity gives
`a ⌣ a = -(a ⌣ a)` for `a` of odd degree, so `2 • (a ⌣ a) = 0`. -/
theorem two_smul_singularCup_self_eq_zero_of_odd (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] {u : T ⟶ R ⊗ R} (hu : u ≫ (β_ R R).hom = u)
    {μ : M ⊗ M ⟶ P} (hμ : (β_ M M).hom ≫ μ = μ) {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (a : X.singularCohomology R k M p) :
    (2 : k) • X.singularCup k u μ p p n h a a = 0 := by
  have hcomm := X.singularCup_gradedComm k hu hμ h a a
  rw [(hp.mul hp).neg_one_pow, neg_one_smul] at hcomm
  rw [two_smul]
  nth_rw 1 [hcomm]
  exact neg_add_cancel _

/-- **Cup squares of odd classes vanish** when `2` is invertible in `k`: for a cocommutative
coefficient morphism `u : T ⟶ R ⊗ R` and a commutative pairing `μ : M ⊗ M ⟶ P`, `a ⌣ a = 0` for
`a` of odd degree. -/
theorem singularCup_self_eq_zero_of_odd (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Invertible (2 : k)] [Linear k C] [MonoidalLinear k C] {u : T ⟶ R ⊗ R}
    (hu : u ≫ (β_ R R).hom = u) {μ : M ⊗ M ⟶ P} (hμ : (β_ M M).hom ≫ μ = μ) {p n : ℕ}
    (hp : Odd p) (h : p + p = n) (a : X.singularCohomology R k M p) :
    X.singularCup k u μ p p n h a a = 0 := by
  rw [← one_smul k (X.singularCup k u μ p p n h a a), ← invOf_mul_self (2 : k),
    mul_smul, X.two_smul_singularCup_self_eq_zero_of_odd k hu hμ hp h a, smul_zero]

end TopCat
