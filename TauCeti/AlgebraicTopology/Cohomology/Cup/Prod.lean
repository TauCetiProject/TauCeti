/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity

/-!
# Cup products of pulled-back classes on a product

Take coefficients in an object `M` with a pairing `μ : M ⊗ M ⟶ M` that is commutative and
associative, and cup products along a coefficient morphism `u : R ⟶ R ⊗ R` that is cocommutative
and coassociative, as for the cohomology `H^*(Z; k)` with coefficients in a commutative ring `k`,
with the cup product along `k ≅ k ⊗ k`. Write `Hⁿ(Z)` for this cohomology of a space `Z`. On a
product `X × Y`, write `pr₁ : X × Y ⟶ X` and `pr₂ : X × Y ⟶ Y` for the projections. The classes
`pr₁^* a ⌣ pr₂^* c` are the cross products `a × c`, and they multiply by the **interchange law**

`(pr₁^* a ⌣ pr₂^* c) ⌣ (pr₁^* a' ⌣ pr₂^* c') = (-1)^(q p') pr₁^* (a ⌣ a') ⌣ pr₂^* (c ⌣ c')`

for `c ∈ H^q(Y)` and `a' ∈ H^p'(X)` (`TopCat.singularCup_fst_snd_singularCup_fst_snd`), the sign
coming from moving `pr₂^* c` past `pr₁^* a'` by graded commutativity
(`TopCat.singularCup_left_gradedComm`).

When `X` is a sphere `Sᵈ⁺¹` and `a` is the generator `θ` of `Hᵈ⁺¹(Sᵈ⁺¹; k)`, every class of
`X × Y` of degree at least `d + 1` has the form `pr₂^* b + pr₁^* a ⌣ pr₂^* c`
(`TopCat.singularCohomologyMap_snd_add_singularCup_sphere`), and `a ⌣ a = 0`. For such an `a` of
degree `p`, the interchange law gives the product formula
(`TopCat.singularCup_singularCohomologyMap_snd_add_singularCup`)

`(pr₂^* b + pr₁^* a ⌣ pr₂^* c) ⌣ (pr₂^* b' + pr₁^* a ⌣ pr₂^* c')`
`  = pr₂^* (b ⌣ b') + pr₁^* a ⌣ pr₂^* (c ⌣ b' + (-1)^(p m) b ⌣ c')`,

where `b ∈ Hᵐ(Y)`. In particular the cup product pairs the summand `pr₂^* H^*(Y)` with the summand
`pr₁^* a ⌣ pr₂^* H^*(Y)`, and the second summand is isotropic.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Theorem 3.11 (graded commutativity) and the cross product formula
  `(a × b) ⌣ (c × d) = (-1)^(|b| |c|) (a ⌣ c) × (b ⌣ d)`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (X Y : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C] {R M : C}
  {u : R ⟶ R ⊗ R} {μ : M ⊗ M ⟶ M}

/-- **The interchange law for cross products**: on `X × Y`, for a cocommutative (`hu`) and
coassociative (`hu'`) coefficient morphism `u : R ⟶ R ⊗ R` and a commutative (`hμ`) and associative
(`hμ'`) pairing `μ : M ⊗ M ⟶ M`,
`(pr₁^* a ⌣ pr₂^* c) ⌣ (pr₁^* a' ⌣ pr₂^* c') = (-1)^(q p') pr₁^* (a ⌣ a') ⌣ pr₂^* (c ⌣ c')`
for `a ∈ Hᵖ(X)`, `c ∈ H^q(Y)`, `a' ∈ H^p'(X)` and `c' ∈ H^q'(Y)`. -/
theorem singularCup_fst_snd_singularCup_fst_snd (hu : u ≫ (β_ R R).hom = u)
    (hu' : u ≫ u ▷ R ≫ (α_ R R R).hom = u ≫ R ◁ u) (hμ : (β_ M M).hom ≫ μ = μ)
    (hμ' : μ ▷ M ≫ μ = (α_ M M M).hom ≫ M ◁ μ ≫ μ) {p q p' q' m m' r s n : ℕ} (hm : p + q = m)
    (hm' : p' + q' = m') (hn : m + m' = n) (hr : p + p' = r) (hs : q + q' = s) (hrs : r + s = n)
    (a : X.singularCohomology R k M p) (c : Y.singularCohomology R k M q)
    (a' : X.singularCohomology R k M p') (c' : Y.singularCohomology R k M q') :
    (X ⊗ Y).singularCup k u μ m m' n hn
        ((X ⊗ Y).singularCup k u μ p q m hm
          (TopCat.singularCohomologyMap (fst X Y) p a) (TopCat.singularCohomologyMap (snd X Y) q c))
        ((X ⊗ Y).singularCup k u μ p' q' m' hm'
          (TopCat.singularCohomologyMap (fst X Y) p' a')
          (TopCat.singularCohomologyMap (snd X Y) q' c')) =
      ((-1 : ℤ) ^ (q * p')) • (X ⊗ Y).singularCup k u μ r s n hrs
        (TopCat.singularCohomologyMap (fst X Y) r (X.singularCup k u μ p p' r hr a a'))
        (TopCat.singularCohomologyMap (snd X Y) s (Y.singularCup k u μ q q' s hs c c')) := by
  -- reassociate, move `pr₂^* c` past `pr₁^* a'` by left commutativity, and reassociate back
  rw [← singularCup_naturality, ← singularCup_naturality,
    singularCup_assoc _ k hu' hμ' hm hn rfl (by omega),
    singularCup_left_gradedComm _ k hu hu' hμ hμ' hs (by omega) hm' rfl, map_zsmul,
    ← singularCup_assoc _ k hu' hμ' hr hrs (by omega) (by omega), mul_comm]

/-- **Cup products of the classes `pr₂^* b + pr₁^* a ⌣ pr₂^* c`**: on `X × Y`, for a cocommutative
(`hu`) and coassociative (`hu'`) coefficient morphism `u : R ⟶ R ⊗ R` and a commutative (`hμ`) and
associative (`hμ'`) pairing `μ : M ⊗ M ⟶ M`, let `a ∈ Hᵖ(X)` satisfy `a ⌣ a = 0`, as the generator
of the top cohomology of a sphere does. For `b ∈ Hᵐ(Y)`, `c ∈ H^q(Y)`, `b' ∈ Hᵐ'(Y)` and
`c' ∈ H^q'(Y)` with `p + q = m` and `p + q' = m'`,

`(pr₂^* b + pr₁^* a ⌣ pr₂^* c) ⌣ (pr₂^* b' + pr₁^* a ⌣ pr₂^* c')`
`  = pr₂^* (b ⌣ b') + pr₁^* a ⌣ pr₂^* (c ⌣ b' + (-1)^(p m) b ⌣ c')`. -/
theorem singularCup_singularCohomologyMap_snd_add_singularCup (hu : u ≫ (β_ R R).hom = u)
    (hu' : u ≫ u ▷ R ≫ (α_ R R R).hom = u ≫ R ◁ u) (hμ : (β_ M M).hom ≫ μ = μ)
    (hμ' : μ ▷ M ≫ μ = (α_ M M M).hom ≫ M ◁ μ ≫ μ) {p q q' m m' n s : ℕ}
    (hm : p + q = m) (hm' : p + q' = m') (hn : m + m' = n) (hs : p + s = n)
    (a : X.singularCohomology R k M p) (ha : X.singularCup k u μ p p (p + p) rfl a a = 0)
    (b : Y.singularCohomology R k M m) (c : Y.singularCohomology R k M q)
    (b' : Y.singularCohomology R k M m') (c' : Y.singularCohomology R k M q') :
    (X ⊗ Y).singularCup k u μ m m' n hn
        (TopCat.singularCohomologyMap (snd X Y) m b +
          (X ⊗ Y).singularCup k u μ p q m hm
            (TopCat.singularCohomologyMap (fst X Y) p a)
            (TopCat.singularCohomologyMap (snd X Y) q c))
        (TopCat.singularCohomologyMap (snd X Y) m' b' +
          (X ⊗ Y).singularCup k u μ p q' m' hm'
            (TopCat.singularCohomologyMap (fst X Y) p a)
            (TopCat.singularCohomologyMap (snd X Y) q' c')) =
      TopCat.singularCohomologyMap (snd X Y) n (Y.singularCup k u μ m m' n hn b b') +
        (X ⊗ Y).singularCup k u μ p s n hs
          (TopCat.singularCohomologyMap (fst X Y) p a)
          (TopCat.singularCohomologyMap (snd X Y) s
            (Y.singularCup k u μ q m' s (by omega) c b' +
              ((-1 : ℤ) ^ (p * m)) • Y.singularCup k u μ m q' s (by omega) b c')) := by
  -- `(pr₁^* a ⌣ pr₂^* c) ⌣ (pr₁^* a ⌣ pr₂^* c')` contains the factor `a ⌣ a = 0`
  have h₁ := singularCup_fst_snd_singularCup_fst_snd X Y k hu hu' hμ hμ' hm hm' hn rfl
    (rfl : q + q' = q + q') (by omega) a c a c'
  rw [ha, map_zero, LinearMap.map_zero₂, smul_zero] at h₁
  -- `(pr₁^* a ⌣ pr₂^* c) ⌣ pr₂^* b' = pr₁^* a ⌣ pr₂^* (c ⌣ b')`
  have h₂ := (X ⊗ Y).singularCup_assoc k hu' hμ' hm hn (by omega : q + m' = s) hs
    (TopCat.singularCohomologyMap (fst X Y) p a) (TopCat.singularCohomologyMap (snd X Y) q c)
    (TopCat.singularCohomologyMap (snd X Y) m' b')
  rw [singularCup_naturality] at h₂
  -- `pr₂^* b ⌣ (pr₁^* a ⌣ pr₂^* c') = (-1)^(p m) pr₁^* a ⌣ pr₂^* (b ⌣ c')`
  have h₃ := (X ⊗ Y).singularCup_left_gradedComm k hu hu' hμ hμ' (by omega : m + q' = s) hs hm'
    hn (TopCat.singularCohomologyMap (fst X Y) p a) (TopCat.singularCohomologyMap (snd X Y) m b)
    (TopCat.singularCohomologyMap (snd X Y) q' c')
  rw [singularCup_naturality] at h₃
  simp only [map_add, LinearMap.add_apply, map_zsmul, singularCup_naturality, h₁, ← h₂, h₃]
  abel

end TopCat
