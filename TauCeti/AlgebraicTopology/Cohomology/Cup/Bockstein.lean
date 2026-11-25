/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Bockstein
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic

/-!
# Bockstein homomorphisms and the cup product

Let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` and `0 ⟶ N₁ ⟶ N₂ ⟶ N₃ ⟶ 0` be short exact sequences of coefficients,
with Bockstein homomorphisms `β` (`TopCat.singularCohomologyBockstein`), and let
`μ : M₂ ⊗ N₂ ⟶ L` be a pairing and `g : L ⟶ L'` a morphism such that, after `g`, `μ` restricted to
`M₁ ⊗ N₂` factors through a pairing `μ₁₃ : M₁ ⊗ N₃ ⟶ L'` and `μ` restricted to `M₂ ⊗ N₁` factors
through a pairing `μ₃₁ : M₃ ⊗ N₁ ⟶ L'`. Let `R`, `S`, `T` be projective objects with a map
`u : T ⟶ R ⊗ S`. Then for every space `X`, `a ∈ Hᵖ(X; R, M₃)` and `b ∈ H^q(X; S, N₃)`,

`β a ⌣ b = (-1)^(p + 1) • a ⌣ β b`   in `H^(p + q + 1)(X; T, L')`,

both cup products being taken along the Alexander–Whitney diagonal `X.alexanderWhitneyDiagonal u`,
the left one with `μ₁₃` and the right one with `μ₃₁`
(`TopCat.singularCup_singularCohomologyBockstein_eq_zsmul`). This holds on every space: lifting
`a` and `b` to cochains `φ` and `ψ` with values in `M₂` and `N₂`, the cochain `g ∘ (φ ⌣ ψ)` has
coboundary a cocycle representing `β a ⌣ b + (-1)ᵖ a ⌣ β b`, by the Leibniz rule. The algebraic
statement, for the cup product of the cochains of chain complexes along any diagonal, is
`TauCeti.ChainComplex.cup_δ_eq_zsmul`.

For the sequence `0 ⟶ ℤ ⟶ ℚ ⟶ ℚ/ℤ ⟶ 0` taken twice, with `R = S = T = 𝟙_` the unit object,
`u = (λ_ (𝟙_)).inv` the inverse unitor, `μ` the multiplication of `ℚ`, `g` the projection to `ℚ/ℤ`
and `μ₁₃`, `μ₃₁` the actions of `ℤ` on `ℚ/ℤ`, this is the mixed-coefficient Bockstein identity
`a ∪ β b = (-1)^(p + 1) β a ∪ b` of Conway–Friedl–Herrmann. Together with the graded
commutativity of the cup product, it determines the symmetry sign of the torsion linking form of a
closed oriented manifold, which is defined through Bockstein lifts to `ℚ/ℤ`.

## Main results

* `TopCat.singularCup_singularCohomologyBockstein_eq_zsmul`: `β a ⌣ b = (-1)^(p + 1) • a ⌣ β b`.

## References

* A. Conway, S. Friedl and G. Herrmann, *Linking forms revisited*, Pure Appl. Math. Q. 12 (2016),
  Lemma 2.6.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.E (Bockstein homomorphisms) and Section 3.2, Lemma 3.6 (the coboundary of a cup
  product).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T : C} [Projective R] [Projective S]

/-- **The Bockstein homomorphisms and the cup product.** For short exact sequences of coefficients
`M` and `N` and pairings `μ : M₂ ⊗ N₂ ⟶ L`, `μ₁₃ : M₁ ⊗ N₃ ⟶ L'` and `μ₃₁ : M₃ ⊗ N₁ ⟶ L'`
compatible through `g : L ⟶ L'`, the Bockstein homomorphisms satisfy, for `a ∈ Hᵖ(X; R, M₃)` and
`b ∈ H^q(X; S, N₃)`,

`β a ⌣ b = (-1)^(p + 1) • a ⌣ β b`   in `H^(p + q + 1)(X; T, L')`,

both cup products being taken along the Alexander–Whitney diagonal `X.alexanderWhitneyDiagonal u`
of `u : T ⟶ R ⊗ S`, the left one with `μ₁₃` and the right one with `μ₃₁`. -/
theorem singularCup_singularCohomologyBockstein_eq_zsmul (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) {M N : ShortComplex C} (hM : M.ShortExact)
    (hN : N.ShortExact) {L L' : C} (g : L ⟶ L') (μ : M.X₂ ⊗ N.X₂ ⟶ L) (μ₁₃ : M.X₁ ⊗ N.X₃ ⟶ L')
    (μ₃₁ : M.X₃ ⊗ N.X₁ ⟶ L') (hμ₁₃ : (M.f ▷ N.X₂) ≫ μ ≫ g = (M.X₁ ◁ N.g) ≫ μ₁₃)
    (hμ₃₁ : (M.X₂ ◁ N.f) ≫ μ ≫ g = (M.g ▷ N.X₁) ≫ μ₃₁) (p q p' q' n : ℕ) (hp : p + 1 = p')
    (hq : q + 1 = q') (h₁ : p' + q = n) (h₂ : p + q' = n) (a : X.singularCohomology R k M.X₃ p)
    (b : X.singularCohomology S k N.X₃ q) :
    X.singularCup k u μ₁₃ p' q n h₁ (X.singularCohomologyBockstein R k hM p p' hp a) b =
      ((-1 : ℤ) ^ (p + 1)) •
        X.singularCup k u μ₃₁ p q' n h₂ a (X.singularCohomologyBockstein S k hN q q' hq b) := by
  rw [TauCeti.singularCup_def, TauCeti.singularCup_def,
    singularCohomologyBockstein_eq_δ R k X hM p p' hp,
    singularCohomologyBockstein_eq_δ S k X hN q q' hq]
  exact TauCeti.ChainComplex.cup_δ_eq_zsmul (X.alexanderWhitneyDiagonal u) hM hN g μ μ₁₃ μ₃₁
    hμ₁₃ hμ₃₁ p q p' q' n hp hq h₁ h₂ a b

end TopCat
