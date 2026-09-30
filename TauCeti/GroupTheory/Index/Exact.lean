/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.Ring

/-!
# Orders along an exact sequence of groups

The order-index formula `Nat.card f.ker * Nat.card f.range = Nat.card G` for a group homomorphism
`f` (`Subgroup.card_ker_mul_card_range`) turns exactness of a sequence of homomorphisms into
identities between the orders of its terms. Along a six-term exact sequence
`1 → A₀ → A₁ → A₂ → A₃ → A₄ → A₅ → 1` the alternating product of the orders is `1`, written
without division as `|A₀| * |A₂| * |A₄| = |A₁| * |A₃| * |A₅|`: at each inner node the order of
the term is the product of the orders of the incoming and outgoing ranges.

The identity holds for `Nat.card` with no finiteness hypothesis, an infinite term contributing
the factor `0` to both sides; for finite groups it is the usual statement. It is the shape a long
exact cohomology sequence takes once one of its terms vanishes, and it is what turns the
additivity of an Euler characteristic along a short exact sequence of coefficients into a
statement about orders.

At a single node of an exact sequence `A₀ → A₁ → A₂` the same count gives a divisibility
`|A₁| ∣ |A₀| * |A₂|`, with no injectivity or surjectivity hypothesis: `|A₁|` is the product of the
orders of the two ranges, which divide `|A₀|` and `|A₂|`.

## Main results

* `MonoidHom.card_dvd_card_mul_card_of_exact`: the order of the middle term of an exact sequence
  `A₀ → A₁ → A₂` divides the product of the orders of the outer ones.
* `MonoidHom.card_mul_card_mul_card_mul_card_mul_card_of_exact`: the nine-term alternating
  identity `|A₀| * |A₂| * |A₄| * |A₆| * |A₈| = |A₁| * |A₃| * |A₅| * |A₇|`, the shape of a long exact
  cohomology sequence cut off by a vanishing `H³`.
* `MonoidHom.card_mul_card_mul_card_of_exact`: the six-term alternating identity
  `|A₀| * |A₂| * |A₄| = |A₁| * |A₃| * |A₅|`, the nine-term one padded with trivial groups.
-/

public section

namespace MonoidHom

variable {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ : Type*} [Group A₀] [Group A₁] [Group A₂] [Group A₃]
  [Group A₄] [Group A₅] [Group A₆] [Group A₇] [Group A₈]

/-- **The order of the middle term of an exact sequence.** For an exact sequence `A₀ → A₁ → A₂` of
groups, `|A₁|` divides `|A₀| * |A₂|`. In particular `A₁` is finite as soon as `A₀` and `A₂` are. -/
@[to_additive card_dvd_card_mul_card_of_exact /-- **The order of the middle term of an exact
sequence.** For an exact sequence `A₀ → A₁ → A₂` of additive groups, `|A₁|` divides
`|A₀| * |A₂|`. In particular `A₁` is finite as soon as `A₀` and `A₂` are. -/]
theorem card_dvd_card_mul_card_of_exact (f₀ : A₀ →* A₁) (f₁ : A₁ →* A₂) (h : f₀.range = f₁.ker) :
    Nat.card A₁ ∣ Nat.card A₀ * Nat.card A₂ := by
  rw [← Subgroup.card_ker_mul_card_range f₁, ← h]
  exact mul_dvd_mul (Subgroup.card_range_dvd f₀) (Subgroup.card_subgroup_dvd_card f₁.range)

/-- **The alternating product of orders along a nine-term exact sequence.** For an exact sequence
`1 → A₀ → A₁ → ⋯ → A₇ → A₈ → 1` of groups,
`|A₀| * |A₂| * |A₄| * |A₆| * |A₈| = |A₁| * |A₃| * |A₅| * |A₇|`. -/
@[to_additive card_mul_card_mul_card_mul_card_mul_card_of_exact /-- **The alternating product of
orders along a nine-term exact sequence.** For an exact sequence `0 → A₀ → A₁ → ⋯ → A₇ → A₈ → 0` of
additive groups, `|A₀| * |A₂| * |A₄| * |A₆| * |A₈| = |A₁| * |A₃| * |A₅| * |A₇|`. -/]
theorem card_mul_card_mul_card_mul_card_mul_card_of_exact (f₀ : A₀ →* A₁) (f₁ : A₁ →* A₂)
    (f₂ : A₂ →* A₃) (f₃ : A₃ →* A₄) (f₄ : A₄ →* A₅) (f₅ : A₅ →* A₆) (f₆ : A₆ →* A₇)
    (f₇ : A₇ →* A₈) (h₀ : Function.Injective f₀) (h₁ : f₀.range = f₁.ker)
    (h₂ : f₁.range = f₂.ker) (h₃ : f₂.range = f₃.ker) (h₄ : f₃.range = f₄.ker)
    (h₅ : f₄.range = f₅.ker) (h₆ : f₅.range = f₆.ker) (h₇ : f₆.range = f₇.ker)
    (h₈ : Function.Surjective f₇) :
    Nat.card A₀ * Nat.card A₂ * Nat.card A₄ * Nat.card A₆ * Nat.card A₈ =
      Nat.card A₁ * Nat.card A₃ * Nat.card A₅ * Nat.card A₇ := by
  have e₀ : Nat.card A₀ = Nat.card f₀.range := by
    rw [← Subgroup.card_ker_mul_card_range f₀, (ker_eq_bot_iff f₀).2 h₀, Subgroup.card_bot, one_mul]
  have e₈ : Nat.card A₈ = Nat.card f₇.range := by
    rw [range_eq_top.2 h₈, Subgroup.card_top]
  -- at each inner node, `|Aᵢ| = |ker fᵢ| * |range fᵢ| = |range fᵢ₋₁| * |range fᵢ|`
  rw [e₀, e₈, ← Subgroup.card_ker_mul_card_range f₁, ← h₁, ← Subgroup.card_ker_mul_card_range f₂,
    ← h₂, ← Subgroup.card_ker_mul_card_range f₃, ← h₃, ← Subgroup.card_ker_mul_card_range f₄,
    ← h₄, ← Subgroup.card_ker_mul_card_range f₅, ← h₅, ← Subgroup.card_ker_mul_card_range f₆,
    ← h₆, ← Subgroup.card_ker_mul_card_range f₇, ← h₇]
  ring

/-- **The alternating product of orders along a six-term exact sequence.** For an exact sequence
`1 → A₀ → A₁ → A₂ → A₃ → A₄ → A₅ → 1` of groups, `|A₀| * |A₂| * |A₄| = |A₁| * |A₃| * |A₅|`. -/
@[to_additive card_mul_card_mul_card_of_exact /-- **The alternating product of orders along a
six-term exact sequence.** For an exact sequence `0 → A₀ → A₁ → A₂ → A₃ → A₄ → A₅ → 0` of additive
groups, `|A₀| * |A₂| * |A₄| = |A₁| * |A₃| * |A₅|`. -/]
theorem card_mul_card_mul_card_of_exact (f₀ : A₀ →* A₁) (f₁ : A₁ →* A₂) (f₂ : A₂ →* A₃)
    (f₃ : A₃ →* A₄) (f₄ : A₄ →* A₅) (h₀ : Function.Injective f₀) (h₁ : f₀.range = f₁.ker)
    (h₂ : f₁.range = f₂.ker) (h₃ : f₂.range = f₃.ker) (h₄ : f₃.range = f₄.ker)
    (h₅ : Function.Surjective f₄) :
    Nat.card A₀ * Nat.card A₂ * Nat.card A₄ = Nat.card A₁ * Nat.card A₃ * Nat.card A₅ := by
  -- pad the sequence with three trivial groups and read off the nine-term identity
  have h := card_mul_card_mul_card_mul_card_mul_card_of_exact f₀ f₁ f₂ f₃ f₄ (1 : A₅ →* Unit)
    (1 : Unit →* Unit) (1 : Unit →* Unit) h₀ h₁ h₂ h₃ h₄ ((range_eq_top.2 h₅).trans ker_one.symm)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Function.surjective_to_subsingleton _)
  simpa only [Nat.card_unique, mul_one] using h

end MonoidHom
