/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
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

## Main results

* `MonoidHom.card_mul_card_mul_card_of_exact`: the six-term alternating identity.
-/

public section

namespace MonoidHom

variable {A₀ A₁ A₂ A₃ A₄ A₅ : Type*} [Group A₀] [Group A₁] [Group A₂] [Group A₃] [Group A₄]
  [Group A₅]

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
  have e₀ : Nat.card A₀ = Nat.card f₀.range := by
    rw [← Subgroup.card_ker_mul_card_range f₀, (ker_eq_bot_iff f₀).2 h₀, Subgroup.card_bot, one_mul]
  have e₅ : Nat.card A₅ = Nat.card f₄.range := by
    rw [range_eq_top.2 h₅, Subgroup.card_top]
  -- at each inner node, `|Aᵢ| = |ker fᵢ| * |range fᵢ| = |range fᵢ₋₁| * |range fᵢ|`
  rw [e₀, e₅, ← Subgroup.card_ker_mul_card_range f₁, ← h₁, ← Subgroup.card_ker_mul_card_range f₂,
    ← h₂, ← Subgroup.card_ker_mul_card_range f₃, ← h₃, ← Subgroup.card_ker_mul_card_range f₄,
    ← h₄]
  ring

end MonoidHom
