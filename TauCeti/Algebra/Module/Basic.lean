/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Affine combinations `u • x + (1 - u) • y` in a module

If `u` is a unit of the scalar ring, then `x = u • y + (1 - u) • x` forces `x = y`: the equation
says `u • (x - y) = 0`. Such equations arise as module relations whose two sides share a term,
for example the relation of an under-strand at a crossing of a link diagram whose incoming arc is
also its outgoing arc.

The braid relation `TauCeti.smul_add_one_sub_smul_braid_relation` compares two ways of crossing
three values pairwise by affine combinations. It is the self-distributivity of the Alexander
quandle, and gives the invariance of the Alexander module of a link diagram under the third
Reidemeister move.
-/

public section

namespace TauCeti

/-- If `u` is a unit, then `x = u • y + (1 - u) • x` forces `x = y`. -/
theorem _root_.IsUnit.eq_of_eq_smul_add_one_sub_smul {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {u : R} (hu : IsUnit u) {x y : M} (h : x = u • y + (1 - u) • x) : x = y := by
  have h' : u • (x - y) = 0 := calc
    u • (x - y) = x - (u • y + (1 - u) • x) := by rw [smul_sub, sub_smul, one_smul]; abel
    _ = 0 := by rw [← h, sub_self]
  exact sub_eq_zero.1 (hu.smul_eq_zero.1 h')

/-- **The braid relation for affine combinations.** Three strands enter a triangle with values
`a`, `b`, `c` and cross pairwise; at a crossing of two strands with entering values `x` and `y`,
they leave with `p • x + (1 - p) • y` and `q • y + (1 - q) • x`, where `p = 1` or `q = 1` according
to which strand is over. Passing the crossings in the order first–second, first–third,
second–third (with intermediate values `x₁`, `y₁`, `z₁`) or in the opposite order (with
intermediate values `x₁'`, `y₁'`, `z₁'`) gives the same three leaving values, as soon as the
strand on top acts on the other two by the same weight, up to inversion when it is read from
opposite sides. This is the self-distributivity of the Alexander quandle. -/
theorem smul_add_one_sub_smul_braid_relation {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {p₀ q₀ p₁ q₁ p₂ q₂ : R}
    (h : (p₀ = 1 ∧ p₁ = 1 ∧ q₀ = q₁ ∧ (p₂ = 1 ∨ q₂ = 1)) ∨
      (q₁ = 1 ∧ q₂ = 1 ∧ p₁ = p₂ ∧ (p₀ = 1 ∨ q₀ = 1)) ∨
      (q₀ = 1 ∧ p₂ = 1 ∧ p₀ * q₂ = 1 ∧ (p₁ = 1 ∨ q₁ = 1)))
    {a b c x₁ y₁ z₁ x₁' y₁' z₁' : M}
    (hx₁ : x₁ = p₀ • a + (1 - p₀) • b) (hy₁ : y₁ = q₀ • b + (1 - q₀) • a)
    (hz₁ : z₁ = q₁ • c + (1 - q₁) • x₁)
    (hy₁' : y₁' = p₂ • b + (1 - p₂) • c) (hz₁' : z₁' = q₂ • c + (1 - q₂) • b)
    (hx₁' : x₁' = p₁ • a + (1 - p₁) • z₁') :
    p₁ • x₁ + (1 - p₁) • c = p₀ • x₁' + (1 - p₀) • y₁' ∧
    p₂ • y₁ + (1 - p₂) • z₁ = q₀ • y₁' + (1 - q₀) • x₁' ∧
    q₂ • z₁ + (1 - q₂) • y₁ = q₁ • z₁' + (1 - q₁) • a := by
  subst hx₁ hy₁ hz₁ hy₁' hz₁' hx₁'
  rcases h with ⟨rfl, rfl, rfl, rfl | rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩ |
    ⟨rfl, rfl, h, rfl | rfl⟩
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | module
    | linear_combination (norm := module) h • ((1 - q₁) • (a - b))
    | linear_combination (norm := module) h • ((1 - p₁) • (b - c))

end TauCeti
