/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Dynamics.SymbolicDynamics.Basic

/-!
# Iterates of the shift

A complement to Mathlib's `SymbolicDynamics.FullShift.mulShift`: iterating the shift by `g`
`k` times is the shift by `g ^ k` (in additive notation, by `k • g`). On a group, a set invariant
under the shift by `g` is invariant under the shift by every power `g ^ k`, `k ∈ ℤ`; on `ℤ → A`,
a set invariant under the two-sided shift `shift 1` is invariant under every shift `shift k`.
The Bernoulli action `(g • x) h = x (g⁻¹ * h)` of a group on `G → A` (Mathlib's `arrowAction`) is
the shift by `g⁻¹`.

## Main results

* `SymbolicDynamics.FullShift.mulShift_iterate`, `SymbolicDynamics.FullShift.shift_iterate`:
  `(mulShift g)^[k] = mulShift (g ^ k)` and `(shift g)^[k] = shift (k • g)`.
* `SymbolicDynamics.FullShift.preimage_mulShift_zpow_eq_of_preimage_mulShift_eq`,
  `SymbolicDynamics.FullShift.preimage_shift_zsmul_eq_of_preimage_shift_eq`: a set invariant
  under `mulShift g` is invariant under every `mulShift (g ^ k)` (additively, `shift (k • g)`).
* `SymbolicDynamics.FullShift.arrowAction_smul_eq_mulShift`: under `arrowAction`,
  `g • x = mulShift g⁻¹ x`.
* `SymbolicDynamics.FullShift.arrowAction_multiplicative_smul_eq_shift`: under `arrowAction` of
  `Multiplicative Λ` on `Λ → A`, `g • x = shift (-toAdd g) x`.
-/

public section

namespace SymbolicDynamics.FullShift

variable {A G : Type*}

section Monoid

variable [Monoid G]

/-- Iterating the shift by `g` `k` times is the shift by `g ^ k`. -/
@[to_additive (attr := simp) /-- Iterating the shift by `g` `k` times is the shift by `k • g`. -/]
theorem mulShift_iterate (g : G) (k : ℕ) : (mulShift (A := A) g)^[k] = mulShift (g ^ k) := by
  induction k with
  | zero => funext x; simp
  | succ k ih => rw [Function.iterate_succ', ih, pow_succ]; funext x; simp [mulShift_mul]

end Monoid

section Group

variable [Group G]

/-- A set invariant under the shift by an element `g` of a group is invariant under the shift by
every power `g ^ k`, `k ∈ ℤ`. -/
@[to_additive /-- A set invariant under the shift by an element `g` of an additive group is
invariant under the shift by every multiple `k • g`, `k ∈ ℤ`. -/]
theorem preimage_mulShift_zpow_eq_of_preimage_mulShift_eq {g : G} {s : Set (G → A)}
    (hs : mulShift g ⁻¹' s = s) (k : ℤ) : mulShift (g ^ k) ⁻¹' s = s := by
  have hstep (k : ℤ) : mulShift (g ^ (k + 1)) = mulShift g ∘ mulShift (A := A) (g ^ k) :=
    funext fun x ↦ by rw [zpow_add_one, mulShift_mul, Function.comp_apply]
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, show mulShift (1 : G) = (id : (G → A) → G → A) from funext mulShift_one,
      Set.preimage_id]
  | succ k ih => rw [hstep, Set.preimage_comp, hs, ih]
  | pred k ih =>
    have h := hstep (-k - 1)
    rw [sub_add_cancel] at h
    rwa [h, Set.preimage_comp, hs] at ih

/-- The Bernoulli action `(g • x) h = x (g⁻¹ * h)` of a group on `G → A` (Mathlib's
`arrowAction`) is the shift by `g⁻¹`. -/
theorem arrowAction_smul_eq_mulShift (g : G) (x : G → A) :
    letI := arrowAction (G := G) (A := G) (B := A)
    g • x = mulShift g⁻¹ x :=
  (rfl)

end Group

/-- The Bernoulli action of `Multiplicative Λ` on `Λ → A` (Mathlib's `arrowAction`, with `Λ` acting
on itself by translation) is the shift by `-toAdd g`: `(g • x) n = x (-toAdd g + n)`. -/
theorem arrowAction_multiplicative_smul_eq_shift {Λ : Type*} [AddGroup Λ] (g : Multiplicative Λ)
    (x : Λ → A) :
    letI := arrowAction (G := Multiplicative Λ) (A := Λ) (B := A)
    g • x = shift (-Multiplicative.toAdd g) x :=
  (rfl)

end SymbolicDynamics.FullShift
