/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Charge exponents and filling charges for multi-place diagrams

Given a finite set of places `Φ`, a partner map `partner : Φ → Φ`, and a set of marked places
`ev : Finset Φ`, an exponent assignment `w : Φ → ℕ → n' → ℕ` is a **charge exponent**
(`TauCeti.IsChargeExponent partner ev w`) if for every exempt pair of heights (`τ ∈ ev`, or
`h = 1` and `partner τ ∈ ev`) and every row `b : n'`, at least one of `w τ 1 b` or
`w (partner τ) h b` is nonzero.

For a diagram `κ : Φ → ℕ → ℕ` with column heights bounded by `N` and a filling `f`, the
**filling charge** `TauCeti.fillingCharge κ f w` is the sum of `w τ h (f τ h j b)` over all
boxes of the diagram.

## Main definitions and results

* `TauCeti.IsChargeExponent`: the charge condition on exponent assignments for exempt pairs.
* `TauCeti.fillingCharge`: the total charge of a filling across all places, heights, columns, and
  boxes.
* `TauCeti.fillingCharge_zero`: the filling charge of the zero assignment is `0`.
* `TauCeti.fillingCharge_congr`: the filling charge depends only on heights `h` with `κ τ h ≠ 0`.
* `TauCeti.dvd_pow_mul_pow_of_isChargeExponent`: for a charge exponent and an exempt pair, any
  divisor `π` of `p` divides `(p ^ w τ 1 b) ^ p ^ e * p ^ w (partner τ) h b`.

## References

* Provenance: adapted from `New.IsChargeExponent`, `New.fillingCharge`, `New.fillingCharge_zero`,
  `New.fillingCharge_congr`, and `New.dvd_subst_coupling_directionSubst_of_charges` in
  `grh/src/New/Derivatives/Divisibility/Count.lean` of `grh-lean`
  (https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

@[expose] public section

namespace TauCeti

open Finset

variable {Φ n' : Type*}

/-- Exponents `w : Φ → ℕ → n' → ℕ` are **charge exponents** for `partner` and marked places `ev`
if, whenever `τ ∈ ev` or (`h = 1` and `partner τ ∈ ev`), at least one of `w τ 1 b` and
`w (partner τ) h b` is nonzero for every `b : n'`. -/
def IsChargeExponent (partner : Φ → Φ) (ev : Finset Φ) (w : Φ → ℕ → n' → ℕ) : Prop :=
  ∀ (τ : Φ) (h : ℕ) (b : n'),
    τ ∈ ev ∨ h = 1 ∧ partner τ ∈ ev → w τ 1 b ≠ 0 ∨ w (partner τ) h b ≠ 0

/-- The total charge of a filling `f` of a diagram `κ` (with column heights `< N`) under the
exponent assignment `w`. -/
def fillingCharge [Fintype Φ] {N : ℕ} (κ : Φ → ℕ → ℕ)
    (f : (τ : Φ) → (h : Fin N) → Fin (κ τ h) → Fin h → n') (w : Φ → ℕ → n' → ℕ) : ℕ :=
  ∑ τ : Φ, ∑ h : Fin N, ∑ j : Fin (κ τ h), ∑ b : Fin h, w τ h (f τ h j b)

/-- The filling charge of the zero exponent assignment is `0`. -/
@[simp]
theorem fillingCharge_zero [Fintype Φ] {N : ℕ} (κ : Φ → ℕ → ℕ)
    (f : (τ : Φ) → (h : Fin N) → Fin (κ τ h) → Fin h → n') :
    fillingCharge κ f 0 = 0 := by
  simp [fillingCharge]

/-- The filling charge depends only on the values `w τ h b` at heights `h` occurring in `κ τ`
(those with `κ τ h ≠ 0`). -/
theorem fillingCharge_congr [Fintype Φ] {N : ℕ} {κ : Φ → ℕ → ℕ}
    {f : (τ : Φ) → (h : Fin N) → Fin (κ τ h) → Fin h → n'}
    {w w' : Φ → ℕ → n' → ℕ}
    (h_eq : ∀ (τ : Φ) (h : ℕ) (b : n'), κ τ h ≠ 0 → w τ h b = w' τ h b) :
    fillingCharge κ f w = fillingCharge κ f w' :=
  sum_congr rfl fun τ _ ↦ sum_congr rfl fun h _ ↦ sum_congr rfl fun j _ ↦
    sum_congr rfl fun b _ ↦ h_eq τ h (f τ h j b) j.pos.ne'

/-- If `w` is a charge exponent for `partner` and `ev`, `p ≠ 0`, and `π ∣ (p : R)`, then for every
exempt pair `(τ, h)` and row `b`, `π` divides `(p ^ w τ 1 b) ^ p ^ e * p ^ w (partner τ) h b`. -/
theorem dvd_pow_mul_pow_of_isChargeExponent {R : Type*} [CommSemiring R]
    {partner : Φ → Φ} {ev : Finset Φ} {w : Φ → ℕ → n' → ℕ}
    (hw : IsChargeExponent partner ev w) {p e : ℕ} (hp : p ≠ 0) {π : R} (hπ : π ∣ (p : R))
    {τ : Φ} {h : ℕ} {b : n'} (h_exempt : τ ∈ ev ∨ h = 1 ∧ partner τ ∈ ev) :
    π ∣ ((p : R) ^ w τ 1 b) ^ p ^ e * (p : R) ^ w (partner τ) h b := by
  have h_factor : (p : R) ∣ ((p : R) ^ w τ 1 b) ^ p ^ e * (p : R) ^ w (partner τ) h b := by
    obtain h_left | h_right := hw τ h b h_exempt
    · exact (dvd_pow (dvd_pow_self (p : R) h_left)
        (Nat.pow_pos (Nat.pos_of_ne_zero hp)).ne').mul_right _
    · exact (dvd_pow_self (p : R) h_right).mul_left _
  exact hπ.trans h_factor

end TauCeti
