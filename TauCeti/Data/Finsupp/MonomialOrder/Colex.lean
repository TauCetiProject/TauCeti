/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.WellFounded

/-!
# The colexicographic monomial order

This file packages the colexicographic order `Colex (σ →₀ ℕ)` as a `MonomialOrder σ`, alongside
Mathlib's `MonomialOrder.lex`. Two exponents are compared at the *largest* index of `σ` where they
differ, so for `σ = Fin n` the variable `X (n - 1)` is the largest and `X 0` the smallest. It is the
lexicographic order for the reversed order of the variables.

## Main declarations

* `TauCeti.MonomialOrder.colex`: the colexicographic `MonomialOrder σ`, for `σ` linearly ordered
  with `WellFoundedLT σ` (automatic when `σ` is finite).
* `TauCeti.MonomialOrder.colex_lt_iff`: the comparison at the largest differing index.
* `TauCeti.MonomialOrder.colex_single_lt_iff`: variables are ordered monotonely,
  `X i < X j ↔ i < j`.
-/

@[expose] public section

namespace TauCeti

namespace MonomialOrder

open Finsupp

variable {σ : Type*} [LinearOrder σ] [WellFoundedLT σ]

/-- The colexicographic order on `σ →₀ ℕ`, as a `MonomialOrder`: exponents are compared at the
largest index where they differ. Variables are ordered monotonely, `X i ≤ X j ↔ i ≤ j`. -/
noncomputable def colex : _root_.MonomialOrder σ where
  syn := Colex (σ →₀ ℕ)
  toSyn := { toEquiv := toColex, map_add' := fun _ _ => rfl }
  toSyn_monotone := Finsupp.toColex_monotone

open scoped _root_.MonomialOrder

theorem colex_le_iff {a b : σ →₀ ℕ} : a ≼[colex] b ↔ toColex a ≤ toColex b :=
  Iff.rfl

theorem colex_lt_iff {a b : σ →₀ ℕ} :
    a ≺[colex] b ↔ ∃ i, (∀ j, i < j → a j = b j) ∧ a i < b i :=
  Colex.lt_iff

/-- If two exponents agree beyond the index `i` and the second is larger at `i`, it is larger in
the colexicographic order. -/
theorem colex_lt_of_eq_of_lt {a b : σ →₀ ℕ} (i : σ) (h_eq : ∀ j, i < j → a j = b j)
    (h_lt : a i < b i) : a ≺[colex] b :=
  colex_lt_iff.mpr ⟨i, h_eq, h_lt⟩

@[simp]
theorem colex_single_lt_iff {a b : σ} : single a 1 ≺[colex] single b 1 ↔ a < b :=
  Finsupp.Colex.single_lt_iff

@[simp]
theorem colex_single_le_iff {a b : σ} : single a 1 ≼[colex] single b 1 ↔ a ≤ b :=
  Finsupp.Colex.single_le_iff

end MonomialOrder

end TauCeti
