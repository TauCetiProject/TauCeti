/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Defs

import Mathlib.Data.Fintype.Order

/-!
# Shifting integer-valued families to natural-number families

An integer-valued family `e : ι → ℤ` bounded below by `-c` becomes nonnegative after shifting by
`c`, so it lifts to a natural-number family `f : ι → ℕ` satisfying `(f i : ℤ) = e i + c`. When `ι`
is finite, every family `e : ι → ℤ` is bounded below, so a uniform natural-number shift `k : ℕ`
exists without supplying a lower bound explicitly (and applying the theorem to `Sum.elim e₁ e₂`
shifts two families by a common `k : ℕ`).

## Main results

* `TauCeti.exists_natCast_eq_add_of_forall_neg_le`: given `e : ι → ℤ` and `c : ℤ` with
  `∀ i, -c ≤ e i`, there exists `f : ι → ℕ` with `(f i : ℤ) = e i + c` for all `i`.
* `TauCeti.exists_natCast_eq_add_natCast`: for `[Finite ι]` and `e : ι → ℤ`, there exist `k : ℕ`
  and `f : ι → ℕ` with `(f i : ℤ) = e i + k` for all `i`.
-/

public section

namespace TauCeti

/-- Any integer-valued family `e : ι → ℤ` bounded below by `-c` lifts after shifting by `c` to a
natural-number family `f : ι → ℕ` satisfying `(f i : ℤ) = e i + c` pointwise. -/
theorem exists_natCast_eq_add_of_forall_neg_le {ι : Sort*} (e : ι → ℤ) {c : ℤ}
    (hc : ∀ i, -c ≤ e i) :
    ∃ f : ι → ℕ, ∀ i, (f i : ℤ) = e i + c :=
  ⟨fun i ↦ (e i + c).toNat, fun i ↦ Int.toNat_of_nonneg (by have := hc i; omega)⟩

/-- Every integer-valued family on a finite domain shifts by a constant natural number to a
natural-number family: there exist `k : ℕ` and `f : ι → ℕ` with `(f i : ℤ) = e i + (k : ℤ)` for
every `i`. -/
theorem exists_natCast_eq_add_natCast {ι : Sort*} [Finite ι] (e : ι → ℤ) :
    ∃ (k : ℕ) (f : ι → ℕ), ∀ i, (f i : ℤ) = e i + (k : ℤ) := by
  obtain ⟨k, hk⟩ := Finite.exists_le fun i ↦ (-e i).toNat
  exact ⟨k, exists_natCast_eq_add_of_forall_neg_le e fun i ↦ by have := hk i; omega⟩

end TauCeti
