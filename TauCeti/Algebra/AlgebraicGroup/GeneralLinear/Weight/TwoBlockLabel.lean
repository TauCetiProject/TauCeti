/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Basic

/-!
# The two-block labelling of the indices

A labelling `τ : Fin k → ℕ` of the indices of `GL_k` defines its weight Levi and parahoric
subgroups (`TauCeti.GeneralLinear.leviSubgroup`, `TauCeti.GeneralLinear.parahoricSubgroup`). The
labelling `twoBlockLabel r` splits the indices into two blocks: label `0` on the indices below
`r` and label `1` on the others.

## Main definitions

* `TauCeti.GeneralLinear.twoBlockLabel`: the labelling of a split into two blocks.

## Main results

* `TauCeti.GeneralLinear.twoBlockLabel_eq_iff`, `TauCeti.GeneralLinear.twoBlockLabel_lt_iff`:
  equality and strict comparison of two labels.

## References

* The formal proof whose route the consumers of this file follow: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

namespace TauCeti.GeneralLinear

variable {k : ℕ}

/-- The labelling `τ_r`: `0` on the indices `b < r` and `1` on the others. -/
def twoBlockLabel (r : ℕ) (b : Fin k) : ℕ := if (b : ℕ) < r then 0 else 1

/-- `τ_r` is `0` on the indices below `r`. -/
@[simp]
theorem twoBlockLabel_of_lt {r : ℕ} {b : Fin k} (h : (b : ℕ) < r) : twoBlockLabel r b = 0 := by
  simp [twoBlockLabel, h]

/-- `τ_r` is `1` on the indices from `r` on. -/
@[simp]
theorem twoBlockLabel_of_le {r : ℕ} {b : Fin k} (h : r ≤ (b : ℕ)) : twoBlockLabel r b = 1 := by
  simp [twoBlockLabel, Nat.not_lt.mpr h]

/-- `τ_r` vanishes exactly on the indices below `r`. -/
@[simp]
theorem twoBlockLabel_eq_zero_iff (r : ℕ) (b : Fin k) : twoBlockLabel r b = 0 ↔ (b : ℕ) < r := by
  simp [twoBlockLabel]

/-- Two indices have the same label exactly when both or neither lie below `r`. -/
theorem twoBlockLabel_eq_iff (r : ℕ) (b b' : Fin k) :
    twoBlockLabel r b = twoBlockLabel r b' ↔ ((b : ℕ) < r ↔ (b' : ℕ) < r) := by
  by_cases hb : (b : ℕ) < r <;> by_cases hb' : (b' : ℕ) < r <;> simp [twoBlockLabel, hb, hb']

/-- The label of `b` is strictly less than the label of `b'` exactly when `b < r ≤ b'`. -/
@[simp]
theorem twoBlockLabel_lt_iff (r : ℕ) (b b' : Fin k) :
    twoBlockLabel r b < twoBlockLabel r b' ↔ (b : ℕ) < r ∧ r ≤ (b' : ℕ) := by
  unfold twoBlockLabel
  split_ifs <;> simp_all

end TauCeti.GeneralLinear
