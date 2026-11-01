/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.AdicCompletion.Newton

/-!
# Checks for the quantitative Newton method

These examples exercise Hensel's lemma with a derivative dividing `π ^ k` on square roots in
`ℤ₂`. The derivative of `X ^ 2 - a` at `1` is `2`, never a unit, so the case `k = 0` does not
apply; with `k = 1` the hypothesis `f(1) ≡ 0 mod 8` is the classical condition `a ≡ 1 mod 8`.
-/

open Polynomial

namespace TauCeti.Examples

-- An element `a ≡ 1 mod 8` of `ℤ₂` has exactly one square root congruent to `1` modulo `4`.
example (a : ℤ_[2]) (ha : 8 ∣ a - 1) : ∃! u : ℤ_[2], 4 ∣ u - 1 ∧ u ^ 2 = a := by
  have : IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] := by
    rw [show ((2 : ℤ_[2])) = ((2 : ℕ) : ℤ_[2]) by norm_num, ← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have h4 : (4 : ℤ_[2]) = 2 ^ (1 + 1) := by norm_num
  obtain ⟨u, ⟨hu, hfu⟩, huniq⟩ := IsAdicComplete.existsUnique_eval_eq_zero_of_dvd_pow
    (f := X ^ 2 - C a) (t := 1) (k := 1) (IsRegular.of_ne_zero two_ne_zero).left
    ⟨1, by simp; norm_num⟩
    (by simpa [dvd_sub_comm] using (show (8 : ℤ_[2]) = 2 ^ (2 * 1 + 1) by norm_num) ▸ ha)
  refine ⟨u, ⟨by simpa using h4 ▸ hu, by simpa [sub_eq_zero] using hfu⟩,
    fun y ⟨hy, hya⟩ ↦ huniq y ⟨by simpa using h4 ▸ hy, by simp [hya]⟩⟩

-- The error bound: if `a ≡ 1 mod 2 ^ e` with `e ≥ 3`, that root is `≡ 1 mod 2 ^ (e - 1)`.
example (a : ℤ_[2]) {e : ℕ} (he : 3 ≤ e) (ha : 2 ^ e ∣ a - 1) {u : ℤ_[2]} (hu : 4 ∣ u - 1)
    (hua : u ^ 2 = a) : 2 ^ (e - 1) ∣ u - 1 :=
  pow_dvd_sub_of_eval_eq_zero_of_dvd_pow (f := X ^ 2 - C a) (t := 1) (k := 1)
    (IsRegular.of_ne_zero two_ne_zero).left ⟨1, by simp; norm_num⟩ he
    (by simpa [dvd_sub_comm] using ha)
    (by simpa using (show (4 : ℤ_[2]) = 2 ^ (1 + 1) by norm_num) ▸ hu) (by simp [hua])

end TauCeti.Examples
