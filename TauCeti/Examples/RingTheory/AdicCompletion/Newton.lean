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
  have hd : (X ^ 2 - C a).derivative.eval 1 ∣ (2 : ℤ_[2]) ^ 1 := by norm_num
  have ha' : (2 : ℤ_[2]) ^ (2 * 1 + 1) ∣ (X ^ 2 - C a).eval 1 := by
    norm_num
    simpa [dvd_sub_comm] using ha
  have h4 : (2 : ℤ_[2]) ^ (1 + 1) = 4 := by norm_num
  simpa [h4, sub_eq_zero, eq_comm] using IsAdicComplete.existsUnique_eval_eq_zero_of_dvd_pow
    (IsRegular.of_ne_zero two_ne_zero).left hd ha'

-- The error bound: if `a ≡ 1 mod 2 ^ e`, that root is `≡ 1 mod 2 ^ (e - 1)`.
example (a : ℤ_[2]) {e : ℕ} (ha : 2 ^ e ∣ a - 1) {u : ℤ_[2]} (hu : 4 ∣ u - 1)
    (hua : u ^ 2 = a) : 2 ^ (e - 1) ∣ u - 1 := by
  have hd : (X ^ 2 - C a).derivative.eval 1 ∣ (2 : ℤ_[2]) ^ 1 := by norm_num
  have ha' : 2 ^ e ∣ (X ^ 2 - C a).eval 1 := by simpa [dvd_sub_comm] using ha
  have hu' : (2 : ℤ_[2]) ^ (1 + 1) ∣ u - 1 := by norm_num [hu]
  exact pow_dvd_sub_of_eval_eq_zero_of_dvd_pow (IsRegular.of_ne_zero two_ne_zero).left hd ha'
    hu' (by simp [hua])

end TauCeti.Examples
