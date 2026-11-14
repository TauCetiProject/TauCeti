/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The exponent arithmetic for iterating the Sobolev embedding

In dimension `n`, the Sobolev embedding `W^{1,p} ⊂ L^s` holds for `p ≤ s` with
`1/p - 1/s ≤ 1/n`. Applied to the weak derivatives, it lowers the derivative order by one while
raising the integrability exponent from `p` to `s`. This file records the exponent arithmetic of
one step of the resulting iteration towards Morrey's condition: if `p ≤ n` and `(k + 1) p > n`,
some admissible `s` satisfies `k s > n`. For `p < n` the critical exponent `1/s = 1/p - 1/n` is
such a witness, and for `p = n` so is `2 n`. This is the exponent arithmetic only, not an
embedding theorem.

## Main declarations

* `TauCeti.exists_le_and_inv_sub_inv_le_and_lt_mul`: one step of the exponent iteration.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open scoped NNReal

namespace TauCeti

/-- One step of the exponent iteration for Morrey's condition `kp > n`: if `p ≤ n` and
`(k + 1) p > n`, there is an exponent `s` admissible for the Sobolev embedding `W^{1,p} ⊂ L^s` in
dimension `n`, that is `p ≤ s` and `1/p - 1/s ≤ 1/n`, with `k s > n`. -/
theorem exists_le_and_inv_sub_inv_le_and_lt_mul {k : ℕ} {p n : ℝ≥0} (hpn : p ≤ n)
    (hkp : n < ((k + 1 : ℕ) : ℝ≥0) * p) :
    ∃ s : ℝ≥0, p ≤ s ∧ (p : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ ∧ n < (k : ℝ≥0) * s := by
  have hkp' : (n : ℝ) < ((k : ℝ) + 1) * p := by exact_mod_cast hkp
  have hpn' : (p : ℝ) ≤ n := hpn
  have hp0 : (0 : ℝ) < p :=
    pos_of_mul_pos_right ((NNReal.coe_nonneg n).trans_lt hkp') (by positivity)
  have hn0 : (0 : ℝ) < n := hp0.trans_le hpn'
  rcases hpn.lt_or_eq with hlt | rfl
  · have hlt' : (p : ℝ) < n := hlt
    have ha : 0 < (p : ℝ)⁻¹ - (n : ℝ)⁻¹ := sub_pos.2 (inv_strictAnti₀ hp0 hlt')
    obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, (s : ℝ) = ((p : ℝ)⁻¹ - (n : ℝ)⁻¹)⁻¹ :=
      ⟨⟨_, (inv_pos.2 ha).le⟩, rfl⟩
    have hs0 : (0 : ℝ) < s := hs ▸ inv_pos.2 ha
    have hsa : (s : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹ := by rw [hs, inv_inv]
    have hn' : 0 < (n : ℝ)⁻¹ := inv_pos.2 hn0
    refine ⟨s, ?_, by linarith, ?_⟩
    · rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hs0 hp0]
      linarith
    · have h1 : (n : ℝ) / p < k + 1 := (div_lt_iff₀ hp0).2 hkp'
      have h2 : (n : ℝ) / s < k := by
        have : (n : ℝ) / s = n / p - 1 := by rw [div_eq_mul_inv, hsa]; field_simp
        linarith
      rw [← NNReal.coe_lt_coe]
      push_cast
      exact (div_lt_iff₀ hs0).1 h2
  · have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hkp'
      · exact hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    refine ⟨2 * p, by rw [two_mul]; exact le_self_add, ?_, ?_⟩
    · have : 0 < (p : ℝ)⁻¹ := inv_pos.2 hp0
      push_cast
      rw [mul_inv]
      linarith
    · rw [← NNReal.coe_lt_coe]
      push_cast
      nlinarith

end TauCeti
