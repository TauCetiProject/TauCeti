/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Defs
import Mathlib.Tactic

/-!
# The exponent step for Morrey with `kp > 2` in dimension two

In dimension two, the Sobolev embedding `W^{1,p} ⊂ L^s` holds for `p ≤ s` with
`1/p - 1/s ≤ 1/2`. Applied to the weak derivatives, it lowers the derivative order by one while
raising the integrability exponent from `p` to `s`. This file records the exponent arithmetic of
one step of the resulting iteration: if `1 ≤ p ≤ 2` and `(k + 1) p > 2`, some admissible `s`
satisfies `k s > 2`. For `p < 2` it is the critical exponent `1/s = 1/p - 1/2`, and for `p = 2`
it is `4`. This is the exponent arithmetic only, not an embedding theorem.

## Main declarations

* `TauCeti.exists_sobolev_exponent_step`: the exponent step.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open scoped NNReal

namespace TauCeti

/-- One step of the exponent iteration for `kp > 2` with `p ≤ 2` in dimension two: there is a
target exponent `s` admissible for the Sobolev embedding `W^{1,p} ⊂ L^s`, that is `p ≤ s` and
`1/p - 1/s ≤ 1/2`, with `k s > 2`. For `p < 2` it is the critical exponent `1/s = 1/p - 1/2`,
and for `p = 2` it is `4`. -/
theorem exists_sobolev_exponent_step {k : ℕ} {p : ℝ≥0} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hkp : 2 < ((k + 1 : ℕ) : ℝ≥0) * p) :
    ∃ s : ℝ≥0, p ≤ s ∧ (p : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹ ∧ 2 < (k : ℝ≥0) * s := by
  have hkp' : (2 : ℝ) < ((k : ℝ) + 1) * p := by exact_mod_cast hkp
  have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  rcases hp2.lt_or_eq with hlt | rfl
  · have hlt' : (p : ℝ) < 2 := by exact_mod_cast hlt
    have hp0 : (0 : ℝ) < p := by positivity
    have ha : 0 < (p : ℝ)⁻¹ - 2⁻¹ := sub_pos.2 (inv_strictAnti₀ (by positivity) hlt')
    obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, (s : ℝ) = ((p : ℝ)⁻¹ - 2⁻¹)⁻¹ := ⟨⟨_, (inv_pos.2 ha).le⟩, rfl⟩
    have hs0 : (0 : ℝ) < s := hs ▸ inv_pos.2 ha
    have hsa : (s : ℝ)⁻¹ = (p : ℝ)⁻¹ - 2⁻¹ := by rw [hs, inv_inv]
    refine ⟨s, ?_, ?_, ?_⟩
    · rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hs0 hp0, hsa]
      have : (2 : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ := inv_anti₀ hp0 hlt'.le
      have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1'
      linarith
    · rw [hsa]
      linarith
    · rw [← NNReal.coe_lt_coe]
      push_cast
      -- `2 / p < k + 1`, so `2 (1/p - 1/2) = 2 / p - 1 < k`.
      have h2p : (2 : ℝ) * (p : ℝ)⁻¹ < k + 1 := by
        rw [← div_eq_mul_inv]
        exact (div_lt_iff₀ hp0).2 hkp'
      have hkey : (2 : ℝ) * ((p : ℝ)⁻¹ - 2⁻¹) < k := by linarith
      rw [hs, ← div_eq_mul_inv]
      exact (lt_div_iff₀ ha).2 hkey
  · refine ⟨4, by norm_num, by norm_num, ?_⟩
    have hk : 1 ≤ k := by
      by_contra h
      have h0 : k = 0 := by omega
      subst h0
      norm_num at hkp'
    rw [← NNReal.coe_lt_coe]
    push_cast
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith

end TauCeti
