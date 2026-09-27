/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import TauCeti.NumberTheory.NumberField.Units.Elimination.Basic

/-!
# The elimination certificate at the golden ratio

In a quadratic field, the candidate minimal polynomials of a unit below
`Real.goldenRatio = (1 + √5)/2` at a real place are the monic quadratics `X² + mX ± 1` with
`|m| ≤ φ + 1`, hence `|m| ≤ 2`, and none of them has a real root in the open interval `(1, φ)`:
the elimination certificate at `B = φ` holds by the root test alone, uniformly in the field.
It certifies a unit of value `φ` at a real place as a generator of the units modulo torsion,
which is the case of `ℚ(√5)` presented by the golden ratio.

## Main results

* `TauCeti.NumberField.Units.unitCandidateEliminationCertificate_goldenRatio`: the certificate
  `UnitCandidateEliminationCertificate K Real.goldenRatio` for every quadratic field `K`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.7.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- **The elimination certificate at the golden ratio.** In a quadratic field, every candidate
polynomial `X² + mX ± 1` with `|m| ≤ φ + 1` has no real root in `(1, φ)`, where
`φ = Real.goldenRatio`. -/
theorem unitCandidateEliminationCertificate_goldenRatio (hdeg : Module.finrank ℚ K = 2) :
    UnitCandidateEliminationCertificate K Real.goldenRatio := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = Real.goldenRatio := ⟨_, rfl⟩
  have hφ2 : φ ^ 2 = φ + 1 := by rw [hφ]; exact Real.goldenRatio_sq
  have hφl : 1 < φ := by rw [hφ]; exact Real.one_lt_goldenRatio
  have hφu : φ < 2 := by rw [hφ]; exact Real.goldenRatio_lt_two
  rw [← hφ, unitCandidateEliminationCertificate_iff]
  intro g hg
  rw [mem_unitCandidates_iff, hdeg] at hg
  obtain ⟨hmonic, hdeg, h0, hk⟩ := hg
  left
  rintro x ⟨hx1, hxφ⟩
  -- The candidate is `X² + mX + c` with `c = ±1` and `|m| ≤ φ + 1`, so `|m| ≤ 2`.
  have hm := hk 1 one_pos one_lt_two
  norm_num at hm
  have hm2 : -3 < g.coeff 1 ∧ g.coeff 1 < 3 := by
    rw [abs_le] at hm
    constructor
    · exact_mod_cast (by linarith : (-3 : ℝ) < g.coeff 1)
    · exact_mod_cast (by linarith : (g.coeff 1 : ℝ) < 3)
  have h2 : g.coeff 2 = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
  have heval : aeval x g = x ^ 2 + g.coeff 1 * x + g.coeff 0 := by
    rw [aeval_eq_sum_range, hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zsmul_eq_mul, h2, Int.cast_one,
      pow_zero, pow_one, zero_add]
    ring
  rw [heval]
  obtain ⟨hm1, hm3⟩ := hm2
  -- The interval facts driving the root test: `x < φ`, `x < 2`, and `1 < x`.
  have hx2 : 1 < x ^ 2 := one_lt_pow₀ hx1 two_ne_zero
  have hA : 0 < (φ - x) * (x + φ - 1) := mul_pos (sub_pos.mpr hxφ) (by linarith)
  have hB : 0 < (x - 1) * (2 - x) := mul_pos (sub_pos.mpr hx1) (by linarith)
  have hC : 0 < (x - 1) * (x - 1) := mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hx1)
  generalize g.coeff 1 = m at hm1 hm3
  interval_cases m <;> rcases h0 with h0 | h0 <;> rw [h0] <;> push_cast <;> nlinarith

end TauCeti.NumberField.Units
