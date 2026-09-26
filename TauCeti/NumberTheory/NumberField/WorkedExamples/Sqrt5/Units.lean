/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import TauCeti.NumberTheory.NumberField.Units.Elimination
public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.RealPlace
import TauCeti.NumberTheory.NumberField.Units.Torsion

/-!
# The fundamental unit and the regulator of `ℚ(√5)`

Let `K` be a number field generated over `ℚ` by an algebraic integer `θ` with
`minpoly ℤ θ = X² − X − 1`, so that `K = ℚ(√5)`. At the real place `w` where `θ` has the value
`φ = (1 + √5)/2`, every candidate minimal polynomial `X² + mX ± 1` of a competing unit has no
real root in the open interval `(1, φ)`. The elimination certificate of
`TauCeti.NumberTheory.NumberField.Units.Elimination` therefore applies: a unit `u` lying over
`θ` generates the unit group modulo torsion, the regulator is `log ((1 + √5)/2)`, and the
torsion subgroup has order `2`.

## Main results

* `TauCeti.NumberField.Sqrt5.unitCandidateEliminationCertificate`: the elimination certificate
  at `B = (1 + √5)/2`, by the root test alone.
* `TauCeti.NumberField.Sqrt5.closure_sup_torsion_eq_top`: a unit lying over `θ` generates the
  units of `ℚ(√5)` modulo torsion.
* `TauCeti.NumberField.Sqrt5.regulator_eq_log_goldenRatio`:
  `regulator K = Real.log ((1 + √5) / 2)`.
* `TauCeti.NumberField.Sqrt5.torsionOrder_eq_two`: the torsion subgroup has order `2`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.7.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace NumberField.Units TauCeti.NumberField
  TauCeti.NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The elimination certificate for `ℚ(√5)`.** Every candidate polynomial `X² + mX ± 1` with
`|m| ≤ φ + 1` has no real root in `(1, φ)`, where `φ = (1 + √5) / 2`. -/
theorem unitCandidateEliminationCertificate (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    UnitCandidateEliminationCertificate K ((1 + Real.sqrt 5) / 2) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = (1 + Real.sqrt 5) / 2 := ⟨_, rfl⟩
  have hφ2 : φ ^ 2 = φ + 1 := by rw [hφ]; exact goldenRatio_sq
  have hφl : 1.6 < φ := by rw [hφ]; exact goldenRatio_bounds.1
  have hφu : φ < 1.62 := by rw [hφ]; exact goldenRatio_bounds.2
  rw [← hφ, unitCandidateEliminationCertificate_iff]
  intro g hg
  rw [mem_unitCandidates_iff, finrank_eq_two hmin hgen] at hg
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
  have heval : aeval x g = x ^ 2 + g.coeff 1 * x + g.coeff 0 := by
    rw [aeval_def, eval₂_eq_eval_map, eval_eq_sum_range,
      natDegree_map_eq_of_injective (algebraMap ℤ ℝ).injective_int, hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_map, eq_intCast, pow_zero,
      mul_one, pow_one, zero_add]
    have h2 : g.coeff 2 = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
    rw [h2, Int.cast_one, one_mul]
    ring
  rw [heval]
  obtain ⟨hm1, hm3⟩ := hm2
  have hx2 : 1 < x ^ 2 := one_lt_pow₀ hx1 two_ne_zero
  generalize g.coeff 1 = m at hm1 hm3
  interval_cases m <;> rcases h0 with h0 | h0 <;> rw [h0] <;> push_cast <;>
    nlinarith [mul_pos (sub_pos.mpr hxφ) (show (0 : ℝ) < x + φ - 1 by linarith)]

/-- **The golden ratio is a fundamental unit of `ℚ(√5)`.** A unit `u` with `(u : 𝓞 K) = θ`
generates the unit group modulo torsion. -/
theorem closure_sup_torsion_eq_top (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ} (hu : (u : 𝓞 K) = θ) :
    Subgroup.closure {u} ⊔ torsion K = ⊤ := by
  obtain ⟨w, hw, hwθ⟩ := exists_isReal_and_apply_eq_goldenRatio hmin hgen
  have hwu : w u = (1 + Real.sqrt 5) / 2 := by rw [hu]; exact hwθ
  have h1 : 1 < w u := by rw [hwu]; linarith [goldenRatio_bounds.1]
  refine UnitCandidateEliminationCertificate.sound ?_ (rank_eq_one hmin hgen)
    (finrank_eq_two hmin hgen ▸ Nat.prime_two) hw h1
  rw [hwu]
  exact unitCandidateEliminationCertificate hmin hgen

/-- **The regulator of `ℚ(√5)`** is `log ((1 + √5) / 2)`. -/
theorem regulator_eq_log_goldenRatio (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ} (hu : (u : 𝓞 K) = θ) :
    regulator K = Real.log ((1 + Real.sqrt 5) / 2) := by
  obtain ⟨w, hw, hwθ⟩ := exists_isReal_and_apply_eq_goldenRatio hmin hgen
  have hwu : w u = (1 + Real.sqrt 5) / 2 := by rw [hu]; exact hwθ
  have h1 : 1 < w u := by rw [hwu]; linarith [goldenRatio_bounds.1]
  rw [regulator_eq_mult_log_of_rank_eq_one (rank_eq_one hmin hgen) u
    (closure_sup_torsion_eq_top hmin hgen hu) w h1, hwu, hw.mult_eq_one, Nat.cast_one, one_mul]

/-- The torsion subgroup of the units of `ℚ(√5)` is `{±1}`, of order `2`. -/
theorem torsionOrder_eq_two (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : torsionOrder K = 2 := by
  obtain ⟨w, hw, -⟩ := exists_isReal_and_apply_eq_goldenRatio hmin hgen
  exact torsionOrder_eq_two_of_isReal hw

end TauCeti.NumberField.Sqrt5
