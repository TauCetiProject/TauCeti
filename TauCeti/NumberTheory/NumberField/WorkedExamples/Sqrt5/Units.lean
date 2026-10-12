/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.RealPlace
import TauCeti.NumberTheory.NumberField.Units.Elimination.GoldenRatio
import TauCeti.NumberTheory.NumberField.Units.Torsion

/-!
# The fundamental unit and the regulator of `ℚ(√5)`

Let `K` be a number field generated over `ℚ` by an algebraic integer `θ` with
`minpoly ℤ θ = X² − X − 1`, so that `K = ℚ(√5)`. At the real place `w` where `θ` has the value
`Real.goldenRatio = (1 + √5)/2`, the elimination certificate at the golden ratio of
`TauCeti.NumberTheory.NumberField.Units.Elimination.GoldenRatio` applies: `θ` is a unit, since
`θ (θ − 1) = 1`, it generates the unit group modulo torsion, the regulator is
`Real.log Real.goldenRatio`, and the torsion subgroup has order `2`.

## Main results

* `TauCeti.NumberField.Sqrt5.mul_sub_one_eq_one`: `θ (θ − 1) = 1`, so `θ` is a unit.
* `TauCeti.NumberField.Sqrt5.closure_sup_torsion_eq_top`: a unit with value `θ` generates the
  units of `ℚ(√5)` modulo torsion.
* `TauCeti.NumberField.Sqrt5.regulator_eq_log_goldenRatio`:
  `regulator K = Real.log Real.goldenRatio`.
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

omit [NumberField K] in
/-- An algebraic integer `θ` with `minpoly ℤ θ = X² − X − 1` is a unit: `θ (θ − 1) = 1`. -/
@[simp]
theorem mul_sub_one_eq_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1) : θ * (θ - 1) = 1 := by
  have h := minpoly.aeval ℤ θ
  simp only [hmin, map_sub, map_pow, aeval_X, map_one] at h
  linear_combination h

/-- **The golden ratio is a fundamental unit of `ℚ(√5)`.** A unit `u` with `(u : 𝓞 K) = θ`
generates the unit group modulo torsion. -/
theorem closure_sup_torsion_eq_top (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ} (hu : (u : 𝓞 K) = θ) :
    Subgroup.closure {u} ⊔ torsion K = ⊤ := by
  obtain ⟨w, hw, hwθ⟩ := exists_isReal_and_apply_eq_goldenRatio hmin hgen
  have hwu : w u = Real.goldenRatio := by rw [hu]; exact hwθ
  have h1 : 1 < w u := by rw [hwu]; exact Real.one_lt_goldenRatio
  refine UnitCandidateEliminationCertificate.sound ?_ (units_rank_eq_one hmin hgen)
    (finrank_eq_two hmin hgen ▸ Nat.prime_two) hw h1
  rw [hwu]
  exact unitCandidateEliminationCertificate_goldenRatio (finrank_eq_two hmin hgen)

/-- **The regulator of `ℚ(√5)`** is `Real.log Real.goldenRatio = log ((1 + √5) / 2)`. -/
theorem regulator_eq_log_goldenRatio (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : regulator K = Real.log Real.goldenRatio := by
  obtain ⟨w, hw, hwθ⟩ := exists_isReal_and_apply_eq_goldenRatio hmin hgen
  -- The unit `θ`, with inverse `θ - 1`.
  let u : (𝓞 K)ˣ := Units.mkOfMulEqOne θ (θ - 1) (mul_sub_one_eq_one hmin)
  have hu : (u : 𝓞 K) = θ := Units.val_mkOfMulEqOne _
  have hwu : w u = Real.goldenRatio := by rw [hu]; exact hwθ
  have h1 : 1 < w u := by rw [hwu]; exact Real.one_lt_goldenRatio
  rw [regulator_eq_mult_log_of_rank_eq_one (units_rank_eq_one hmin hgen) u
    (closure_sup_torsion_eq_top hmin hgen hu) w h1, hwu, hw.mult_eq_one, Nat.cast_one, one_mul]

/-- The torsion subgroup of the units of `ℚ(√5)` has order `2`. -/
theorem torsionOrder_eq_two (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : torsionOrder K = 2 := by
  obtain ⟨w, hw, -⟩ := exists_isReal_and_apply_eq_goldenRatio hmin hgen
  exact torsionOrder_eq_two_of_isReal hw

end TauCeti.NumberField.Sqrt5
