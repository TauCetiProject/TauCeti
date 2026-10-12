/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.Regulator

/-!
# Certifying a generator of the units modulo torsion in rank one

For a number field of unit rank one, a non-torsion unit generates the unit group modulo torsion
exactly when no unit has a smaller nonzero logarithmic embedding. The statement uses Mathlib's
logarithmic embedding and torsion subgroup. It turns the generation condition used in the
rank-one regulator formula into a minimality test on units.

The criterion makes the abstract generation condition testable through logarithmic norms.
The placewise comparison in `Units.Regulator` expresses these norms as weighted logarithms
at a chosen infinite place.

## Main results

* `TauCeti.NumberField.Units.generates_mod_torsion_iff_no_smaller_logEmbedding`: the rank-one
  generator criterion.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.7.
-/

public section
noncomputable section

open NumberField NumberField.Units NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- A non-torsion unit in a rank-one number field generates all units modulo torsion exactly
when there is no unit with a strictly smaller nonzero logarithmic embedding. -/
theorem generates_mod_torsion_iff_no_smaller_logEmbedding (hr : rank K = 1)
    (u : (𝓞 K)ˣ) (hu : u ∉ torsion K) :
    Subgroup.closure {u} ⊔ torsion K = ⊤ ↔
      ¬ ∃ v : (𝓞 K)ˣ, 0 < ‖logEmbedding K (Additive.ofMul v)‖ ∧
        ‖logEmbedding K (Additive.ofMul v)‖ <
          ‖logEmbedding K (Additive.ofMul u)‖ := by
  classical
  have hnorm (v : (𝓞 K)ˣ) :
      ‖logEmbedding K (Additive.ofMul v)‖ =
        ((Subgroup.closure {v} ⊔ torsion K).index : ℝ) * regulator K := by
    rw [norm_logEmbedding_eq_mult_abs_log hr v NumberField.Units.dirichletUnitTheorem.w₀,
      mult_abs_log_eq_index_mul_regulator hr v NumberField.Units.dirichletUnitTheorem.w₀]
  have hupos : 0 < ‖logEmbedding K (Additive.ofMul u)‖ := by
    rw [norm_pos_iff, ne_eq, NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff]
    exact hu
  constructor
  · intro hgen ⟨v, hvpos, hvlt⟩
    have hi : (Subgroup.closure {u} ⊔ torsion K).index = 1 :=
      Subgroup.index_eq_one.mpr hgen
    rw [hnorm v] at hvpos hvlt
    rw [hnorm u, hi, Nat.cast_one, one_mul] at hvlt
    have hvindex : 1 ≤ (Subgroup.closure {v} ⊔ torsion K).index := by
      by_contra h
      have hzero : (Subgroup.closure {v} ⊔ torsion K).index = 0 := by omega
      simp [hzero] at hvpos
    have := regulator_pos K
    exact (not_lt_of_ge (le_mul_of_one_le_left this.le (by exact_mod_cast hvindex))) hvlt
  · intro hmin
    let i : Fin (rank K) := ⟨0, by omega⟩
    let g : (𝓞 K)ˣ := fundSystem K i
    have hrange : Set.range (fundSystem K) = {g} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩
        congr 1
        exact Fin.ext (by omega)
      · rintro rfl
        exact ⟨i, rfl⟩
    have hggen : Subgroup.closure {g} ⊔ torsion K = ⊤ := by
      simpa only [hrange] using closure_fundSystem_sup_torsion_eq_top (K := K)
    have hgindex : (Subgroup.closure {g} ⊔ torsion K).index = 1 :=
      Subgroup.index_eq_one.mpr hggen
    have hgpos : 0 < ‖logEmbedding K (Additive.ofMul g)‖ := by
      rw [hnorm, hgindex]
      simpa using regulator_pos K
    have hule : ‖logEmbedding K (Additive.ofMul u)‖ ≤
        ‖logEmbedding K (Additive.ofMul g)‖ :=
      le_of_not_gt (fun h => hmin ⟨g, hgpos, h⟩)
    have hi : (Subgroup.closure {u} ⊔ torsion K).index = 1 := by
      have hidxpos : 0 < (Subgroup.closure {u} ⊔ torsion K).index := by
        by_contra h
        have hzero : (Subgroup.closure {u} ⊔ torsion K).index = 0 := by omega
        rw [hnorm, hzero] at hupos
        simp at hupos
      rw [hnorm u, hnorm g, hgindex, Nat.cast_one, one_mul] at hule
      have hle : (Subgroup.closure {u} ⊔ torsion K).index ≤ 1 := by
        have hreal : ((Subgroup.closure {u} ⊔ torsion K).index : ℝ) ≤ 1 :=
          le_of_mul_le_mul_right (by simpa using hule) (regulator_pos K)
        exact_mod_cast hreal
      omega
    exact Subgroup.index_eq_one.mp hi

end TauCeti.NumberField.Units
