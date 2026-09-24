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

The logarithmic space has one coordinate in rank one. The regulator-index formula identifies
the norm of that coordinate with the subgroup index times the positive regulator. If the index
of a proposed unit exceeds one, a fundamental unit supplies the smaller unit.

## Main results

* `TauCeti.NumberField.Units.norm_logEmbedding_eq_mult_abs_log`: at every infinite place, the
  log-embedding norm is the absolute value of the weighted logarithm there.
* `TauCeti.NumberField.Units.logEmbedding_norm_lt_iff_at_place`: compares log-embedding norms
  using the absolute logarithm at a chosen place.
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
/-- In unit rank one, the logarithmic embedding has one coordinate. Its norm is the absolute
value of the weighted logarithm at any place other than Mathlib's distinguished place. -/
private theorem norm_logEmbedding_eq_mult_abs_log_of_rank_eq_one (hr : rank K = 1)
    (u : (𝓞 K)ˣ) (w : InfinitePlace K)
    (hw : w ≠ NumberField.Units.dirichletUnitTheorem.w₀) :
    ‖logEmbedding K (Additive.ofMul u)‖ = w.mult * |Real.log (w u)| := by
  classical
  have hplaces : Fintype.card (InfinitePlace K) = 2 := by
    unfold rank at hr
    omega
  have hcard : Fintype.card {v : InfinitePlace K //
      v ≠ NumberField.Units.dirichletUnitTheorem.w₀} = 1 := by
    simp [Fintype.card_subtype_compl, hplaces]
  have : Subsingleton {v : InfinitePlace K //
      v ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  let : Unique {v : InfinitePlace K //
      v ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
    ⟨⟨⟨w, hw⟩⟩, fun _ => Subsingleton.elim _ _⟩
  have hdefault : (default : {v : InfinitePlace K //
      v ≠ NumberField.Units.dirichletUnitTheorem.w₀}) = ⟨w, hw⟩ :=
    Subsingleton.elim _ _
  rw [Pi.norm_def]
  simp [Finset.univ_unique, hdefault,
    NumberField.Units.dirichletUnitTheorem.logEmbedding_component]

open scoped Classical in
/-- In unit rank one, the norm of the logarithmic embedding is the weighted absolute logarithm
at *any* infinite place. The regulator-index formula identifies the values at different places,
including Mathlib's distinguished place. -/
theorem norm_logEmbedding_eq_mult_abs_log (hr : rank K = 1) (u : (𝓞 K)ˣ)
    (w : InfinitePlace K) :
    ‖logEmbedding K (Additive.ofMul u)‖ = w.mult * |Real.log (w u)| := by
  have hplaces : Fintype.card (InfinitePlace K) = 2 := by
    unfold rank at hr
    omega
  have : Nontrivial (InfinitePlace K) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w', hw'⟩ := exists_ne (NumberField.Units.dirichletUnitTheorem.w₀ (K := K))
  calc
    ‖logEmbedding K (Additive.ofMul u)‖ =
        w'.mult * |Real.log (w' u)| :=
      norm_logEmbedding_eq_mult_abs_log_of_rank_eq_one hr u w' hw'
    _ = ((Subgroup.closure {u} ⊔ torsion K).index : ℝ) * regulator K :=
      mult_abs_log_eq_index_mul_regulator hr u w'
    _ = w.mult * |Real.log (w u)| :=
      (mult_abs_log_eq_index_mul_regulator hr u w).symm

open scoped Classical in
/-- At a place where `u` has absolute value greater than one, comparing log-embedding norms
amounts to comparing the absolute logarithm of `v` with the logarithm of `u` at that place. -/
theorem logEmbedding_norm_lt_iff_at_place (hr : rank K = 1) (u v : (𝓞 K)ˣ)
    (w : InfinitePlace K) (hw : 1 < w u) :
    ‖logEmbedding K (Additive.ofMul v)‖ < ‖logEmbedding K (Additive.ofMul u)‖ ↔
      |Real.log (w v)| < Real.log (w u) := by
  rw [norm_logEmbedding_eq_mult_abs_log hr v w,
    norm_logEmbedding_eq_mult_abs_log hr u w, abs_of_pos (Real.log_pos hw)]
  have hmult : (0 : ℝ) < (w.mult : ℝ) := by
    exact_mod_cast (NumberField.InfinitePlace.mult_pos (w := w))
  exact ⟨fun h => lt_of_mul_lt_mul_left h hmult.le,
    fun h => mul_lt_mul_of_pos_left h hmult⟩

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
  have hplaces : Fintype.card (InfinitePlace K) = 2 := by
    unfold rank at hr
    omega
  have : Nontrivial (InfinitePlace K) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, hw⟩ := exists_ne (NumberField.Units.dirichletUnitTheorem.w₀ (K := K))
  have hnorm (v : (𝓞 K)ˣ) :
      ‖logEmbedding K (Additive.ofMul v)‖ =
        ((Subgroup.closure {v} ⊔ torsion K).index : ℝ) * regulator K := by
    rw [norm_logEmbedding_eq_mult_abs_log_of_rank_eq_one hr v w hw,
      mult_abs_log_eq_index_mul_regulator hr v w]
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
