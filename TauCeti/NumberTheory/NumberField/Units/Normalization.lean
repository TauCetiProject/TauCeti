/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.GeneratorCriterion
public import TauCeti.NumberTheory.NumberField.Units.Basic

/-!
# Normalizing a competing unit at a real place

At a real infinite place, an absolute value forgets the sign of an embedding. To turn the
rank-one minimality criterion for logarithmic embeddings into a search among real roots in an
interval, invert a unit if its absolute value is below one and multiply it by a torsion unit
to make its real embedding positive. Given a suitable bound `B`, the resulting unit has a
real image strictly between `1` and `B`.

The normalization is used before enumerating possible minimal polynomials: it accounts for
both the inversion and the sign that are invisible in the absolute-value criterion.

## Main results

* `exists_normalized_unit_between`: a unit detected by the chosen place, with sufficiently
  small logarithmic absolute value, yields a unit whose real embedding lies in the search interval.
* `generates_mod_torsion_iff_no_unit_between_real`: at rank one, a unit expanding at a real
  place generates modulo torsion exactly when that interval contains no unit.
-/

public section
noncomputable section

open NumberField NumberField.Units NumberField.InfinitePlace
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.NumberField.Units

open scoped Classical in
/-- A unit with `w v ≠ 1` whose logarithmic absolute value is below `log B` can be inverted and
multiplied by a torsion unit so that its real image lies in the open interval from `1` to `B`. -/
theorem exists_normalized_unit_between (B : ℝ) (v : (𝓞 K)ˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (hBpos : 0 < B)
    (hv : w v ≠ 1) (hvbound : |Real.log (w v)| < Real.log B) :
    ∃ (ε : torsion K) (δ : (𝓞 K)ˣ),
      (δ = v ∨ δ = v⁻¹) ∧
      1 < embedding_of_isReal hw ((ε.1 * δ : (𝓞 K)ˣ) : K) ∧
      embedding_of_isReal hw ((ε.1 * δ : (𝓞 K)ˣ) : K) < B := by
  have hvlog : 0 < |Real.log (w v)| := by
    exact abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one (Units.pos_at_place v w) hv)
  have hB : 1 < B :=
    (Real.log_pos_iff hBpos.le).mp (lt_of_le_of_lt (abs_nonneg _) hvbound)
  have hvpos : 0 < w v := Units.pos_at_place v w
  by_cases h : 1 < w v
  · obtain ⟨ε, hε⟩ := w.exists_torsion_mul_embedding_eq_abs hw v
    refine ⟨ε, v, Or.inl rfl, ?_, ?_⟩
    · rwa [hε]
    · rw [hε]
      apply (Real.log_lt_log_iff hvpos (zero_lt_one.trans hB)).mp
      exact (abs_of_pos (Real.log_pos h) ▸ hvbound)
  · have hlt : w v < 1 := by
      have hne : w v ≠ 1 := by
        intro heq
        simp [heq] at hvlog
      exact lt_of_le_of_ne (le_of_not_gt h) hne
    have hwInv : w (v⁻¹) = (w v)⁻¹ := by simp
    have hinv : 1 < w (v⁻¹) := by
      rw [hwInv]
      exact (one_lt_inv₀ hvpos).mpr hlt
    have hlogInv : Real.log (w (v⁻¹)) = -Real.log (w v) := by
      rw [hwInv, Real.log_inv]
    obtain ⟨ε, hε⟩ := w.exists_torsion_mul_embedding_eq_abs hw (v⁻¹)
    refine ⟨ε, v⁻¹, Or.inr rfl, ?_, ?_⟩
    · rw [hε]
      simpa using hinv
    · rw [hε]
      apply (Real.log_lt_log_iff (Units.pos_at_place (v⁻¹) w)
        (zero_lt_one.trans hB)).mp
      simpa [hlogInv, abs_of_neg (Real.log_neg hvpos hlt)] using hvbound

open scoped Classical in
/-- At unit rank one, a unit expanding at a real place generates the units modulo torsion if
and only if no unit has real image strictly between `1` and `w u`, the absolute value of the
generator's real embedding. The equivalence includes
the torsion sign and inversion needed to pass from the intrinsic logarithmic criterion to this
one-sided interval. -/
theorem generates_mod_torsion_iff_no_unit_between_real (hr : rank K = 1)
    (u : (𝓞 K)ˣ) (w : InfinitePlace K) (hw : w.IsReal) (hu : 1 < w u) :
    Subgroup.closure {u} ⊔ torsion K = ⊤ ↔
      ¬ ∃ v : (𝓞 K)ˣ,
        1 < embedding_of_isReal hw (v : K) ∧
          embedding_of_isReal hw (v : K) < w u := by
  have hut : u ∉ torsion K := by
    intro h
    exact (ne_of_gt hu) ((mem_torsion K).mp h w)
  rw [generates_mod_torsion_iff_no_smaller_logEmbedding hr u hut]
  constructor
  · intro h ⟨v, hvlo, hvhi⟩
    have hvpos : 0 < embedding_of_isReal hw (v : K) := zero_lt_one.trans hvlo
    have hvw : w v = embedding_of_isReal hw (v : K) := by
      rw [← norm_embedding_of_isReal hw (v : K), Real.norm_eq_abs,
        abs_of_pos hvpos]
    have hvlog : 0 < Real.log (w v) := by
      rw [hvw]
      exact Real.log_pos hvlo
    have hv₀ : 0 < ‖logEmbedding K (Additive.ofMul v)‖ := by
      rw [norm_logEmbedding_eq_mult_abs_log hr v w, abs_of_pos hvlog]
      have hm : (0 : ℝ) < w.mult := by
        exact_mod_cast (NumberField.InfinitePlace.mult_pos (w := w))
      exact mul_pos hm hvlog
    have hv₁ : ‖logEmbedding K (Additive.ofMul v)‖ <
        ‖logEmbedding K (Additive.ofMul u)‖ :=
      (logEmbedding_norm_lt_iff_at_place hr u v w hu).mpr <| by
        rw [abs_of_pos hvlog, hvw]
        exact Real.log_lt_log hvpos hvhi
    exact h ⟨v, hv₀, hv₁⟩
  · intro h ⟨v, hv₀, hv₁⟩
    obtain ⟨ε, δ, _, hδlo, hδhi⟩ :=
      exists_normalized_unit_between (w u) v w hw (zero_lt_one.trans hu) (by
        intro heq
        have hz : ‖logEmbedding K (Additive.ofMul v)‖ = 0 := by
          rw [norm_logEmbedding_eq_mult_abs_log hr v w, heq]
          simp
        exact (ne_of_gt hv₀) hz)
        ((logEmbedding_norm_lt_iff_at_place hr u v w hu).mp hv₁)
    exact h ⟨ε.1 * δ, hδlo, hδhi⟩

end TauCeti.NumberField.Units
