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

* `exists_torsion_mul_one_lt_embedding_of_isReal_and_log_eq_abs`: any unit with `w v ≠ 1` at a real
  place `w` can be inverted if necessary and multiplied by a torsion unit so that its real image
  exceeds `1` and has logarithm `|log (w v)|`.
* `exists_normalized_unit_between`: a unit detected by the chosen place, with sufficiently
  small logarithmic absolute value, yields a unit whose real embedding lies in the search interval.
* `exists_one_lt_embedding_of_isReal_and_regulator_eq_log`: at unit rank one and any real place `w`,
  there exists a unit with real image exceeding `1` whose logarithm equals `regulator K`.
* `generates_mod_torsion_iff_no_unit_between_real`: at rank one, a unit expanding at a real
  place generates modulo torsion exactly when that interval contains no unit.
-/

public section
noncomputable section

open NumberField NumberField.Units NumberField.InfinitePlace
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.NumberField.Units

omit [NumberField K] in
/-- Any unit `v` with `w v ≠ 1` at a real place `w` can be inverted if necessary and multiplied by
a torsion unit so that its real image exceeds `1` and has logarithm `|log (w v)|`. -/
theorem exists_torsion_mul_one_lt_embedding_of_isReal_and_log_eq_abs (v : (𝓞 K)ˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (hv : w v ≠ 1) :
    ∃ (ε : torsion K) (δ : (𝓞 K)ˣ),
      (δ = v ∨ δ = v⁻¹) ∧
      1 < embedding_of_isReal hw ((ε.val * δ : (𝓞 K)ˣ) : K) ∧
      Real.log (embedding_of_isReal hw ((ε.val * δ : (𝓞 K)ˣ) : K)) = |Real.log (w v)| := by
  have hvpos : 0 < w v := Units.pos_at_place v w
  rcases lt_trichotomy 1 (w v) with h | h | h
  · obtain ⟨ε, hε⟩ := w.exists_torsion_mul_embedding_eq_abs hw v
    exact ⟨ε, v, Or.inl rfl, hε.symm ▸ h, by rw [hε, abs_of_pos (Real.log_pos h)]⟩
  · exact absurd h.symm hv
  · have hwInv : w (v⁻¹ : (𝓞 K)ˣ) = (w v)⁻¹ := by simp
    have hinv : 1 < w (v⁻¹ : (𝓞 K)ˣ) := hwInv.symm ▸ (one_lt_inv₀ hvpos).mpr h
    obtain ⟨ε, hε⟩ := w.exists_torsion_mul_embedding_eq_abs hw v⁻¹
    refine ⟨ε, v⁻¹, Or.inr rfl, hε.symm ▸ hinv, ?_⟩
    rw [hε, hwInv, Real.log_inv, abs_of_neg (Real.log_neg hvpos h)]

omit [NumberField K] in
/-- A unit with `w v ≠ 1` whose logarithmic absolute value is below `log B` can be inverted and
multiplied by a torsion unit so that its real image lies in the open interval from `1` to `B`. -/
theorem exists_normalized_unit_between (B : ℝ) (v : (𝓞 K)ˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (hBpos : 0 < B)
    (hv : w v ≠ 1) (hvbound : |Real.log (w v)| < Real.log B) :
    ∃ (ε : torsion K) (δ : (𝓞 K)ˣ),
      (δ = v ∨ δ = v⁻¹) ∧
      1 < embedding_of_isReal hw ((ε.val * δ : (𝓞 K)ˣ) : K) ∧
      embedding_of_isReal hw ((ε.val * δ : (𝓞 K)ˣ) : K) < B := by
  obtain ⟨ε, δ, hδ, hgt, hlog⟩ :=
    exists_torsion_mul_one_lt_embedding_of_isReal_and_log_eq_abs v w hw hv
  exact ⟨ε, δ, hδ, hgt,
    (Real.log_lt_log_iff (zero_lt_one.trans hgt) hBpos).mp (hlog.trans_lt hvbound)⟩

/-- **Normalized fundamental unit in unit rank one.** At any real infinite place `w` of a number
field `K` of unit rank one, there exists a unit `u` whose real image exceeds `1` and whose
logarithm equals `regulator K`. -/
theorem exists_one_lt_embedding_of_isReal_and_regulator_eq_log (hr : rank K = 1)
    {w : InfinitePlace K} (hw : w.IsReal) :
    ∃ u : (𝓞 K)ˣ, 1 < embedding_of_isReal hw (u : K) ∧
      regulator K = Real.log (embedding_of_isReal hw (u : K)) := by
  obtain ⟨g, hg⟩ := exists_closure_sup_torsion_eq_top_of_rank_eq_one hr
  have hreg : regulator K = |Real.log (w g)| := by
    rw [regulator_eq_mult_abs_log_of_rank_eq_one hr g hg w, hw.mult_eq_one, Nat.cast_one, one_mul]
  have hg1 : w g ≠ 1 := fun h1 ↦ (regulator_pos K).ne' (by simp [hreg, h1])
  obtain ⟨ε, δ, -, hgt, hlog⟩ :=
    exists_torsion_mul_one_lt_embedding_of_isReal_and_log_eq_abs g w hw hg1
  exact ⟨ε.val * δ, hgt, hreg.trans hlog.symm⟩

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
    exact h ⟨ε.val * δ, hδlo, hδhi⟩

end TauCeti.NumberField.Units
