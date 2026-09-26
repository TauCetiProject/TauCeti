/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.GeneratorCriterion

/-!
# Normalizing a competing unit at a real place

At a real infinite place, an absolute value forgets the sign of an embedding. To turn the
rank-one minimality criterion for logarithmic embeddings into a search among real roots in an
interval, invert a unit if its absolute value is below one and multiply it by a torsion unit
`1` or `-1` to make its real embedding positive. The resulting unit has a positive real image
strictly between `1` and the proposed generator's image.

The normalization is used before enumerating possible minimal polynomials: it accounts for
both the inversion and the sign that are invisible in the absolute-value criterion.

## Main results

* `exists_normalized_unit_between`: every smaller non-torsion logarithmic competitor yields a
  unit whose real embedding lies in the search interval.
* `generates_mod_torsion_iff_no_unit_between_real`: at rank one, a unit expanding at a real
  place generates modulo torsion exactly when that interval contains no unit.
-/

public section
noncomputable section

open NumberField NumberField.Units NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- At a real place, multiply a unit by a torsion unit of order at most two so that its real
embedding is its (positive) absolute value. -/
theorem exists_torsion_mul_embedding_eq_abs (w : InfinitePlace K) (hw : w.IsReal)
    (v : (𝓞 K)ˣ) :
    ∃ ε : torsion K,
      embedding_of_isReal hw ((ε.1 * v : (𝓞 K)ˣ) : K) = w v := by
  let φ := embedding_of_isReal hw
  have hv : |φ (v : K)| = w v := by
    simpa [Real.norm_eq_abs] using (norm_embedding_of_isReal hw (v : K))
  by_cases h : 0 ≤ φ (v : K)
  · refine ⟨1, ?_⟩
    simpa [φ, abs_of_nonneg h] using hv
  · refine ⟨⟨-1, neg_one_mem_torsion⟩, ?_⟩
    have hneg : φ (v : K) < 0 := lt_of_not_ge h
    simpa [φ, abs_of_neg hneg] using hv

open scoped Classical in
/-- A unit with strictly smaller nonzero logarithmic embedding than `u` can be inverted and
multiplied by a torsion sign so that, at a real place where `u` expands, it has real image in
the open interval from `1` to the absolute value of `u`. -/
theorem exists_normalized_unit_between (hr : rank K = 1) (u v : (𝓞 K)ˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (hu : 1 < w u)
    (hv₀ : 0 < ‖logEmbedding K (Additive.ofMul v)‖)
    (hv₁ : ‖logEmbedding K (Additive.ofMul v)‖ <
      ‖logEmbedding K (Additive.ofMul u)‖) :
    ∃ (ε : torsion K) (δ : (𝓞 K)ˣ),
      (δ = v ∨ δ = v⁻¹) ∧
      1 < embedding_of_isReal hw ((ε.1 * δ : (𝓞 K)ˣ) : K) ∧
      embedding_of_isReal hw ((ε.1 * δ : (𝓞 K)ˣ) : K) < w u := by
  have hvlog : 0 < |Real.log (w v)| := by
    rw [norm_logEmbedding_eq_mult_abs_log hr v w] at hv₀
    have hm : (0 : ℝ) < w.mult := by
      exact_mod_cast (NumberField.InfinitePlace.mult_pos (w := w))
    exact pos_of_mul_pos_right hv₀ hm.le
  have hvbound : |Real.log (w v)| < Real.log (w u) :=
    (logEmbedding_norm_lt_iff_at_place hr u v w hu).mp hv₁
  have hvpos : 0 < w v := Units.pos_at_place v w
  by_cases h : 1 < w v
  · obtain ⟨ε, hε⟩ := exists_torsion_mul_embedding_eq_abs w hw v
    refine ⟨ε, v, Or.inl rfl, ?_, ?_⟩
    · rwa [hε]
    · rw [hε]
      apply (Real.log_lt_log_iff hvpos (Units.pos_at_place u w)).mp
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
    obtain ⟨ε, hε⟩ := exists_torsion_mul_embedding_eq_abs w hw (v⁻¹)
    refine ⟨ε, v⁻¹, Or.inr rfl, ?_, ?_⟩
    · rw [hε]
      simpa using hinv
    · rw [hε]
      apply (Real.log_lt_log_iff (Units.pos_at_place (v⁻¹) w)
        (Units.pos_at_place u w)).mp
      simpa [hlogInv, abs_of_neg (Real.log_neg hvpos hlt)] using hvbound

open scoped Classical in
/-- At unit rank one, a unit expanding at a real place generates the units modulo torsion if
and only if no unit has real image strictly between `1` and its image. The equivalence includes
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
      exists_normalized_unit_between hr u v w hw hu hv₀ hv₁
    exact h ⟨ε.1 * δ, hδlo, hδhi⟩

end TauCeti.NumberField.Units
