/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Embedding
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Sobolev
import TauCeti.Analysis.Sobolev.Embedding

/-!
# Higher-order subcritical embeddings on bounded convex domains

A first-order Sobolev–Poincaré gain can be iterated while retaining any prescribed target
Sobolev order. The embedding preserves the value almost everywhere and works for any additive
Haar measure.
-/

public section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal
open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {Ω : Opens E}
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- On a bounded convex open set, `k` subcritical reciprocal-exponent gains of size `t`
embed order `j + k` into order `j` at the improved exponent, preserving the value almost
everywhere. -/
-- Adapted from the exponent induction in `exists_lipschitzWkpW1pEmbedding` in
-- TauCeti/Analysis/Sobolev/LipschitzDomain/Wkp/Embedding.lean, retaining target order `j`.
theorem Convex.exists_wkp_value_ae_eq_of_inv_add_eq (hc : Convex ℝ (Ω : Set E))
    (hb : IsBounded (Ω : Set E)) (j : ℕ)
    {t : ℝ≥0∞} (ht : t < (finrank ℝ E : ℝ≥0∞)⁻¹) :
    ∀ (k : ℕ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], q ≠ ⊤ →
      q⁻¹ + k * t = p⁻¹ → ∀ u : Wkp μ Ω p (j + k),
        ∃ v : Wkp μ Ω q j,
          Wkp.value j v =ᵐ[μ.restrict (Ω : Set E)] Wkp.value (j + k) u
  | 0, p, q, _, _, _, h, u => by
    have hqp : q = p := by simpa using h
    subst p
    exact ⟨u, .rfl⟩
  | k + 1, p, q, _, _, hq, h, u => by
    obtain ⟨r, hr, hrinv⟩ := exists_inv_eq_inv_add_of_ne_top hq (k * t)
    have hre : r⁻¹ + t = p⁻¹ := by
      rw [hrinv, ← h]
      push_cast
      ring
    have hr₁ : Fact (1 ≤ r) := ⟨one_le_of_inv_add_eq_inv hre⟩
    have hpr : p ≤ (r.toNNReal : ℝ≥0∞) := by
      rw [ENNReal.coe_toNNReal hr, ← ENNReal.inv_le_inv, ← hre]
      exact le_self_add
    have ht₀ : t ≠ ⊤ := ht.ne_top
    have hri : r⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ((zero_lt_one.trans_le hr₁.out).ne')
    have hni : (finrank ℝ E : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
    have htr : t.toReal < (finrank ℝ E : ℝ)⁻¹ := by
      simpa only [ENNReal.toReal_inv, ENNReal.toReal_natCast] using
        (ENNReal.toReal_lt_toReal ht₀ hni).2 ht
    have hgain : p.toReal⁻¹ - r.toReal⁻¹ = t.toReal := by
      rw [← ENNReal.toReal_inv, ← hre, ENNReal.toReal_add hri ht₀,
        ENNReal.toReal_inv, add_sub_cancel_left]
    have hδ : p.toReal⁻¹ - (r.toNNReal : ℝ)⁻¹ < (finrank ℝ E : ℝ)⁻¹ := by
      simpa only [ENNReal.coe_toNNReal_eq_toReal, hgain] using htr
    have hm (z : W1p μ Ω p) : MemLp (W1p.value z) r (μ.restrict (Ω : Set E)) :=
      (ENNReal.coe_toNNReal hr) ▸ W1p.memLp_value_of_subcritical_gain_of_convex z hc hb hpr hδ
    obtain ⟨w, hw⟩ := Wkp.exists_value_ae_eq_of_memLp hm (j + k) u
    obtain ⟨v, hv⟩ := Convex.exists_wkp_value_ae_eq_of_inv_add_eq hc hb j ht k hq hrinv.symm w
    exact ⟨v, hv.trans hw⟩
