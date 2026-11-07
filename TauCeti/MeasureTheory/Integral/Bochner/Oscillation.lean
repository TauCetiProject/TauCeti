/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Oscillation control from small integrals

Let `f : ℝ → E` be a function into a normed space, `S` a subset of an interval `(a, b)`, and `G`
an integrable function on `(a, b)`. Suppose that on every subinterval `(α, β)` some point `s'` of
`S ∩ (α, β)` has `‖f s - f s'‖² ≤ ∫_{(α, β)} G` for all `s ∈ S ∩ (α, β)`. Since the integral of
`G` over a short interval is small, `S` is dense in `[a, b]` and the oscillation of `f` on `S`
near every point of `[a, b]` tends to zero. Consequently `f` has a limit along `S` at each point
of `[a, b]`, and extends continuously from `S` to `[a, b]`. This is the step that produces a
continuous representative of a function known only almost everywhere, for example for the
time-continuity of functions in a Gelfand triple.

## Main results

* `TauCeti.exists_pos_setIntegral_Ioo_lt`: the integral of an integrable function over a short
  interval is arbitrarily small.
* `TauCeti.dense_and_dist_lt_of_oscillation`: the density of `S` and the vanishing oscillation of
  `f` on `S`.
-/

public section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace TauCeti

/-- The integral of a function integrable on `(a, b)` over `(a, b) ∩ (x - δ, x + δ)` is smaller than
any given positive bound once `δ` is small enough. -/
theorem exists_pos_setIntegral_Ioo_lt {a b : ℝ} {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a b)) (x : ℝ)
    {η : ℝ} (hη : 0 < η) : ∃ δ > 0, ∫ r in Ioo ((x - δ) ⊔ a) ((x + δ) ⊓ b), g r < η := by
  have hT : Tendsto (fun δ ↦ ∫ r in Ioo (x - δ) (x + δ), g r ∂volume.restrict (Ioo a b)) (𝓝 0)
      (𝓝 0) := by
    refine Integrable.tendsto_setIntegral_nhds_zero hg ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun δ ↦ ENNReal.ofReal (2 * δ)) ?_ (fun _ ↦ zero_le) fun δ ↦ ?_
    · have hc : Continuous fun δ : ℝ ↦ ENNReal.ofReal (2 * δ) :=
        ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
      simpa using hc.tendsto 0
    · refine (Measure.restrict_apply_le _ _).trans_eq ?_
      dsimp only
      rw [Real.volume_Ioo]
      ring_nf
  obtain ⟨δ, hδ, hδη⟩ := Metric.tendsto_nhds_nhds.1 hT η hη
  refine ⟨δ / 2, by positivity, ?_⟩
  have h := @hδη (δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
  rw [Real.dist_eq, sub_zero, Measure.restrict_restrict measurableSet_Ioo, Ioo_inter_Ioo] at h
  exact (le_abs_self _).trans_lt h

/-- **Oscillation control along a set.** Let `a < b`, let `S ⊆ (a, b)`, and suppose that on every
subinterval `(α, β)` with `a ≤ α < β ≤ b` some `s' ∈ S ∩ (α, β)` satisfies
`‖f s - f s'‖² ≤ ∫_{(α, β)} G` for all `s ∈ S ∩ (α, β)`, where `G` is integrable on `(a, b)`. Then
`S` is dense in `[a, b]`, and for every `x ∈ [a, b]` the oscillation of `f` on `S` near `x` tends
to zero. -/
theorem dense_and_dist_lt_of_oscillation {E : Type*} [NormedAddCommGroup E] {a b : ℝ} {f : ℝ → E}
    {S : Set ℝ} {G : ℝ → ℝ} (hab : a < b) (hS : S ⊆ Ioo a b) (hG : IntegrableOn G (Ioo a b))
    (hosc : ∀ α β : ℝ, a ≤ α → α < β → β ≤ b → ∃ s' ∈ S ∩ Ioo α β,
      ∀ s ∈ S ∩ Ioo α β, ‖f s - f s'‖ ^ 2 ≤ ∫ r in Ioo α β, G r) :
    Icc a b ⊆ closure S ∧ ∀ x ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ S, ∀ r ∈ S,
      dist s x < δ → dist r x < δ → dist (f s) (f r) < ε := by
  refine ⟨?_, ?_⟩
  · intro x hx
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    have hαβ : (x - ε) ⊔ a < (x + ε) ⊓ b :=
      sup_lt_iff.2 ⟨lt_inf_iff.2 ⟨by linarith, by linarith [hx.2]⟩,
        lt_inf_iff.2 ⟨by linarith [hx.1], hab⟩⟩
    obtain ⟨s', ⟨hs'S, hs'K⟩, -⟩ := hosc _ _ le_sup_right hαβ inf_le_right
    rw [← Ioo_inter_Ioo] at hs'K
    refine ⟨s', hs'S, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs'K.1.1, hs'K.1.2]
  · intro x hx ε hε
    obtain ⟨δ, hδ, hsm⟩ := exists_pos_setIntegral_Ioo_lt hG x
      (η := (ε / 2) ^ 2) (by positivity)
    have hαβ : (x - δ) ⊔ a < (x + δ) ⊓ b :=
      sup_lt_iff.2 ⟨lt_inf_iff.2 ⟨by linarith, by linarith [hx.2]⟩,
        lt_inf_iff.2 ⟨by linarith [hx.1], hab⟩⟩
    obtain ⟨s', hs'K, hs'⟩ := hosc _ _ le_sup_right hαβ inf_le_right
    have hclose (t : ℝ) (ht : t ∈ S) (hd : dist t x < δ) : dist (f t) (f s') < ε / 2 := by
      rw [Real.dist_eq, abs_lt] at hd
      have htK : t ∈ S ∩ Ioo ((x - δ) ⊔ a) ((x + δ) ⊓ b) :=
        ⟨ht, by rw [← Ioo_inter_Ioo]; exact ⟨⟨by linarith, by linarith⟩, hS ht⟩⟩
      rw [dist_eq_norm]
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) ((hs' t htK).trans_lt hsm)
    refine ⟨δ, hδ, fun s hs r hr hsd hrd ↦ ?_⟩
    calc dist (f s) (f r) ≤ dist (f s) (f s') + dist (f r) (f s') :=
          dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hclose s hs hsd) (hclose r hr hrd)
      _ = ε := add_halves ε

end TauCeti
