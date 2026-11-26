/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Infinite sums in `Lᵖ`: pointwise behaviour and absolutely convergent series in `L^r`

If a family `u` in `Lᵖ` has sum `v` in the `Lᵖ` norm, then `‖v x‖ₑ ≤ ∑' i, ‖u i x‖ₑ` at almost
every point. Unlike `MeasureTheory.Lp.hasSum_coeFn_tsum`, this needs neither a countable index
type nor summability of the norms `‖u i‖`: it only uses that some sequence of finite partial sums
converges to `v` almost everywhere. A typical use is a sum of functions with disjoint supports in
`L²`, whose norms are square-summable but need not be summable.

Conversely, a series `∑ᵢ xᵢ` of `Lᵖ` functions whose `L^r` seminorms are summable has a sum `v` in
the Banach space `L^r`, even though the `xᵢ` are a priori elements of a different space `Lᵖ`, and
the tails of the series obey `‖v - ∑_{i ∈ s} xᵢ‖_{L^r} ≤ ∑_{i ∉ s} ‖xᵢ‖_{L^r}`.

## Main declarations

* `MeasureTheory.Lp.ae_enorm_le_tsum_enorm_of_hasSum`: the pointwise bound.
* `MeasureTheory.Lp.ae_eq_of_hasSum_of_ae_hasSum`: for a countable family, the sum in `Lᵖ`
  agrees almost everywhere with the pointwise sum, wherever the latter exists.
* `MeasureTheory.exists_eLpNorm_sub_sum_le_tsum_compl`: a series of `Lᵖ` functions whose `L^r`
  seminorms are summable has a sum in `L^r`, with the tail bound
  `‖v - ∑_{i ∈ s} xᵢ‖_{L^r} ≤ ∑_{i ∉ s} ‖xᵢ‖_{L^r}`.
-/

public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

namespace Lp

variable {α E κ : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If a family `u` in `Lᵖ` has sum `v`, then at almost every point the extended norm of `v` is at
most the sum of the extended norms of the `u i`. -/
theorem ae_enorm_le_tsum_enorm_of_hasSum {u : κ → Lp E p μ} {v : Lp E p μ} (h : HasSum u v) :
    ∀ᵐ x ∂μ, ‖v x‖ₑ ≤ ∑' i, ‖u i x‖ₑ := by
  -- A summable family in the metric space `Lᵖ` has countable support, so we may sum over it.
  have := h.summable.countable_support.to_subtype
  obtain ⟨S, -, hS⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hasSum_subtype_support.2 h)).exists_seq_tendsto_ae'
  have hsum : ∀ᵐ x ∂μ, ∀ n, (⇑(∑ i ∈ S n, u i) : α → E) x = ∑ i ∈ S n, u i x :=
    ae_all_iff.2 fun n => coeFn_fun_finsetSum (S n) _
  filter_upwards [hS, hsum] with x hx hxsum
  refine le_of_tendsto' (continuous_eNorm.tendsto _ |>.comp hx) fun n => ?_
  simp only [Function.comp_apply, hxsum n]
  exact (eNorm_sum_le _ _).trans <| (_root_.sum_le_tsum _).trans <|
    tsum_comp_le_tsum_of_injective Subtype.val_injective fun i => ‖u i x‖ₑ

/-- If a countable family `u` in `Lᵖ` has sum `v`, and at almost every point the values `u i x`
have sum `g x`, then `v = g` almost everywhere: the `Lᵖ` sum agrees with the pointwise sum. -/
theorem ae_eq_of_hasSum_of_ae_hasSum [Countable κ] {u : κ → Lp E p μ} {v : Lp E p μ}
    {g : α → E} (h : HasSum u v) (hg : ∀ᵐ x ∂μ, HasSum (fun i ↦ u i x) (g x)) :
    v =ᵐ[μ] g := by
  obtain ⟨S, hS, hSv⟩ := (tendstoInMeasure_of_tendsto_Lp h).exists_seq_tendsto_ae'
  have hsum : ∀ᵐ x ∂μ, ∀ n, (⇑(∑ i ∈ S n, u i) : α → E) x = ∑ i ∈ S n, u i x :=
    ae_all_iff.2 fun n => coeFn_fun_finsetSum (S n) _
  filter_upwards [hSv, hsum, hg] with x hx hxsum hgx
  simp only [hxsum] at hx
  exact tendsto_nhds_unique hx (hgx.comp hS)

end Lp

variable {α ι F : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]
  {p r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- **Absolutely convergent series in `L^r`.** If `xᵢ ∈ Lᵖ(μ)` have summable `L^r` seminorms, then
`∑ᵢ xᵢ` has a sum `v` in `L^r(μ)`: for every finite set `s` of indices,
`‖v - ∑_{i ∈ s} xᵢ‖_{L^r} ≤ ∑_{i ∉ s} ‖xᵢ‖_{L^r}`, and
`‖∑_{i ∈ t} xᵢ - ∑_{i ∈ s} xᵢ‖_{L^r} → ‖v - ∑_{i ∈ s} xᵢ‖_{L^r}` as the finite set `t` grows. -/
theorem exists_eLpNorm_sub_sum_le_tsum_compl [CompleteSpace F] {x : ι → Lp F p μ}
    (hx : ∑' i, eLpNorm (x i) r μ ≠ ∞) :
    ∃ v : Lp F r μ,
      (∀ s : Finset ι,
        eLpNorm (⇑v - ⇑(∑ i ∈ s, x i)) r μ ≤ ∑' i : ↥(s : Set ι)ᶜ, eLpNorm (x i) r μ) ∧
      ∀ s : Finset ι, Tendsto (fun t : Finset ι ↦ eLpNorm (⇑(∑ i ∈ t, x i) - ⇑(∑ i ∈ s, x i)) r μ)
        atTop (𝓝 (eLpNorm (⇑v - ⇑(∑ i ∈ s, x i)) r μ)) := by
  have hmem (i : ι) : MemLp (x i) r μ :=
    memLp_iff.2 ((le_tsum _ i).trans_lt hx.lt_top)
  set y : ι → Lp F r μ := fun i ↦ (hmem i).toLp _
  have hy (i : ι) : ‖y i‖ₑ = eLpNorm (x i) r μ := Lp.eNorm_toLp _
  have hsum : Summable y :=
    .of_norm (tsum_eNorm_ne_top_iff_summable_norm.1 (by simpa only [hy] using hx))
  -- A partial sum of the `xᵢ` and the same partial sum of the `yᵢ` are the same function.
  have hcoe (t : Finset ι) : ⇑(∑ i ∈ t, x i) =ᵐ[μ] ⇑(∑ i ∈ t, y i) := by
    filter_upwards [Lp.coeFn_finsetSum t x, Lp.coeFn_finsetSum t y,
      t.eventually_all.2 fun i _ ↦ (hmem i).coeFn_toLp] with a h₁ h₂ h₃
    simp only [h₁, h₂, Finset.sum_apply, y]
    exact Finset.sum_congr rfl fun i hi ↦ (h₃ i hi).symm
  have hnorm (v : Lp F r μ) (s : Finset ι) :
      eLpNorm (⇑v - ⇑(∑ i ∈ s, x i)) r μ = ‖v - ∑ i ∈ s, y i‖ₑ := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae
      (((EventuallyEq.refl _ (⇑v)).sub (hcoe s)).trans (Lp.coeFn_sub _ _).symm)
  refine ⟨∑' i, y i, fun s ↦ ?_, fun s ↦ ?_⟩
  · rw [hnorm _ s, ← hsum.sum_add_tsum_compl, add_sub_cancel_left]
    refine eNorm_tsum_le_tsum_eNorm.trans_eq ?_
    simp only [hy]
  · have hlim := ((hsum.hasSum.sub_const (∑ i ∈ s, y i)).eNorm)
    rw [← hnorm _ s] at hlim
    refine hlim.congr fun t ↦ ?_
    rw [eLpNorm_congr_ae ((hcoe t).sub (hcoe s) |>.trans (Lp.coeFn_sub _ _).symm), ← Lp.eNorm_def]

end MeasureTheory
