/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Order.IntermediateValue

/-!
# Exit times of a curve from small balls around a crossed point

For a continuous curve `γ : ℝ → E` starting at `γ t₀` within distance `ε` of `s` (for instance
`γ t₀ = s` and `0 ≤ ε`), with distance `ε` reached at the window endpoint, the **first exit
time at radius `ε`** on the right is the first parameter `t ≥ t₀` in `[t₀, t₀ + δ]` with
`‖γ t - s‖ = ε`; symmetrically on the left. This
file constructs the exit times as `sInf`/`sSup` of the closed set of outside-the-ball times
and establishes the API the principal-value excision consumes: the exit time lies in the window,
sits at exact distance `ε` (for small `ε`), and tends to `t₀` one-sidedly
as `ε → 0⁺`, and eventually has exact radius — the `t_eps` hypotheses of
`Contour.antiderivative_diff_across_crossing_tendsto_zero`.

## Main definitions

* `Contour.firstExitTimeRight γ t₀ δ s ε` — `sInf {t ∈ [t₀, t₀+δ] | ε ≤ ‖γ t - s‖}`.
* `Contour.firstExitTimeLeft γ t₀ δ s ε` — `sSup {t ∈ [t₀-δ, t₀] | ε ≤ ‖γ t - s‖}` (the latest
  outside-the-ball time before `t₀`, i.e. the first exit when moving left from `t₀`).

## Main results

* `Contour.firstExitTimeRight_mem_Icc` / `Left` — the exit time lies in the window.
* `Contour.norm_sub_firstExitTimeRight_eq` / `Left` — the exit time is at exact distance `ε`.
* `Contour.tendsto_firstExitTimeRight` / `Left` — the exit time tends to `t₀` one-sidedly as
  `ε → 0⁺`, provided `γ` leaves `s` on the window.
* `Contour.eventually_norm_sub_firstExitTimeRight_eq` / `Left` — eventual exact radius along
  `𝓝[>] 0`.

The exit-time definitions and window bounds require only subtraction and a norm. The fixed-radius
estimates hold in a seminormed additive commutative group and assume only that `γ t₀` lies in the
closed (for the strict bounds, open) ball of radius `ε` about `s`.
The results as `ε → 0⁺` are stated in a normed additive commutative group: their hypothesis that
`γ` leaves `s` must give a positive distance from `s`, which a seminorm does not guarantee.

## Provenance

Migrated from `firstExitTimeRight`/`firstExitTimeLeft` and their API in `ExitTime.lean` of the
AINTLIB `LeanModularForms` development, restated for a curve into a seminormed group. See
N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

section Norm

variable {E : Type*} [Sub E] [Norm E]

/-- **First exit time at radius `ε` (right side)**: the `sInf` of the times
`t ∈ [t₀, t₀ + δ]` with `ε ≤ ‖γ t - s‖`; the junk value is `sInf ∅` when the curve never
reaches distance `ε` in the window. -/
def firstExitTimeRight (γ : ℝ → E) (t₀ δ : ℝ) (s : E) (ε : ℝ) : ℝ :=
  sInf {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}

/-- The set defining `firstExitTimeRight` contains the window endpoint when the curve is far
enough there. -/
private theorem right_endpoint_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ + δ) - s‖) :
    (t₀ + δ) ∈ {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖} :=
  ⟨⟨by linarith, le_rfl⟩, h_far⟩

/-- The set defining `firstExitTimeRight` is bounded below by `t₀`. -/
private theorem right_set_bddBelow (γ : ℝ → E) (t₀ δ ε : ℝ) (s : E) :
    ∀ t ∈ {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}, t₀ ≤ t :=
  fun _ ⟨hmem, _⟩ => hmem.1

/-- **The right exit time lies in the window** `[t₀, t₀ + δ]`. -/
theorem firstExitTimeRight_mem_Icc {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    firstExitTimeRight γ t₀ δ s ε ∈ Icc t₀ (t₀ + δ) :=
  ⟨le_csInf ⟨t₀ + δ, right_endpoint_mem hδ hε_le⟩ (right_set_bddBelow γ t₀ δ ε s),
    csInf_le ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩ (right_endpoint_mem hδ hε_le)⟩

/-- **Upper bound through any witness (right)**: the right exit time is at most any window
time whose displacement norm is at least `ε`. -/
theorem firstExitTimeRight_le_of_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc t₀ (t₀ + δ)) (h_far : ε ≤ ‖γ t₁ - s‖) :
    firstExitTimeRight γ t₀ δ s ε ≤ t₁ :=
  csInf_le ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩ ⟨ht₁, h_far⟩

/-- **First exit time at radius `ε` (left side)**: the `sSup` of the times `t ∈ [t₀ - δ, t₀]`
with `ε ≤ ‖γ t - s‖` — the latest outside-the-ball time before `t₀`, which is the first exit
when moving left from `t₀`. The junk value is `sSup ∅` when the defining set is empty. -/
def firstExitTimeLeft (γ : ℝ → E) (t₀ δ : ℝ) (s : E) (ε : ℝ) : ℝ :=
  sSup {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}

/-- The set defining `firstExitTimeLeft` contains the window endpoint when the curve is far
enough there. -/
private theorem left_endpoint_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ - δ) - s‖) :
    (t₀ - δ) ∈ {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖} :=
  ⟨⟨le_rfl, by linarith⟩, h_far⟩

/-- The set defining `firstExitTimeLeft` is bounded above by `t₀`. -/
private theorem left_set_bddAbove (γ : ℝ → E) (t₀ δ ε : ℝ) (s : E) :
    ∀ t ∈ {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}, t ≤ t₀ :=
  fun _ ⟨hmem, _⟩ => hmem.2

/-- **The left exit time lies in the window** `[t₀ - δ, t₀]`. -/
theorem firstExitTimeLeft_mem_Icc {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    firstExitTimeLeft γ t₀ δ s ε ∈ Icc (t₀ - δ) t₀ :=
  ⟨le_csSup ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩ (left_endpoint_mem hδ hε_le),
    csSup_le ⟨t₀ - δ, left_endpoint_mem hδ hε_le⟩ (left_set_bddAbove γ t₀ δ ε s)⟩

/-- **Lower bound through any witness (left)**: the left exit time is at least any window
time whose displacement norm is at least `ε`. -/
theorem le_firstExitTimeLeft_of_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (t₀ - δ) t₀) (h_far : ε ≤ ‖γ t₁ - s‖) :
    t₁ ≤ firstExitTimeLeft γ t₀ δ s ε :=
  le_csSup ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩ ⟨ht₁, h_far⟩

end Norm

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Radius lower bound at the right exit time**: the `sInf` of the closed set of
outside-the-ball times is itself outside the open ball. -/
theorem le_norm_sub_firstExitTimeRight {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ε ≤ ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ :=
  (((hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici).csInf_mem
    ⟨t₀ + δ, right_endpoint_mem hδ hε_le⟩
    ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩).2

/-- **The right exit time is strictly after `t₀`** when the curve starts strictly inside the
ball of radius `ε` about `s`. -/
theorem lt_firstExitTimeRight {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_inside : ‖γ t₀ - s‖ < ε) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    t₀ < firstExitTimeRight γ t₀ δ s ε :=
  (firstExitTimeRight_mem_Icc hδ hε_le).1.lt_of_ne fun h =>
    (le_norm_sub_firstExitTimeRight hδ hγ_cont hε_le).not_gt (by rwa [← h])

/-- **Exact radius at the right exit time**: for `‖γ t₀ - s‖ ≤ ε ≤ ‖γ (t₀ + δ) - s‖`, the curve
is at distance exactly `ε` at `firstExitTimeRight γ t₀ δ s ε`. -/
theorem norm_sub_firstExitTimeRight_eq {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_inside : ‖γ t₀ - s‖ ≤ ε) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ = ε := by
  refine le_antisymm ?_ (le_norm_sub_firstExitTimeRight hδ hγ_cont hε_le)
  by_contra! h
  have hτ := firstExitTimeRight_mem_Icc hδ hε_le
  have hcont : ContinuousOn (fun t => ‖γ t - s‖)
      (Icc t₀ (firstExitTimeRight γ t₀ δ s ε)) :=
    ((hγ_cont.mono (Icc_subset_Icc_right hτ.2)).sub continuousOn_const).norm
  obtain ⟨t, ht, hnorm⟩ := intermediate_value_Ico hτ.1 hcont ⟨h_inside, h⟩
  have hle := firstExitTimeRight_le_of_mem ⟨ht.1, ht.2.le.trans hτ.2⟩ hnorm.ge
  exact hle.not_gt ht.2

/-- **Radius lower bound at the left exit time**: the `sSup` of the closed set of
outside-the-ball times is itself outside the open ball. -/
theorem le_norm_sub_firstExitTimeLeft {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀)) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ε ≤ ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ :=
  (((hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici).csSup_mem
    ⟨t₀ - δ, left_endpoint_mem hδ hε_le⟩
    ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩).2

/-- **The left exit time is strictly before `t₀`**: the counterpart of
`lt_firstExitTimeRight`. -/
theorem firstExitTimeLeft_lt {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_inside : ‖γ t₀ - s‖ < ε) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    firstExitTimeLeft γ t₀ δ s ε < t₀ :=
  (firstExitTimeLeft_mem_Icc hδ hε_le).2.lt_of_ne fun h =>
    (le_norm_sub_firstExitTimeLeft hδ hγ_cont hε_le).not_gt (by rwa [h])

/-- **Exact radius at the left exit time**: the counterpart of
`norm_sub_firstExitTimeRight_eq`. -/
theorem norm_sub_firstExitTimeLeft_eq {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_inside : ‖γ t₀ - s‖ ≤ ε) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ = ε := by
  refine le_antisymm ?_ (le_norm_sub_firstExitTimeLeft hδ hγ_cont hε_le)
  by_contra! h
  have hτ := firstExitTimeLeft_mem_Icc hδ hε_le
  have hcont : ContinuousOn (fun t => ‖γ t - s‖)
      (Icc (firstExitTimeLeft γ t₀ δ s ε) t₀) :=
    ((hγ_cont.mono (Icc_subset_Icc_left hτ.1)).sub continuousOn_const).norm
  obtain ⟨t, ht, hnorm⟩ := intermediate_value_Ioc' hτ.2 hcont ⟨h_inside, h⟩
  have hle := le_firstExitTimeLeft_of_mem ⟨hτ.1.trans ht.1.le, ht.2⟩ hnorm.ge
  exact hle.not_gt ht.1

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- **The right exit time tends to `t₀` from above as `ε → 0⁺`**, provided `γ` leaves `s` on
`(t₀, t₀ + δ]`. -/
theorem tendsto_firstExitTimeRight {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ioc t₀ (t₀ + δ), γ t ≠ s) :
    Tendsto (fun ε => firstExitTimeRight γ t₀ δ s ε) (𝓝[>] 0) (𝓝[>] t₀) := by
  refine (nhdsGT_basis t₀).tendsto_right_iff.2 fun b hb => ?_
  obtain ⟨t₁, ht₀₁, ht₁b⟩ := exists_between (lt_min hb (lt_add_of_pos_right t₀ hδ))
  have ht₁ : t₁ ∈ Ioc t₀ (t₀ + δ) := ⟨ht₀₁, ht₁b.le.trans (min_le_right _ _)⟩
  filter_upwards [Ioo_mem_nhdsGT (norm_sub_pos_iff.2 (h_leave t₁ ht₁)),
    Ioo_mem_nhdsGT (norm_sub_pos_iff.2 (h_leave (t₀ + δ) ⟨by linarith, le_rfl⟩))] with ε h₁ hδε
  exact ⟨lt_firstExitTimeRight hδ.le hγ_cont (by simpa [h_s] using h₁.1) hδε.2.le,
    (firstExitTimeRight_le_of_mem (Ioc_subset_Icc_self ht₁) h₁.2.le).trans_lt
      (ht₁b.trans_le (min_le_left _ _))⟩

/-- **The left exit time tends to `t₀` from below as `ε → 0⁺`**: the counterpart of
`tendsto_firstExitTimeRight`. -/
theorem tendsto_firstExitTimeLeft {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ico (t₀ - δ) t₀, γ t ≠ s) :
    Tendsto (fun ε => firstExitTimeLeft γ t₀ δ s ε) (𝓝[>] 0) (𝓝[<] t₀) := by
  refine (nhdsLT_basis t₀).tendsto_right_iff.2 fun a ha => ?_
  obtain ⟨t₁, hat₁, ht₁₀⟩ := exists_between (max_lt ha (sub_lt_self t₀ hδ))
  have ht₁ : t₁ ∈ Ico (t₀ - δ) t₀ := ⟨(le_max_right _ _).trans hat₁.le, ht₁₀⟩
  filter_upwards [Ioo_mem_nhdsGT (norm_sub_pos_iff.2 (h_leave t₁ ht₁)),
    Ioo_mem_nhdsGT (norm_sub_pos_iff.2 (h_leave (t₀ - δ) ⟨le_rfl, by linarith⟩))] with ε h₁ hδε
  exact ⟨((le_max_left _ _).trans_lt hat₁).trans_le
      (le_firstExitTimeLeft_of_mem (Ico_subset_Icc_self ht₁) h₁.2.le),
    firstExitTimeLeft_lt hδ.le hγ_cont (by simpa [h_s] using h₁.1) hδε.2.le⟩

/-- **Eventual exact radius (right)**: for all sufficiently small `ε > 0`, the right exit time
is at distance exactly `ε`, provided the window endpoint differs from `s`. This is the
radius hypothesis of
`Contour.antiderivative_diff_across_crossing_tendsto_zero`. -/
theorem eventually_norm_sub_firstExitTimeRight_eq {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (h_leave : γ (t₀ + δ) ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ = ε := by
  filter_upwards [Ioo_mem_nhdsGT (norm_sub_pos_iff.2 h_leave)] with ε hε
  exact norm_sub_firstExitTimeRight_eq hδ hγ_cont (by simpa [h_s] using hε.1.le) hε.2.le

/-- **Eventual exact radius (left)**: the counterpart of
`eventually_norm_sub_firstExitTimeRight_eq`, assuming only that the left endpoint
differs from `s`. -/
theorem eventually_norm_sub_firstExitTimeLeft_eq {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (h_leave : γ (t₀ - δ) ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ = ε := by
  filter_upwards [Ioo_mem_nhdsGT (norm_sub_pos_iff.2 h_leave)] with ε hε
  exact norm_sub_firstExitTimeLeft_eq hδ hγ_cont (by simpa [h_s] using hε.1.le) hε.2.le

end Normed

end TauCeti.Contour

end
