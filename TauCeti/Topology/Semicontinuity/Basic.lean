/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lower semicontinuity, sublevel minimization, and sequential characterizations

A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s`, for an arbitrary `G : Set X → β` with values in a
complete linear order, is lower semicontinuous (`TauCeti.lowerSemicontinuous_iSup_nhds`): a strict
lower bound witnessed by a neighbourhood of `x` is witnessed by the same set at every point of its
interior. Lower envelopes and lower and upper Γ-limits are of this form.

A lower semicontinuous subadditive function `A` with values in `ℝ≥0∞` and `A 0 = 0`, such as a
lower semicontinuous extended seminorm, satisfies the triangle inequality for convergent series:
`A (∑ f) ≤ ∑' b, A (f b)` (`LowerSemicontinuous.le_tsum_of_hasSum`). No continuity of `A` is needed,
because the bound on the partial sums passes to their limit through the closed sublevel set.

For constrained minimization on a set `s`:
* `IsMinOn.of_inter_preimage_Iic` transfers a minimum on a nonempty sublevel `s ∩ f ⁻¹' Iic b` to
  the whole set `s`, and `LowerSemicontinuousOn.exists_isMinOn_of_isCompact_inter_preimage_Iic`
  deduces attainment of the minimum from compactness of a single nonempty sublevel.
* `IsMinOn.csInf_eq` and `TauCeti.isMinOn_iff_eq_csInf` identify the minimum value on `s` with
  `sInf (f '' s)`, while `IsMinOn.setOf_eq_inter_preimage_Iic` and
  `LowerSemicontinuousOn.isClosed_setOf_isMinOn` realize the set of minimizers as a sublevel set.
* `LowerSemicontinuousOn.le_liminf_of_tendsto`, `LowerSemicontinuousOn.le_of_tendsto`, and
  `TauCeti.lowerSemicontinuousOn_iff_forall_seq_le_liminf` connect topological lower
  semicontinuity on `s` to sequential `liminf` inequalities, with equivalence when `s` is a
  sequential space.
* `TauCeti.exists_seq_forall_mem_and_lt_csInf_add` constructs minimizing sequences in `s` within a
  prescribed positive vanishing error tolerance of `sInf (f '' s)`.
-/

public section

open Filter Set Topology

namespace IsMinOn

/-- A minimum of `f` on a nonempty sublevel `s ∩ f ⁻¹' Iic b` is a minimum of `f` on `s`. -/
theorem of_inter_preimage_Iic {α β : Type*} [LinearOrder β] {f : α → β} {s : Set α} {b : β}
    {a : α} (hmin : IsMinOn f (s ∩ f ⁻¹' Iic b) a) (hne : (s ∩ f ⁻¹' Iic b).Nonempty) :
    IsMinOn f s a := by
  obtain ⟨x₀, hx₀, hfx₀⟩ := hne
  intro x hx
  rcases le_total (f x) b with hfx | hbx
  · exact hmin ⟨hx, hfx⟩
  · exact (hmin ⟨hx₀, hfx₀⟩).trans (hfx₀.trans hbx)

/-- At a minimizer `a ∈ s` of `f` on `s`, the infimum `sInf (f '' s)` equals `f a`. -/
theorem csInf_eq {α β : Type*} [ConditionallyCompleteLinearOrder β] {f : α → β} {s : Set α}
    {a : α} (hmin : IsMinOn f s a) (ha : a ∈ s) :
    sInf (f '' s) = f a :=
  (hmin.isGLB ha).csInf_eq ⟨f a, mem_image_of_mem f ha⟩

/-- If `a ∈ s` minimizes `f` on `s`, the set of minimizers `{x ∈ s | IsMinOn f s x}` coincides
with the sublevel `s ∩ f ⁻¹' Iic (f a)`. -/
theorem setOf_eq_inter_preimage_Iic {α β : Type*} [LinearOrder β] {f : α → β} {s : Set α}
    {a : α} (hmin : IsMinOn f s a) (ha : a ∈ s) :
    {x ∈ s | IsMinOn f s x} = s ∩ f ⁻¹' Iic (f a) :=
  ext fun _ ↦ ⟨fun ⟨hx, hxm⟩ ↦ ⟨hx, hxm ha⟩,
    fun ⟨hx, hfx⟩ ↦ ⟨hx, fun _ hy ↦ hfx.trans (hmin hy)⟩⟩

end IsMinOn

namespace LowerSemicontinuousWithinAt

/-- Along any filter tending to `x` within `s`, the value `f x` of a function lower semicontinuous
within `s` at `x` is bounded above by `liminf (f ∘ u)`. -/
theorem le_liminf_of_tendsto {X β ι : Type*} [TopologicalSpace X] [CompleteLinearOrder β]
    {f : X → β} {s : Set X} {x : X} {l : Filter ι} {u : ι → X}
    (hf : LowerSemicontinuousWithinAt f s x) (hu : Tendsto u l (𝓝[s] x)) :
    f x ≤ liminf (f ∘ u) l :=
  hf.le_liminf.trans (hu.liminf_le_liminf_comp (u := f))

/-- Along any nontrivial filter tending to `x` within `s` along which `f ∘ u` converges to `r`, a
function lower semicontinuous within `s` at `x` satisfies `f x ≤ r`. -/
theorem le_of_tendsto {X β ι : Type*} [TopologicalSpace X] [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] {f : X → β} {s : Set X} {x : X} {r : β} {l : Filter ι} [l.NeBot]
    {u : ι → X} (hf : LowerSemicontinuousWithinAt f s x) (hu : Tendsto u l (𝓝[s] x))
    (hfu : Tendsto (f ∘ u) l (𝓝 r)) :
    f x ≤ r := by
  by_contra! hrf
  by_cases h : ∃ c, r < c ∧ c < f x
  · obtain ⟨c, hrc, hcf⟩ := h
    obtain ⟨i, hci, hic⟩ :=
      ((hu.eventually (hf c hcf)).and (hfu.eventually (Iio_mem_nhds hrc))).exists
    exact lt_asymm hci hic
  · obtain ⟨i, hri, hix⟩ :=
      ((hu.eventually (hf r hrf)).and (hfu.eventually (Iio_mem_nhds hrf))).exists
    exact h ⟨f (u i), hri, hix⟩

end LowerSemicontinuousWithinAt

namespace LowerSemicontinuousOn

/-- If `f` is lower semicontinuous on `s` and a nonempty sublevel `s ∩ f ⁻¹' Iic b` is compact,
then `f` attains its minimum on `s`. -/
theorem exists_isMinOn_of_isCompact_inter_preimage_Iic {X β : Type*} [TopologicalSpace X]
    [LinearOrder β] {f : X → β} {s : Set X} {b : β} (hf : LowerSemicontinuousOn f s)
    (hne : (s ∩ f ⁻¹' Iic b).Nonempty) (hK : IsCompact (s ∩ f ⁻¹' Iic b)) :
    ∃ a ∈ s, IsMinOn f s a := by
  obtain ⟨a, ⟨ha, -⟩, hmin⟩ := (hf.mono inter_subset_left).exists_isMinOn hne hK
  exact ⟨a, ha, hmin.of_inter_preimage_Iic hne⟩

/-- On a closed set `s`, the set of minimizers `{x ∈ s | IsMinOn f s x}` of a function lower
semicontinuous on `s` is closed. -/
theorem isClosed_setOf_isMinOn {X β : Type*} [TopologicalSpace X] [LinearOrder β] {f : X → β}
    {s : Set X} (hf : LowerSemicontinuousOn f s) (hs : IsClosed s) :
    IsClosed {x ∈ s | IsMinOn f s x} := by
  rcases ({x ∈ s | IsMinOn f s x}).eq_empty_or_nonempty with hemp | ⟨a, ha, hmin⟩
  · exact hemp.symm ▸ isClosed_empty
  · obtain ⟨v, hv, hsv⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hf (f a)
    rw [hmin.setOf_eq_inter_preimage_Iic ha, hsv]
    exact hs.inter hv

/-- If `f` is lower semicontinuous on `s`, then along any family eventually in `s` and converging
to `x ∈ s`, `f x ≤ liminf (f ∘ u)`. -/
theorem le_liminf_of_tendsto {X β ι : Type*} [TopologicalSpace X] [CompleteLinearOrder β]
    {f : X → β} {s : Set X} {x : X} {l : Filter ι} {u : ι → X}
    (hf : LowerSemicontinuousOn f s) (hx : x ∈ s) (hus : ∀ᶠ i in l, u i ∈ s)
    (hu : Tendsto u l (𝓝 x)) :
    f x ≤ liminf (f ∘ u) l :=
  LowerSemicontinuousWithinAt.le_liminf_of_tendsto (hf x hx)
    (tendsto_nhdsWithin_iff.2 ⟨hu, hus⟩)

/-- If `f` is lower semicontinuous on `s`, then along any nontrivial filter along which `u` stays
eventually in `s`, converges to `x ∈ s`, and `f ∘ u` converges to `r`, one has `f x ≤ r`. -/
theorem le_of_tendsto {X β ι : Type*} [TopologicalSpace X] [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] {f : X → β} {s : Set X} {x : X} {r : β} {l : Filter ι} [l.NeBot]
    {u : ι → X} (hf : LowerSemicontinuousOn f s) (hx : x ∈ s) (hus : ∀ᶠ i in l, u i ∈ s)
    (hu : Tendsto u l (𝓝 x)) (hfu : Tendsto (f ∘ u) l (𝓝 r)) :
    f x ≤ r :=
  LowerSemicontinuousWithinAt.le_of_tendsto (hf x hx)
    (tendsto_nhdsWithin_iff.2 ⟨hu, hus⟩) hfu

end LowerSemicontinuousOn

namespace TauCeti

section

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β]

/-- A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s` is lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_nhds (G : Set X → β) :
    LowerSemicontinuous fun x ↦ ⨆ s ∈ 𝓝 x, G s := by
  intro x c hc
  obtain ⟨s, hcs⟩ := lt_iSup_iff.1 hc
  obtain ⟨hs, hcs⟩ := lt_iSup_iff.1 hcs
  filter_upwards [eventually_mem_nhds_iff.2 hs] with y hy
  exact hcs.trans_le (le_iSup₂_of_le s hy le_rfl)

/-- On a sequential subspace `s`, lower semicontinuity of `f` on `s` is equivalent to the
sequential inequality `f x ≤ liminf (f ∘ u) atTop` along every sequence in `s` converging to a
point of `s`. -/
theorem lowerSemicontinuousOn_iff_forall_seq_le_liminf {f : X → β} {s : Set X}
    [SequentialSpace s] :
    LowerSemicontinuousOn f s ↔
      ∀ (u : ℕ → X) (x : X), (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  refine ⟨fun hf u x hus hx hu ↦ hf.le_liminf_of_tendsto hx (Eventually.of_forall hus) hu,
    fun hseq ↦ ?_⟩
  rw [← lowerSemicontinuous_restrict_iff, lowerSemicontinuous_iff_isClosed_preimage]
  intro b
  refine IsSeqClosed.isClosed fun v x hv hvx ↦ ?_
  have hlim : Tendsto (fun n ↦ (v n : X)) atTop (𝓝 (x : X)) :=
    (continuous_subtype_val.tendsto x).comp hvx
  exact (hseq (fun n ↦ v n) x (fun n ↦ (v n).2) x.2 hlim).trans <|
    liminf_le_of_frequently_le (Frequently.of_forall hv)

end

/-- When `f '' s` is bounded below, `a ∈ s` minimizes `f` on `s` if and only if
`f a = sInf (f '' s)`. -/
theorem isMinOn_iff_eq_csInf {α β : Type*} [ConditionallyCompleteLinearOrder β] {f : α → β}
    {s : Set α} {a : α} (ha : a ∈ s) (hbdd : BddBelow (f '' s)) :
    IsMinOn f s a ↔ f a = sInf (f '' s) :=
  ⟨fun h ↦ (h.csInf_eq ha).symm, fun h _ hx ↦ h ▸ csInf_le hbdd (mem_image_of_mem f hx)⟩

/-- If `s` is nonempty and `f '' s` is bounded below, then for any positive vanishing error
sequence `ε : ℕ → ℝ` there exists a minimizing sequence `u` in `s` satisfying
`f (u n) < sInf (f '' s) + ε n` for all `n` and `f (u n) → sInf (f '' s)`. -/
theorem exists_seq_forall_mem_and_lt_csInf_add {α : Type*} {f : α → ℝ} {s : Set α}
    (hs : s.Nonempty) (hbdd : BddBelow (f '' s)) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ u : ℕ → α, (∀ n, u n ∈ s) ∧ (∀ n, f (u n) < sInf (f '' s) + ε n) ∧
      Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  have hlt (n : ℕ) : ∃ x ∈ s, f x < sInf (f '' s) + ε n := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hfx⟩ :=
      (csInf_lt_iff hbdd (hs.image f)).1 (lt_add_of_pos_right (sInf (f '' s)) (hε n))
    exact ⟨x, hx, hfx⟩
  choose u hu hfu using hlt
  refine ⟨u, hu, hfu, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hbdd (mem_image_of_mem f (hu n))) (fun n ↦ (hfu n).le)⟩
  simpa only [add_zero] using tendsto_const_nhds.add hε0

end TauCeti

open scoped ENNReal

namespace LowerSemicontinuous

variable {E β : Type*} [AddCommMonoid E] [TopologicalSpace E] {A : E → ℝ≥0∞}

/-- A lower semicontinuous subadditive function with values in `ℝ≥0∞` vanishing at zero bounds
the sum of a convergent series by the sum of its values on the terms. -/
theorem le_tsum_of_hasSum (hA : LowerSemicontinuous A) (h0 : A 0 = 0)
    (hadd : ∀ x y, A (x + y) ≤ A x + A y) {f : β → E} {s : E} (hf : HasSum f s) :
    A s ≤ ∑' b, A (f b) :=
  (hA.isClosed_preimage _).mem_of_tendsto hf <| Filter.Eventually.of_forall fun t ↦
    (Finset.le_sum_of_subadditive A h0.le hadd t f).trans (sum_le_tsum t)

end LowerSemicontinuous
