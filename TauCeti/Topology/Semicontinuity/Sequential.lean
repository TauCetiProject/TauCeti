/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Sequential lower semicontinuity

A function `f : α → β` is *sequentially lower semicontinuous* on a set `s` if along every sequence
`u : ℕ → α` in `s` converging to `x ∈ s`, every strict lower bound of `f x` eventually bounds
`f (u n)` strictly from below.

For a `LinearOrder` codomain, this is equivalent to sequential closedness of every relative
sublevel set, and on a `SequentialSpace` (such as a first-countable space or a weakly compact
subset of a normed space) it agrees with topological `LowerSemicontinuousOn`. For a
`CompleteLinearOrder` codomain, and for real-valued functions coerced to `EReal`, it is equivalent
to the lower-limit inequality `f x ≤ liminf (f ∘ u) atTop`. For a real-valued function bounded
below on `s`, it is further equivalent to `f x ≤ r` whenever `u n → x` and `f (u n) → r`.

On a nonempty sequentially compact set, a sequentially lower semicontinuous real-valued (or
first-countable complete-linear-order-valued) function is bounded below and attains its minimum.

## Main declarations

* `TauCeti.SeqLowerSemicontinuousOn`, `TauCeti.SeqLowerSemicontinuous`: sequential lower
  semicontinuity on a set and globally.
* `TauCeti.seqLowerSemicontinuous_iff_isSeqClosed_preimage`: sublevel sequential closedness.
* `TauCeti.lowerSemicontinuous_iff_seqLowerSemicontinuous`,
  `TauCeti.lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn`: agreement with topological lower
  semicontinuity on sequential spaces.
* `TauCeti.seqLowerSemicontinuousOn_iff_le_liminf`,
  `TauCeti.seqLowerSemicontinuousOn_iff_le_liminf_ereal`: `liminf` characterizations.
* `TauCeti.seqLowerSemicontinuousOn_iff_forall_le_of_tendsto`: finite-limit characterization
  for real-valued functions bounded below.
* `TauCeti.SeqLowerSemicontinuousOn.exists_isMinOn`,
  `TauCeti.SeqLowerSemicontinuousOn.exists_isMinOn_real`: attainment of minima on sequentially
  compact sets.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {α β γ : Type*} [TopologicalSpace α]

/-- A function `f : α → β` is *sequentially lower semicontinuous* on `s` if whenever a sequence
`u : ℕ → α` in `s` converges to `x ∈ s`, every strict lower bound of `f x` eventually bounds
`f (u n)` strictly from below. -/
def SeqLowerSemicontinuousOn [LT β] (f : α → β) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ u : ℕ → α, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
    ∀ b < f x, ∀ᶠ n in atTop, b < f (u n)

/-- A function `f : α → β` is *sequentially lower semicontinuous* if whenever a sequence
`u : ℕ → α` converges to `x`, every strict lower bound of `f x` eventually bounds `f (u n)`
strictly from below. -/
def SeqLowerSemicontinuous [LT β] (f : α → β) : Prop :=
  ∀ x : α, ∀ u : ℕ → α, Tendsto u atTop (𝓝 x) →
    ∀ b < f x, ∀ᶠ n in atTop, b < f (u n)

/-- Characterization of `SeqLowerSemicontinuousOn` by its defining property. -/
theorem seqLowerSemicontinuousOn_iff [LT β] {f : α → β} {s : Set α} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ u : ℕ → α, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        ∀ b < f x, ∀ᶠ n in atTop, b < f (u n) :=
  Iff.rfl

/-- Characterization of `SeqLowerSemicontinuous` by its defining property. -/
theorem seqLowerSemicontinuous_iff [LT β] {f : α → β} :
    SeqLowerSemicontinuous f ↔
      ∀ x : α, ∀ u : ℕ → α, Tendsto u atTop (𝓝 x) →
        ∀ b < f x, ∀ᶠ n in atTop, b < f (u n) :=
  Iff.rfl

section Basic

variable [LT β] {f g : α → β} {s t : Set α}

/-- Sequential lower semicontinuity on `univ` is global sequential lower semicontinuity. -/
@[simp] theorem seqLowerSemicontinuousOn_univ_iff :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f := by
  simp [SeqLowerSemicontinuousOn, SeqLowerSemicontinuous]

/-- Sequential lower semicontinuity of the restriction to `s` is sequential lower
semicontinuity on `s`. -/
@[simp] theorem seqLowerSemicontinuous_restrict_iff :
    SeqLowerSemicontinuous (s.domRestrict f) ↔ SeqLowerSemicontinuousOn f s := by
  constructor
  · intro hf x hx u hu hux b hb
    exact hf ⟨x, hx⟩ (fun n ↦ ⟨u n, hu n⟩) (tendsto_subtype_rng.mpr hux) b hb
  · intro hf ⟨x, hx⟩ u hux b hb
    exact hf x hx (fun n ↦ (u n : α)) (fun n ↦ (u n).2) (tendsto_subtype_rng.mp hux) b hb

/-- Every function is sequentially lower semicontinuous on the empty set. -/
@[simp] theorem seqLowerSemicontinuousOn_empty : SeqLowerSemicontinuousOn f ∅ :=
  fun _ hx ↦ hx.elim

/-- Every function is sequentially lower semicontinuous on a singleton. -/
@[simp] theorem seqLowerSemicontinuousOn_singleton (x : α) :
    SeqLowerSemicontinuousOn f {x} :=
  fun _ hy _ hu _ _ hb ↦ Eventually.of_forall fun n ↦ by
    simpa only [mem_singleton_iff.mp hy, mem_singleton_iff.mp (hu n)] using hb

/-- Every constant function is sequentially lower semicontinuous on any set. -/
@[simp] theorem seqLowerSemicontinuousOn_const (c : β) :
    SeqLowerSemicontinuousOn (fun _ : α ↦ c) s :=
  fun _ _ _ _ _ _ hb ↦ Eventually.of_forall fun _ ↦ hb

/-- Every constant function is sequentially lower semicontinuous. -/
@[simp] theorem seqLowerSemicontinuous_const (c : β) :
    SeqLowerSemicontinuous (fun _ : α ↦ c) :=
  fun _ _ _ _ hb ↦ Eventually.of_forall fun _ ↦ hb

/-- Sequential lower semicontinuity on `s` depends only on the values of `f` on `s`. -/
theorem seqLowerSemicontinuousOn_congr (h : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s := by
  constructor
  · intro hf x hx u hu hux b hb
    rw [← h hx] at hb
    exact (hf x hx u hu hux b hb).mono fun n hn ↦ h (hu n) ▸ hn
  · intro hg x hx u hu hux b hb
    rw [h hx] at hb
    exact (hg x hx u hu hux b hb).mono fun n hn ↦ (h (hu n)).symm ▸ hn

/-- A globally sequentially lower semicontinuous function is sequentially lower semicontinuous
on every set. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousOn (hf : SeqLowerSemicontinuous f)
    (s : Set α) : SeqLowerSemicontinuousOn f s :=
  fun x _ u _ hux ↦ hf x u hux

/-- Sequential lower semicontinuity on a set is inherited by subsets. -/
theorem SeqLowerSemicontinuousOn.mono (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) :
    SeqLowerSemicontinuousOn f t :=
  fun x hx u hu ↦ hf x (hts hx) u (fun n ↦ hts (hu n))

/-- Right composition of a sequentially lower semicontinuous function with a map continuous on
the domain set. -/
theorem SeqLowerSemicontinuousOn.comp [TopologicalSpace γ] {g : γ → α} {t : Set γ}
    (hf : SeqLowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hmaps : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun x hx u hu hux ↦
    hf (g x) (hmaps hx) (g ∘ u) (fun n ↦ hmaps (hu n))
      ((hg x hx).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hux
        (Eventually.of_forall hu)))

/-- Right composition of a sequentially lower semicontinuous function on `s` with a sequentially
continuous map sending `t` into `s`. -/
theorem SeqLowerSemicontinuousOn.comp_seqContinuous [TopologicalSpace γ] {g : γ → α} {t : Set γ}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqContinuous g) (hmaps : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun x hx u hu hux ↦
    hf (g x) (hmaps hx) (g ∘ u) (fun n ↦ hmaps (hu n)) (hg hux)

/-- Right composition of a sequentially lower semicontinuous function with a sequentially
continuous map. -/
theorem SeqLowerSemicontinuous.comp [TopologicalSpace γ] {g : γ → α}
    (hf : SeqLowerSemicontinuous f) (hg : SeqContinuous g) :
    SeqLowerSemicontinuous (f ∘ g) :=
  fun x u hux ↦ hf (g x) (g ∘ u) (hg hux)

end Basic

end TauCeti

section FromMathlib

variable {α β : Type*} [TopologicalSpace α] {f : α → β} {s : Set α}

/-- Every lower semicontinuous function on `s` is sequentially lower semicontinuous on `s`. -/
theorem LowerSemicontinuousOn.seqLowerSemicontinuousOn [Preorder β]
    (hf : LowerSemicontinuousOn f s) : TauCeti.SeqLowerSemicontinuousOn f s :=
  fun x hx u hu hux b hb ↦
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hux
      (Eventually.of_forall hu)).eventually (hf x hx b hb)

/-- Every lower semicontinuous function is sequentially lower semicontinuous. -/
theorem LowerSemicontinuous.seqLowerSemicontinuous [Preorder β]
    (hf : LowerSemicontinuous f) : TauCeti.SeqLowerSemicontinuous f :=
  fun x _ hux b hb ↦ hux.eventually (hf x b hb)

/-- Every function continuous on `s` into a linear order with closed lower rays is sequentially
lower semicontinuous on `s`. -/
theorem ContinuousOn.seqLowerSemicontinuousOn [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] (hf : ContinuousOn f s) : TauCeti.SeqLowerSemicontinuousOn f s :=
  fun x hx u hu hux _ hb ↦
    ((hf x hx).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hux
      (Eventually.of_forall hu))).eventually (Ioi_mem_nhds hb)

/-- Every continuous function into a linear order with closed lower rays is sequentially lower
semicontinuous. -/
theorem Continuous.seqLowerSemicontinuous [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] (hf : Continuous f) : TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hux _ hb ↦ (hf.tendsto _ |>.comp hux).eventually (Ioi_mem_nhds hb)

/-- Every sequentially continuous function into a linear order with closed lower rays is
sequentially lower semicontinuous. -/
theorem SeqContinuous.seqLowerSemicontinuous [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] (hf : SeqContinuous f) : TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hux _ hb ↦ (hf hux).eventually (Ioi_mem_nhds hb)

end FromMathlib

namespace TauCeti

section Sublevels

variable {α β : Type*} [TopologicalSpace α] [LinearOrder β] {f : α → β} {s : Set α}

/-- A function into a linear order is sequentially lower semicontinuous if and only if every
sublevel `f ⁻¹' Iic b` is sequentially closed. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage :
    SeqLowerSemicontinuous f ↔ ∀ b, IsSeqClosed (f ⁻¹' Iic b) := by
  constructor
  · intro hf b u x hu hux
    by_contra hlt
    rw [mem_preimage, mem_Iic, not_le] at hlt
    obtain ⟨n, hn⟩ := (hf x u hux b hlt).exists
    exact hn.not_ge (hu n)
  · intro h x u hux b hb
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop, f (u n) ≤ b := by
      simpa only [not_eventually, not_lt] using hnot
    obtain ⟨φ, hφ_mono, hφ_le⟩ := extraction_of_frequently_atTop hfreq
    have hx : f x ≤ b := h b hφ_le (hux.comp hφ_mono.tendsto_atTop)
    exact hb.not_ge hx

/-- Every sublevel of a sequentially lower semicontinuous function is sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_preimage (hf : SeqLowerSemicontinuous f) (b : β) :
    IsSeqClosed (f ⁻¹' Iic b) :=
  seqLowerSemicontinuous_iff_isSeqClosed_preimage.mp hf b

/-- A function into a linear order is sequentially lower semicontinuous on `s` if and only if
every sublevel is sequentially closed relative to `s`. -/
theorem seqLowerSemicontinuousOn_iff_forall_le_of_le :
    SeqLowerSemicontinuousOn f s ↔
      ∀ b, ∀ (u : ℕ → α) (x : α), (∀ n, u n ∈ s ∧ f (u n) ≤ b) → x ∈ s →
        Tendsto u atTop (𝓝 x) → f x ≤ b := by
  rw [← seqLowerSemicontinuous_restrict_iff, seqLowerSemicontinuous_iff_isSeqClosed_preimage]
  constructor
  · intro h b u x hu hx hux
    exact h b (x := fun n ↦ ⟨u n, (hu n).1⟩) (p := ⟨x, hx⟩) (fun n ↦ (hu n).2)
      (tendsto_subtype_rng.mpr hux)
  · intro h b u ⟨x, hx⟩ hu hux
    exact h b (fun n ↦ (u n : α)) x (fun n ↦ ⟨(u n).2, hu n⟩) hx (tendsto_subtype_rng.mp hux)

/-- If `s` is sequentially closed and `f` is sequentially lower semicontinuous on `s`, then
every relative sublevel `{x ∈ s | f x ≤ b}` is sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_sublevel (hf : SeqLowerSemicontinuousOn f s)
    (hs : IsSeqClosed s) (b : β) : IsSeqClosed {x ∈ s | f x ≤ b} := by
  intro u x hu hux
  have hx : x ∈ s := hs (fun n ↦ (hu n).1) hux
  exact ⟨hx, seqLowerSemicontinuousOn_iff_forall_le_of_le.mp hf b u x hu hx hux⟩

/-- On a sequential space, topological and sequential lower semicontinuity coincide. -/
theorem lowerSemicontinuous_iff_seqLowerSemicontinuous [SequentialSpace α] :
    LowerSemicontinuous f ↔ SeqLowerSemicontinuous f := by
  rw [lowerSemicontinuous_iff_isClosed_preimage, seqLowerSemicontinuous_iff_isSeqClosed_preimage]
  simp only [isSeqClosed_iff_isClosed]

/-- On a subset whose induced topology is sequential, topological and sequential lower
semicontinuity coincide. -/
theorem lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn [SequentialSpace s] :
    LowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn f s := by
  rw [← lowerSemicontinuous_restrict_iff, ← seqLowerSemicontinuous_restrict_iff]
  exact lowerSemicontinuous_iff_seqLowerSemicontinuous

end Sublevels

section Liminf

variable {α γ : Type*} [TopologicalSpace α]

/-- In a complete linear order, sequential lower semicontinuity is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along every convergent sequence `u → x`. -/
theorem seqLowerSemicontinuous_iff_le_liminf [CompleteLinearOrder γ] {f : α → γ} :
    SeqLowerSemicontinuous f ↔
      ∀ (x : α) (u : ℕ → α), Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  refine forall₂_congr fun x u ↦ imp_congr_right fun _ ↦ ?_
  simpa only [Function.comp_apply] using (le_liminf_iff (u := f ∘ u) (f := atTop)).symm

/-- In a complete linear order, sequential lower semicontinuity on `s` is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along every sequence `u` in `s` converging to `x ∈ s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf [CompleteLinearOrder γ] {f : α → γ} {s : Set α} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ u : ℕ → α, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        f x ≤ liminf (f ∘ u) atTop := by
  refine forall₂_congr fun x _ ↦ forall₂_congr fun u _ ↦ imp_congr_right fun _ ↦ ?_
  simpa only [Function.comp_apply] using (le_liminf_iff (u := f ∘ u) (f := atTop)).symm

/-- A sequentially lower semicontinuous function into a complete linear order satisfies
`f x ≤ liminf (f ∘ u) atTop` along every convergent sequence. -/
theorem SeqLowerSemicontinuous.le_liminf [CompleteLinearOrder γ] {f : α → γ}
    (hf : SeqLowerSemicontinuous f) {u : ℕ → α} {x : α} (hux : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (f ∘ u) atTop :=
  seqLowerSemicontinuous_iff_le_liminf.mp hf x u hux

/-- A function sequentially lower semicontinuous on `s` into a complete linear order satisfies
`f x ≤ liminf (f ∘ u) atTop` along every sequence in `s` converging to `x ∈ s`. -/
theorem SeqLowerSemicontinuousOn.le_liminf [CompleteLinearOrder γ] {f : α → γ} {s : Set α}
    (hf : SeqLowerSemicontinuousOn f s) {u : ℕ → α} {x : α}
    (hu : ∀ n, u n ∈ s) (hx : x ∈ s) (hux : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (f ∘ u) atTop :=
  seqLowerSemicontinuousOn_iff_le_liminf.mp hf x hx u hu hux

/-- Coercing a real-valued function to `EReal` preserves and reflects sequential lower
semicontinuity on `s`. -/
theorem seqLowerSemicontinuousOn_coe_ereal_iff {f : α → ℝ} {s : Set α} :
    SeqLowerSemicontinuousOn (fun x ↦ (f x : EReal)) s ↔ SeqLowerSemicontinuousOn f s := by
  constructor
  · intro hf x hx u hu hux b hb
    filter_upwards [hf x hx u hu hux (b : EReal) (EReal.coe_lt_coe_iff.mpr hb)] with n hn
    exact EReal.coe_lt_coe_iff.mp hn
  · intro hf x hx u hu hux b hb
    induction b using EReal.rec with
    | bot => exact Eventually.of_forall fun n ↦ EReal.bot_lt_coe (f (u n))
    | top => exact (not_top_lt hb).elim
    | coe r =>
      filter_upwards [hf x hx u hu hux r (EReal.coe_lt_coe_iff.mp hb)] with n hn
      exact EReal.coe_lt_coe_iff.mpr hn

/-- Coercing a real-valued function to `EReal` preserves and reflects global sequential lower
semicontinuity. -/
theorem seqLowerSemicontinuous_coe_ereal_iff {f : α → ℝ} :
    SeqLowerSemicontinuous (fun x ↦ (f x : EReal)) ↔ SeqLowerSemicontinuous f := by
  simpa only [← seqLowerSemicontinuousOn_univ_iff] using
    seqLowerSemicontinuousOn_coe_ereal_iff (f := f) (s := univ)

/-- A real-valued function is sequentially lower semicontinuous on `s` if and only if
`(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop` along every sequence in `s`
converging to `x ∈ s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf_ereal {f : α → ℝ} {s : Set α} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ u : ℕ → α, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff, seqLowerSemicontinuousOn_iff_le_liminf]
  rfl

/-- A real-valued function is sequentially lower semicontinuous if and only if
`(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop` along every convergent sequence. -/
theorem seqLowerSemicontinuous_iff_le_liminf_ereal {f : α → ℝ} :
    SeqLowerSemicontinuous f ↔
      ∀ (x : α) (u : ℕ → α), Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuous_coe_ereal_iff, seqLowerSemicontinuous_iff_le_liminf]
  rfl

end Liminf

section FiniteLimit

variable {α β : Type*} [TopologicalSpace α] {f : α → β} {s : Set α}

/-- Along a sequence in `s` converging to `x ∈ s` whose values converge to `r`, a function
sequentially lower semicontinuous on `s` into a linear order with closed upper rays satisfies
`f x ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] (hf : SeqLowerSemicontinuousOn f s) {u : ℕ → α} {x : α} {r : β}
    (hu : ∀ n, u n ∈ s) (hx : x ∈ s) (hux : Tendsto u atTop (𝓝 x))
    (hfu : Tendsto (f ∘ u) atTop (𝓝 r)) : f x ≤ r := by
  by_contra! hlt
  by_cases hmid : ∃ b, r < b ∧ b < f x
  · obtain ⟨b, hrb, hbf⟩ := hmid
    obtain ⟨n, h1, h2⟩ :=
      ((hf x hx u hu hux b hbf).and (hfu.eventually (Iio_mem_nhds hrb))).exists
    exact h1.not_gt h2
  · obtain ⟨n, h1, h2⟩ :=
      ((hf x hx u hu hux r hlt).and (hfu.eventually (Iio_mem_nhds hlt))).exists
    exact hmid ⟨f (u n), h1, h2⟩

/-- Along a sequence converging to `x` whose values converge to `r`, a sequentially lower
semicontinuous function into a linear order with closed upper rays satisfies `f x ≤ r`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] (hf : SeqLowerSemicontinuous f) {u : ℕ → α} {x : α} {r : β}
    (hux : Tendsto u atTop (𝓝 x)) (hfu : Tendsto (f ∘ u) atTop (𝓝 r)) : f x ≤ r :=
  (hf.seqLowerSemicontinuousOn univ).le_of_tendsto (fun _ ↦ mem_univ _) (mem_univ _) hux hfu

/-- When a real-valued function is bounded below on `s`, sequential lower semicontinuity on `s`
is equivalent to the finite-limit inequality `f x ≤ r` whenever `u n → x` in `s` and
`f (u n) → r`. -/
theorem seqLowerSemicontinuousOn_iff_forall_le_of_tendsto {f : α → ℝ} (hb : BddBelow (f '' s)) :
    SeqLowerSemicontinuousOn f s ↔
      ∀ (u : ℕ → α) (x : α) (r : ℝ), (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 r) → f x ≤ r := by
  refine ⟨fun hf u x r hu hx hux hfu ↦ hf.le_of_tendsto hu hx hux hfu, fun h ↦ ?_⟩
  rw [seqLowerSemicontinuousOn_iff_forall_le_of_le]
  intro b u x hu hx hux
  obtain ⟨m, hm⟩ := hb
  have hmem : ∀ n, f (u n) ∈ Icc m b := fun n ↦ ⟨hm (mem_image_of_mem f (hu n).1), (hu n).2⟩
  obtain ⟨r, hr, φ, hφ_mono, hφ_lim⟩ := isCompact_Icc.tendsto_subseq hmem
  exact (h (u ∘ φ) x r (fun n ↦ (hu (φ n)).1) hx (hux.comp hφ_mono.tendsto_atTop) hφ_lim).trans hr.2

end FiniteLimit

section SeqCompactMin

variable {α β : Type*} [TopologicalSpace α] {f : α → β} {s : Set α}

/-- A sequentially lower semicontinuous function bounded below on a nonempty sequentially
compact set attains its minimum there, when the codomain is a first-countable conditionally
complete linear order with the order topology. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_bddBelow [ConditionallyCompleteLinearOrder β]
    [TopologicalSpace β] [OrderTopology β] [FirstCountableTopology β]
    (hf : SeqLowerSemicontinuousOn f s) (hne : s.Nonempty) (hs : IsSeqCompact s)
    (hb : BddBelow (f '' s)) : ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨y, hy_mem, hy_lim⟩ := mem_closure_iff_seq_limit.mp (csInf_mem_closure (hne.image f) hb)
  choose u hu hfu using hy_mem
  obtain ⟨x, hx, φ, hφ_mono, hφ_lim⟩ := hs hu
  have hf_lim : Tendsto (f ∘ (u ∘ φ)) atTop (𝓝 (sInf (f '' s))) := by
    have : f ∘ (u ∘ φ) = y ∘ φ := funext fun n ↦ hfu (φ n)
    rw [this]
    exact hy_lim.comp hφ_mono.tendsto_atTop
  have hle : f x ≤ sInf (f '' s) :=
    hf.le_of_tendsto (fun n ↦ hu (φ n)) hx hφ_lim hf_lim
  exact ⟨x, hx, fun a ha ↦ hle.trans (csInf_le hb (mem_image_of_mem f ha))⟩

/-- A sequentially lower semicontinuous function into a first-countable complete linear order
with the order topology attains its minimum on every nonempty sequentially compact set. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn [CompleteLinearOrder β]
    [TopologicalSpace β] [OrderTopology β] [FirstCountableTopology β]
    (hf : SeqLowerSemicontinuousOn f s) (hne : s.Nonempty) (hs : IsSeqCompact s) :
    ∃ x ∈ s, IsMinOn f s x :=
  hf.exists_isMinOn_of_bddBelow hne hs (OrderBot.bddBelow _)

/-- A real-valued sequentially lower semicontinuous function attains its minimum on every
nonempty sequentially compact set, without an a priori lower bound. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_real {f : α → ℝ}
    (hf : SeqLowerSemicontinuousOn f s) (hne : s.Nonempty) (hs : IsSeqCompact s) :
    ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨x, hx, hmin⟩ :=
    (seqLowerSemicontinuousOn_coe_ereal_iff.mpr hf).exists_isMinOn hne hs
  exact ⟨x, hx, fun a ha ↦ EReal.coe_le_coe_iff.mp (hmin ha)⟩

/-- A real-valued sequentially lower semicontinuous function is bounded below on every
sequentially compact set. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact {f : α → ℝ}
    (hf : SeqLowerSemicontinuousOn f s) (hs : IsSeqCompact s) : BddBelow (f '' s) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨_, _, hmin⟩ := hf.exists_isMinOn_real hne hs
    exact hmin.bddBelow

end SeqCompactMin

section Algebra

/-- Along a sequence `u` with limit `x`, the sequential lower semicontinuity condition at `x`
is equivalent to topological `LowerSemicontinuousAt` at `⊤ : ℕ∞` of the extended map
`k ↦ f (WithTop.recTopCoe x u k)`. -/
private theorem lowerSemicontinuousAt_recTopCoe_top_iff {α β : Type*} [Preorder β]
    (f : α → β) {x : α} {u : ℕ → α} :
    LowerSemicontinuousAt (fun k : ℕ∞ ↦ f (WithTop.recTopCoe x u k)) ⊤ ↔
      ∀ b < f x, ∀ᶠ n : ℕ in atTop, b < f (u n) := by
  refine forall₂_congr fun b hb ↦ ⟨fun h ↦ ENat.tendsto_natCast_nhds_top.eventually h, fun h ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  filter_upwards [Ioi_mem_nhds (ENat.natCast_lt_top N)] with k hk
  cases k with
  | top => exact hb
  | coe n => exact hN n (Nat.cast_lt.mp (mem_Ioi.mp hk)).le

variable {α β γ : Type*} [TopologicalSpace α] {s : Set α}

/-- Left composition of a sequentially lower semicontinuous function on `s` with a continuous
monotone function. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuousOn [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    {g : β → γ} {f : α → β} (hg : Continuous g) (hf : SeqLowerSemicontinuousOn f s)
    (hmono : Monotone g) : SeqLowerSemicontinuousOn (g ∘ f) s :=
  fun x hx u hu hux ↦
    (lowerSemicontinuousAt_recTopCoe_top_iff (g ∘ f)).mp <|
      hg.continuousAt.comp_lowerSemicontinuousAt
        ((lowerSemicontinuousAt_recTopCoe_top_iff f).mpr (hf x hx u hu hux)) hmono

/-- Left composition of a sequentially lower semicontinuous function with a continuous monotone
function. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuous [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    {g : β → γ} {f : α → β} (hg : Continuous g) (hf : SeqLowerSemicontinuous f)
    (hmono : Monotone g) : SeqLowerSemicontinuous (g ∘ f) :=
  seqLowerSemicontinuousOn_univ_iff.mp <|
    hg.comp_seqLowerSemicontinuousOn (seqLowerSemicontinuousOn_univ_iff.mpr hf) hmono

section Add

variable [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ] [TopologicalSpace γ]
  [OrderTopology γ] {f g : α → γ}

/-- The sum of two sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`, assuming continuity of addition at each `(f x, g x)` for `x ∈ s`. -/
theorem SeqLowerSemicontinuousOn.add' (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuousOn (fun x ↦ f x + g x) s :=
  fun x hx u hu hux ↦
    (lowerSemicontinuousAt_recTopCoe_top_iff (fun y ↦ f y + g y)).mp <|
      ((lowerSemicontinuousAt_recTopCoe_top_iff f).mpr (hf x hx u hu hux)).add'
        ((lowerSemicontinuousAt_recTopCoe_top_iff g).mpr (hg x hx u hu hux)) (hcont x hx)

/-- The sum of two sequentially lower semicontinuous functions is sequentially lower
semicontinuous, assuming continuity of addition at each `(f x, g x)`. -/
theorem SeqLowerSemicontinuous.add' (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuous (fun x ↦ f x + g x) :=
  seqLowerSemicontinuousOn_univ_iff.mp <|
    (seqLowerSemicontinuousOn_univ_iff.mpr hf).add'
      (seqLowerSemicontinuousOn_univ_iff.mpr hg) fun x _ ↦ hcont x

variable [ContinuousAdd γ]

/-- The sum of two sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.add (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x + g x) s :=
  hf.add' hg fun _ _ ↦ continuous_add.continuousAt

/-- The sum of two sequentially lower semicontinuous functions is sequentially lower
semicontinuous. -/
theorem SeqLowerSemicontinuous.add (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous (fun x ↦ f x + g x) :=
  hf.add' hg fun _ ↦ continuous_add.continuousAt

/-- A finite sum of sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_sum {ι : Type*} {f : ι → α → γ} {t : Finset ι}
    (hf : ∀ i ∈ t, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ∑ i ∈ t, f i x) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i t)).add
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- A finite sum of sequentially lower semicontinuous functions is sequentially lower
semicontinuous. -/
theorem seqLowerSemicontinuous_sum {ι : Type*} {f : ι → α → γ} {t : Finset ι}
    (hf : ∀ i ∈ t, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous (fun x ↦ ∑ i ∈ t, f i x) :=
  seqLowerSemicontinuousOn_univ_iff.mp <|
    seqLowerSemicontinuousOn_sum fun i hi ↦ (hf i hi).seqLowerSemicontinuousOn univ

end Add

section SupInf

variable [LinearOrder γ] {f g : α → γ}

/-- The pointwise supremum of two sequentially lower semicontinuous functions on `s` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.sup (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s :=
  fun x hx u hu hux ↦
    (lowerSemicontinuousAt_recTopCoe_top_iff (fun y ↦ f y ⊔ g y)).mp <|
      ((lowerSemicontinuousAt_recTopCoe_top_iff f).mpr (hf x hx u hu hux)).sup
        ((lowerSemicontinuousAt_recTopCoe_top_iff g).mpr (hg x hx u hu hux))

/-- The pointwise supremum of two sequentially lower semicontinuous functions is sequentially
lower semicontinuous. -/
theorem SeqLowerSemicontinuous.sup (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous (fun x ↦ f x ⊔ g x) :=
  seqLowerSemicontinuousOn_univ_iff.mp <|
    (seqLowerSemicontinuousOn_univ_iff.mpr hf).sup (seqLowerSemicontinuousOn_univ_iff.mpr hg)

/-- The pointwise infimum of two sequentially lower semicontinuous functions on `s` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.inf (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊓ g x) s :=
  fun x hx u hu hux ↦
    (lowerSemicontinuousAt_recTopCoe_top_iff (fun y ↦ f y ⊓ g y)).mp <|
      ((lowerSemicontinuousAt_recTopCoe_top_iff f).mpr (hf x hx u hu hux)).inf
        ((lowerSemicontinuousAt_recTopCoe_top_iff g).mpr (hg x hx u hu hux))

/-- The pointwise infimum of two sequentially lower semicontinuous functions is sequentially
lower semicontinuous. -/
theorem SeqLowerSemicontinuous.inf (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous (fun x ↦ f x ⊓ g x) :=
  seqLowerSemicontinuousOn_univ_iff.mp <|
    (seqLowerSemicontinuousOn_univ_iff.mpr hf).inf (seqLowerSemicontinuousOn_univ_iff.mpr hg)

end SupInf

section IndexedSup

variable {ι : Sort*}

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions on `s`
into a conditionally complete linear order is sequentially lower semicontinuous on `s`,
provided the family is pointwise bounded above on `s`. -/
theorem seqLowerSemicontinuousOn_ciSup [ConditionallyCompleteLinearOrder γ] {f : ι → α → γ}
    (hbdd : ∀ x ∈ s, BddAbove (range fun i ↦ f i x))
    (hf : ∀ i, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, f i x) s := by
  intro x hx u hu hux
  refine (lowerSemicontinuousAt_recTopCoe_top_iff (fun y ↦ ⨆ i, f i y)).mp <|
    lowerSemicontinuousAt_ciSup ?_ fun i ↦
      (lowerSemicontinuousAt_recTopCoe_top_iff (f i)).mpr (hf i x hx u hu hux)
  refine Eventually.of_forall fun k ↦ ?_
  cases k with
  | top => exact hbdd x hx
  | coe n => exact hbdd (u n) (hu n)

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions on `s`
into a complete linear order is sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_iSup [CompleteLinearOrder γ] {f : ι → α → γ}
    (hf : ∀ i, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, f i x) s :=
  seqLowerSemicontinuousOn_ciSup (fun _ _ ↦ OrderTop.bddAbove _) hf

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions into a
conditionally complete linear order is sequentially lower semicontinuous, provided the family
is pointwise bounded above. -/
theorem seqLowerSemicontinuous_ciSup [ConditionallyCompleteLinearOrder γ] {f : ι → α → γ}
    (hbdd : ∀ x, BddAbove (range fun i ↦ f i x))
    (hf : ∀ i, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous (fun x ↦ ⨆ i, f i x) :=
  seqLowerSemicontinuousOn_univ_iff.mp <|
    seqLowerSemicontinuousOn_ciSup (fun x _ ↦ hbdd x) fun i ↦ (hf i).seqLowerSemicontinuousOn univ

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions into a
complete linear order is sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_iSup [CompleteLinearOrder γ] {f : ι → α → γ}
    (hf : ∀ i, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous (fun x ↦ ⨆ i, f i x) :=
  seqLowerSemicontinuous_ciSup (fun _ ↦ OrderTop.bddAbove _) hf

end IndexedSup

end Algebra

end TauCeti
