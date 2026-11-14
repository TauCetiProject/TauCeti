/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
public import TauCeti.Order.Filter.Extr
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Sequential lower semicontinuity

A function `f : X → β` into a preorder is *sequentially lower semicontinuous* on `s : Set X`
(`TauCeti.SeqLowerSemicontinuousOn f s`) if every strict lower bound `b < f x` at `x ∈ s`
eventually persists along every sequence in `s` converging to `x`. Without topologies on `β` or
countability hypotheses on `X`, topological lower semicontinuity implies sequential lower
semicontinuity (`LowerSemicontinuousOn.seqLowerSemicontinuousOn`), and the two notions coincide
whenever the domain (or subspace `s`) is a `SequentialSpace`
(`TauCeti.seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn`).

When `β` is a linear order, sequential lower semicontinuity is equivalent to sequential closedness
of all sublevels `f ⁻¹' Iic b` (`TauCeti.seqLowerSemicontinuous_iff_isSeqClosed_preimage`), and on
a sequentially closed set `s` to sequential closedness of `{x ∈ s | f x ≤ b}`
(`TauCeti.seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel`). When `β` is a complete linear order,
it is equivalent to the sequential `liminf` inequality `f x ≤ liminf (f ∘ u) atTop`
(`TauCeti.seqLowerSemicontinuousOn_iff_le_liminf`); for `f : X → ℝ`, coercion to `EReal` expresses
the same property without boundedness assumptions on `f ∘ u`
(`TauCeti.seqLowerSemicontinuousOn_real_iff_le_liminf_ereal`).

When `β` carries a `ClosedIciTopology`, convergent images `f (u n) → r` along `u n → x` satisfy
`f x ≤ r` (`TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto`), so any cluster point of a sequence
whose values tend to `sInf (f '' s)` is a minimizer (`isMinOn_of_tendsto_csInf`). For real-valued
functions, every nonempty bounded-below image admits a minimizing sequence within `1 / (n + 1)` of
`sInf (f '' s)` (`TauCeti.exists_seq_lt_csInf_add_one_div`), and sequential compactness yields
boundedness from below and attainment of the minimum (`SeqLowerSemicontinuousOn.exists_isMinOn`).

## References

* G. Dal Maso, *An Introduction to Γ-Convergence*, Birkhäuser 1993, Chapter 1.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
-/

public section

open Filter Function Set Topology

namespace TauCeti

section Preorder

variable {X : Type*} [TopologicalSpace X] {β : Type*} [Preorder β]

/-- `f : X → β` is sequentially lower semicontinuous on `s` if every strict lower bound `b < f x`
at `x ∈ s` holds eventually along every sequence in `s` converging to `x`. -/
def SeqLowerSemicontinuousOn (f : X → β) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ b < f x, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) →
    Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, b < f (u n)

/-- `f : X → β` is sequentially lower semicontinuous if every strict lower bound `b < f x` holds
eventually along every sequence converging to `x`. -/
def SeqLowerSemicontinuous (f : X → β) : Prop :=
  ∀ x, ∀ b < f x, ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, b < f (u n)

/-- Unfolding characterization of `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem seqLowerSemicontinuousOn_iff {f : X → β} {s : Set X} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ b < f x, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) →
        Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, b < f (u n) :=
  Iff.rfl

/-- Unfolding characterization of `TauCeti.SeqLowerSemicontinuous`. -/
theorem seqLowerSemicontinuous_iff {f : X → β} :
    SeqLowerSemicontinuous f ↔
      ∀ x, ∀ b < f x, ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, b < f (u n) :=
  Iff.rfl

/-- Sequential lower semicontinuity on `univ` is global sequential lower semicontinuity. -/
@[simp]
theorem seqLowerSemicontinuousOn_univ_iff {f : X → β} :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f := by
  simp [SeqLowerSemicontinuousOn, SeqLowerSemicontinuous]

/-- Sequential lower semicontinuity of `s.domRestrict f` on the subspace `s` is equivalent to
`SeqLowerSemicontinuousOn f s`. -/
@[simp]
theorem seqLowerSemicontinuous_domRestrict_iff {f : X → β} {s : Set X} :
    SeqLowerSemicontinuous (s.domRestrict f) ↔ SeqLowerSemicontinuousOn f s := by
  refine ⟨fun hf x hx b hb u hu hux ↦ ?_, fun hf ⟨x, hx⟩ b hb u hux ↦ ?_⟩
  · refine hf ⟨x, hx⟩ b hb (u := fun n ↦ ⟨u n, hu n⟩) ?_
    exact IsInducing.subtypeVal.tendsto_nhds_iff.2 hux
  · exact hf x hx b hb (fun n ↦ (u n).2) ((continuous_subtype_val.tendsto _).comp hux)

/-- Every function is vacuously sequentially lower semicontinuous on the empty set. -/
@[simp]
theorem seqLowerSemicontinuousOn_empty (f : X → β) : SeqLowerSemicontinuousOn f ∅ := by
  simp [SeqLowerSemicontinuousOn]

/-- Constant functions are sequentially lower semicontinuous on any set. -/
@[simp]
theorem seqLowerSemicontinuousOn_const {s : Set X} {c : β} :
    SeqLowerSemicontinuousOn (fun _ ↦ c) s :=
  fun _ _ _ hb _ _ _ ↦ .of_forall fun _ ↦ hb

/-- Constant functions are sequentially lower semicontinuous. -/
@[simp]
theorem seqLowerSemicontinuous_const {c : β} :
    SeqLowerSemicontinuous (fun _ : X ↦ c) :=
  fun _ _ hb _ _ ↦ .of_forall fun _ ↦ hb

/-- Global sequential lower semicontinuity restricts to any subset. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousOn {f : X → β}
    (hf : SeqLowerSemicontinuous f) (s : Set X) : SeqLowerSemicontinuousOn f s :=
  fun x _ b hb _ _ hux ↦ hf x b hb hux

/-- Sequential lower semicontinuity is monotone under shrinking the domain set. -/
theorem SeqLowerSemicontinuousOn.mono {f : X → β} {s t : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) : SeqLowerSemicontinuousOn f t :=
  fun x hx b hb _ hu hux ↦ hf x (hts hx) b hb (fun n ↦ hts (hu n)) hux

/-- Sequential lower semicontinuity on `s` depends only on the values of the function on `s`. -/
theorem SeqLowerSemicontinuousOn.congr {f g : X → β} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (h : EqOn f g s) : SeqLowerSemicontinuousOn g s :=
  fun x hx b hb _ hu hux ↦
    (hf x hx b (h hx ▸ hb) hu hux).mono fun n hn ↦ h (hu n) ▸ hn

/-- Congruence of `SeqLowerSemicontinuousOn` under `EqOn`. -/
theorem seqLowerSemicontinuousOn_congr {f g : X → β} {s : Set X} (h : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

/-- Right composition with a sequentially continuous map preserves sequential lower
semicontinuity. -/
theorem SeqLowerSemicontinuous.comp_seqContinuous {Y : Type*} [TopologicalSpace Y]
    {f : X → β} {g : Y → X} (hf : SeqLowerSemicontinuous f) (hg : SeqContinuous g) :
    SeqLowerSemicontinuous (f ∘ g) :=
  fun y b hb _ huy ↦ hf (g y) b hb (hg huy)

/-- Right composition with a map continuous on `t` and mapping `t` into `s` preserves sequential
lower semicontinuity on sets. -/
theorem SeqLowerSemicontinuousOn.comp_continuousOn {Y : Type*} [TopologicalSpace Y]
    {f : X → β} {s : Set X} {g : Y → X} {t : Set Y}
    (hf : SeqLowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hgs : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun y hy b hb _ hu huy ↦
    hf (g y) (hgs hy) b hb (fun n ↦ hgs (hu n))
      ((hg y hy).tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ huy (.of_forall hu)))

/-- Topological lower semicontinuity implies sequential lower semicontinuity. -/
theorem _root_.LowerSemicontinuous.seqLowerSemicontinuous {f : X → β}
    (hf : LowerSemicontinuous f) : SeqLowerSemicontinuous f :=
  fun x b hb _ hux ↦ hux.eventually (hf x b hb)

/-- Topological lower semicontinuity on `s` implies sequential lower semicontinuity on `s`. -/
theorem _root_.LowerSemicontinuousOn.seqLowerSemicontinuousOn {f : X → β} {s : Set X}
    (hf : LowerSemicontinuousOn f s) : SeqLowerSemicontinuousOn f s :=
  fun x hx b hb _ hu hux ↦
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hux (.of_forall hu)).eventually
      (hf x hx b hb)

private theorem seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage_Ioi {f : X → β} :
    SeqLowerSemicontinuous f ↔ ∀ b, IsSeqClosed (f ⁻¹' Ioi b)ᶜ := by
  refine ⟨fun hf b u x hu hux hbx ↦ ?_, fun h x b hb u hux ↦ ?_⟩
  · obtain ⟨n, hn⟩ := (hf x b hbx hux).exists
    exact hu n hn
  · by_contra hnot
    obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop (not_eventually.1 hnot)
    exact h b hle (hux.comp hφ.tendsto_atTop) hb

/-- On a `SequentialSpace`, sequential and topological lower semicontinuity coincide for any
preordered codomain. -/
theorem seqLowerSemicontinuous_iff_lowerSemicontinuous [SequentialSpace X] {f : X → β} :
    SeqLowerSemicontinuous f ↔ LowerSemicontinuous f := by
  rw [seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage_Ioi,
    lowerSemicontinuous_iff_isOpen_preimage]
  simp_rw [isSeqClosed_iff_isClosed, isClosed_compl_iff]

/-- On a subset `s` whose subspace topology is a `SequentialSpace`, sequential and topological
lower semicontinuity on `s` coincide for any preordered codomain. -/
theorem seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn {s : Set X} [SequentialSpace s]
    {f : X → β} :
    SeqLowerSemicontinuousOn f s ↔ LowerSemicontinuousOn f s := by
  rw [← seqLowerSemicontinuous_domRestrict_iff, seqLowerSemicontinuous_iff_lowerSemicontinuous,
    lowerSemicontinuous_restrict_iff]

end Preorder

section LinearOrder

variable {X : Type*} [TopologicalSpace X] {β : Type*} [LinearOrder β]

/-- Into a linear order, `f` is sequentially lower semicontinuous if and only if every sublevel set
`f ⁻¹' Iic b` is sequentially closed. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage {f : X → β} :
    SeqLowerSemicontinuous f ↔ ∀ b, IsSeqClosed (f ⁻¹' Iic b) := by
  simp_rw [seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage_Ioi, ← preimage_compl, compl_Ioi]

/-- Sublevels of a sequentially lower semicontinuous function into a linear order are sequentially
closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_preimage {f : X → β}
    (hf : SeqLowerSemicontinuous f) (b : β) : IsSeqClosed (f ⁻¹' Iic b) :=
  seqLowerSemicontinuous_iff_isSeqClosed_preimage.1 hf b

/-- Relative sublevels `{x ∈ s | f x ≤ b}` of a sequentially lower semicontinuous function on a
sequentially closed set `s` are sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_sublevel {f : X → β} {s : Set X}
    (hs : IsSeqClosed s) (hf : SeqLowerSemicontinuousOn f s) (b : β) :
    IsSeqClosed {x ∈ s | f x ≤ b} := by
  intro u x hu hux
  have hxs : x ∈ s := hs (fun n ↦ (hu n).1) hux
  refine ⟨hxs, le_of_not_gt fun hbx ↦ ?_⟩
  obtain ⟨n, hn⟩ := (hf x hxs b hbx (fun n ↦ (hu n).1) hux).exists
  exact hn.not_ge (hu n).2

/-- On a sequentially closed set `s`, sequential lower semicontinuity into a linear order is
equivalent to sequential closedness of every relative sublevel `{x ∈ s | f x ≤ b}`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel {f : X → β} {s : Set X}
    (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b, IsSeqClosed {x ∈ s | f x ≤ b} := by
  refine ⟨fun hf ↦ hf.isSeqClosed_sublevel hs, fun h x _ b hb u hu hux ↦ ?_⟩
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, f (u n) ≤ b := by
    simpa only [not_eventually, not_lt] using hnot
  obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop hfreq
  exact hb.not_ge (h b (fun k ↦ ⟨hu (φ k), hle k⟩) (hux.comp hφ.tendsto_atTop)).2

/-- A sequentially continuous function into a linear order with `ClosedIicTopology` is sequentially
lower semicontinuous. -/
theorem _root_.SeqContinuous.seqLowerSemicontinuous [TopologicalSpace β] [ClosedIicTopology β]
    {f : X → β} (hf : SeqContinuous f) : SeqLowerSemicontinuous f :=
  fun _ _ hb _ hux ↦ (hf hux).eventually (Ioi_mem_nhds hb)

end LinearOrder

section CompleteLinearOrder

variable {X : Type*} [TopologicalSpace X] {β : Type*} [CompleteLinearOrder β]

/-- Into a complete linear order, sequential lower semicontinuity on `s` is equivalent to the
`liminf` inequality `f x ≤ liminf (f ∘ u) atTop` along sequences in `s` converging to `x ∈ s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf {f : X → β} {s : Set X} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        f x ≤ liminf (fun n ↦ f (u n)) atTop :=
  ⟨fun hf x hx _ hu hux ↦ by rw [le_liminf_iff]; exact fun b hb ↦ hf x hx b hb hu hux,
    fun hf x hx b hb _ hu hux ↦ eventually_lt_of_lt_liminf (hb.trans_le (hf x hx hu hux))⟩

/-- Along any sequence in `s` converging to `x ∈ s`, a sequentially lower semicontinuous function
into a complete linear order satisfies `f x ≤ liminf (f ∘ u) atTop`. -/
theorem SeqLowerSemicontinuousOn.le_liminf {f : X → β} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) {x : X} (hx : x ∈ s) {u : ℕ → X}
    (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (fun n ↦ f (u n)) atTop :=
  seqLowerSemicontinuousOn_iff_le_liminf.1 hf x hx hu hux

/-- Into a complete linear order, global sequential lower semicontinuity is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along every sequence `u` converging to `x`. -/
theorem seqLowerSemicontinuous_iff_le_liminf {f : X → β} :
    SeqLowerSemicontinuous f ↔
      ∀ x, ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → f x ≤ liminf (fun n ↦ f (u n)) atTop := by
  simp [← seqLowerSemicontinuousOn_univ_iff, seqLowerSemicontinuousOn_iff_le_liminf]

/-- Along any sequence converging to `x`, a sequentially lower semicontinuous function into a
complete linear order satisfies `f x ≤ liminf (f ∘ u) atTop`. -/
theorem SeqLowerSemicontinuous.le_liminf {f : X → β}
    (hf : SeqLowerSemicontinuous f) {x : X} {u : ℕ → X} (hux : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (fun n ↦ f (u n)) atTop :=
  seqLowerSemicontinuous_iff_le_liminf.1 hf x hux

end CompleteLinearOrder

section ClosedIciTopology

variable {X : Type*} [TopologicalSpace X]

/-- If `f` is sequentially lower semicontinuous on `s`, `u n ∈ s` converges to `x ∈ s`, and
`f (u n)` converges to `r` in a linear order with `ClosedIciTopology`, then `f x ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto {β : Type*} [LinearOrder β]
    [TopologicalSpace β] [ClosedIciTopology β] {f : X → β} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) {x : X} (hx : x ∈ s) {u : ℕ → X}
    (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x)) {r : β}
    (hfu : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) :
    f x ≤ r := by
  by_contra! hlt
  obtain ⟨a', ha', b', hb', hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
  obtain ⟨n, h₁, h₂⟩ :=
    ((hfu.eventually (Iio_mem_nhds ha')).and (hf x hx b' hb' hu hux)).exists
  exact lt_irrefl _ (hdisj _ h₁ _ h₂)

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto {β : Type*} [LinearOrder β]
    [TopologicalSpace β] [ClosedIciTopology β] {f : X → β}
    (hf : SeqLowerSemicontinuous f) {x : X} {u : ℕ → X} (hux : Tendsto u atTop (𝓝 x))
    {r : β} (hfu : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) :
    f x ≤ r :=
  (hf.seqLowerSemicontinuousOn univ).le_of_tendsto (mem_univ x) (fun _ ↦ mem_univ _) hux hfu

/-- The limit in `s` of a minimizing sequence for a sequentially lower semicontinuous function into
a conditionally complete linear order with `ClosedIciTopology` is a minimizer on `s`. -/
theorem SeqLowerSemicontinuousOn.isMinOn_of_tendsto_csInf {β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {f : X → β} {s : Set X} (hf : SeqLowerSemicontinuousOn f s) (hbdd : BddBelow (f '' s))
    {x : X} (hx : x ∈ s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x))
    (hfu : Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s)))) :
    IsMinOn f s x :=
  fun _ hy ↦ (hf.le_of_tendsto hx hu hux hfu).trans (csInf_le hbdd (mem_image_of_mem f hy))

end ClosedIciTopology

section Real

/-- Any sequence in `s` whose real values exceed `sInf (f '' s)` by at most `ε n → 0` is a
minimizing sequence: `f (u n) → sInf (f '' s)`. -/
theorem tendsto_csInf_of_le_csInf_add {X : Type*} {f : X → ℝ} {s : Set X}
    (hbdd : BddBelow (f '' s)) {u : ℕ → X} (hu : ∀ n, u n ∈ s) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hle : ∀ n, f (u n) ≤ sInf (f '' s) + ε n) :
    Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hbdd (mem_image_of_mem f (hu n))) hle
  simpa only [add_zero] using tendsto_const_nhds.add hε

/-- Every nonempty set on which a real-valued function is bounded below admits a minimizing
sequence `u n ∈ s` with `f (u n) < sInf (f '' s) + 1 / (n + 1)` and `f (u n) → sInf (f '' s)`. -/
theorem exists_seq_lt_csInf_add_one_div {X : Type*} {f : X → ℝ} {s : Set X}
    (hne : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧
      (∀ n, f (u n) < sInf (f '' s) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  have hex (n : ℕ) : ∃ x ∈ s, f x < sInf (f '' s) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hne.image f) (lt_add_of_pos_right _ (one_div_pos.2 n.cast_add_one_pos))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hex
  exact ⟨u, hu, hlt, tendsto_csInf_of_le_csInf_add hbdd hu
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) fun n ↦ (hlt n).le⟩

variable {X : Type*} [TopologicalSpace X]

/-- Coercing a real-valued function to `EReal` preserves `SeqLowerSemicontinuousOn`. -/
@[simp]
theorem seqLowerSemicontinuousOn_coe_ereal_iff {f : X → ℝ} {s : Set X} :
    SeqLowerSemicontinuousOn (fun x ↦ (f x : EReal)) s ↔ SeqLowerSemicontinuousOn f s := by
  refine ⟨fun hf x hx b hb u hu hux ↦ ?_, fun hf x hx b hb u hu hux ↦ ?_⟩
  · simpa only [EReal.coe_lt_coe_iff] using
      hf x hx (b : EReal) (EReal.coe_lt_coe_iff.2 hb) hu hux
  · induction b using EReal.rec with
    | bot => exact .of_forall fun n ↦ EReal.bot_lt_coe (f (u n))
    | coe r =>
      exact (hf x hx r (EReal.coe_lt_coe_iff.1 hb) hu hux).mono fun _ hn ↦
        EReal.coe_lt_coe_iff.2 hn
    | top => exact (not_top_lt hb).elim

/-- Coercing a real-valued function to `EReal` preserves `SeqLowerSemicontinuous`. -/
@[simp]
theorem seqLowerSemicontinuous_coe_ereal_iff {f : X → ℝ} :
    SeqLowerSemicontinuous (fun x ↦ (f x : EReal)) ↔ SeqLowerSemicontinuous f := by
  simp_rw [← seqLowerSemicontinuousOn_univ_iff, seqLowerSemicontinuousOn_coe_ereal_iff]

/-- A real-valued function is sequentially lower semicontinuous on `s` if and only if its coercion
to `EReal` satisfies the sequential `liminf` inequality along convergent sequences in `s`. -/
theorem seqLowerSemicontinuousOn_real_iff_le_liminf_ereal {f : X → ℝ} {s : Set X} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff, seqLowerSemicontinuousOn_iff_le_liminf]

/-- A sequentially lower semicontinuous real-valued function on a sequentially compact set is
bounded below. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact {f : X → ℝ} {s : Set X}
    (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    BddBelow (f '' s) := by
  by_contra hnot
  have hex (n : ℕ) : ∃ x ∈ s, f x < -(n : ℝ) := by
    by_contra! hge
    exact hnot ⟨-(n : ℝ), by rintro _ ⟨x, hx, rfl⟩; exact hge x hx⟩
  choose u hu hlt using hex
  obtain ⟨x, hx, φ, hφ, hux⟩ := hs hu
  have hev : ∀ᶠ k in atTop, f x - 1 < f (u (φ k)) :=
    hf x hx (f x - 1) (sub_one_lt _) (fun k ↦ hu (φ k)) hux
  have hle : ∀ᶠ k : ℕ in atTop, -(k : ℝ) ≤ f x - 1 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (-(f x - 1))] with k hk
    linarith
  obtain ⟨k, hk₁, hk₂⟩ := (hev.and hle).exists
  have hφk : (k : ℝ) ≤ φ k := Nat.cast_le.2 (hφ.id_le k)
  linarith [hlt (φ k)]

/-- **Sequential extreme value theorem.** A sequentially lower semicontinuous real-valued function
on a nonempty sequentially compact set attains its minimum. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn {f : X → ℝ} {s : Set X}
    (hne : s.Nonempty) (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x := by
  have hbdd := hf.bddBelow_of_isSeqCompact hs
  obtain ⟨u, hu, -, hfu⟩ := exists_seq_lt_csInf_add_one_div hne hbdd
  obtain ⟨x, hx, φ, hφ, hux⟩ := hs hu
  exact ⟨x, hx, hf.isMinOn_of_tendsto_csInf hbdd hx (fun n ↦ hu (φ n)) hux
    (hfu.comp hφ.tendsto_atTop)⟩

end Real

end TauCeti
