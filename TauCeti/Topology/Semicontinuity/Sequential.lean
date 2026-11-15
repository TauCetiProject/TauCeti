/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Sequential lower semicontinuity

A function `f : X → β` into a preorder is *sequentially lower semicontinuous* on `s : Set X`
(`TauCeti.SeqLowerSemicontinuousOn f s`) if every strict lower bound `b < f x` at `x ∈ s`
eventually persists along every sequence in `s` converging to `x`. Without topologies on `β` or
countability hypotheses on `X`, topological lower semicontinuity implies sequential lower
semicontinuity (`LowerSemicontinuousOn.seqLowerSemicontinuousOn`), and the two notions coincide
whenever the domain (or subspace `s`) is a `SequentialSpace`
(`TauCeti.seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn`). Sequential lower semicontinuity is
preserved under precomposition with sequentially continuous maps, monotone continuous
post-composition, addition, finite sums, finite suprema and infima, and indexed suprema.

Into any preorder, sequential lower semicontinuity is equivalent to sequential closedness of
`(f ⁻¹' Ioi b)ᶜ` (`TauCeti.seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage_Ioi`). When `β` is
a linear order, this becomes sequential closedness of all sublevels `f ⁻¹' Iic b`
(`TauCeti.seqLowerSemicontinuous_iff_isSeqClosed_preimage`), and on a sequentially closed set `s`
sequential closedness of `{x ∈ s | f x ≤ b}`
(`TauCeti.seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel`). When `β` is a complete linear order,
it is equivalent to the sequential `liminf` inequality `f x ≤ liminf (f ∘ u) atTop`
(`TauCeti.seqLowerSemicontinuousOn_iff_le_liminf`); for `f : X → ℝ`, coercion to `EReal` expresses
the same property without boundedness assumptions on `f ∘ u`
(`TauCeti.seqLowerSemicontinuousOn_real_iff_le_liminf_ereal`).

When `β` is a linear order with `ClosedIciTopology`, convergent images `f (u n) → r` along
`u n → x` in `s` satisfy `f x ≤ r` (`TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto`), so when `β`
is a conditionally complete linear order with `ClosedIciTopology` and `f '' s` is bounded below, any
sequential (or subsequential) limit in `s` of a minimizing sequence in `s` is a minimizer
(`TauCeti.SeqLowerSemicontinuousOn.isMinOn_of_tendsto_csInf`). Into a second-countable linear order
with `ClosedIicTopology`, sequential compactness yields attainment of the minimum on nonempty sets
(`TauCeti.SeqLowerSemicontinuousOn.exists_isMinOn`) and, when `β` is nonempty, boundedness from
below (`TauCeti.SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact`).

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

/-- If `f` is sequentially lower semicontinuous on `s`, `x ∈ s`, `b < f x`, and `u` is a sequence
in `s` converging to `x`, then eventually `b < f (u n)`. -/
theorem SeqLowerSemicontinuousOn.eventually_lt {f : X → β} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) {x : X} (hx : x ∈ s) {b : β} (hb : b < f x)
    {u : ℕ → X} (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x)) :
    ∀ᶠ n in atTop, b < f (u n) :=
  hf x hx b hb hu hux

/-- If `f` is sequentially lower semicontinuous, `b < f x`, and `u` converges to `x`, then
eventually `b < f (u n)`. -/
theorem SeqLowerSemicontinuous.eventually_lt {f : X → β}
    (hf : SeqLowerSemicontinuous f) {x : X} {b : β} (hb : b < f x)
    {u : ℕ → X} (hux : Tendsto u atTop (𝓝 x)) :
    ∀ᶠ n in atTop, b < f (u n) :=
  hf x b hb hux

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
  fun _ _ _ hb _ _ hux ↦ hf.eventually_lt hb hux

/-- Sequential lower semicontinuity is monotone under shrinking the domain set. -/
theorem SeqLowerSemicontinuousOn.mono {f : X → β} {s t : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) : SeqLowerSemicontinuousOn f t :=
  fun _ hx _ hb _ hu hux ↦ hf.eventually_lt (hts hx) hb (fun n ↦ hts (hu n)) hux

/-- Sequential lower semicontinuity on `s` depends only on the values of the function on `s`. -/
theorem SeqLowerSemicontinuousOn.congr {f g : X → β} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (h : EqOn f g s) : SeqLowerSemicontinuousOn g s :=
  fun _ hx _ hb _ hu hux ↦
    (hf.eventually_lt hx (h hx ▸ hb) hu hux).mono fun n hn ↦ h (hu n) ▸ hn

/-- Congruence of `SeqLowerSemicontinuousOn` under `EqOn`. -/
theorem seqLowerSemicontinuousOn_congr {f g : X → β} {s : Set X} (h : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

/-- Right composition with a sequentially continuous map preserves sequential lower
semicontinuity. -/
theorem SeqLowerSemicontinuous.comp_seqContinuous {Y : Type*} [TopologicalSpace Y]
    {f : X → β} {g : Y → X} (hf : SeqLowerSemicontinuous f) (hg : SeqContinuous g) :
    SeqLowerSemicontinuous (f ∘ g) :=
  fun _ _ hb _ huy ↦ hf.eventually_lt hb (hg huy)

/-- Right composition with a sequentially continuous map mapping `t` into `s` preserves sequential
lower semicontinuity on sets. -/
theorem SeqLowerSemicontinuousOn.comp_seqContinuous {Y : Type*} [TopologicalSpace Y]
    {f : X → β} {s : Set X} {g : Y → X} {t : Set Y}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqContinuous g) (hgs : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun _ hy _ hb _ hu huy ↦ hf.eventually_lt (hgs hy) hb (fun n ↦ hgs (hu n)) (hg huy)

/-- Right composition with a map continuous on `t` and mapping `t` into `s` preserves sequential
lower semicontinuity on sets. -/
theorem SeqLowerSemicontinuousOn.comp_continuousOn {Y : Type*} [TopologicalSpace Y]
    {f : X → β} {s : Set X} {g : Y → X} {t : Set Y}
    (hf : SeqLowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hgs : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun y hy _ hb _ hu huy ↦
    hf.eventually_lt (hgs hy) hb (fun n ↦ hgs (hu n))
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

private theorem seqLowerSemicontinuous_iff_lowerSemicontinuousAt_onePoint {f : X → β} :
    SeqLowerSemicontinuous f ↔
      ∀ (x : X) ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) →
        LowerSemicontinuousAt (fun z : OnePoint ℕ ↦ f (z.elim x u)) OnePoint.infty := by
  have hcoclosed : coclosedCompact ℕ = atTop := by
    rw [coclosedCompact_eq_cocompact, cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
  refine ⟨fun hf x u hux b hb ↦ ?_, fun hf x b hb u hux ↦ ?_⟩
  · rw [OnePoint.nhds_infty_eq, hcoclosed, eventually_sup, eventually_map, eventually_pure]
    exact ⟨hf.eventually_lt hb hux, hb⟩
  · have hev := hf x hux b hb
    rw [OnePoint.nhds_infty_eq, hcoclosed, eventually_sup, eventually_map] at hev
    exact hev.1

/-- Into a preorder, `f` is sequentially lower semicontinuous if and only if `(f ⁻¹' Ioi b)ᶜ` is
sequentially closed for every `b`. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage_Ioi {f : X → β} :
    SeqLowerSemicontinuous f ↔ ∀ b, IsSeqClosed (f ⁻¹' Ioi b)ᶜ := by
  refine ⟨fun hf b u x hu hux hbx ↦ ?_, fun h x b hb u hux ↦ ?_⟩
  · obtain ⟨n, hn⟩ := (hf.eventually_lt hbx hux).exists
    exact hu n hn
  · by_contra hnot
    obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop (not_eventually.1 hnot)
    exact h b hle (hux.comp hφ.tendsto_atTop) hb

/-- For a sequentially lower semicontinuous function into a preorder, `(f ⁻¹' Ioi b)ᶜ` is
sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_compl_preimage_Ioi {f : X → β}
    (hf : SeqLowerSemicontinuous f) (b : β) : IsSeqClosed (f ⁻¹' Ioi b)ᶜ :=
  seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage_Ioi.1 hf b

/-- On a sequentially closed set `s`, sequential lower semicontinuity into a preorder is equivalent
to sequential closedness of `s ∩ (f ⁻¹' Ioi b)ᶜ` for every `b`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_compl_preimage_Ioi {f : X → β} {s : Set X}
    (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b, IsSeqClosed (s ∩ (f ⁻¹' Ioi b)ᶜ) := by
  refine ⟨fun hf b u x hu hux ↦ ?_, fun h x _ b hb u hu hux ↦ ?_⟩
  · have hxs : x ∈ s := hs (fun n ↦ (hu n).1) hux
    refine ⟨hxs, fun hbx ↦ ?_⟩
    obtain ⟨n, hn⟩ := (hf.eventually_lt hxs hbx (fun n ↦ (hu n).1) hux).exists
    exact (hu n).2 hn
  · by_contra hnot
    obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop (not_eventually.1 hnot)
    exact (h b (fun k ↦ ⟨hu (φ k), hle k⟩) (hux.comp hφ.tendsto_atTop)).2 hb

/-- On a sequentially closed set `s`, `s ∩ (f ⁻¹' Ioi b)ᶜ` is sequentially closed when `f` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_compl_preimage_Ioi {f : X → β} {s : Set X}
    (hs : IsSeqClosed s) (hf : SeqLowerSemicontinuousOn f s) (b : β) :
    IsSeqClosed (s ∩ (f ⁻¹' Ioi b)ᶜ) :=
  (seqLowerSemicontinuousOn_iff_isSeqClosed_compl_preimage_Ioi hs).1 hf b

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

section Composition

variable {X : Type*} [TopologicalSpace X]
  {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
  {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [ClosedIicTopology δ]

/-- Left composition with a function continuous and monotone on `t` preserves sequential lower
semicontinuity on `s` whenever `f` maps `s` into `t`. -/
theorem _root_.ContinuousOn.comp_seqLowerSemicontinuousOn {g : γ → δ} {f : X → γ} {s : Set X}
    {t : Set γ} (hg : ContinuousOn g t) (hf : SeqLowerSemicontinuousOn f s)
    (h : MapsTo f s t) (gmon : MonotoneOn g t) :
    SeqLowerSemicontinuousOn (g ∘ f) s := by
  intro x hx y hy u hu hux
  by_cases! hl : ∃ l, l < f x
  · obtain ⟨U, hU, hUt⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hg (f x) (h hx) (Ioi_mem_nhds hy))
    obtain ⟨z, hzlt, hz⟩ := exists_Ioc_subset_of_mem_nhds hU hl
    filter_upwards [hf x hx z hzlt hu hux] with n hn
    by_cases hle : f (u n) ≤ f x
    · exact hUt ⟨hz ⟨hn, hle⟩, h (hu n)⟩
    · exact hy.trans_le (gmon (h hx) (h (hu n)) (le_of_not_ge hle))
  · exact .of_forall fun n ↦ hy.trans_le (gmon (h hx) (h (hu n)) (hl (f (u n))))

/-- Left composition with a function continuous and monotone on `t` preserves global sequential
lower semicontinuity whenever `f` takes values in `t`. -/
theorem _root_.ContinuousOn.comp_seqLowerSemicontinuous {g : γ → δ} {f : X → γ} {t : Set γ}
    (hg : ContinuousOn g t) (hf : SeqLowerSemicontinuous f) (h : ∀ x, f x ∈ t)
    (gmon : MonotoneOn g t) :
    SeqLowerSemicontinuous (g ∘ f) := by
  rw [← seqLowerSemicontinuousOn_univ_iff] at hf ⊢
  exact hg.comp_seqLowerSemicontinuousOn hf (fun x _ ↦ h x) gmon

/-- Left composition with a monotone continuous function preserves `SeqLowerSemicontinuousOn`. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuousOn {g : γ → δ} {f : X → γ} {s : Set X}
    (hg : Continuous g) (hf : SeqLowerSemicontinuousOn f s) (gmon : Monotone g) :
    SeqLowerSemicontinuousOn (g ∘ f) s :=
  hg.continuousOn.comp_seqLowerSemicontinuousOn hf (mapsTo_univ _ _) (gmon.monotoneOn _)

/-- Left composition with a monotone continuous function preserves `SeqLowerSemicontinuous`. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuous {g : γ → δ} {f : X → γ}
    (hg : Continuous g) (hf : SeqLowerSemicontinuous f) (gmon : Monotone g) :
    SeqLowerSemicontinuous (g ∘ f) :=
  hg.continuousOn.comp_seqLowerSemicontinuous hf (fun _ ↦ mem_univ _) (gmon.monotoneOn _)

end Composition

section Addition

variable {ι X γ : Type*} [TopologicalSpace X] [AddCommMonoid γ] [LinearOrder γ]
  [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ]

/-- The sum of two sequentially lower semicontinuous functions is sequentially lower semicontinuous,
assuming addition is continuous at `(f x, g x)` for every `x` (covering `EReal`). -/
theorem SeqLowerSemicontinuous.add' {f g : X → γ}
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuous fun z ↦ f z + g z := by
  rw [seqLowerSemicontinuous_iff_lowerSemicontinuousAt_onePoint] at hf hg ⊢
  exact fun x _ hux ↦ (hf x hux).add' (hg x hux) (hcont x)

/-- The sum of two functions sequentially lower semicontinuous on `s` is sequentially lower
semicontinuous on `s`, assuming addition is continuous at `(f x, g x)` for every `x ∈ s`
(covering `EReal`). -/
theorem SeqLowerSemicontinuousOn.add' {f g : X → γ} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuousOn (fun z ↦ f z + g z) s := by
  rw [← seqLowerSemicontinuous_domRestrict_iff] at hf hg ⊢
  exact hf.add' hg fun x ↦ hcont x.1 x.2

/-- Under `[ContinuousAdd γ]`, the sum of two sequentially lower semicontinuous functions is
sequentially lower semicontinuous. -/
theorem SeqLowerSemicontinuous.add [ContinuousAdd γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous fun z ↦ f z + g z :=
  hf.add' hg fun _ ↦ continuous_add.continuousAt

/-- Under `[ContinuousAdd γ]`, the sum of two functions sequentially lower semicontinuous on `s` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.add [ContinuousAdd γ] {f g : X → γ} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun z ↦ f z + g z) s :=
  hf.add' hg fun _ _ ↦ continuous_add.continuousAt

/-- Under `[ContinuousAdd γ]`, a finite sum of sequentially lower semicontinuous functions is
sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_sum [ContinuousAdd γ] {f : ι → X → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous fun z ↦ ∑ i ∈ a, f i z := by
  rw [seqLowerSemicontinuous_iff_lowerSemicontinuousAt_onePoint]
  exact fun x u hux ↦
    lowerSemicontinuousAt_sum (f := fun i (z : OnePoint ℕ) ↦ f i (z.elim x u)) fun i hi ↦
      seqLowerSemicontinuous_iff_lowerSemicontinuousAt_onePoint.1 (ha i hi) x hux

/-- Under `[ContinuousAdd γ]`, a finite sum of functions sequentially lower semicontinuous on `s` is
sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_sum [ContinuousAdd γ] {f : ι → X → γ} {a : Finset ι}
    {s : Set X} (ha : ∀ i ∈ a, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun z ↦ ∑ i ∈ a, f i z) s := by
  rw [← seqLowerSemicontinuous_domRestrict_iff]
  exact seqLowerSemicontinuous_sum fun i hi ↦
    seqLowerSemicontinuous_domRestrict_iff.2 (ha i hi)

end Addition

section LinearOrder

variable {X : Type*} [TopologicalSpace X] {β : Type*} [LinearOrder β]

/-- The pointwise supremum of two sequentially lower semicontinuous functions into a linear order is
sequentially lower semicontinuous. -/
theorem SeqLowerSemicontinuous.sup {f g : X → β}
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous fun x ↦ f x ⊔ g x := by
  rw [seqLowerSemicontinuous_iff_lowerSemicontinuousAt_onePoint] at hf hg ⊢
  exact fun x _ hux ↦ (hf x hux).sup (hg x hux)

/-- The pointwise supremum of two functions sequentially lower semicontinuous on `s` into a linear
order is sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.sup {f g : X → β} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s := by
  rw [← seqLowerSemicontinuous_domRestrict_iff] at hf hg ⊢
  exact hf.sup hg

/-- The pointwise infimum of two sequentially lower semicontinuous functions into a linear order is
sequentially lower semicontinuous. -/
theorem SeqLowerSemicontinuous.inf {f g : X → β}
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous fun x ↦ f x ⊓ g x := by
  rw [seqLowerSemicontinuous_iff_lowerSemicontinuousAt_onePoint] at hf hg ⊢
  exact fun x _ hux ↦ (hf x hux).inf (hg x hux)

/-- The pointwise infimum of two functions sequentially lower semicontinuous on `s` into a linear
order is sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.inf {f g : X → β} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊓ g x) s := by
  rw [← seqLowerSemicontinuous_domRestrict_iff] at hf hg ⊢
  exact hf.inf hg

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

/-- On a sequentially closed set `s`, sequential lower semicontinuity into a linear order is
equivalent to sequential closedness of every relative sublevel `{x ∈ s | f x ≤ b}`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel {f : X → β} {s : Set X}
    (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b, IsSeqClosed {x ∈ s | f x ≤ b} := by
  simp_rw [seqLowerSemicontinuousOn_iff_isSeqClosed_compl_preimage_Ioi hs, ← preimage_compl,
    compl_Ioi]
  rfl

/-- Relative sublevels `{x ∈ s | f x ≤ b}` of a sequentially lower semicontinuous function on a
sequentially closed set `s` are sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_sublevel {f : X → β} {s : Set X}
    (hs : IsSeqClosed s) (hf : SeqLowerSemicontinuousOn f s) (b : β) :
    IsSeqClosed {x ∈ s | f x ≤ b} :=
  (seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel hs).1 hf b

/-- A sequentially continuous function into a linear order with `ClosedIicTopology` is sequentially
lower semicontinuous. -/
theorem _root_.SeqContinuous.seqLowerSemicontinuous [TopologicalSpace β] [ClosedIicTopology β]
    {f : X → β} (hf : SeqContinuous f) : SeqLowerSemicontinuous f :=
  fun _ _ hb _ hux ↦ (hf hux).eventually (Ioi_mem_nhds hb)

end LinearOrder

section Supremum

variable {ι : Sort*} {X : Type*} [TopologicalSpace X]

/-- Pointwise conditionally complete supremum of sequentially lower semicontinuous functions bounded
above at every point is sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_ciSup {β : Type*} [ConditionallyCompleteLinearOrder β]
    {f : ι → X → β} (bdd : ∀ x, BddAbove (range fun i ↦ f i x))
    (h : ∀ i, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous fun x ↦ ⨆ i, f i x := by
  rw [seqLowerSemicontinuous_iff_lowerSemicontinuousAt_onePoint]
  exact fun x u hux ↦
    lowerSemicontinuousAt_ciSup (.of_forall fun z : OnePoint ℕ ↦ bdd (z.elim x u))
      fun i ↦ seqLowerSemicontinuous_iff_lowerSemicontinuousAt_onePoint.1 (h i) x hux

/-- Pointwise conditionally complete supremum on `s` of functions sequentially lower semicontinuous
on `s` and bounded above at every point of `s` is sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_ciSup {β : Type*} [ConditionallyCompleteLinearOrder β]
    {f : ι → X → β} {s : Set X} (bdd : ∀ x ∈ s, BddAbove (range fun i ↦ f i x))
    (h : ∀ i, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, f i x) s := by
  rw [← seqLowerSemicontinuous_domRestrict_iff]
  exact seqLowerSemicontinuous_ciSup (fun x ↦ bdd x.1 x.2)
    fun i ↦ seqLowerSemicontinuous_domRestrict_iff.2 (h i)

/-- Pointwise supremum of sequentially lower semicontinuous functions into a complete linear order
is sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_iSup {β : Type*} [CompleteLinearOrder β]
    {f : ι → X → β} (h : ∀ i, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous fun x ↦ ⨆ i, f i x :=
  seqLowerSemicontinuous_ciSup (by simp) h

/-- Pointwise supremum of functions sequentially lower semicontinuous on `s` into a complete linear
order is sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_iSup {β : Type*} [CompleteLinearOrder β]
    {f : ι → X → β} {s : Set X} (h : ∀ i, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, f i x) s :=
  seqLowerSemicontinuousOn_ciSup (by simp) h

/-- Bounded indexed supremum of sequentially lower semicontinuous functions into a complete linear
order is sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_biSup {β : Type*} [CompleteLinearOrder β] {p : ι → Prop}
    {f : ∀ i, p i → X → β} (h : ∀ i hi, SeqLowerSemicontinuous (f i hi)) :
    SeqLowerSemicontinuous fun x ↦ ⨆ (i) (hi), f i hi x :=
  seqLowerSemicontinuous_iSup fun i ↦ seqLowerSemicontinuous_iSup fun hi ↦ h i hi

/-- Bounded indexed supremum of functions sequentially lower semicontinuous on `s` into a complete
linear order is sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_biSup {β : Type*} [CompleteLinearOrder β] {p : ι → Prop}
    {f : ∀ i, p i → X → β} {s : Set X} (h : ∀ i hi, SeqLowerSemicontinuousOn (f i hi) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ (i) (hi), f i hi x) s :=
  seqLowerSemicontinuousOn_iSup fun i ↦ seqLowerSemicontinuousOn_iSup fun hi ↦ h i hi

end Supremum

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

/-- If `f` is sequentially lower semicontinuous on `s` into a conditionally complete linear order
with `ClosedIciTopology`, `f '' s` is bounded below, and `u` is a sequence in `s` converging to
`x ∈ s` with `f (u n) → sInf (f '' s)`, then `x` is a minimizer of `f` on `s`. -/
theorem SeqLowerSemicontinuousOn.isMinOn_of_tendsto_csInf {β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {f : X → β} {s : Set X} (hf : SeqLowerSemicontinuousOn f s) (hbdd : BddBelow (f '' s))
    {x : X} (hx : x ∈ s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x))
    (hfu : Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s)))) :
    IsMinOn f s x :=
  fun _ hy ↦ (hf.le_of_tendsto hx hu hux hfu).trans (csInf_le hbdd (mem_image_of_mem f hy))

end ClosedIciTopology

section SeqCompact

variable {X : Type*} [TopologicalSpace X] {β : Type*} [LinearOrder β] [TopologicalSpace β]
  [ClosedIicTopology β] [SecondCountableTopology β]

/-- **Sequential extreme value theorem.** A sequentially lower semicontinuous function into a
second-countable linear order with `ClosedIicTopology` attains its minimum on every nonempty
sequentially compact set. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn {f : X → β} {s : Set X}
    (hne : s.Nonempty) (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x := by
  by_contra! hno
  have hmem (x : X) (hx : x ∈ s) : f x ∈ ⋃ y ∈ s, Ioi (f y) := by
    obtain ⟨y, hys, hyx⟩ := by simpa only [IsMinOn, IsMinFilter, eventually_principal, not_forall,
      Classical.not_imp, not_le] using hno x hx
    exact mem_biUnion hys hyx
  obtain ⟨t, hts, htc, htu⟩ :=
    TopologicalSpace.isOpen_biUnion_countable s (fun y ↦ Ioi (f y)) fun _ _ ↦ isOpen_Ioi
  have htne : t.Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨y, hyt, -⟩ := mem_iUnion₂.1 (htu.symm ▸ hmem x₀ hx₀)
    exact ⟨y, hyt⟩
  obtain ⟨v, rfl⟩ := htc.exists_eq_range htne
  have hv (n : ℕ) : v n ∈ s := hts (mem_range_self n)
  have hex (n : ℕ) : ∃ w ∈ s, ∀ k ≤ n, f w ≤ f (v k) := by
    obtain ⟨j, -, hmin⟩ :=
      Finset.exists_min_image (Finset.range (n + 1)) (f ∘ v) Finset.nonempty_range_add_one
    exact ⟨v j, hv j, fun k hk ↦ hmin k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))⟩
  choose w hw hle using hex
  obtain ⟨x, hx, φ, hφ, hwx⟩ := hs hw
  obtain ⟨_, ⟨m, rfl⟩, hmx⟩ : ∃ y ∈ range v, f y < f x := by
    simpa only [← htu, mem_iUnion, mem_Ioi, exists_prop] using hmem x hx
  obtain ⟨k, hlt, hmk⟩ :=
    ((hf x hx (f (v m)) hmx (fun k ↦ hw (φ k)) hwx).and (eventually_ge_atTop m)).exists
  exact hlt.not_ge (hle (φ k) m (hmk.trans (hφ.id_le k)))

/-- A sequentially lower semicontinuous function into a nonempty second-countable linear order with
`ClosedIicTopology` is bounded below on every sequentially compact set. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact [Nonempty β] {f : X → β} {s : Set X}
    (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    BddBelow (f '' s) := by
  obtain rfl | hne := s.eq_empty_or_nonempty
  · simp
  · obtain ⟨_, -, hmin⟩ := hf.exists_isMinOn hne hs
    exact hmin.bddBelow

end SeqCompact

section Real

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

/-- Along any sequence in `s` converging to `x ∈ s`, a real-valued function sequentially lower
semicontinuous on `s` satisfies `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`. -/
theorem SeqLowerSemicontinuousOn.le_liminf_ereal {f : X → ℝ} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) {x : X} (hx : x ∈ s) {u : ℕ → X}
    (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x)) :
    (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop :=
  seqLowerSemicontinuousOn_real_iff_le_liminf_ereal.1 hf x hx hu hux

/-- A real-valued function is sequentially lower semicontinuous if and only if its coercion to
`EReal` satisfies the sequential `liminf` inequality along every convergent sequence. -/
theorem seqLowerSemicontinuous_real_iff_le_liminf_ereal {f : X → ℝ} :
    SeqLowerSemicontinuous f ↔
      ∀ x, ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuous_coe_ereal_iff, seqLowerSemicontinuous_iff_le_liminf]

/-- Along any sequence converging to `x`, a sequentially lower semicontinuous real-valued function
satisfies `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`. -/
theorem SeqLowerSemicontinuous.le_liminf_ereal {f : X → ℝ}
    (hf : SeqLowerSemicontinuous f) {x : X} {u : ℕ → X} (hux : Tendsto u atTop (𝓝 x)) :
    (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop :=
  seqLowerSemicontinuous_real_iff_le_liminf_ereal.1 hf x hux

end Real

end TauCeti
