/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences

/-!
# Sequential lower semicontinuity

`TauCeti.SeqLowerSemicontinuousOn f s` says that along every sequence of points of `s` converging
to a point `x ∈ s`, the values of `f` are eventually above every strict lower bound of `f x`. For
values in a complete linear order, such as `EReal`, this is the inequality
`f x ≤ liminf f (u n)` (`TauCeti.seqLowerSemicontinuousOn_iff_le_liminf`).

Lower semicontinuity implies sequential lower semicontinuity, and the two agree on Fréchet–Urysohn
spaces, in particular on first-countable spaces. They can differ for the weak topology of an
infinite-dimensional normed space, where the direct method of the calculus of variations runs
along weakly convergent minimizing sequences and only needs the sequential notion.

A sequence is minimizing for `f` on a set `t` when its values are eventually below every number
exceeding a value of `f` on `t`; for real values this holds when they converge to the infimum of
`f` on `t`, or tend to `-∞`. A limit in `s` of a minimizing sequence of points of `s` minimizes a
sequentially lower semicontinuous function on `t`
(`TauCeti.SeqLowerSemicontinuousOn.isMinOn_of_tendsto`).

## Main declarations

* `TauCeti.SeqLowerSemicontinuousOn`: sequential lower semicontinuity on a set.
* `LowerSemicontinuousOn.seqLowerSemicontinuousOn`: lower semicontinuity implies its sequential
  version; `TauCeti.seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn` is the converse on
  Fréchet–Urysohn spaces.
* `TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto`: the value at the limit is at most the limit
  of the values.
* `TauCeti.SeqLowerSemicontinuousOn.isMinOn_of_tendsto`: limits of minimizing sequences are
  minimizers.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {α β : Type*} [TopologicalSpace α]

/-- A function `f` is sequentially lower semicontinuous on `s` if, along every sequence of points
of `s` converging to a point `x ∈ s`, the values of `f` are eventually above every strict lower
bound of `f x`. -/
def SeqLowerSemicontinuousOn [Preorder β] (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃u : ℕ → α⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
    ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- Unfolding of `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem seqLowerSemicontinuousOn_iff [Preorder β] {f : α → β} {s : Set α} :
    SeqLowerSemicontinuousOn f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃u : ℕ → α⦄, (∀ n, u n ∈ s) →
      Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- In a complete linear order, sequential lower semicontinuity is the inequality
`f x ≤ liminf f (u n)` along every sequence in `s` converging to a point `x ∈ s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf [CompleteLinearOrder β] {f : α → β}
    {s : Set α} :
    SeqLowerSemicontinuousOn f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃u : ℕ → α⦄, (∀ n, u n ∈ s) →
      Tendsto u atTop (𝓝 x) → f x ≤ liminf (fun n ↦ f (u n)) atTop := by
  refine forall₂_congr fun _ _ ↦ forall₃_congr fun _ _ _ ↦ ?_
  exact (le_liminf_iff).symm

/-- A lower semicontinuous function is sequentially lower semicontinuous. -/
theorem _root_.LowerSemicontinuousOn.seqLowerSemicontinuousOn [Preorder β] {f : α → β}
    {s : Set α} (hf : LowerSemicontinuousOn f s) : SeqLowerSemicontinuousOn f s :=
  fun x hx _ hus hu y hy ↦ (tendsto_nhdsWithin_iff.2 ⟨hu, .of_forall hus⟩).eventually (hf x hx y hy)

namespace SeqLowerSemicontinuousOn

/-- Sequential lower semicontinuity passes to subsets. -/
theorem mono [Preorder β] {f : α → β} {s t : Set α} (hf : SeqLowerSemicontinuousOn f s)
    (hts : t ⊆ s) : SeqLowerSemicontinuousOn f t := fun _ hx _ hu hlim ↦
  hf (hts hx) (fun n ↦ hts (hu n)) hlim

/-- On a Fréchet–Urysohn space, sequential lower semicontinuity implies lower semicontinuity. -/
theorem lowerSemicontinuousOn [FrechetUrysohnSpace α] [Preorder β] {f : α → β} {s : Set α}
    (hf : SeqLowerSemicontinuousOn f s) : LowerSemicontinuousOn f s := by
  intro x hx y hy
  by_contra h
  -- `x` is a limit of points of `s` at which `f` is not above `y`.
  have hcl : x ∈ closure {x' | ¬y < f x' ∧ x' ∈ s} := by
    rw [mem_closure_iff_frequently]
    simp_rw [mem_ofPred_eq]
    rw [← frequently_nhdsWithin_iff]
    exact not_eventually.1 h
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  obtain ⟨n, hn⟩ := (hf hx (fun n ↦ (hu n).2) hlim y hy).exists
  exact (hu n).1 hn

variable [LinearOrder β] {f : α → β} {s : Set α} {x : α} {u : ℕ → α}

/-- If the values of a sequentially lower semicontinuous function along a sequence in `s`
converging to `x ∈ s` are eventually below every number exceeding `b`, that is, if their upper
limit is at most `b`, then `f x ≤ b`. -/
theorem le_of_forall_gt_eventually_lt (hf : SeqLowerSemicontinuousOn f s) (hx : x ∈ s)
    (hu : ∀ n, u n ∈ s) (hlim : Tendsto u atTop (𝓝 x)) {b : β}
    (hb : ∀ c > b, ∀ᶠ n in atTop, f (u n) < c) : f x ≤ b := by
  by_contra! hbx
  -- Some value `c = f (u n)` lies strictly between `b` and `f x`; the values along the sequence
  -- are then eventually both above and below `c`.
  obtain ⟨n, hbn, hnx⟩ := ((hf hx hu hlim b hbx).and (hb _ hbx)).exists
  obtain ⟨m, hm⟩ := ((hf hx hu hlim _ hnx).and (hb _ hbn)).exists
  exact lt_asymm hm.1 hm.2

/-- Along a sequence in `s` converging to `x ∈ s`, the value of a sequentially lower
semicontinuous function at `x` is at most the limit of its values. -/
theorem le_of_tendsto [TopologicalSpace β] [ClosedIciTopology β]
    (hf : SeqLowerSemicontinuousOn f s) (hx : x ∈ s) (hu : ∀ n, u n ∈ s)
    (hlim : Tendsto u atTop (𝓝 x)) {r : β} (hr : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) :
    f x ≤ r :=
  hf.le_of_forall_gt_eventually_lt hx hu hlim fun _ hc ↦ hr.eventually (Iio_mem_nhds hc)

/-- **Limits of minimizing sequences are minimizers.** If a sequence in `s` converges to a point
`x ∈ s` and is minimizing for `f` on `t`, that is, its values are eventually below every number
exceeding a value of `f` on `t`, then `x` minimizes `f` on `t`. -/
theorem isMinOn_of_tendsto (hf : SeqLowerSemicontinuousOn f s) (hx : x ∈ s)
    (hu : ∀ n, u n ∈ s) (hlim : Tendsto u atTop (𝓝 x)) {t : Set α}
    (hmin : ∀ v ∈ t, ∀ c > f v, ∀ᶠ n in atTop, f (u n) < c) : IsMinOn f t x :=
  isMinOn_iff.2 fun _ hv ↦ hf.le_of_forall_gt_eventually_lt hx hu hlim (hmin _ hv)

end SeqLowerSemicontinuousOn

/-- On a Fréchet–Urysohn space, for instance a first-countable space, sequential lower
semicontinuity and lower semicontinuity agree. -/
theorem seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn [FrechetUrysohnSpace α] [Preorder β]
    {f : α → β} {s : Set α} : SeqLowerSemicontinuousOn f s ↔ LowerSemicontinuousOn f s :=
  ⟨SeqLowerSemicontinuousOn.lowerSemicontinuousOn,
    LowerSemicontinuousOn.seqLowerSemicontinuousOn⟩

end TauCeti
