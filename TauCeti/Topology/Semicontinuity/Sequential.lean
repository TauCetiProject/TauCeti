/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Sequential lower semicontinuity

A function `f : X → β` from a topological space to a preordered type is *sequentially lower
semicontinuous* at `x` within `s` if every strict lower bound `y < f x` eventually holds along
every sequence in `s` converging to `x`.

This notion parallels `LowerSemicontinuousWithinAt` and recovers all standard sequential
formulations under minimal hypotheses on `β`:

* In any linear order, sequential lower semicontinuity is equivalent to sequential closedness of
  sublevel sets, so it agrees with topological lower semicontinuity on every sequential space
  (and on every subset whose subspace topology is sequential).
* In any complete linear order, it is equivalent to the `liminf` inequality
  `f x ≤ liminf (f ∘ u) atTop` along convergent sequences; for `f : X → ℝ` it is equivalent to
  the `EReal`-valued `liminf` inequality `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`,
  and when `f` is bounded below on `s` it is also equivalent to the finite-limit inequality
  `Tendsto (f ∘ u) atTop (𝓝 r) → f x ≤ r`.
* On a nonempty sequentially compact set, a sequentially lower semicontinuous function with values
  in a first-countable conditionally complete linear order (when bounded below) or in `ℝ` (with no
  lower-bound hypothesis) attains its minimum.

## Implementation notes

The four predicates (`SeqLowerSemicontinuousWithinAt`, `SeqLowerSemicontinuousAt`,
`SeqLowerSemicontinuousOn`, `SeqLowerSemicontinuous`) and the proof plans for their `liminf`,
finite-limit, monotone-composition, and additive stability lemmas parallel
`LowerSemicontinuousWithinAt` in `Mathlib.Topology.Semicontinuity.Basic`.
-/

public section

open Filter Function Set Topology

namespace TauCeti

section Preorder

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Preorder β]
  {f g : X → β} {s t : Set X} {x : X}

/-- A function `f : X → β` is sequentially lower semicontinuous within `s` at `x` if every strict
lower bound `y < f x` eventually holds along every sequence in `s` converging to `x`. -/
def SeqLowerSemicontinuousWithinAt (f : X → β) (s : Set X) (x : X) : Prop :=
  ∀ y < f x, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, y < f (u n)

/-- A function `f : X → β` is sequentially lower semicontinuous at `x` if every strict lower bound
`y < f x` eventually holds along every sequence converging to `x`. -/
def SeqLowerSemicontinuousAt (f : X → β) (x : X) : Prop :=
  ∀ y < f x, ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, y < f (u n)

/-- A function `f : X → β` is sequentially lower semicontinuous on `s` if it is sequentially lower
semicontinuous within `s` at each point of `s`. -/
def SeqLowerSemicontinuousOn (f : X → β) (s : Set X) : Prop :=
  ∀ x ∈ s, SeqLowerSemicontinuousWithinAt f s x

/-- A function `f : X → β` is sequentially lower semicontinuous if it is sequentially lower
semicontinuous at every point. -/
def SeqLowerSemicontinuous (f : X → β) : Prop :=
  ∀ x, SeqLowerSemicontinuousAt f x

/-- Defining characterization of `SeqLowerSemicontinuousWithinAt`. -/
theorem seqLowerSemicontinuousWithinAt_iff :
    SeqLowerSemicontinuousWithinAt f s x ↔
      ∀ y < f x, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Defining characterization of `SeqLowerSemicontinuousAt`. -/
theorem seqLowerSemicontinuousAt_iff :
    SeqLowerSemicontinuousAt f x ↔
      ∀ y < f x, ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Defining characterization of `SeqLowerSemicontinuousOn`. -/
theorem seqLowerSemicontinuousOn_iff :
    SeqLowerSemicontinuousOn f s ↔ ∀ x ∈ s, SeqLowerSemicontinuousWithinAt f s x :=
  Iff.rfl

/-- Defining characterization of `SeqLowerSemicontinuous`. -/
theorem seqLowerSemicontinuous_iff :
    SeqLowerSemicontinuous f ↔ ∀ x, SeqLowerSemicontinuousAt f x :=
  Iff.rfl

/-- Sequential lower semicontinuity within `univ` is sequential lower semicontinuity at the
point. -/
@[simp] theorem seqLowerSemicontinuousWithinAt_univ_iff :
    SeqLowerSemicontinuousWithinAt f univ x ↔ SeqLowerSemicontinuousAt f x := by
  simp [SeqLowerSemicontinuousWithinAt, SeqLowerSemicontinuousAt]

/-- Sequential lower semicontinuity on `univ` is global sequential lower semicontinuity. -/
@[simp] theorem seqLowerSemicontinuousOn_univ_iff :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f := by
  simp [SeqLowerSemicontinuousOn, SeqLowerSemicontinuous]

/-- Every function is sequentially lower semicontinuous on the empty set. -/
@[simp] theorem seqLowerSemicontinuousOn_empty : SeqLowerSemicontinuousOn f ∅ :=
  fun _ hx ↦ False.elim hx

/-- Every function is sequentially lower semicontinuous on a singleton. -/
@[simp] theorem seqLowerSemicontinuousOn_singleton (a : X) :
    SeqLowerSemicontinuousOn f {a} := by
  rintro x rfl y hy u hu _
  exact .of_forall fun n ↦ by simpa [mem_singleton_iff.mp (hu n)] using hy

/-- Constant functions are sequentially lower semicontinuous within any set. -/
@[simp] theorem seqLowerSemicontinuousWithinAt_const {c : β} :
    SeqLowerSemicontinuousWithinAt (fun _ : X ↦ c) s x :=
  fun _ hy _ _ _ ↦ .of_forall fun _ ↦ hy

/-- Constant functions are sequentially lower semicontinuous at any point. -/
@[simp] theorem seqLowerSemicontinuousAt_const {c : β} :
    SeqLowerSemicontinuousAt (fun _ : X ↦ c) x :=
  fun _ hy _ _ ↦ .of_forall fun _ ↦ hy

/-- Constant functions are sequentially lower semicontinuous on any set. -/
@[simp] theorem seqLowerSemicontinuousOn_const {c : β} :
    SeqLowerSemicontinuousOn (fun _ : X ↦ c) s :=
  fun _ _ ↦ seqLowerSemicontinuousWithinAt_const

/-- Constant functions are sequentially lower semicontinuous. -/
@[simp] theorem seqLowerSemicontinuous_const {c : β} :
    SeqLowerSemicontinuous (fun _ : X ↦ c) :=
  fun _ ↦ seqLowerSemicontinuousAt_const

/-- Sequential lower semicontinuity on `s` is equivalent to sequential lower semicontinuity of
the restriction to the subspace `s`. -/
@[simp] theorem seqLowerSemicontinuous_restrict_iff :
    SeqLowerSemicontinuous (s.domRestrict f) ↔ SeqLowerSemicontinuousOn f s := by
  refine ⟨fun h x hx y hy u hu hlim ↦ ?_, fun h ⟨x, hx⟩ y hy v hlim ↦ ?_⟩
  · let v : ℕ → s := fun n ↦ ⟨u n, hu n⟩
    have hv : Tendsto v atTop (𝓝 ⟨x, hx⟩) :=
      Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr hlim
    exact h ⟨x, hx⟩ y hy hv
  · exact h x hx y hy (fun n ↦ (v n).2) ((continuous_subtype_val.tendsto _).comp hlim)

/-- Sequential lower semicontinuity within a set is monotone in the set. -/
theorem SeqLowerSemicontinuousWithinAt.mono (hf : SeqLowerSemicontinuousWithinAt f s x)
    (hts : t ⊆ s) : SeqLowerSemicontinuousWithinAt f t x :=
  fun y hy _ hu hlim ↦ hf y hy (fun n ↦ hts (hu n)) hlim

/-- Sequential lower semicontinuity at `x` implies sequential lower semicontinuity within any
set at `x`. -/
theorem SeqLowerSemicontinuousAt.seqLowerSemicontinuousWithinAt
    (hf : SeqLowerSemicontinuousAt f x) (s : Set X) :
    SeqLowerSemicontinuousWithinAt f s x :=
  fun y hy _ _ hlim ↦ hf y hy hlim

/-- Sequential lower semicontinuity on `s` gives sequential lower semicontinuity within `s` at
every point of `s`. -/
theorem SeqLowerSemicontinuousOn.seqLowerSemicontinuousWithinAt
    (hf : SeqLowerSemicontinuousOn f s) (hx : x ∈ s) :
    SeqLowerSemicontinuousWithinAt f s x :=
  hf x hx

/-- Sequential lower semicontinuity on a set is inherited by subsets. -/
theorem SeqLowerSemicontinuousOn.mono (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) :
    SeqLowerSemicontinuousOn f t :=
  fun x hx ↦ (hf x (hts hx)).mono hts

/-- Global sequential lower semicontinuity implies sequential lower semicontinuity at every
point. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousAt
    (hf : SeqLowerSemicontinuous f) (x : X) : SeqLowerSemicontinuousAt f x :=
  hf x

/-- Global sequential lower semicontinuity implies sequential lower semicontinuity within any set
at any point. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousWithinAt
    (hf : SeqLowerSemicontinuous f) (s : Set X) (x : X) :
    SeqLowerSemicontinuousWithinAt f s x :=
  (hf x).seqLowerSemicontinuousWithinAt s

/-- Global sequential lower semicontinuity implies sequential lower semicontinuity on any set. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousOn
    (hf : SeqLowerSemicontinuous f) (s : Set X) : SeqLowerSemicontinuousOn f s :=
  fun x _ ↦ hf.seqLowerSemicontinuousWithinAt s x

/-- Sequential lower semicontinuity on `s` depends only on the values of the function on `s`. -/
theorem seqLowerSemicontinuousOn_congr (h : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s := by
  refine ⟨fun hf x hx y hy u hu hlim ↦ ?_, fun hg x hx y hy u hu hlim ↦ ?_⟩
  · rw [← h hx] at hy
    exact (hf x hx y hy hu hlim).mono fun n hn ↦ h (hu n) ▸ hn
  · rw [h hx] at hy
    exact (hg x hx y hy hu hlim).mono fun n hn ↦ h (hu n) ▸ hn

/-- Precomposing a sequentially lower semicontinuous function with a sequentially continuous map
preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.comp_seqContinuous {h : Y → X}
    (hf : SeqLowerSemicontinuous f) (hh : SeqContinuous h) :
    SeqLowerSemicontinuous (f ∘ h) :=
  fun y b hb _ hu ↦ hf (h y) b hb (hh hu)

/-- Precomposing a sequentially lower semicontinuous function on `s` with a map continuous on `q`
mapping `q` into `s` preserves sequential lower semicontinuity on `q`. -/
theorem SeqLowerSemicontinuousOn.comp_continuousOn {h : Y → X} {q : Set Y}
    (hf : SeqLowerSemicontinuousOn f s) (hh : ContinuousOn h q) (hqs : MapsTo h q s) :
    SeqLowerSemicontinuousOn (f ∘ h) q := by
  intro y hy b hb u hu hlim
  have hnhds : Tendsto u atTop (𝓝[q] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, .of_forall hu⟩
  exact hf (h y) (hqs hy) b hb (fun n ↦ hqs (hu n)) ((hh y hy).tendsto.comp hnhds)

/-- Topological lower semicontinuity within `s` at `x` implies sequential lower semicontinuity
within `s` at `x`. -/
theorem _root_.LowerSemicontinuousWithinAt.seqLowerSemicontinuousWithinAt
    (hf : LowerSemicontinuousWithinAt f s x) : SeqLowerSemicontinuousWithinAt f s x :=
  fun y hy _ hu hlim ↦
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, .of_forall hu⟩).eventually (hf y hy)

/-- Topological lower semicontinuity at `x` implies sequential lower semicontinuity at `x`. -/
theorem _root_.LowerSemicontinuousAt.seqLowerSemicontinuousAt
    (hf : LowerSemicontinuousAt f x) : SeqLowerSemicontinuousAt f x :=
  fun y hy _ hlim ↦ hlim.eventually (hf y hy)

/-- Topological lower semicontinuity on `s` implies sequential lower semicontinuity on `s`. -/
theorem _root_.LowerSemicontinuousOn.seqLowerSemicontinuousOn
    (hf : LowerSemicontinuousOn f s) : SeqLowerSemicontinuousOn f s :=
  fun _ hx ↦ (hf.lowerSemicontinuousWithinAt hx).seqLowerSemicontinuousWithinAt

/-- Topological lower semicontinuity implies sequential lower semicontinuity. -/
theorem _root_.LowerSemicontinuous.seqLowerSemicontinuous
    (hf : LowerSemicontinuous f) : SeqLowerSemicontinuous f :=
  fun x ↦ (hf.lowerSemicontinuousAt x).seqLowerSemicontinuousAt

end Preorder

section LinearOrder

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] {f g : X → β} {s : Set X} {x : X}

/-- Pointwise maximum preserves sequential lower semicontinuity within a set. -/
theorem SeqLowerSemicontinuousWithinAt.max (hf : SeqLowerSemicontinuousWithinAt f s x)
    (hg : SeqLowerSemicontinuousWithinAt g s x) :
    SeqLowerSemicontinuousWithinAt (fun z ↦ max (f z) (g z)) s x := by
  intro y hy u hu hlim
  rcases lt_max_iff.mp hy with hfy | hgy
  · exact (hf y hfy hu hlim).mono fun _ hn ↦ lt_max_of_lt_left hn
  · exact (hg y hgy hu hlim).mono fun _ hn ↦ lt_max_of_lt_right hn

/-- Pointwise maximum preserves sequential lower semicontinuity on a set. -/
theorem SeqLowerSemicontinuousOn.max (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun z ↦ max (f z) (g z)) s :=
  fun x hx ↦ (hf x hx).max (hg x hx)

/-- Pointwise minimum preserves sequential lower semicontinuity within a set. -/
theorem SeqLowerSemicontinuousWithinAt.min (hf : SeqLowerSemicontinuousWithinAt f s x)
    (hg : SeqLowerSemicontinuousWithinAt g s x) :
    SeqLowerSemicontinuousWithinAt (fun z ↦ min (f z) (g z)) s x := by
  intro y hy u hu hlim
  obtain ⟨hfy, hgy⟩ := lt_min_iff.mp hy
  exact ((hf y hfy hu hlim).and (hg y hgy hu hlim)).mono fun _ hn ↦ lt_min hn.1 hn.2

/-- Pointwise minimum preserves sequential lower semicontinuity on a set. -/
theorem SeqLowerSemicontinuousOn.min (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun z ↦ min (f z) (g z)) s :=
  fun x hx ↦ (hf x hx).min (hg x hx)

/-- In a linear order, sequential lower semicontinuity is equivalent to sequential closedness of
every sublevel set `f ⁻¹' Iic b`. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage :
    SeqLowerSemicontinuous f ↔ ∀ b, IsSeqClosed (f ⁻¹' Iic b) := by
  refine ⟨fun hf b u x hu hlim ↦ ?_, fun h x y hy u hlim ↦ ?_⟩
  · change f x ≤ b
    by_contra! hbx
    obtain ⟨n, hn⟩ := (hf x b hbx hlim).exists
    exact not_le_of_gt hn (hu n)
  · by_contra hnot
    have hfreq : ∃ᶠ n in atTop, f (u n) ≤ y := by
      simpa only [not_eventually, not_lt] using hnot
    obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop hfreq
    exact not_le_of_gt hy (h y hle (hlim.comp hφ.tendsto_atTop))

/-- Every sublevel set of a sequentially lower semicontinuous function into a linear order is
sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_preimage
    (hf : SeqLowerSemicontinuous f) (b : β) : IsSeqClosed (f ⁻¹' Iic b) :=
  seqLowerSemicontinuous_iff_isSeqClosed_preimage.mp hf b

/-- On a sequentially closed set, every relative sublevel `{x ∈ s | f x ≤ b}` of a sequentially
lower semicontinuous function is sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_sublevel
    (hf : SeqLowerSemicontinuousOn f s) (hs : IsSeqClosed s) (b : β) :
    IsSeqClosed {x ∈ s | f x ≤ b} := by
  intro u x hu hlim
  have hxs : x ∈ s := hs (fun n ↦ (hu n).1) hlim
  refine ⟨hxs, ?_⟩
  by_contra! hbx
  obtain ⟨n, hn⟩ := (hf x hxs b hbx (fun n ↦ (hu n).1) hlim).exists
  exact not_le_of_gt hn (hu n).2

/-- On a sequentially closed set, sequential lower semicontinuity is equivalent to sequential
closedness of every relative sublevel `{x ∈ s | f x ≤ b}`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b, IsSeqClosed {x ∈ s | f x ≤ b} := by
  refine ⟨fun hf ↦ hf.isSeqClosed_sublevel hs, fun h x _ y hy u hu hlim ↦ ?_⟩
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, f (u n) ≤ y := by
    simpa only [not_eventually, not_lt] using hnot
  obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop hfreq
  exact not_le_of_gt hy ((h y (fun n ↦ ⟨hu (φ n), hle n⟩) (hlim.comp hφ.tendsto_atTop)).2)

/-- On a sequential space, sequential lower semicontinuity implies topological lower
semicontinuity. -/
theorem SeqLowerSemicontinuous.lowerSemicontinuous [SequentialSpace X]
    (hf : SeqLowerSemicontinuous f) : LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_preimage.mpr fun b ↦ (hf.isSeqClosed_preimage b).isClosed

/-- On a sequential space, topological and sequential lower semicontinuity agree. -/
theorem lowerSemicontinuous_iff_seqLowerSemicontinuous [SequentialSpace X] :
    LowerSemicontinuous f ↔ SeqLowerSemicontinuous f :=
  ⟨LowerSemicontinuous.seqLowerSemicontinuous, SeqLowerSemicontinuous.lowerSemicontinuous⟩

/-- On a subset whose subspace topology is sequential, sequential lower semicontinuity implies
topological lower semicontinuity. -/
theorem SeqLowerSemicontinuousOn.lowerSemicontinuousOn [SequentialSpace s]
    (hf : SeqLowerSemicontinuousOn f s) : LowerSemicontinuousOn f s :=
  lowerSemicontinuous_restrict_iff.mp
    (seqLowerSemicontinuous_restrict_iff.mpr hf).lowerSemicontinuous

/-- On a subset whose subspace topology is sequential, topological and sequential lower
semicontinuity agree. -/
theorem lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn [SequentialSpace s] :
    LowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn f s :=
  ⟨LowerSemicontinuousOn.seqLowerSemicontinuousOn, SeqLowerSemicontinuousOn.lowerSemicontinuousOn⟩

end LinearOrder

section CompleteLinearOrder

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β]
  {f : X → β} {s : Set X} {x : X}

/-- In a complete linear order, sequential lower semicontinuity within `s` at `x` is equivalent
to `f x ≤ liminf (f ∘ u) atTop` along every sequence in `s` converging to `x`. -/
theorem seqLowerSemicontinuousWithinAt_iff_le_liminf :
    SeqLowerSemicontinuousWithinAt f s x ↔
      ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  refine ⟨fun hf u hu hlim ↦ ?_, fun hf y hy u hu hlim ↦
    eventually_lt_of_lt_liminf (hy.trans_le (hf hu hlim))⟩
  by_contra! hlt
  obtain ⟨z, ltz, y, ylt, hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
  refine ltz.not_ge (le_liminf_of_le (by isBoundedDefault) ?_)
  exact (hf y ylt hu hlim).mono fun _ h₂ ↦ le_of_not_gt fun h₃ ↦ (hdisj _ h₃ _ h₂).false

alias ⟨SeqLowerSemicontinuousWithinAt.le_liminf, _⟩ :=
  seqLowerSemicontinuousWithinAt_iff_le_liminf

/-- In a complete linear order, sequential lower semicontinuity at `x` is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along every sequence converging to `x`. -/
theorem seqLowerSemicontinuousAt_iff_le_liminf :
    SeqLowerSemicontinuousAt f x ↔
      ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  rw [← seqLowerSemicontinuousWithinAt_univ_iff, seqLowerSemicontinuousWithinAt_iff_le_liminf]
  simp

alias ⟨SeqLowerSemicontinuousAt.le_liminf, _⟩ := seqLowerSemicontinuousAt_iff_le_liminf

/-- In a complete linear order, sequential lower semicontinuity on `s` is equivalent to the
`liminf` inequality along every sequence in `s` converging to a point of `s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        f x ≤ liminf (f ∘ u) atTop := by
  simp only [seqLowerSemicontinuousOn_iff, seqLowerSemicontinuousWithinAt_iff_le_liminf]

alias ⟨SeqLowerSemicontinuousOn.le_liminf, _⟩ := seqLowerSemicontinuousOn_iff_le_liminf

/-- In a complete linear order, global sequential lower semicontinuity is equivalent to the
`liminf` inequality along every convergent sequence. -/
theorem seqLowerSemicontinuous_iff_le_liminf :
    SeqLowerSemicontinuous f ↔
      ∀ (x : X) ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  simp only [seqLowerSemicontinuous_iff, seqLowerSemicontinuousAt_iff_le_liminf]

alias ⟨SeqLowerSemicontinuous.le_liminf, _⟩ := seqLowerSemicontinuous_iff_le_liminf

end CompleteLinearOrder

section ClosedIciTopology

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] [TopologicalSpace β]
  [ClosedIciTopology β] {f : X → β} {s : Set X} {x : X} {r : β}

/-- Along a sequence in `s` converging to `x` whose values under `f` converge to `r`, sequential
lower semicontinuity within `s` at `x` gives `f x ≤ r`. -/
theorem SeqLowerSemicontinuousWithinAt.le_of_tendsto
    (hf : SeqLowerSemicontinuousWithinAt f s x) {u : ℕ → X}
    (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x)) (hfr : Tendsto (f ∘ u) atTop (𝓝 r)) :
    f x ≤ r := by
  by_contra! hlt
  obtain ⟨z, rltz, y, yltfx, hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
  obtain ⟨n, hn₁, hn₂⟩ := ((hfr.eventually (Iio_mem_nhds rltz)).and (hf y yltfx hu hux)).exists
  exact (hdisj _ hn₁ _ hn₂).false

/-- Along a sequence converging to `x` whose values under `f` converge to `r`, sequential lower
semicontinuity at `x` gives `f x ≤ r`. -/
theorem SeqLowerSemicontinuousAt.le_of_tendsto
    (hf : SeqLowerSemicontinuousAt f x) {u : ℕ → X}
    (hux : Tendsto u atTop (𝓝 x)) (hfr : Tendsto (f ∘ u) atTop (𝓝 r)) :
    f x ≤ r :=
  (hf.seqLowerSemicontinuousWithinAt univ).le_of_tendsto (fun _ ↦ mem_univ _) hux hfr

/-- Along a sequence in `s` converging to `x ∈ s` whose values under `f` converge to `r`,
sequential lower semicontinuity on `s` gives `f x ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto
    (hf : SeqLowerSemicontinuousOn f s) (hx : x ∈ s) {u : ℕ → X}
    (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x)) (hfr : Tendsto (f ∘ u) atTop (𝓝 r)) :
    f x ≤ r :=
  (hf x hx).le_of_tendsto hu hux hfr

/-- Along a sequence converging to `x` whose values under `f` converge to `r`, global sequential
lower semicontinuity gives `f x ≤ r`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto
    (hf : SeqLowerSemicontinuous f) {u : ℕ → X}
    (hux : Tendsto u atTop (𝓝 x)) (hfr : Tendsto (f ∘ u) atTop (𝓝 r)) :
    f x ≤ r :=
  (hf x).le_of_tendsto hux hfr

end ClosedIciTopology

section OrderTopology

variable {X β δ : Type*} [TopologicalSpace X]
  [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
  [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
  {f : X → β} {s : Set X} {x : X}

/-- A sequentially continuous function into an ordered topological space is sequentially lower
semicontinuous. -/
theorem _root_.SeqContinuous.seqLowerSemicontinuous (hf : SeqContinuous f) :
    SeqLowerSemicontinuous f :=
  fun _ _ hy _ hlim ↦ (hf hlim).eventually (Ioi_mem_nhds hy)

/-- Continuous functions within `s` at `x` are sequentially lower semicontinuous within `s` at
`x`. -/
theorem _root_.ContinuousWithinAt.seqLowerSemicontinuousWithinAt
    (hf : ContinuousWithinAt f s x) : SeqLowerSemicontinuousWithinAt f s x :=
  hf.lowerSemicontinuousWithinAt.seqLowerSemicontinuousWithinAt

/-- Continuous functions at `x` are sequentially lower semicontinuous at `x`. -/
theorem _root_.ContinuousAt.seqLowerSemicontinuousAt
    (hf : ContinuousAt f x) : SeqLowerSemicontinuousAt f x :=
  hf.lowerSemicontinuousAt.seqLowerSemicontinuousAt

/-- Continuous functions on `s` are sequentially lower semicontinuous on `s`. -/
theorem _root_.ContinuousOn.seqLowerSemicontinuousOn
    (hf : ContinuousOn f s) : SeqLowerSemicontinuousOn f s :=
  hf.lowerSemicontinuousOn.seqLowerSemicontinuousOn

/-- Continuous functions are sequentially lower semicontinuous. -/
theorem _root_.Continuous.seqLowerSemicontinuous
    (hf : Continuous f) : SeqLowerSemicontinuous f :=
  hf.lowerSemicontinuous.seqLowerSemicontinuous

/-- Left-composing a sequentially lower semicontinuous function with a monotone function
continuous at `f x` preserves sequential lower semicontinuity within `s` at `x`. -/
theorem _root_.ContinuousAt.comp_seqLowerSemicontinuousWithinAt {g : β → δ}
    (hg : ContinuousAt g (f x)) (hf : SeqLowerSemicontinuousWithinAt f s x)
    (gmon : Monotone g) : SeqLowerSemicontinuousWithinAt (g ∘ f) s x := by
  intro y hy u hu hlim
  by_cases! h : ∃ l, l < f x
  · obtain ⟨z, zlt, hz⟩ : ∃ z < f x, Ioc z (f x) ⊆ g ⁻¹' Ioi y :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    refine (hf z zlt hu hlim).mono fun n hn ↦ ?_
    calc
      y < g (min (f x) (f (u n))) := hz (by simp [zlt, hn])
      _ ≤ g (f (u n)) := gmon (min_le_right _ _)
  · exact .of_forall fun n ↦ hy.trans_le (gmon (h (f (u n))))

/-- Left-composing a sequentially lower semicontinuous function with a continuous monotone map
preserves sequential lower semicontinuity on `s`. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuousOn {g : β → δ}
    (hg : Continuous g) (hf : SeqLowerSemicontinuousOn f s) (gmon : Monotone g) :
    SeqLowerSemicontinuousOn (g ∘ f) s :=
  fun x hx ↦ hg.continuousAt.comp_seqLowerSemicontinuousWithinAt (hf x hx) gmon

/-- Left-composing a sequentially lower semicontinuous function with a continuous monotone map
preserves global sequential lower semicontinuity. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuous {g : β → δ}
    (hg : Continuous g) (hf : SeqLowerSemicontinuous f) (gmon : Monotone g) :
    SeqLowerSemicontinuous (g ∘ f) := by
  rw [← seqLowerSemicontinuousOn_univ_iff] at hf ⊢
  exact hg.comp_seqLowerSemicontinuousOn hf gmon

end OrderTopology

section Algebra

variable {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}

/-- In a densely ordered commutative group, the sum of two sequentially lower semicontinuous
functions within `s` at `x` is sequentially lower semicontinuous within `s` at `x`. -/
theorem SeqLowerSemicontinuousWithinAt.add {β : Type*} [AddCommGroup β] [LinearOrder β]
    [IsOrderedAddMonoid β] [DenselyOrdered β] {f g : X → β}
    (hf : SeqLowerSemicontinuousWithinAt f s x)
    (hg : SeqLowerSemicontinuousWithinAt g s x) :
    SeqLowerSemicontinuousWithinAt (fun z ↦ f z + g z) s x := by
  intro y hy u hu hlim
  obtain ⟨z₁, hz₁_gt, hz₁_lt⟩ := exists_between (sub_lt_iff_lt_add.mpr hy)
  have hz₂_lt : y - z₁ < g x := sub_lt_comm.mp hz₁_gt
  refine ((hf z₁ hz₁_lt hu hlim).and (hg (y - z₁) hz₂_lt hu hlim)).mono fun n ⟨h₁, h₂⟩ ↦ ?_
  calc
    y = z₁ + (y - z₁) := (add_sub_cancel _ _).symm
    _ < f (u n) + g (u n) := add_lt_add h₁ h₂

/-- In a densely ordered commutative group, the sum of two sequentially lower semicontinuous
functions at `x` is sequentially lower semicontinuous at `x`. -/
theorem SeqLowerSemicontinuousAt.add {β : Type*} [AddCommGroup β] [LinearOrder β]
    [IsOrderedAddMonoid β] [DenselyOrdered β] {f g : X → β}
    (hf : SeqLowerSemicontinuousAt f x) (hg : SeqLowerSemicontinuousAt g x) :
    SeqLowerSemicontinuousAt (fun z ↦ f z + g z) x := by
  rw [← seqLowerSemicontinuousWithinAt_univ_iff] at hf hg ⊢
  exact hf.add hg

/-- In a densely ordered commutative group, the sum of two sequentially lower semicontinuous
functions on `s` is sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.add {β : Type*} [AddCommGroup β] [LinearOrder β]
    [IsOrderedAddMonoid β] [DenselyOrdered β] {f g : X → β}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun z ↦ f z + g z) s :=
  fun x hx ↦ (hf x hx).add (hg x hx)

/-- In a densely ordered commutative group, the sum of two sequentially lower semicontinuous
functions is sequentially lower semicontinuous. -/
theorem SeqLowerSemicontinuous.add {β : Type*} [AddCommGroup β] [LinearOrder β]
    [IsOrderedAddMonoid β] [DenselyOrdered β] {f g : X → β}
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous (fun z ↦ f z + g z) :=
  fun x ↦ (hf x).add (hg x)

/-- Positive left scaling preserves sequential lower semicontinuity within `s` at `x`. -/
theorem SeqLowerSemicontinuousWithinAt.const_mul {β : Type*} [Semifield β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : X → β} (hf : SeqLowerSemicontinuousWithinAt f s x)
    {c : β} (hc : 0 < c) : SeqLowerSemicontinuousWithinAt (fun z ↦ c * f z) s x :=
  fun y hy _ hu hlim ↦
    (hf (y / c) ((div_lt_iff₀' hc).mpr hy) hu hlim).mono fun _ hn ↦ (div_lt_iff₀' hc).mp hn

/-- Positive left scaling preserves sequential lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.const_mul {β : Type*} [Semifield β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : X → β} (hf : SeqLowerSemicontinuousOn f s)
    {c : β} (hc : 0 < c) : SeqLowerSemicontinuousOn (fun z ↦ c * f z) s :=
  fun x hx ↦ (hf x hx).const_mul hc

/-- Positive left scaling preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.const_mul {β : Type*} [Semifield β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : X → β} (hf : SeqLowerSemicontinuous f)
    {c : β} (hc : 0 < c) : SeqLowerSemicontinuous (fun z ↦ c * f z) :=
  fun x ↦ seqLowerSemicontinuousWithinAt_univ_iff.mp
    ((seqLowerSemicontinuousWithinAt_univ_iff.mpr (hf x)).const_mul hc)

/-- Positive right scaling preserves sequential lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.mul_const {β : Type*} [Semifield β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : X → β} (hf : SeqLowerSemicontinuousOn f s)
    {c : β} (hc : 0 < c) : SeqLowerSemicontinuousOn (fun z ↦ f z * c) s := by
  simpa only [mul_comm] using hf.const_mul hc

/-- Dividing by a positive constant preserves sequential lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.div_const {β : Type*} [Semifield β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : X → β} (hf : SeqLowerSemicontinuousOn f s)
    {c : β} (hc : 0 < c) : SeqLowerSemicontinuousOn (fun z ↦ f z / c) s := by
  simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.mpr hc)

end Algebra

section RealAndEReal

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X} {x : X}

/-- Coercing a real-valued function to `EReal` does not change sequential lower semicontinuity
within `s` at `x`. -/
@[simp] theorem seqLowerSemicontinuousWithinAt_coe_ereal_iff :
    SeqLowerSemicontinuousWithinAt (fun z ↦ (f z : EReal)) s x ↔
      SeqLowerSemicontinuousWithinAt f s x := by
  refine ⟨fun h y hy u hu hlim ↦ ?_, fun h y hy u hu hlim ↦ ?_⟩
  · exact (h y (EReal.coe_lt_coe_iff.mpr hy) hu hlim).mono fun _ ↦ EReal.coe_lt_coe_iff.mp
  · induction y with
    | bot => exact .of_forall fun n ↦ EReal.bot_lt_coe (f (u n))
    | coe r =>
      exact (h r (EReal.coe_lt_coe_iff.mp hy) hu hlim).mono fun _ ↦ EReal.coe_lt_coe_iff.mpr
    | top => exact False.elim (not_top_lt hy)

/-- Coercing a real-valued function to `EReal` does not change sequential lower semicontinuity
at `x`. -/
@[simp] theorem seqLowerSemicontinuousAt_coe_ereal_iff :
    SeqLowerSemicontinuousAt (fun z ↦ (f z : EReal)) x ↔ SeqLowerSemicontinuousAt f x := by
  rw [← seqLowerSemicontinuousWithinAt_univ_iff, seqLowerSemicontinuousWithinAt_coe_ereal_iff,
    seqLowerSemicontinuousWithinAt_univ_iff]

/-- Coercing a real-valued function to `EReal` does not change sequential lower semicontinuity
on `s`. -/
@[simp] theorem seqLowerSemicontinuousOn_coe_ereal_iff :
    SeqLowerSemicontinuousOn (fun z ↦ (f z : EReal)) s ↔ SeqLowerSemicontinuousOn f s := by
  simp only [seqLowerSemicontinuousOn_iff, seqLowerSemicontinuousWithinAt_coe_ereal_iff]

/-- Coercing a real-valued function to `EReal` does not change global sequential lower
semicontinuity. -/
@[simp] theorem seqLowerSemicontinuous_coe_ereal_iff :
    SeqLowerSemicontinuous (fun z ↦ (f z : EReal)) ↔ SeqLowerSemicontinuous f := by
  simp only [seqLowerSemicontinuous_iff, seqLowerSemicontinuousAt_coe_ereal_iff]

/-- For a real-valued function, sequential lower semicontinuity on `s` is equivalent to the
`EReal` lower-limit inequality `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop` along
convergent sequences in `s`, including sequences whose values are unbounded above. -/
theorem seqLowerSemicontinuousOn_iff_ereal_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff, seqLowerSemicontinuousOn_iff_le_liminf]
  rfl

/-- For a real-valued function, global sequential lower semicontinuity is equivalent to the
`EReal` lower-limit inequality along all convergent sequences. -/
theorem seqLowerSemicontinuous_iff_ereal_le_liminf :
    SeqLowerSemicontinuous f ↔
      ∀ (x : X) ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuous_coe_ereal_iff, seqLowerSemicontinuous_iff_le_liminf]
  rfl

/-- When a real-valued function is bounded below on `s`, sequential lower semicontinuity on `s` is
equivalent to the finite-limit inequality `Tendsto (f ∘ u) atTop (𝓝 r) → f x ≤ r` along sequences
in `s` converging to `x ∈ s`. Without a lower bound on `f`, the finite-limit condition is strictly
weaker because sequences with `f (u n) → -∞` satisfy it vacuously. -/
theorem seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow (hb : BddBelow (f '' s)) :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ ⦃u : ℕ → X⦄ ⦃r : ℝ⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        Tendsto (f ∘ u) atTop (𝓝 r) → f x ≤ r := by
  refine ⟨fun hf x hx _ _ hu hux hfr ↦ hf.le_of_tendsto hx hu hux hfr,
    fun h x hx y hy u hu hlim ↦ ?_⟩
  obtain ⟨m, hm⟩ := hb
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, f (u n) ≤ y := by
    simpa only [not_eventually, not_lt] using hnot
  obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop hfreq
  have hIcc : ∀ n, f (u (φ n)) ∈ Icc m y :=
    fun n ↦ ⟨hm (mem_image_of_mem f (hu (φ n))), hle n⟩
  obtain ⟨r, ⟨-, hry⟩, ψ, hψ, hfr⟩ := isCompact_Icc.tendsto_subseq hIcc
  exact not_le_of_gt hy
    ((h x hx (fun n ↦ hu (φ (ψ n))) (hlim.comp (hφ.comp hψ).tendsto_atTop) hfr).trans hry)

end RealAndEReal

section IsSeqCompact

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- On a nonempty sequentially compact set, a sequentially lower semicontinuous function into a
first-countable conditionally complete linear order that is bounded below on `s` attains its
minimum. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_bddBelow {β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] {f : X → β}
    (hne : s.Nonempty) (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s)
    (hb : BddBelow (f '' s)) : ∃ a ∈ s, IsMinOn f s a := by
  obtain ⟨y, -, hy_lim, hy_mem⟩ := exists_seq_tendsto_sInf (hne.image f) hb
  choose u hu hfu using hy_mem
  obtain ⟨a, ha, φ, hφ, ha_lim⟩ := hs hu
  have hfa : f a ≤ sInf (f '' s) := by
    refine hf.le_of_tendsto ha (fun n ↦ hu (φ n)) ha_lim ?_
    have hyφ : Tendsto (y ∘ φ) atTop (𝓝 (sInf (f '' s))) := hy_lim.comp hφ.tendsto_atTop
    simpa only [Function.comp_def, hfu] using hyφ
  exact ⟨a, ha, fun x hx ↦ hfa.trans (csInf_le hb (mem_image_of_mem f hx))⟩

/-- On a nonempty sequentially compact set, a sequentially lower semicontinuous function into a
first-countable complete linear order attains its minimum. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_completeLinearOrder {β : Type*}
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] [FirstCountableTopology β]
    {f : X → β} (hne : s.Nonempty) (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    ∃ a ∈ s, IsMinOn f s a :=
  hf.exists_isMinOn_of_bddBelow hne hs ⟨⊥, fun _ _ ↦ bot_le⟩

/-- On a nonempty sequentially compact set, a sequentially lower semicontinuous real-valued
function attains its minimum, with no lower-bound assumption required. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn {f : X → ℝ}
    (hne : s.Nonempty) (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    ∃ a ∈ s, IsMinOn f s a := by
  obtain ⟨a, ha, hmin⟩ :=
    (seqLowerSemicontinuousOn_coe_ereal_iff.mpr hf).exists_isMinOn_of_completeLinearOrder hne hs
  exact ⟨a, ha, fun x hx ↦ EReal.coe_le_coe_iff.mp (hmin hx)⟩

/-- A sequentially lower semicontinuous real-valued function on a sequentially compact set is
bounded below. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact {f : X → ℝ}
    (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) : BddBelow (f '' s) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨a, -, hmin⟩ := hf.exists_isMinOn hne hs
    exact hmin.bddBelow

end IsSeqCompact

end TauCeti
