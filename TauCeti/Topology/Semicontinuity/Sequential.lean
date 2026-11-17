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
import TauCeti.Topology.Order.IsLUB

/-!
# Sequential lower semicontinuity

A function `f : α → β` is *sequentially lower semicontinuous* on a set `s` if whenever a sequence
`u` in `s` converges to `x ∈ s` and `y < f x`, eventually `y < f (u n)`. This is the sequential
counterpart of `LowerSemicontinuousOn`, needed in non-first-countable topologies such as the weak
topology of a normed space.

In a linear order, sequential lower semicontinuity is equivalent to sequential closedness of every
relative sublevel set; in a complete linear order it is equivalent to `f x ≤ liminf (f ∘ u) atTop`
along convergent sequences, and for real-valued functions to the same inequality in `EReal`. Along
sequences whose values converge to a limit `r`, it implies `f x ≤ r`; for a function bounded below
on `s` taking values in a first-countable linear order with compact closed intervals (such as `ℝ`),
that finite-limit property is in fact equivalent to sequential lower semicontinuity (without a lower
bound, sequences with `f (u n) → -∞` escape the finite-limit test).

Every lower semicontinuous function is sequentially lower semicontinuous, and the converse holds
when the domain (or the restricted subset) is a `SequentialSpace`. On a nonempty sequentially
compact set, a sequentially lower semicontinuous function is bounded below and attains its minimum.

## Main definitions

* `TauCeti.SeqLowerSemicontinuousOn`: sequential lower semicontinuity of a function on a set.
* `TauCeti.SeqLowerSemicontinuous`: global sequential lower semicontinuity of a function.

## Main results

* `TauCeti.seqLowerSemicontinuousOn_iff_isSeqClosed_restrict_preimage` and
  `TauCeti.seqLowerSemicontinuousOn_iff_isSeqClosed_inter_preimage_Iic`: sublevel characterizations.
* `TauCeti.seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn`: agreement with topological lower
  semicontinuity on sequential spaces.
* `TauCeti.seqLowerSemicontinuousOn_iff_le_liminf` and
  `TauCeti.seqLowerSemicontinuousOn_iff_coe_le_liminf`: `liminf` characterizations in complete
  linear orders and in `EReal` for real-valued functions.
* `TauCeti.seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow`: equivalence with the
  finite-limit inequality for bounded-below functions into spaces with compact closed intervals.
* `TauCeti.SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact`: sequential extreme value
  theorem for sequentially lower semicontinuous functions.
-/

public section

open Filter Set Topology

namespace TauCeti

/-! ### Definitions and basic API -/

section Defs

variable {α β : Type*} [TopologicalSpace α] [LT β] {f g : α → β} {s t : Set α}

/-- A function `f` is sequentially lower semicontinuous on `s` if whenever a sequence in `s`
converges to `x ∈ s` and `y < f x`, eventually `y < f (u n)`. -/
def SeqLowerSemicontinuousOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, (∀ n, u n ∈ s) → x ∈ s →
    Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- A function `f` is sequentially lower semicontinuous if whenever a sequence converges to `x` and
`y < f x`, eventually `y < f (u n)`. -/
def SeqLowerSemicontinuous (f : α → β) : Prop :=
  ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- Unfolding characterization of `SeqLowerSemicontinuousOn`. -/
theorem seqLowerSemicontinuousOn_iff :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Unfolding characterization of `SeqLowerSemicontinuous`. -/
theorem seqLowerSemicontinuous_iff :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Sequential lower semicontinuity on `univ` is global sequential lower semicontinuity. -/
@[simp]
theorem seqLowerSemicontinuousOn_univ_iff :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f :=
  ⟨fun h _ _ hux ↦ h (fun _ ↦ mem_univ _) (mem_univ _) hux,
    fun h _ _ _ _ hux ↦ h hux⟩

/-- Sequential lower semicontinuity on `s` is equivalent to global sequential lower semicontinuity
of the restriction to `s`. -/
@[simp]
theorem seqLowerSemicontinuous_restrict_iff :
    SeqLowerSemicontinuous (s.domRestrict f) ↔ SeqLowerSemicontinuousOn f s := by
  constructor
  · intro h u x hu hx hux
    exact h (u := fun n ↦ ⟨u n, hu n⟩) (x := ⟨x, hx⟩) (tendsto_subtype_rng.2 hux)
  · intro h u x hux
    exact h (fun n ↦ (u n).2) x.2 (tendsto_subtype_rng.1 hux)

/-- Every function is sequentially lower semicontinuous on the empty set. -/
@[simp]
theorem seqLowerSemicontinuousOn_empty : SeqLowerSemicontinuousOn f ∅ :=
  fun _ _ _ hx ↦ hx.elim

/-- Every function is sequentially lower semicontinuous on a singleton. -/
@[simp]
theorem seqLowerSemicontinuousOn_singleton (a : α) : SeqLowerSemicontinuousOn f {a} := by
  intro u x hu hx _ y hy
  obtain rfl : x = a := hx
  exact Eventually.of_forall fun n ↦ by simpa only [mem_singleton_iff.1 (hu n)] using hy

/-- A globally sequentially lower semicontinuous function is sequentially lower semicontinuous on
every set. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousOn (hf : SeqLowerSemicontinuous f)
    (s : Set α) : SeqLowerSemicontinuousOn f s :=
  fun _ _ _ _ hux ↦ hf hux

/-- Sequential lower semicontinuity on a set passes to subsets. -/
theorem SeqLowerSemicontinuousOn.mono (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) :
    SeqLowerSemicontinuousOn f t :=
  fun _ _ hu hx ↦ hf (fun n ↦ hts (hu n)) (hts hx)

/-- Sequential lower semicontinuity on `s` depends only on the values of the function on `s`. -/
theorem SeqLowerSemicontinuousOn.congr (hf : SeqLowerSemicontinuousOn f s) (hfg : EqOn f g s) :
    SeqLowerSemicontinuousOn g s := by
  intro u x hu hx hux y hy
  rw [← hfg hx] at hy
  filter_upwards [hf hu hx hux y hy] with n hn
  rwa [← hfg (hu n)]

/-- Sequential lower semicontinuity on `s` is invariant under agreement on `s`. -/
theorem seqLowerSemicontinuousOn_congr (hfg : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s :=
  ⟨fun hf ↦ hf.congr hfg, fun hg ↦ hg.congr hfg.symm⟩

/-- Every constant function is sequentially lower semicontinuous on any set. -/
@[simp]
theorem seqLowerSemicontinuousOn_const (c : β) : SeqLowerSemicontinuousOn (fun _ : α ↦ c) s :=
  fun _ _ _ _ _ _ hy ↦ Eventually.of_forall fun _ ↦ hy

/-- Every constant function is sequentially lower semicontinuous. -/
@[simp]
theorem seqLowerSemicontinuous_const (c : β) : SeqLowerSemicontinuous (fun _ : α ↦ c) :=
  fun _ _ _ _ hy ↦ Eventually.of_forall fun _ ↦ hy

/-- Precomposition with a sequentially continuous map preserves global sequential lower
semicontinuity. -/
theorem SeqLowerSemicontinuous.comp {γ : Type*} [TopologicalSpace γ] {g : γ → α}
    (hf : SeqLowerSemicontinuous f) (hg : SeqContinuous g) :
    SeqLowerSemicontinuous (f ∘ g) :=
  fun _ _ hux ↦ hf (hg hux)

/-- Precomposition with a sequentially continuous map preserves sequential lower semicontinuity
on a set. -/
theorem SeqLowerSemicontinuousOn.comp {γ : Type*} [TopologicalSpace γ] {g : γ → α} {t : Set γ}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqContinuous g) (hgt : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun _ _ hu hx hux ↦ hf (fun n ↦ hgt (hu n)) (hgt hx) (hg hux)

end Defs

end TauCeti

/-! ### Comparison with topological lower semicontinuity and sequential continuity -/

section Comparison

variable {α β : Type*} [TopologicalSpace α] {f : α → β} {s : Set α}

/-- Every lower semicontinuous function on a set is sequentially lower semicontinuous there. -/
theorem LowerSemicontinuousOn.seqLowerSemicontinuousOn [Preorder β]
    (hf : LowerSemicontinuousOn f s) : TauCeti.SeqLowerSemicontinuousOn f s :=
  fun _ _ hu hx hux y hy ↦ (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hux
    (Filter.Eventually.of_forall hu)).eventually (hf _ hx y hy)

/-- Every lower semicontinuous function is sequentially lower semicontinuous. -/
theorem LowerSemicontinuous.seqLowerSemicontinuous [Preorder β]
    (hf : LowerSemicontinuous f) : TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hux y hy ↦ hux.eventually (hf _ y hy)

/-- Every sequentially continuous function into a linear order with closed initial rays is
sequentially lower semicontinuous. -/
theorem SeqContinuous.seqLowerSemicontinuous [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] (hf : SeqContinuous f) : TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hux _ hy ↦ (hf hux).eventually (Ioi_mem_nhds hy)

/-- Every sequentially continuous function into a linear order with closed initial rays is
sequentially lower semicontinuous on any set. -/
theorem SeqContinuous.seqLowerSemicontinuousOn [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] (hf : SeqContinuous f) (s : Set α) :
    TauCeti.SeqLowerSemicontinuousOn f s :=
  hf.seqLowerSemicontinuous.seqLowerSemicontinuousOn s

end Comparison

namespace TauCeti

/-! ### Sublevel characterizations and sequential spaces -/

section LinearOrder

variable {α β : Type*} [TopologicalSpace α] [LinearOrder β] {f : α → β} {s : Set α}

/-- Global sequential lower semicontinuity is equivalent to sequential closedness of every
sublevel set. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage :
    SeqLowerSemicontinuous f ↔ ∀ b : β, IsSeqClosed (f ⁻¹' Iic b) := by
  constructor
  · intro hf b u x hu hux
    exact le_of_not_gt fun hlt ↦ by
      obtain ⟨n, hn⟩ := (hf hux b hlt).exists
      exact hn.not_ge (hu n)
  · intro h u x hux y hy
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop, f (u n) ≤ y := by
      simpa only [not_eventually, not_lt] using hnot
    obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop hfreq
    exact hy.not_ge (h y hle (hux.comp hφ.tendsto_atTop))

/-- Sublevel sets of a sequentially lower semicontinuous function are sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_preimage (hf : SeqLowerSemicontinuous f) (b : β) :
    IsSeqClosed (f ⁻¹' Iic b) :=
  seqLowerSemicontinuous_iff_isSeqClosed_preimage.1 hf b

/-- Sequential lower semicontinuity on `s` is equivalent to sequential closedness of every
sublevel set in the subtype `s`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_restrict_preimage :
    SeqLowerSemicontinuousOn f s ↔ ∀ b : β, IsSeqClosed (s.domRestrict f ⁻¹' Iic b) := by
  rw [← seqLowerSemicontinuous_restrict_iff, seqLowerSemicontinuous_iff_isSeqClosed_preimage]

/-- Sequential lower semicontinuity on `s` is equivalent to preservation of every upper bound `b`
along convergent sequences in `s`. -/
theorem seqLowerSemicontinuousOn_iff_forall_le :
    SeqLowerSemicontinuousOn f s ↔
      ∀ b : β, ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, (∀ n, u n ∈ s) → (∀ n, f (u n) ≤ b) → x ∈ s →
        Tendsto u atTop (𝓝 x) → f x ≤ b := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_restrict_preimage]
  constructor
  · intro h b u x hu hub hx hux
    exact h b (x := fun n ↦ ⟨u n, hu n⟩) (p := ⟨x, hx⟩) hub (tendsto_subtype_rng.2 hux)
  · intro h b u x hub hux
    exact h b (fun n ↦ (u n).2) hub x.2 (tendsto_subtype_rng.1 hux)

/-- On a sequentially closed set, sequential lower semicontinuity is equivalent to sequential
closedness of every relative sublevel set. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_inter_preimage_Iic (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b : β, IsSeqClosed (s ∩ f ⁻¹' Iic b) := by
  rw [seqLowerSemicontinuousOn_iff_forall_le]
  constructor
  · intro h b u x hu hux
    have hx : x ∈ s := hs (fun n ↦ (hu n).1) hux
    exact ⟨hx, h b (fun n ↦ (hu n).1) (fun n ↦ (hu n).2) hx hux⟩
  · intro h b u x hu hub _ hux
    exact (h b (fun n ↦ ⟨hu n, hub n⟩) hux).2

/-- Relative sublevel sets of a sequentially lower semicontinuous function on a sequentially closed
set are sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_inter_preimage_Iic (hf : SeqLowerSemicontinuousOn f s)
    (hs : IsSeqClosed s) (b : β) : IsSeqClosed (s ∩ f ⁻¹' Iic b) :=
  (seqLowerSemicontinuousOn_iff_isSeqClosed_inter_preimage_Iic hs).1 hf b

/-- On a sequential space, sequential and topological lower semicontinuity coincide. -/
theorem seqLowerSemicontinuous_iff_lowerSemicontinuous [SequentialSpace α] :
    SeqLowerSemicontinuous f ↔ LowerSemicontinuous f := by
  rw [seqLowerSemicontinuous_iff_isSeqClosed_preimage, lowerSemicontinuous_iff_isClosed_preimage]
  simp only [isSeqClosed_iff_isClosed]

/-- On a subset whose induced topology is sequential, sequential and topological lower
semicontinuity coincide. -/
theorem seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn [SequentialSpace s] :
    SeqLowerSemicontinuousOn f s ↔ LowerSemicontinuousOn f s := by
  rw [← seqLowerSemicontinuous_restrict_iff, ← lowerSemicontinuous_restrict_iff,
    seqLowerSemicontinuous_iff_lowerSemicontinuous]

end LinearOrder

/-! ### `liminf` and finite-limit characterizations -/

section Liminf

variable {α β : Type*} [TopologicalSpace α] {s : Set α}

/-- In a complete linear order, sequential lower semicontinuity on `s` is equivalent to the
`liminf` inequality along convergent sequences in `s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf [CompleteLinearOrder β] {f : α → β} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, (∀ n, u n ∈ s) → x ∈ s → Tendsto u atTop (𝓝 x) →
        f x ≤ liminf (fun n ↦ f (u n)) atTop := by
  refine ⟨fun hf u x hu hx hux ↦ ?_, fun hf u x hu hx hux y hy ↦ ?_⟩
  · rw [le_liminf_iff]
    exact fun y hy ↦ hf hu hx hux y hy
  · exact eventually_lt_of_lt_liminf (hy.trans_le (hf hu hx hux))

/-- A sequentially lower semicontinuous function into a complete linear order satisfies the
`liminf` inequality along convergent sequences in `s`. -/
theorem SeqLowerSemicontinuousOn.le_liminf [CompleteLinearOrder β] {f : α → β}
    (hf : SeqLowerSemicontinuousOn f s) {u : ℕ → α} {x : α} (hu : ∀ n, u n ∈ s) (hx : x ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) : f x ≤ liminf (fun n ↦ f (u n)) atTop :=
  seqLowerSemicontinuousOn_iff_le_liminf.1 hf hu hx hux

/-- In a complete linear order, global sequential lower semicontinuity is equivalent to the
`liminf` inequality along convergent sequences. -/
theorem seqLowerSemicontinuous_iff_le_liminf [CompleteLinearOrder β] {f : α → β} :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, Tendsto u atTop (𝓝 x) → f x ≤ liminf (fun n ↦ f (u n)) atTop := by
  rw [← seqLowerSemicontinuousOn_univ_iff, seqLowerSemicontinuousOn_iff_le_liminf]
  exact ⟨fun h _ _ hux ↦ h (fun _ ↦ mem_univ _) (mem_univ _) hux, fun h _ _ _ _ hux ↦ h hux⟩

/-- A globally sequentially lower semicontinuous function into a complete linear order satisfies
the `liminf` inequality along convergent sequences. -/
theorem SeqLowerSemicontinuous.le_liminf [CompleteLinearOrder β] {f : α → β}
    (hf : SeqLowerSemicontinuous f) {u : ℕ → α} {x : α} (hux : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (fun n ↦ f (u n)) atTop :=
  seqLowerSemicontinuous_iff_le_liminf.1 hf hux

/-- A real-valued function is sequentially lower semicontinuous on `s` if and only if its
coercion into `EReal` satisfies the `liminf` inequality along convergent sequences in `s`. -/
theorem seqLowerSemicontinuousOn_iff_coe_le_liminf {f : α → ℝ} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, (∀ n, u n ∈ s) → x ∈ s → Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_iff_le_liminf (f := fun x ↦ (f x : EReal))]
  constructor
  · intro hf u x hu hx hux y hy
    obtain ⟨r, hry, hrf⟩ := EReal.exists_between_coe_real hy
    filter_upwards [hf hu hx hux r (EReal.coe_lt_coe_iff.1 hrf)] with n hn
    exact hry.trans (EReal.coe_lt_coe_iff.2 hn)
  · intro hf u x hu hx hux r hr
    filter_upwards [hf hu hx hux (r : EReal) (EReal.coe_lt_coe_iff.2 hr)] with n hn
    exact EReal.coe_lt_coe_iff.1 hn

/-- A sequentially lower semicontinuous real-valued function satisfies the `EReal` `liminf`
inequality along convergent sequences in `s`. -/
theorem SeqLowerSemicontinuousOn.coe_le_liminf {f : α → ℝ} (hf : SeqLowerSemicontinuousOn f s)
    {u : ℕ → α} {x : α} (hu : ∀ n, u n ∈ s) (hx : x ∈ s) (hux : Tendsto u atTop (𝓝 x)) :
    (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop :=
  seqLowerSemicontinuousOn_iff_coe_le_liminf.1 hf hu hx hux

/-- A real-valued function is globally sequentially lower semicontinuous if and only if its
coercion into `EReal` satisfies the `liminf` inequality along convergent sequences. -/
theorem seqLowerSemicontinuous_iff_coe_le_liminf {f : α → ℝ} :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄, Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_univ_iff, seqLowerSemicontinuousOn_iff_coe_le_liminf]
  exact ⟨fun h _ _ hux ↦ h (fun _ ↦ mem_univ _) (mem_univ _) hux, fun h _ _ _ _ hux ↦ h hux⟩

/-- A globally sequentially lower semicontinuous real-valued function satisfies the `EReal`
`liminf` inequality along convergent sequences. -/
theorem SeqLowerSemicontinuous.coe_le_liminf {f : α → ℝ} (hf : SeqLowerSemicontinuous f)
    {u : ℕ → α} {x : α} (hux : Tendsto u atTop (𝓝 x)) :
    (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop :=
  seqLowerSemicontinuous_iff_coe_le_liminf.1 hf hux

/-- Along a convergent sequence in `s` whose function values converge to `r`, sequential lower
semicontinuity yields `f x ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] {f : α → β} (hf : SeqLowerSemicontinuousOn f s)
    {u : ℕ → α} {x : α} {r : β} (hu : ∀ n, u n ∈ s) (hx : x ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) (hfu : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) :
    f x ≤ r := by
  by_contra! hlt
  obtain ⟨z, hrz, y, hyx, hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
  obtain ⟨n, hn₁, hn₂⟩ := ((hfu.eventually (Iio_mem_nhds hrz)).and (hf hu hx hux y hyx)).exists
  exact (hdisj _ hn₁ _ hn₂).false

/-- Along a convergent sequence whose function values converge to `r`, global sequential lower
semicontinuity yields `f x ≤ r`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] {f : α → β} (hf : SeqLowerSemicontinuous f)
    {u : ℕ → α} {x : α} {r : β} (hux : Tendsto u atTop (𝓝 x))
    (hfu : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) : f x ≤ r :=
  (hf.seqLowerSemicontinuousOn univ).le_of_tendsto (fun _ ↦ mem_univ _) (mem_univ _) hux hfu

/-- For a function bounded below on `s` into a first-countable linear order with compact closed
intervals (such as `ℝ`), the finite-limit inequality implies sequential lower semicontinuity on
`s`. The lower bound is necessary: without it, sequences with `f (u n) → -∞` satisfy the
finite-limit hypothesis vacuously. -/
theorem seqLowerSemicontinuousOn_of_le_of_tendsto_of_bddBelow [LinearOrder β] [TopologicalSpace β]
    [CompactIccSpace β] [FirstCountableTopology β] {f : α → β}
    (hbdd : BddBelow (f '' s))
    (h : ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄ ⦃r : β⦄, (∀ n, u n ∈ s) → x ∈ s →
      Tendsto u atTop (𝓝 x) → Tendsto (fun n ↦ f (u n)) atTop (𝓝 r) → f x ≤ r) :
    SeqLowerSemicontinuousOn f s := by
  rw [seqLowerSemicontinuousOn_iff_forall_le]
  intro b u x hu hub hx hux
  obtain ⟨m, hm⟩ := hbdd
  have hmem : ∀ n, f (u n) ∈ Icc m b :=
    fun n ↦ ⟨hm (mem_image_of_mem f (hu n)), hub n⟩
  obtain ⟨r, hr, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  exact (h (fun n ↦ hu (φ n)) hx (hux.comp hφ.tendsto_atTop) hlim).trans hr.2

/-- For a function bounded below on `s` into a first-countable linear order with compact closed
intervals and closed upper rays (such as `ℝ`), sequential lower semicontinuity on `s` is equivalent
to the finite-limit inequality along convergent sequences in `s`. -/
theorem seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow [LinearOrder β] [TopologicalSpace β]
    [CompactIccSpace β] [FirstCountableTopology β] [ClosedIciTopology β] {f : α → β}
    (hbdd : BddBelow (f '' s)) :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → α⦄ ⦃x : α⦄ ⦃r : β⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → Tendsto (fun n ↦ f (u n)) atTop (𝓝 r) → f x ≤ r :=
  ⟨fun hf _ _ _ hu hx hux hfu ↦ hf.le_of_tendsto hu hx hux hfu,
    seqLowerSemicontinuousOn_of_le_of_tendsto_of_bddBelow hbdd⟩

end Liminf

/-! ### Algebraic and lattice combinators -/

section Combinators

variable {α β : Type*} [TopologicalSpace α] {f g : α → β} {s : Set α}

/-- The sum of two sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`, assuming continuity of addition at the values on `s` (for applications
such as `EReal`). -/
theorem SeqLowerSemicontinuousOn.add' [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [TopologicalSpace β] [OrderTopology β]
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : β × β ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuousOn (fun x ↦ f x + g x) s := by
  intro u x hu hx hux y hy
  let c : OnePoint ℕ → α := fun k ↦ k.elim x u
  have hnhds : 𝓝 (OnePoint.infty : OnePoint ℕ) =
      map ((↑) : ℕ → OnePoint ℕ) atTop ⊔ pure OnePoint.infty := by
    rw [OnePoint.nhds_infty_eq, coclosedCompact_eq_cocompact, cocompact_eq_cofinite,
      Nat.cofinite_eq_atTop]
  have hf' : LowerSemicontinuousAt (f ∘ c) OnePoint.infty := fun z hz ↦ by
    rw [Filter.Eventually, hnhds, mem_sup]
    exact ⟨hf hu hx hux z hz, hz⟩
  have hg' : LowerSemicontinuousAt (g ∘ c) OnePoint.infty := fun z hz ↦ by
    rw [Filter.Eventually, hnhds, mem_sup]
    exact ⟨hg hu hx hux z hz, hz⟩
  have hsum := hf'.add' hg' (hcont x hx) y hy
  rw [Filter.Eventually, hnhds, mem_sup] at hsum
  exact hsum.1

/-- The sum of two globally sequentially lower semicontinuous functions is sequentially lower
semicontinuous, assuming pointwise continuity of addition. -/
theorem SeqLowerSemicontinuous.add' [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [TopologicalSpace β] [OrderTopology β]
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : β × β ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuous (fun x ↦ f x + g x) :=
  seqLowerSemicontinuousOn_univ_iff.1
    ((hf.seqLowerSemicontinuousOn univ).add' (hg.seqLowerSemicontinuousOn univ) fun x _ ↦ hcont x)

/-- The sum of two sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.add [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x + g x) s :=
  hf.add' hg fun _ _ ↦ continuous_add.continuousAt

/-- The sum of two globally sequentially lower semicontinuous functions is sequentially lower
semicontinuous. -/
theorem SeqLowerSemicontinuous.add [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous (fun x ↦ f x + g x) :=
  hf.add' hg fun _ ↦ continuous_add.continuousAt

/-- A finite sum of sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_sum {ι : Type*} [AddCommMonoid β] [LinearOrder β]
    [IsOrderedAddMonoid β] [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
    {F : ι → α → β} {a : Finset ι} (hF : ∀ i ∈ a, SeqLowerSemicontinuousOn (F i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ∑ i ∈ a, F i x) s := by
  classical
  induction a using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using seqLowerSemicontinuousOn_const (0 : β)
  | insert i a hia ih =>
    simp only [Finset.sum_insert hia]
    exact (hF i (Finset.mem_insert_self i a)).add
      (ih fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))

/-- A finite sum of globally sequentially lower semicontinuous functions is sequentially lower
semicontinuous. -/
theorem seqLowerSemicontinuous_sum {ι : Type*} [AddCommMonoid β] [LinearOrder β]
    [IsOrderedAddMonoid β] [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
    {F : ι → α → β} {a : Finset ι} (hF : ∀ i ∈ a, SeqLowerSemicontinuous (F i)) :
    SeqLowerSemicontinuous (fun x ↦ ∑ i ∈ a, F i x) :=
  seqLowerSemicontinuousOn_univ_iff.1 <|
    seqLowerSemicontinuousOn_sum fun i hi ↦ (hF i hi).seqLowerSemicontinuousOn univ

/-- Left composition with a continuous monotone map preserves sequential lower semicontinuity
on `s`. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuousOn {γ : Type*}
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    {g : β → γ} (hg : Continuous g) (hf : SeqLowerSemicontinuousOn f s) (hmono : Monotone g) :
    SeqLowerSemicontinuousOn (g ∘ f) s := by
  intro u x hu hx hux y hy
  let c : OnePoint ℕ → α := fun k ↦ k.elim x u
  have hnhds : 𝓝 (OnePoint.infty : OnePoint ℕ) =
      map ((↑) : ℕ → OnePoint ℕ) atTop ⊔ pure OnePoint.infty := by
    rw [OnePoint.nhds_infty_eq, coclosedCompact_eq_cocompact, cocompact_eq_cofinite,
      Nat.cofinite_eq_atTop]
  have hf' : LowerSemicontinuousAt (f ∘ c) OnePoint.infty := fun z hz ↦ by
    rw [Filter.Eventually, hnhds, mem_sup]
    exact ⟨hf hu hx hux z hz, hz⟩
  have hcomp := hg.continuousAt.comp_lowerSemicontinuousAt hf' hmono y hy
  rw [Filter.Eventually, hnhds, mem_sup] at hcomp
  exact hcomp.1

/-- Left composition with a continuous monotone map preserves global sequential lower
semicontinuity. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuous {γ : Type*}
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    {g : β → γ} (hg : Continuous g) (hf : SeqLowerSemicontinuous f) (hmono : Monotone g) :
    SeqLowerSemicontinuous (g ∘ f) :=
  seqLowerSemicontinuousOn_univ_iff.1
    (hg.comp_seqLowerSemicontinuousOn (hf.seqLowerSemicontinuousOn univ) hmono)

/-- Nonnegative scalar multiplication preserves sequential lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.const_mul [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
    (hf : SeqLowerSemicontinuousOn f s) {c : β} (hc : 0 ≤ c) :
    SeqLowerSemicontinuousOn (fun x ↦ c * f x) s := by
  rcases hc.eq_or_lt with rfl | hcpos
  · simpa only [zero_mul] using seqLowerSemicontinuousOn_const (0 : β)
  · intro u x hu hx hux y hy
    filter_upwards [hf hu hx hux (c⁻¹ * y) ((inv_mul_lt_iff₀ hcpos).2 hy)] with n hn
    exact (inv_mul_lt_iff₀ hcpos).1 hn

/-- Nonnegative scalar multiplication preserves global sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.const_mul [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
    (hf : SeqLowerSemicontinuous f) {c : β} (hc : 0 ≤ c) :
    SeqLowerSemicontinuous (fun x ↦ c * f x) :=
  seqLowerSemicontinuousOn_univ_iff.1 ((hf.seqLowerSemicontinuousOn univ).const_mul hc)

/-- The pointwise supremum of two sequentially lower semicontinuous functions on `s` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.sup [LinearOrder β]
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s := by
  intro u x hu hx hux y hy
  rcases lt_sup_iff.1 hy with hy | hy
  · exact (hf hu hx hux y hy).mono fun _ h ↦ lt_sup_of_lt_left h
  · exact (hg hu hx hux y hy).mono fun _ h ↦ lt_sup_of_lt_right h

/-- The pointwise supremum of two globally sequentially lower semicontinuous functions is
sequentially lower semicontinuous. -/
theorem SeqLowerSemicontinuous.sup [LinearOrder β]
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous (fun x ↦ f x ⊔ g x) :=
  seqLowerSemicontinuousOn_univ_iff.1
    ((hf.seqLowerSemicontinuousOn univ).sup (hg.seqLowerSemicontinuousOn univ))

/-- The pointwise infimum of two sequentially lower semicontinuous functions on `s` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.inf [LinearOrder β]
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊓ g x) s := by
  intro u x hu hx hux y hy
  rw [lt_inf_iff] at hy
  filter_upwards [hf hu hx hux y hy.1, hg hu hx hux y hy.2] with n h₁ h₂
  exact lt_inf_iff.2 ⟨h₁, h₂⟩

/-- The pointwise infimum of two globally sequentially lower semicontinuous functions is
sequentially lower semicontinuous. -/
theorem SeqLowerSemicontinuous.inf [LinearOrder β]
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous (fun x ↦ f x ⊓ g x) :=
  seqLowerSemicontinuousOn_univ_iff.1
    ((hf.seqLowerSemicontinuousOn univ).inf (hg.seqLowerSemicontinuousOn univ))

/-- The pointwise supremum of a pointwise bounded-above family of sequentially lower
semicontinuous functions on `s` is sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_ciSup {ι : Sort*} [ConditionallyCompleteLinearOrder β]
    {F : ι → α → β} (hbdd : ∀ x ∈ s, BddAbove (range fun i ↦ F i x))
    (hF : ∀ i, SeqLowerSemicontinuousOn (F i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, F i x) s := by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using seqLowerSemicontinuousOn_const (sSup ∅ : β)
  · intro u x hu hx hux y hy
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hy
    filter_upwards [hF i hu hx hux y hi] with n hn
    exact hn.trans_le (le_ciSup (hbdd (u n) (hu n)) i)

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions into a
complete linear order is sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_iSup {ι : Sort*} [CompleteLinearOrder β]
    {F : ι → α → β} (hF : ∀ i, SeqLowerSemicontinuousOn (F i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, F i x) s :=
  seqLowerSemicontinuousOn_ciSup (fun _ _ ↦ OrderTop.bddAbove _) hF

/-- The pointwise supremum of a pointwise bounded-above family of globally sequentially lower
semicontinuous functions is sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_ciSup {ι : Sort*} [ConditionallyCompleteLinearOrder β]
    {F : ι → α → β} (hbdd : ∀ x, BddAbove (range fun i ↦ F i x))
    (hF : ∀ i, SeqLowerSemicontinuous (F i)) :
    SeqLowerSemicontinuous (fun x ↦ ⨆ i, F i x) :=
  seqLowerSemicontinuousOn_univ_iff.1 <|
    seqLowerSemicontinuousOn_ciSup (fun x _ ↦ hbdd x) fun i ↦ (hF i).seqLowerSemicontinuousOn univ

/-- The pointwise supremum of a family of globally sequentially lower semicontinuous functions
into a complete linear order is sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_iSup {ι : Sort*} [CompleteLinearOrder β]
    {F : ι → α → β} (hF : ∀ i, SeqLowerSemicontinuous (F i)) :
    SeqLowerSemicontinuous (fun x ↦ ⨆ i, F i x) :=
  seqLowerSemicontinuous_ciSup (fun _ ↦ OrderTop.bddAbove _) hF

end Combinators

/-! ### Sequential extreme value theorem -/

section Minimization

/-- A sequentially lower semicontinuous function is bounded below on a sequentially compact set,
provided `atBot` in the codomain is countably generated. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact {α β : Type*} [TopologicalSpace α]
    [LinearOrder β] [Nonempty β] [IsCountablyGenerated (atBot : Filter β)]
    {f : α → β} {s : Set α} (hf : SeqLowerSemicontinuousOn f s) (hs : IsSeqCompact s) :
    BddBelow (f '' s) := by
  by_contra hnbdd
  obtain ⟨b, hb⟩ := Filter.exists_seq_tendsto (atBot : Filter β)
  have hstep (n : ℕ) : ∃ x ∈ s, f x < b n := by
    have hnot : ¬ b n ∈ lowerBounds (f '' s) := fun h ↦ hnbdd ⟨b n, h⟩
    simpa only [mem_lowerBounds, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, not_forall, not_le, exists_prop] using hnot
  choose u hu hlt using hstep
  obtain ⟨x, hx, φ, hφ, hux⟩ := hs hu
  have hnotx : ¬ f x ∈ lowerBounds (f '' s) := fun h ↦ hnbdd ⟨f x, h⟩
  simp only [mem_lowerBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, not_forall, not_le] at hnotx
  obtain ⟨y, _, hy⟩ := hnotx
  have hlarge := hf (fun n ↦ hu (φ n)) hx hux (f y) hy
  have hsmall := (hb.comp hφ.tendsto_atTop).eventually (Iic_mem_atBot (f y))
  obtain ⟨n, hn₁, hn₂⟩ := (hlarge.and hsmall).exists
  exact (hn₁.trans (hlt (φ n))).not_ge hn₂

/-- **Sequential extreme value theorem.** A sequentially lower semicontinuous function attains its
minimum on a nonempty sequentially compact set. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact {α β : Type*}
    [TopologicalSpace α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [FirstCountableTopology β] [IsCountablyGenerated (atBot : Filter β)]
    {f : α → β} {s : Set α} (hf : SeqLowerSemicontinuousOn f s)
    (hne : s.Nonempty) (hs : IsSeqCompact s) :
    ∃ x ∈ s, IsMinOn f s x := by
  have : Nonempty β := ⟨f hne.some⟩
  have hbdd : BddBelow (f '' s) := hf.bddBelow_of_isSeqCompact hs
  obtain ⟨u, hu, -, hlim⟩ := exists_seq_antitone_tendsto_sInf_image hne hbdd
  obtain ⟨x, hx, φ, hφ, hux⟩ := hs hu
  have hle : f x ≤ sInf (f '' s) :=
    hf.le_of_tendsto (fun n ↦ hu (φ n)) hx hux (hlim.comp hφ.tendsto_atTop)
  exact ⟨x, hx, fun y hy ↦ hle.trans (csInf_le hbdd (mem_image_of_mem f hy))⟩

end Minimization

end TauCeti
