/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Order.Filter.Extr

/-!
# Sequential lower semicontinuity

A function `f : X → β` from a topological space to a preorder is sequentially lower
semicontinuous (`TauCeti.SeqLowerSemicontinuous`) if every strict lower bound `y < f x`
eventually persists along every sequence converging to `x`. Its set-restricted counterpart
`TauCeti.SeqLowerSemicontinuousOn` requires both the limit `x` and all terms of the sequence
to lie in the set `s`, matching `SeqLowerSemicontinuous (s.domRestrict f)`.

When `β` is a linear order, sequential lower semicontinuity is equivalent to sequential
closedness of every sublevel `{x | f x ≤ b}` (and, on a sequentially closed domain `s`, of
every restricted sublevel `{x ∈ s | f x ≤ b}`). Consequently, topological and sequential
lower semicontinuity agree whenever the domain (or subtype) is a `SequentialSpace`.

In complete linear orders, sequential lower semicontinuity is characterized by the limit
inferior inequality `f x ≤ liminf (f ∘ u) atTop`; for real-valued functions, casting to
`EReal` avoids boundedness side conditions on `liminf`. In any linear order with the order
topology, sequential lower semicontinuity passes inequalities through convergent function
values (`f x ≤ b` whenever `u → x` and `f ∘ u → b`), and on bounded-below sets in a
first-countable order topology with compact closed intervals that finite-limit property is
again equivalent to sequential lower semicontinuity. Finally, on a nonempty sequentially
compact set, sequential lower semicontinuity yields existence of a minimizer.

## References

* G. Dal Maso, *An Introduction to Γ-Convergence*, Chapter 1.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §3.2.
-/

public section

open Filter Function Set Topology

namespace TauCeti

section Preorder

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Preorder β]
  {f g : X → β} {s t : Set X}

/-- A function `f : X → β` is sequentially lower semicontinuous if for every sequence `u`
converging to `x` and every `y < f x`, eventually `y < f (u n)`. -/
def SeqLowerSemicontinuous (f : X → β) : Prop :=
  ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- A function `f : X → β` is sequentially lower semicontinuous on `s` if for every sequence
`u` in `s` converging to `x ∈ s` and every `y < f x`, eventually `y < f (u n)`. -/
def SeqLowerSemicontinuousOn (f : X → β) (s : Set X) : Prop :=
  ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, x ∈ s → (∀ n, u n ∈ s) →
    Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- Unfolding characterization of `TauCeti.SeqLowerSemicontinuous`. -/
theorem seqLowerSemicontinuous_iff :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Unfolding characterization of `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem seqLowerSemicontinuousOn_iff :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, x ∈ s → (∀ n, u n ∈ s) →
        Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Sequential lower semicontinuity on `univ` coincides with global sequential lower
semicontinuity. -/
@[simp]
theorem seqLowerSemicontinuousOn_univ_iff :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f := by
  simp [SeqLowerSemicontinuousOn, SeqLowerSemicontinuous]

/-- Sequential lower semicontinuity on `s` coincides with sequential lower semicontinuity of
`s.domRestrict f` on the subtype `s`. -/
@[simp]
theorem seqLowerSemicontinuous_restrict_iff :
    SeqLowerSemicontinuous (s.domRestrict f) ↔ SeqLowerSemicontinuousOn f s := by
  constructor
  · intro hf u x hx hu hux y hy
    let v : ℕ → s := fun n ↦ ⟨u n, hu n⟩
    have hvx : Tendsto v atTop (𝓝 ⟨x, hx⟩) := tendsto_subtype_rng.2 hux
    exact hf hvx y hy
  · intro hf u x hux y hy
    exact hf x.2 (fun n ↦ (u n).2) (continuous_subtype_val.tendsto x |>.comp hux) y hy

/-- A constant function is sequentially lower semicontinuous. -/
@[simp]
theorem seqLowerSemicontinuous_const {c : β} : SeqLowerSemicontinuous (fun _ : X ↦ c) :=
  fun _ _ _ _ hy ↦ Eventually.of_forall fun _ ↦ hy

/-- A constant function is sequentially lower semicontinuous on any set. -/
@[simp]
theorem seqLowerSemicontinuousOn_const {c : β} : SeqLowerSemicontinuousOn (fun _ : X ↦ c) s :=
  fun _ _ _ _ _ _ hy ↦ Eventually.of_forall fun _ ↦ hy

/-- Every function is vacuously sequentially lower semicontinuous on the empty set. -/
@[simp]
theorem seqLowerSemicontinuousOn_empty : SeqLowerSemicontinuousOn f ∅ := by
  simp [SeqLowerSemicontinuousOn]

/-- Every function is sequentially lower semicontinuous on a singleton. -/
@[simp]
theorem seqLowerSemicontinuousOn_singleton {a : X} : SeqLowerSemicontinuousOn f {a} := by
  intro u x hx hu _ y hy
  rcases mem_singleton_iff.1 hx with rfl
  exact Eventually.of_forall fun n ↦ by simpa [mem_singleton_iff.1 (hu n)] using hy

/-- Global sequential lower semicontinuity restricts to any subset. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousOn (hf : SeqLowerSemicontinuous f)
    (s : Set X) : SeqLowerSemicontinuousOn f s :=
  fun _ _ _ _ hux y hy ↦ hf hux y hy

/-- Sequential lower semicontinuity is monotone with respect to shrinking the domain set. -/
theorem SeqLowerSemicontinuousOn.mono (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) :
    SeqLowerSemicontinuousOn f t :=
  fun _ _ hx hu hux y hy ↦ hf (hts hx) (fun n ↦ hts (hu n)) hux y hy

/-- Sequential lower semicontinuity on `s` depends only on the values of `f` on `s`. -/
theorem SeqLowerSemicontinuousOn.congr (hf : SeqLowerSemicontinuousOn f s) (h : EqOn f g s) :
    SeqLowerSemicontinuousOn g s := by
  intro u x hx hu hux y hy
  rw [← h hx] at hy
  exact (hf hx hu hux y hy).mono fun n hn ↦ h (hu n) ▸ hn

/-- Functions agreeing on `s` have the same sequential lower semicontinuity on `s`. -/
theorem seqLowerSemicontinuousOn_congr (h : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

/-- Precomposing a sequentially lower semicontinuous map with a sequentially continuous map
preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.comp_seqContinuous {g : Y → X}
    (hf : SeqLowerSemicontinuous f) (hg : SeqContinuous g) :
    SeqLowerSemicontinuous (f ∘ g) :=
  fun _ _ hux y hy ↦ hf (hg hux) y hy

/-- Precomposing with a map whose subtype restriction `t → s` is sequentially continuous
preserves sequential lower semicontinuity on sets. -/
theorem SeqLowerSemicontinuousOn.comp_seqContinuous_restrict {g : Y → X} {t : Set Y}
    (hf : SeqLowerSemicontinuousOn f s) (hgs : MapsTo g t s)
    (hg : SeqContinuous (hgs.restrict g t s)) :
    SeqLowerSemicontinuousOn (f ∘ g) t := by
  rw [← seqLowerSemicontinuous_restrict_iff] at hf ⊢
  exact hf.comp_seqContinuous hg

/-- Precomposing with a map continuous on `t` and mapping `t` into `s` preserves sequential
lower semicontinuity on sets. -/
theorem SeqLowerSemicontinuousOn.comp_continuousOn {g : Y → X} {t : Set Y}
    (hf : SeqLowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hgs : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  hf.comp_seqContinuous_restrict hgs (hg.mapsToRestrict hgs).seqContinuous

end Preorder

end TauCeti

/-- A sequentially continuous map into a linear order topology is sequentially lower
semicontinuous. -/
theorem SeqContinuous.seqLowerSemicontinuous {X β : Type*} [TopologicalSpace X]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : X → β} (hf : SeqContinuous f) :
    TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hux _ hy ↦ hf hux (Ioi_mem_nhds hy)

/-- Every lower semicontinuous map is sequentially lower semicontinuous. -/
theorem LowerSemicontinuous.seqLowerSemicontinuous {X β : Type*} [TopologicalSpace X]
    [Preorder β] {f : X → β} (hf : LowerSemicontinuous f) :
    TauCeti.SeqLowerSemicontinuous f :=
  fun _ x hux y hy ↦ hux.eventually (hf x y hy)

/-- Every map lower semicontinuous on `s` is sequentially lower semicontinuous on `s`. -/
theorem LowerSemicontinuousOn.seqLowerSemicontinuousOn {X β : Type*} [TopologicalSpace X]
    [Preorder β] {f : X → β} {s : Set X} (hf : LowerSemicontinuousOn f s) :
    TauCeti.SeqLowerSemicontinuousOn f s := by
  rw [← TauCeti.seqLowerSemicontinuous_restrict_iff]
  exact (lowerSemicontinuous_restrict_iff.2 hf).seqLowerSemicontinuous

namespace TauCeti

section LinearOrder

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] {f : X → β} {s : Set X}

/-- Sequential lower semicontinuity into a linear order is equivalent to sequential closedness
of every sublevel `{x | f x ≤ b}`. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage :
    SeqLowerSemicontinuous f ↔ ∀ b, IsSeqClosed (f ⁻¹' Iic b) := by
  constructor
  · intro hf b u x hu hux
    change f x ≤ b
    by_contra! hlt
    obtain ⟨n, hn⟩ := (hf hux b hlt).exists
    exact hn.not_ge (hu n)
  · intro h u x hux y hy
    by_contra! hfreq
    obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop hfreq
    exact hy.not_ge (h y hle (hux.comp hφ.tendsto_atTop))

/-- Every sublevel `{x | f x ≤ b}` of a sequentially lower semicontinuous map into a linear
order is sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_preimage (hf : SeqLowerSemicontinuous f) (b : β) :
    IsSeqClosed (f ⁻¹' Iic b) :=
  seqLowerSemicontinuous_iff_isSeqClosed_preimage.1 hf b

/-- On `s`, sequential lower semicontinuity into a linear order is equivalent to preservation
of upper bounds `f (u n) ≤ b` along sequences in `s` converging to a point of `s`. -/
theorem seqLowerSemicontinuousOn_iff_forall_le_of_tendsto :
    SeqLowerSemicontinuousOn f s ↔
      ∀ (b : β) ⦃u : ℕ → X⦄ ⦃x : X⦄,
        x ∈ s → (∀ n, u n ∈ s) → (∀ n, f (u n) ≤ b) → Tendsto u atTop (𝓝 x) → f x ≤ b := by
  rw [← seqLowerSemicontinuous_restrict_iff, seqLowerSemicontinuous_iff_isSeqClosed_preimage]
  constructor
  · intro h b u x hx hu hub hux
    let v : ℕ → s := fun n ↦ ⟨u n, hu n⟩
    exact h b (x := v) (p := ⟨x, hx⟩) hub (tendsto_subtype_rng.2 hux)
  · intro h b u x hub hux
    exact h b x.2 (fun n ↦ (u n).2) hub ((continuous_subtype_val.tendsto x).comp hux)

/-- If every restricted sublevel `{x ∈ s | f x ≤ b}` is sequentially closed, then `f` is
sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_of_forall_isSeqClosed_sublevel
    (h : ∀ b, IsSeqClosed {x ∈ s | f x ≤ b}) : SeqLowerSemicontinuousOn f s :=
  seqLowerSemicontinuousOn_iff_forall_le_of_tendsto.2 fun b _ _ _ hu hub hux ↦
    (h b (fun n ↦ ⟨hu n, hub n⟩) hux).2

/-- On a sequentially closed set `s`, sequential lower semicontinuity makes every sublevel
`{x ∈ s | f x ≤ b}` sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_sublevel (hs : IsSeqClosed s)
    (hf : SeqLowerSemicontinuousOn f s) (b : β) :
    IsSeqClosed {x ∈ s | f x ≤ b} := by
  intro u x hu hux
  have hx : x ∈ s := hs (fun n ↦ (hu n).1) hux
  exact ⟨hx, seqLowerSemicontinuousOn_iff_forall_le_of_tendsto.1 hf b hx
    (fun n ↦ (hu n).1) (fun n ↦ (hu n).2) hux⟩

/-- On a sequentially closed set `s`, sequential lower semicontinuity is equivalent to
sequential closedness of every restricted sublevel `{x ∈ s | f x ≤ b}`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b, IsSeqClosed {x ∈ s | f x ≤ b} :=
  ⟨fun hf b ↦ hf.isSeqClosed_sublevel hs b,
    seqLowerSemicontinuousOn_of_forall_isSeqClosed_sublevel⟩

/-- On a sequential space, sequential lower semicontinuity implies topological lower
semicontinuity. -/
theorem SeqLowerSemicontinuous.lowerSemicontinuous [SequentialSpace X]
    (hf : SeqLowerSemicontinuous f) : LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_preimage.2 fun b ↦ (hf.isSeqClosed_preimage b).isClosed

/-- On a sequential space, topological and sequential lower semicontinuity coincide. -/
theorem lowerSemicontinuous_iff_seqLowerSemicontinuous [SequentialSpace X] :
    LowerSemicontinuous f ↔ SeqLowerSemicontinuous f :=
  ⟨LowerSemicontinuous.seqLowerSemicontinuous, SeqLowerSemicontinuous.lowerSemicontinuous⟩

/-- When the subtype `s` is a sequential space, sequential lower semicontinuity on `s`
implies topological lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.lowerSemicontinuousOn [SequentialSpace s]
    (hf : SeqLowerSemicontinuousOn f s) : LowerSemicontinuousOn f s :=
  lowerSemicontinuous_restrict_iff.1
    (seqLowerSemicontinuous_restrict_iff.2 hf).lowerSemicontinuous

/-- When the subtype `s` is a sequential space, topological and sequential lower
semicontinuity on `s` coincide. -/
theorem lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn [SequentialSpace s] :
    LowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn f s :=
  ⟨LowerSemicontinuousOn.seqLowerSemicontinuousOn,
    SeqLowerSemicontinuousOn.lowerSemicontinuousOn⟩

end LinearOrder

section Liminf

variable {X : Type*} [TopologicalSpace X] {s : Set X}

section CompleteLinearOrder

variable {β : Type*} [CompleteLinearOrder β] {f : X → β}

/-- Into a complete linear order, sequential lower semicontinuity is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along every sequence `u` converging to `x`. -/
theorem seqLowerSemicontinuous_iff_le_liminf :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · intro hf u x hux
    by_contra! hlt
    obtain ⟨z, hzf, y, hly, hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
    exact hzf.not_ge <| le_liminf_of_le (by isBoundedDefault) <|
      (hf hux y hly).mono fun n hn ↦ le_of_not_gt fun hzn ↦ (hdisj _ hzn _ hn).false
  · intro hf u x hux y hy
    exact eventually_lt_of_lt_liminf (hy.trans_le (hf hux))

/-- Along any sequence `u` converging to `x`, a sequentially lower semicontinuous map into a
complete linear order satisfies `f x ≤ liminf (f ∘ u) atTop`. -/
theorem SeqLowerSemicontinuous.le_liminf (hf : SeqLowerSemicontinuous f)
    {u : ℕ → X} {x : X} (hux : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (f ∘ u) atTop :=
  seqLowerSemicontinuous_iff_le_liminf.1 hf hux

/-- On `s`, sequential lower semicontinuity into a complete linear order is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along every sequence `u` in `s` converging to `x ∈ s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄,
        x ∈ s → (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  rw [← seqLowerSemicontinuous_restrict_iff, seqLowerSemicontinuous_iff_le_liminf]
  constructor
  · intro h u x hx hu hux
    let v : ℕ → s := fun n ↦ ⟨u n, hu n⟩
    exact h (u := v) (x := ⟨x, hx⟩) (tendsto_subtype_rng.2 hux)
  · intro h u x hux
    exact h x.2 (fun n ↦ (u n).2) ((continuous_subtype_val.tendsto x).comp hux)

/-- Along any sequence `u` in `s` converging to `x ∈ s`, a map sequentially lower
semicontinuous on `s` into a complete linear order satisfies `f x ≤ liminf (f ∘ u) atTop`. -/
theorem SeqLowerSemicontinuousOn.le_liminf (hf : SeqLowerSemicontinuousOn f s)
    {u : ℕ → X} {x : X} (hx : x ∈ s) (hu : ∀ n, u n ∈ s) (hux : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (f ∘ u) atTop :=
  seqLowerSemicontinuousOn_iff_le_liminf.1 hf hx hu hux

end CompleteLinearOrder

section Real

variable {f : X → ℝ}

/-- Casting a real-valued function to `EReal` preserves sequential lower semicontinuity. -/
@[simp]
theorem seqLowerSemicontinuous_coe_ereal_iff :
    SeqLowerSemicontinuous (fun x ↦ (f x : EReal)) ↔ SeqLowerSemicontinuous f := by
  constructor
  · intro hf u x hux y hy
    simpa only [EReal.coe_lt_coe_iff] using hf hux (y : EReal) (EReal.coe_lt_coe_iff.2 hy)
  · intro hf u x hux y hy
    induction y with
    | bot =>
      exact (hf hux (f x - 1) (sub_one_lt _)).mono fun n _ ↦ EReal.bot_lt_coe _
    | coe r =>
      simpa only [EReal.coe_lt_coe_iff] using hf hux r (EReal.coe_lt_coe_iff.1 hy)
    | top =>
      exact (not_top_lt hy).elim

/-- Casting a real-valued function to `EReal` preserves sequential lower semicontinuity on
`s`. -/
@[simp]
theorem seqLowerSemicontinuousOn_coe_ereal_iff :
    SeqLowerSemicontinuousOn (fun x ↦ (f x : EReal)) s ↔ SeqLowerSemicontinuousOn f s := by
  rw [← seqLowerSemicontinuous_restrict_iff, ← seqLowerSemicontinuous_restrict_iff]
  exact seqLowerSemicontinuous_coe_ereal_iff (f := s.domRestrict f)

/-- For a real-valued map `f`, sequential lower semicontinuity is equivalent to the `EReal`
limit inferior bound `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop` along every
convergent sequence, without coboundedness hypotheses on `f ∘ u`. -/
theorem seqLowerSemicontinuous_iff_coe_le_liminf :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄,
        Tendsto u atTop (𝓝 x) → (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuous_coe_ereal_iff, seqLowerSemicontinuous_iff_le_liminf]
  rfl

/-- For a real-valued map `f`, sequential lower semicontinuity on `s` is equivalent to the
`EReal` limit inferior bound `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop` along
every sequence in `s` converging to `x ∈ s`. -/
theorem seqLowerSemicontinuousOn_iff_coe_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, x ∈ s → (∀ n, u n ∈ s) →
        Tendsto u atTop (𝓝 x) → (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff, seqLowerSemicontinuousOn_iff_le_liminf]
  rfl

end Real

end Liminf

section OrderTopology

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : X → β} {s : Set X}

/-- If `f` is sequentially lower semicontinuous on `s`, `u` is a sequence in `s` converging to
`x ∈ s`, and `f ∘ u` converges to `b`, then `f x ≤ b`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto (hf : SeqLowerSemicontinuousOn f s)
    {u : ℕ → X} {x : X} {b : β} (hx : x ∈ s) (hu : ∀ n, u n ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) (hfu : Tendsto (f ∘ u) atTop (𝓝 b)) :
    f x ≤ b := by
  by_contra! hlt
  by_cases! hmid : ∃ c, b < c ∧ c < f x
  · obtain ⟨c, hbc, hcf⟩ := hmid
    obtain ⟨n, hn₁, hn₂⟩ := ((hfu.eventually (Iio_mem_nhds hbc)).and (hf hx hu hux c hcf)).exists
    exact hn₁.not_gt hn₂
  · obtain ⟨n, hn₁, hn₂⟩ := ((hfu.eventually (Iio_mem_nhds hlt)).and (hf hx hu hux b hlt)).exists
    exact hn₁.not_ge (hmid _ hn₂)

/-- If `f` is sequentially lower semicontinuous, `u` converges to `x`, and `f ∘ u` converges to
`b`, then `f x ≤ b`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto (hf : SeqLowerSemicontinuous f)
    {u : ℕ → X} {x : X} {b : β} (hux : Tendsto u atTop (𝓝 x))
    (hfu : Tendsto (f ∘ u) atTop (𝓝 b)) :
    f x ≤ b :=
  (hf.seqLowerSemicontinuousOn univ).le_of_tendsto (mem_univ x) (fun _ ↦ mem_univ _) hux hfu

/-- When `f '' s` is bounded below and closed intervals in `β` are compact and first-countable,
sequential lower semicontinuity on `s` is equivalent to `f x ≤ b` whenever `u` in `s` converges
to `x ∈ s` and `f ∘ u` converges to a finite limit `b`. -/
theorem seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow
    [CompactIccSpace β] [FirstCountableTopology β] (hbdd : BddBelow (f '' s)) :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄ {b : β}, x ∈ s → (∀ n, u n ∈ s) →
        Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 b) → f x ≤ b := by
  refine ⟨fun hf u x b hx hu hux hfu ↦ hf.le_of_tendsto hx hu hux hfu, fun h ↦ ?_⟩
  rw [seqLowerSemicontinuousOn_iff_forall_le_of_tendsto]
  intro b u x hx hu hub hux
  obtain ⟨a, ha⟩ := hbdd
  have hmem (n : ℕ) : f (u n) ∈ Icc a b := ⟨ha (mem_image_of_mem f (hu n)), hub n⟩
  obtain ⟨c, hcIcc, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  exact (h hx (fun n ↦ hu (φ n)) (hux.comp hφ.tendsto_atTop) hlim).trans hcIcc.2

end OrderTopology

section SeqCompact

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- On a nonempty sequentially compact set, a sequentially lower semicontinuous function into a
first-countable conditionally complete linear order topology attains its minimum whenever it is
bounded below on `s`. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_bddBelow {β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] {f : X → β}
    (hs_ne : s.Nonempty) (hs : IsSeqCompact s)
    (hf : SeqLowerSemicontinuousOn f s) (hbdd : BddBelow (f '' s)) :
    ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨y, _, hy_lim, hy_mem⟩ := exists_seq_tendsto_sInf (hs_ne.image f) hbdd
  choose u hu hfu using hy_mem
  obtain ⟨x, hx, φ, hφ, hux⟩ := hs hu
  have hlim : Tendsto (f ∘ (u ∘ φ)) atTop (𝓝 (sInf (f '' s))) := by
    simpa only [Function.comp_def, hfu] using hy_lim.comp hφ.tendsto_atTop
  exact ⟨x, hx, (isMinOn_iff_le_csInf_image hs_ne hbdd).2
    (hf.le_of_tendsto hx (fun n ↦ hu (φ n)) hux hlim)⟩

/-- On a nonempty sequentially compact set, a sequentially lower semicontinuous function into a
first-countable complete linear order topology attains its minimum. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact {β : Type*}
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] [FirstCountableTopology β]
    {f : X → β} (hs_ne : s.Nonempty) (hs : IsSeqCompact s)
    (hf : SeqLowerSemicontinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x :=
  hf.exists_isMinOn_of_bddBelow hs_ne hs (OrderBot.bddBelow _)

/-- On a nonempty sequentially compact set, a real-valued sequentially lower semicontinuous
function attains its minimum without assuming a lower bound in advance. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_real {f : X → ℝ}
    (hs_ne : s.Nonempty) (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨x, hx, hmin⟩ :=
    (seqLowerSemicontinuousOn_coe_ereal_iff.2 hf).exists_isMinOn_of_isSeqCompact hs_ne hs
  exact ⟨x, hx, fun z hz ↦ EReal.coe_le_coe_iff.1 (hmin hz)⟩

/-- A real-valued sequentially lower semicontinuous function is bounded below on any
sequentially compact set. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact {f : X → ℝ}
    (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    BddBelow (f '' s) := by
  rcases s.eq_empty_or_nonempty with rfl | hs_ne
  · simp
  · obtain ⟨_, _, hmin⟩ := hf.exists_isMinOn_real hs_ne hs
    exact hmin.bddBelow

end SeqCompact

end TauCeti
