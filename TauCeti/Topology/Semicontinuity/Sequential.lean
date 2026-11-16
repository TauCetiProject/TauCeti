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
import Mathlib.Topology.Order.IsLUB

/-!
# Sequential lower semicontinuity

A function `f : X → β` from a topological space to a type with `<` is *sequentially lower
semicontinuous on `s`* (`TauCeti.SeqLowerSemicontinuousOn f s`) if along every sequence in `s`
converging to `x ∈ s`, every strict lower bound `y < f x` holds eventually. The global version
is `TauCeti.SeqLowerSemicontinuous f`.

When `β` is a linear order, sequential lower semicontinuity is equivalent to sequential closedness
of every sublevel set; when `β` is a complete linear order, it is equivalent to the `liminf`
inequality `f x ≤ liminf (f ∘ u) atTop`; for real-valued functions, it is equivalent to the
`EReal` `liminf` inequality `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`, allowing
sequences whose values are unbounded above.

Topological lower semicontinuity always implies sequential lower semicontinuity, and the two
notions coincide on any sequential space (in particular on any Fréchet–Urysohn subset). On a
sequentially compact set, a sequentially lower semicontinuous function has sequentially compact
sublevels; if its image is bounded below (which is automatic for real-valued functions), it
attains its minimum on any nonempty sequentially compact set.

## Main definitions

* `TauCeti.SeqLowerSemicontinuousOn`: sequential lower semicontinuity on a subset.
* `TauCeti.SeqLowerSemicontinuous`: global sequential lower semicontinuity.

## Main results

* `TauCeti.seqLowerSemicontinuousOn_iff_sublevel`,
  `TauCeti.seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel`: sublevel characterizations.
* `LowerSemicontinuousOn.seqLowerSemicontinuousOn` and
  `TauCeti.seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn`: relation to topological lower
  semicontinuity, with equivalence on sequential subspaces.
* `TauCeti.seqLowerSemicontinuousOn_iff_le_liminf`,
  `TauCeti.seqLowerSemicontinuousOn_iff_coe_le_liminf_ereal`: `liminf` characterizations.
* `TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto` and
  `TauCeti.seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow`: finite-limit characterization
  for functions bounded below into a first-countable order topology with compact closed intervals.
* `TauCeti.SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact_of_bddBelow` and
  `TauCeti.SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact`: sequential extreme value
  theorems.
-/

public section

open Filter Set Topology

namespace TauCeti

section Defs

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LT β]
  {f g : X → β} {s t : Set X}

/-- A function `f : X → β` is *sequentially lower semicontinuous on `s`* if along every sequence
in `s` converging to `x ∈ s`, every strict lower bound `y < f x` holds eventually. -/
def SeqLowerSemicontinuousOn (f : X → β) (s : Set X) : Prop :=
  ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
    Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- A function `f : X → β` is *sequentially lower semicontinuous* if along every sequence
converging to `x`, every strict lower bound `y < f x` holds eventually. -/
def SeqLowerSemicontinuous (f : X → β) : Prop :=
  ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄,
    Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- Definitional characterization of sequential lower semicontinuity on a set. -/
theorem seqLowerSemicontinuousOn_iff :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Definitional characterization of global sequential lower semicontinuity. -/
theorem seqLowerSemicontinuous_iff :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄,
        Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Along a convergent sequence in `s`, a sequentially lower semicontinuous function on `s`
eventually stays strictly above every strict lower bound of its value at the limit. -/
theorem SeqLowerSemicontinuousOn.eventually_lt (hf : SeqLowerSemicontinuousOn f s)
    {u : ℕ → X} {x : X} (hu : ∀ n, u n ∈ s) (hx : x ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) {y : β} (hy : y < f x) :
    ∀ᶠ n in atTop, y < f (u n) :=
  hf hu hx hux y hy

/-- Along a convergent sequence, a sequentially lower semicontinuous function eventually stays
strictly above every strict lower bound of its value at the limit. -/
theorem SeqLowerSemicontinuous.eventually_lt (hf : SeqLowerSemicontinuous f)
    {u : ℕ → X} {x : X} (hux : Tendsto u atTop (𝓝 x)) {y : β} (hy : y < f x) :
    ∀ᶠ n in atTop, y < f (u n) :=
  hf hux y hy

/-- Sequential lower semicontinuity on `univ` is global sequential lower semicontinuity. -/
@[simp] theorem seqLowerSemicontinuousOn_univ_iff :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f := by
  simp [SeqLowerSemicontinuousOn, SeqLowerSemicontinuous]

/-- Sequential lower semicontinuity on `s` is global sequential lower semicontinuity of the
restriction to the subtype `s`. -/
@[simp] theorem seqLowerSemicontinuous_restrict_iff :
    SeqLowerSemicontinuous (s.domRestrict f) ↔ SeqLowerSemicontinuousOn f s := by
  constructor
  · intro hf u x hu hx hux y hy
    exact hf (u := fun n ↦ ⟨u n, hu n⟩) (x := ⟨x, hx⟩) (tendsto_subtype_rng.2 hux) y hy
  · intro hf u x hux y hy
    exact hf (fun n ↦ (u n).2) x.2 ((continuous_subtype_val.tendsto x).comp hux) y hy

/-- Every function is sequentially lower semicontinuous on the empty set. -/
@[simp] theorem seqLowerSemicontinuousOn_empty : SeqLowerSemicontinuousOn f ∅ :=
  fun _ _ _ hx ↦ hx.elim

/-- Every function is sequentially lower semicontinuous on a singleton. -/
@[simp] theorem seqLowerSemicontinuousOn_singleton {x : X} :
    SeqLowerSemicontinuousOn f {x} :=
  fun _ _ hu hx _ _ hy ↦ Eventually.of_forall fun n ↦ by
    rwa [mem_singleton_iff.1 (hu n), ← mem_singleton_iff.1 hx]

/-- Every constant function is sequentially lower semicontinuous on any set. -/
@[simp] theorem seqLowerSemicontinuousOn_const {y : β} :
    SeqLowerSemicontinuousOn (fun _ : X ↦ y) s :=
  fun _ _ _ _ _ _ hz ↦ Eventually.of_forall fun _ ↦ hz

/-- Every constant function is sequentially lower semicontinuous. -/
@[simp] theorem seqLowerSemicontinuous_const {y : β} :
    SeqLowerSemicontinuous (fun _ : X ↦ y) :=
  fun _ _ _ _ hz ↦ Eventually.of_forall fun _ ↦ hz

/-- Global sequential lower semicontinuity implies sequential lower semicontinuity on any set. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousOn
    (hf : SeqLowerSemicontinuous f) (s : Set X) : SeqLowerSemicontinuousOn f s :=
  fun _ _ _ _ hux ↦ hf hux

/-- Sequential lower semicontinuity on a set passes to subsets. -/
theorem SeqLowerSemicontinuousOn.mono (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) :
    SeqLowerSemicontinuousOn f t :=
  fun _ _ hu hx hux ↦ hf (fun n ↦ hts (hu n)) (hts hx) hux

/-- Sequential lower semicontinuity on a set depends only on values on that set. -/
theorem SeqLowerSemicontinuousOn.congr (hf : SeqLowerSemicontinuousOn f s) (hfg : EqOn f g s) :
    SeqLowerSemicontinuousOn g s := by
  intro u x hu hx hux y hy
  rw [← hfg hx] at hy
  filter_upwards [hf hu hx hux y hy] with n hn
  rwa [← hfg (hu n)]

/-- Functions agreeing on `s` have equivalent sequential lower semicontinuity on `s`. -/
theorem seqLowerSemicontinuousOn_congr (hfg : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s :=
  ⟨fun hf ↦ hf.congr hfg, fun hg ↦ hg.congr hfg.symm⟩

/-- Precomposing with a sequentially continuous map preserves global sequential lower
semicontinuity. -/
theorem SeqLowerSemicontinuous.comp_seqContinuous (hf : SeqLowerSemicontinuous f) {g : Y → X}
    (hg : SeqContinuous g) : SeqLowerSemicontinuous (f ∘ g) :=
  fun _ _ hux ↦ hf (hg hux)

/-- Precomposing with a sequentially continuous map mapping `s` into `t` preserves sequential
lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.comp_seqContinuous (hf : SeqLowerSemicontinuousOn f t)
    {g : Y → X} {s : Set Y} (hg : SeqContinuous g) (hst : MapsTo g s t) :
    SeqLowerSemicontinuousOn (f ∘ g) s :=
  fun _ _ hu hx hux ↦ hf (fun n ↦ hst (hu n)) (hst hx) (hg hux)

/-- Precomposing with a map continuous on `s` into `t` preserves sequential lower
semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.comp_continuousOn (hf : SeqLowerSemicontinuousOn f t)
    {g : Y → X} {s : Set Y} (hg : ContinuousOn g s) (hst : MapsTo g s t) :
    SeqLowerSemicontinuousOn (f ∘ g) s := by
  intro u x hu hx hux
  have hgu : Tendsto (g ∘ u) atTop (𝓝 (g x)) :=
    (hg x hx).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hux
      (Eventually.of_forall hu))
  exact hf (fun n ↦ hst (hu n)) (hst hx) hgu

end Defs

end TauCeti

/-! ### Comparison with topological lower semicontinuity -/

section Comparison

variable {X β : Type*} [TopologicalSpace X] {f : X → β} {s : Set X}

/-- Topological lower semicontinuity on a set implies sequential lower semicontinuity there. -/
theorem LowerSemicontinuousOn.seqLowerSemicontinuousOn [Preorder β]
    (hf : LowerSemicontinuousOn f s) : TauCeti.SeqLowerSemicontinuousOn f s := by
  intro u x hu hx hux y hy
  have hnhds : Tendsto u atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hux (Eventually.of_forall hu)
  exact hnhds.eventually (hf x hx y hy)

/-- Topological lower semicontinuity implies sequential lower semicontinuity. -/
theorem LowerSemicontinuous.seqLowerSemicontinuous [Preorder β] (hf : LowerSemicontinuous f) :
    TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hux y hy ↦ hux.eventually (hf _ y hy)

/-- A sequentially continuous function into an order topology is sequentially lower
semicontinuous. -/
theorem SeqContinuous.seqLowerSemicontinuous [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] (hf : SeqContinuous f) : TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hux _ hy ↦ (hf hux).eventually (Ioi_mem_nhds hy)

end Comparison

namespace TauCeti

/-! ### Sublevel characterizations and equivalence on sequential spaces -/

section LinearOrder

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] {f g : X → β} {s : Set X}

/-- Sequential lower semicontinuity on a set is equivalent to passing upper bounds along
convergent sequences in that set. -/
theorem seqLowerSemicontinuousOn_iff_sublevel :
    SeqLowerSemicontinuousOn f s ↔
      ∀ b, ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → (∀ n, f (u n) ≤ b) → f x ≤ b := by
  constructor
  · intro hf b u x hu hx hux hle
    by_contra! hlt
    obtain ⟨n, hn⟩ := (hf hu hx hux b hlt).exists
    exact not_lt_of_ge (hle n) hn
  · intro h u x hu hx hux y hy
    by_contra hnot
    rw [not_eventually] at hnot
    obtain ⟨φ, hφ, hle⟩ := extraction_of_frequently_atTop hnot
    have hfx : f x ≤ y := h y (fun n ↦ hu (φ n)) hx (hux.comp hφ.tendsto_atTop)
      fun n ↦ not_lt.1 (hle n)
    exact not_lt_of_ge hfx hy

/-- Global sequential lower semicontinuity into a linear order is equivalent to sequential
closedness of every sublevel preimage `f ⁻¹' Iic b`. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage :
    SeqLowerSemicontinuous f ↔ ∀ b, IsSeqClosed (f ⁻¹' Iic b) := by
  rw [← seqLowerSemicontinuousOn_univ_iff, seqLowerSemicontinuousOn_iff_sublevel]
  simp only [mem_univ, forall_const, IsSeqClosed, mem_preimage, mem_Iic]
  exact ⟨fun h b _ _ hle hlim ↦ h b hlim hle, fun h b _ _ hlim hle ↦ h b hle hlim⟩

/-- Every sublevel preimage of a sequentially lower semicontinuous function into a linear order
is sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_preimage
    (hf : SeqLowerSemicontinuous f) (b : β) : IsSeqClosed (f ⁻¹' Iic b) :=
  seqLowerSemicontinuous_iff_isSeqClosed_preimage.1 hf b

/-- On a sequentially closed set, sequential lower semicontinuity into a linear order is
equivalent to sequential closedness of every relative sublevel `{x ∈ s | f x ≤ b}`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b, IsSeqClosed {x ∈ s | f x ≤ b} := by
  rw [seqLowerSemicontinuousOn_iff_sublevel]
  constructor
  · intro hf b u x hu hux
    have hx : x ∈ s := hs (fun n ↦ (hu n).1) hux
    exact ⟨hx, hf b (fun n ↦ (hu n).1) hx hux (fun n ↦ (hu n).2)⟩
  · intro h b u x hu _ hux hle
    exact (h b (fun n ↦ ⟨hu n, hle n⟩) hux).2

/-- On a sequentially closed set, every relative sublevel of a sequentially lower semicontinuous
function into a linear order is sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_sublevel
    (hf : SeqLowerSemicontinuousOn f s) (hs : IsSeqClosed s) (b : β) :
    IsSeqClosed {x ∈ s | f x ≤ b} :=
  (seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel hs).1 hf b

/-- On a sequential space, sequential and topological lower semicontinuity into a linear order
coincide. -/
theorem seqLowerSemicontinuous_iff_lowerSemicontinuous [SequentialSpace X] :
    SeqLowerSemicontinuous f ↔ LowerSemicontinuous f := by
  rw [seqLowerSemicontinuous_iff_isSeqClosed_preimage, lowerSemicontinuous_iff_isClosed_preimage]
  simp only [isSeqClosed_iff_isClosed]

/-- On a sequential space, a sequentially lower semicontinuous function into a linear order is
lower semicontinuous. -/
theorem SeqLowerSemicontinuous.lowerSemicontinuous [SequentialSpace X]
    (hf : SeqLowerSemicontinuous f) : LowerSemicontinuous f :=
  seqLowerSemicontinuous_iff_lowerSemicontinuous.1 hf

/-- On a subset whose induced topology is a sequential space, sequential and topological lower
semicontinuity into a linear order coincide. -/
theorem seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn [SequentialSpace s] :
    SeqLowerSemicontinuousOn f s ↔ LowerSemicontinuousOn f s := by
  rw [← seqLowerSemicontinuous_restrict_iff, ← lowerSemicontinuous_restrict_iff,
    seqLowerSemicontinuous_iff_lowerSemicontinuous]

/-- On a subset whose induced topology is a sequential space, a sequentially lower semicontinuous
function into a linear order is lower semicontinuous. -/
theorem SeqLowerSemicontinuousOn.lowerSemicontinuousOn [SequentialSpace s]
    (hf : SeqLowerSemicontinuousOn f s) : LowerSemicontinuousOn f s :=
  seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn.1 hf

/-- The pointwise supremum of two sequentially lower semicontinuous functions on `s` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.sup (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) : SeqLowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s := by
  intro u x hu hx hux y hy
  simp only [lt_sup_iff] at hy ⊢
  rcases hy with hy | hy
  · filter_upwards [hf hu hx hux y hy] with n using Or.inl
  · filter_upwards [hg hu hx hux y hy] with n using Or.inr

/-- The pointwise supremum of two sequentially lower semicontinuous functions is sequentially
lower semicontinuous. -/
theorem SeqLowerSemicontinuous.sup (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g) : SeqLowerSemicontinuous (fun x ↦ f x ⊔ g x) := by
  rw [← seqLowerSemicontinuousOn_univ_iff] at *
  exact hf.sup hg

/-- The pointwise infimum of two sequentially lower semicontinuous functions on `s` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.inf (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) : SeqLowerSemicontinuousOn (fun x ↦ f x ⊓ g x) s := by
  intro u x hu hx hux y hy
  simp only [lt_inf_iff] at hy ⊢
  exact (hf hu hx hux y hy.1).and (hg hu hx hux y hy.2)

/-- The pointwise infimum of two sequentially lower semicontinuous functions is sequentially
lower semicontinuous. -/
theorem SeqLowerSemicontinuous.inf (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g) : SeqLowerSemicontinuous (fun x ↦ f x ⊓ g x) := by
  rw [← seqLowerSemicontinuousOn_univ_iff] at *
  exact hf.inf hg

/-- Every sublevel of a sequentially lower semicontinuous function on a sequentially compact set
is sequentially compact. -/
theorem SeqLowerSemicontinuousOn.isSeqCompact_sublevel (hf : SeqLowerSemicontinuousOn f s)
    (hs : IsSeqCompact s) (b : β) : IsSeqCompact {x ∈ s | f x ≤ b} := by
  intro u hu
  obtain ⟨x, hx, φ, hφ, hlim⟩ := hs fun n ↦ (hu n).1
  refine ⟨x, ⟨hx, ?_⟩, φ, hφ, hlim⟩
  exact seqLowerSemicontinuousOn_iff_sublevel.1 hf b (fun n ↦ (hu (φ n)).1) hx hlim
    fun n ↦ (hu (φ n)).2

end LinearOrder

/-! ### Suprema -/

section Sup

variable {X : Type*} {ι : Sort*} {δ δ' : Type*} [TopologicalSpace X]
  [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ'] {s : Set X}

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions on `s` into
a conditionally complete linear order is sequentially lower semicontinuous on `s` when bounded
above at every point of `s`. -/
theorem seqLowerSemicontinuousOn_ciSup {f : ι → X → δ'}
    (hbdd : ∀ x ∈ s, BddAbove (range fun i ↦ f i x))
    (hf : ∀ i, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, f i x) s := by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using seqLowerSemicontinuousOn_const
  · intro u x hu hx hux y hy
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hy
    filter_upwards [hf i hu hx hux y hi] with n hn
    exact hn.trans_le (le_ciSup (hbdd (u n) (hu n)) i)

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions on `s` into
a complete linear order is sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_iSup {f : ι → X → δ}
    (hf : ∀ i, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, f i x) s :=
  seqLowerSemicontinuousOn_ciSup (fun _ _ ↦ OrderTop.bddAbove _) hf

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions into a
conditionally complete linear order is sequentially lower semicontinuous when bounded above
pointwise. -/
theorem seqLowerSemicontinuous_ciSup {f : ι → X → δ'}
    (hbdd : ∀ x, BddAbove (range fun i ↦ f i x))
    (hf : ∀ i, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous (fun x ↦ ⨆ i, f i x) := by
  rw [← seqLowerSemicontinuousOn_univ_iff]
  exact seqLowerSemicontinuousOn_ciSup (fun x _ ↦ hbdd x)
    fun i ↦ (hf i).seqLowerSemicontinuousOn _

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions into a
complete linear order is sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_iSup {f : ι → X → δ}
    (hf : ∀ i, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous (fun x ↦ ⨆ i, f i x) :=
  seqLowerSemicontinuous_ciSup (fun _ ↦ OrderTop.bddAbove _) hf

end Sup

/-! ### `liminf` characterizations -/

section Liminf

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β] {f : X → β} {s : Set X}

/-- Sequential lower semicontinuity into a complete linear order is equivalent to the `liminf`
inequality along every convergent sequence in the set. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · intro hf u x hu hx hux
    by_contra! hlt
    obtain ⟨z, ltz, y, ylt, hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
    exact ltz.not_ge
      (le_liminf_of_le (by isBoundedDefault) ((hf hu hx hux y ylt).mono fun _ hn ↦
        le_of_not_gt fun hle ↦ (hdisj _ hle _ hn).false))
  · intro h u x hu hx hux y hy
    exact eventually_lt_of_lt_liminf (hy.trans_le (h hu hx hux))

/-- Along a convergent sequence in `s`, a sequentially lower semicontinuous function into a
complete linear order satisfies `f x ≤ liminf (f ∘ u) atTop`. -/
theorem SeqLowerSemicontinuousOn.le_liminf (hf : SeqLowerSemicontinuousOn f s)
    {u : ℕ → X} {x : X} (hu : ∀ n, u n ∈ s) (hx : x ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) : f x ≤ liminf (f ∘ u) atTop :=
  seqLowerSemicontinuousOn_iff_le_liminf.1 hf hu hx hux

/-- Global sequential lower semicontinuity into a complete linear order is equivalent to the
`liminf` inequality along every convergent sequence. -/
theorem seqLowerSemicontinuous_iff_le_liminf :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄,
        Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  rw [← seqLowerSemicontinuousOn_univ_iff, seqLowerSemicontinuousOn_iff_le_liminf]
  simp

/-- Along a convergent sequence, a sequentially lower semicontinuous function into a complete
linear order satisfies `f x ≤ liminf (f ∘ u) atTop`. -/
theorem SeqLowerSemicontinuous.le_liminf (hf : SeqLowerSemicontinuous f)
    {u : ℕ → X} {x : X} (hux : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (f ∘ u) atTop :=
  seqLowerSemicontinuous_iff_le_liminf.1 hf hux

end Liminf

section ERealLiminf

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X}

/-- Coercing a real-valued function to `EReal` preserves and reflects sequential lower
semicontinuity on a set. -/
@[simp] theorem seqLowerSemicontinuousOn_coe_ereal_iff :
    SeqLowerSemicontinuousOn (fun x ↦ (f x : EReal)) s ↔ SeqLowerSemicontinuousOn f s := by
  constructor
  · intro hf u x hu hx hux y hy
    filter_upwards [hf hu hx hux (y : EReal) (EReal.coe_lt_coe_iff.2 hy)] with n hn
    exact EReal.coe_lt_coe_iff.1 hn
  · intro hf u x hu hx hux y hy
    induction y with
    | bot => exact Eventually.of_forall fun n ↦ EReal.bot_lt_coe (f (u n))
    | top => exact (not_top_lt hy).elim
    | coe r =>
      filter_upwards [hf hu hx hux r (EReal.coe_lt_coe_iff.1 hy)] with n hn
      exact EReal.coe_lt_coe_iff.2 hn

/-- Coercing a real-valued function to `EReal` preserves and reflects global sequential lower
semicontinuity. -/
@[simp] theorem seqLowerSemicontinuous_coe_ereal_iff :
    SeqLowerSemicontinuous (fun x ↦ (f x : EReal)) ↔ SeqLowerSemicontinuous f := by
  simpa only [seqLowerSemicontinuousOn_univ_iff] using
    (seqLowerSemicontinuousOn_coe_ereal_iff (f := f) (s := univ))

/-- Sequential lower semicontinuity of a real-valued function on `s` is equivalent to the `EReal`
`liminf` inequality along every convergent sequence in `s`. -/
theorem seqLowerSemicontinuousOn_iff_coe_le_liminf_ereal :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff, seqLowerSemicontinuousOn_iff_le_liminf]
  simp only [Function.comp_def]

/-- Along a convergent sequence in `s`, a sequentially lower semicontinuous real-valued function
satisfies `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`. -/
theorem SeqLowerSemicontinuousOn.coe_le_liminf_ereal (hf : SeqLowerSemicontinuousOn f s)
    {u : ℕ → X} {x : X} (hu : ∀ n, u n ∈ s) (hx : x ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) :
    (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop :=
  seqLowerSemicontinuousOn_iff_coe_le_liminf_ereal.1 hf hu hx hux

/-- Global sequential lower semicontinuity of a real-valued function is equivalent to the `EReal`
`liminf` inequality along every convergent sequence. -/
theorem seqLowerSemicontinuous_iff_coe_le_liminf_ereal :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_univ_iff, seqLowerSemicontinuousOn_iff_coe_le_liminf_ereal]
  simp

end ERealLiminf

/-! ### Limit inequality, postcomposition, and algebraic operations -/

section OrderTopology

variable {X β γ : Type*} [TopologicalSpace X]
  [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
  {f : X → β} {s : Set X}

/-- If `u n → x` in `s` and `f (u n) → r`, then a sequentially lower semicontinuous function on
`s` satisfies `f x ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto (hf : SeqLowerSemicontinuousOn f s)
    {u : ℕ → X} {x : X} {r : β} (hu : ∀ n, u n ∈ s) (hx : x ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) (hlim : Tendsto (f ∘ u) atTop (𝓝 r)) :
    f x ≤ r := by
  by_contra! hlt
  obtain ⟨z, rz, y, yfx, hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
  obtain ⟨n, hnz, hny⟩ :=
    ((hlim.eventually (Iio_mem_nhds rz)).and (hf hu hx hux y yfx)).exists
  exact (hdisj _ hnz _ hny).false

/-- If `u n → x` and `f (u n) → r`, then a sequentially lower semicontinuous function satisfies
`f x ≤ r`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto (hf : SeqLowerSemicontinuous f)
    {u : ℕ → X} {x : X} {r : β}
    (hux : Tendsto u atTop (𝓝 x)) (hlim : Tendsto (f ∘ u) atTop (𝓝 r)) :
    f x ≤ r :=
  (hf.seqLowerSemicontinuousOn univ).le_of_tendsto (fun _ ↦ mem_univ _) (mem_univ _) hux hlim

/-- When `f '' s` is bounded below in a first-countable order topology with compact closed
intervals (such as `ℝ`), sequential lower semicontinuity on `s` is equivalent to the
limit-inequality condition along sequences whose values converge. -/
theorem seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow
    [CompactIccSpace β] [FirstCountableTopology β] (hbdd : BddBelow (f '' s)) :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄ ⦃r : β⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 r) → f x ≤ r := by
  refine ⟨fun hf _ _ _ hu hx hux hlim ↦ hf.le_of_tendsto hu hx hux hlim, fun h ↦ ?_⟩
  rw [seqLowerSemicontinuousOn_iff_sublevel]
  intro b u x hu hx hux hle
  obtain ⟨m, hm⟩ := hbdd
  have hmem : ∀ n, f (u n) ∈ Icc m b := fun n ↦ ⟨hm (mem_image_of_mem f (hu n)), hle n⟩
  obtain ⟨r, hr, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  exact (h (fun n ↦ hu (φ n)) hx (hux.comp hφ.tendsto_atTop) hlim).trans hr.2

/-- Postcomposing a sequentially lower semicontinuous function on `s` with a continuous monotone
function preserves sequential lower semicontinuity on `s`. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuousOn
    [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    {g : β → γ} (hg : Continuous g) (hf : SeqLowerSemicontinuousOn f s) (gmon : Monotone g) :
    SeqLowerSemicontinuousOn (g ∘ f) s := by
  intro u x hu hx hux y hy
  by_cases hl : ∃ l, l < f x
  · obtain ⟨z, hz, hIoc⟩ :=
      exists_Ioc_subset_of_mem_nhds (hg.continuousAt (Ioi_mem_nhds hy)) hl
    filter_upwards [hf hu hx hux z hz] with n hn
    calc y < g (min (f x) (f (u n))) := hIoc (by simp [hz, hn])
      _ ≤ g (f (u n)) := gmon (min_le_right _ _)
  · exact Eventually.of_forall fun n ↦
      hy.trans_le (gmon (not_lt.1 fun h ↦ hl ⟨f (u n), h⟩))

/-- Postcomposing a sequentially lower semicontinuous function with a continuous monotone function
preserves sequential lower semicontinuity. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuous
    [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    {g : β → γ} (hg : Continuous g) (hf : SeqLowerSemicontinuous f) (gmon : Monotone g) :
    SeqLowerSemicontinuous (g ∘ f) := by
  rw [← seqLowerSemicontinuousOn_univ_iff] at *
  exact hg.comp_seqLowerSemicontinuousOn hf gmon

/-- Multiplying a sequentially lower semicontinuous function on `s` on the left by a nonnegative
constant preserves sequential lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.const_mul [MulZeroClass β] [PosMulMono β] [ContinuousMul β]
    (hf : SeqLowerSemicontinuousOn f s) {c : β} (hc : 0 ≤ c) :
    SeqLowerSemicontinuousOn (fun x ↦ c * f x) s :=
  (continuous_const_mul c).comp_seqLowerSemicontinuousOn hf fun _ _ h ↦
    mul_le_mul_of_nonneg_left h hc

/-- Multiplying a sequentially lower semicontinuous function on the left by a nonnegative constant
preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.const_mul [MulZeroClass β] [PosMulMono β] [ContinuousMul β]
    (hf : SeqLowerSemicontinuous f) {c : β} (hc : 0 ≤ c) :
    SeqLowerSemicontinuous (fun x ↦ c * f x) :=
  (continuous_const_mul c).comp_seqLowerSemicontinuous hf fun _ _ h ↦
    mul_le_mul_of_nonneg_left h hc

end OrderTopology

section Addition

variable {X ι β : Type*} [TopologicalSpace X]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [TopologicalSpace β] [OrderTopology β] {f g : X → β} {s : Set X}

/-- The sum of two sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`, assuming addition is continuous at `(f x, g x)` for each `x ∈ s`. -/
theorem SeqLowerSemicontinuousOn.add' (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : β × β ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuousOn (fun x ↦ f x + g x) s := by
  intro u x hu hx hux y hy
  obtain ⟨U, V, hU, hfxU, hV, hgxV, hUV⟩ :
      ∃ U V : Set β, IsOpen U ∧ f x ∈ U ∧ IsOpen V ∧ g x ∈ V ∧
        U ×ˢ V ⊆ {p : β × β | y < p.1 + p.2} :=
    mem_nhds_prod_iff'.1 (hcont x hx (isOpen_Ioi.mem_nhds hy))
  have hmin {h : X → β} (hh : SeqLowerSemicontinuousOn h s) {W : Set β} (hW : IsOpen W)
      (hxW : h x ∈ W) : ∀ᶠ n in atTop, min (h (u n)) (h x) ∈ W := by
    by_cases hl : ∃ l, l < h x
    · obtain ⟨z, hz, hIoc⟩ := exists_Ioc_subset_of_mem_nhds (hW.mem_nhds hxW) hl
      filter_upwards [hh hu hx hux z hz] with n hn
      by_cases hle : h (u n) ≤ h x
      · simpa [min_eq_left hle] using hIoc ⟨hn, hle⟩
      · simpa [min_eq_right (le_of_not_ge hle)] using hxW
    · simp only [not_exists, not_lt] at hl
      exact Eventually.of_forall fun n ↦ by simpa [min_eq_right (hl (h (u n)))] using hxW
  filter_upwards [hmin hf hU hfxU, hmin hg hV hgxV] with n h₁ h₂
  have hmem : (min (f (u n)) (f x), min (g (u n)) (g x)) ∈ U ×ˢ V := ⟨h₁, h₂⟩
  calc y < min (f (u n)) (f x) + min (g (u n)) (g x) := hUV hmem
    _ ≤ f (u n) + g (u n) := add_le_add (min_le_left _ _) (min_le_left _ _)

/-- The sum of two sequentially lower semicontinuous functions is sequentially lower
semicontinuous, assuming addition is continuous at `(f x, g x)` for each `x`. -/
theorem SeqLowerSemicontinuous.add' (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : β × β ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuous (fun x ↦ f x + g x) := by
  rw [← seqLowerSemicontinuousOn_univ_iff] at *
  exact hf.add' hg fun x _ ↦ hcont x

variable [ContinuousAdd β]

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
theorem seqLowerSemicontinuousOn_sum {f : ι → X → β} {a : Finset ι}
    (ha : ∀ i ∈ a, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ∑ i ∈ a, f i x) s := by
  classical
  induction a using Finset.induction_on with
  | empty => simp
  | insert i a hi ih =>
    simp only [Finset.sum_insert hi]
    exact (ha i (Finset.mem_insert_self i a)).add
      (ih fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))

/-- A finite sum of sequentially lower semicontinuous functions is sequentially lower
semicontinuous. -/
theorem seqLowerSemicontinuous_sum {f : ι → X → β} {a : Finset ι}
    (ha : ∀ i ∈ a, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous (fun x ↦ ∑ i ∈ a, f i x) := by
  rw [← seqLowerSemicontinuousOn_univ_iff]
  exact seqLowerSemicontinuousOn_sum fun i hi ↦ (ha i hi).seqLowerSemicontinuousOn univ

end Addition

/-! ### Sequential minimization and extreme value theorems -/

section Minimization

variable {X β : Type*} [TopologicalSpace X]

/-- If a minimizing sequence in `s` converges to `x ∈ s` and `f` is sequentially lower
semicontinuous on `s`, then `x` minimizes `f` on `s`. -/
theorem SeqLowerSemicontinuousOn.isMinOn_of_tendsto_sInf
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : X → β} {s : Set X} (hf : SeqLowerSemicontinuousOn f s) (hbdd : BddBelow (f '' s))
    {u : ℕ → X} {x : X} (hu : ∀ n, u n ∈ s) (hx : x ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) (hmin : Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' s)))) :
    IsMinOn f s x := fun _ hy ↦
  (hf.le_of_tendsto hu hx hux hmin).trans (csInf_le hbdd (mem_image_of_mem f hy))

/-- **Sequential extreme value theorem.** A sequentially lower semicontinuous function bounded
below on a nonempty sequentially compact set attains its minimum there. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact_of_bddBelow
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] {f : X → β} {s : Set X}
    (hf : SeqLowerSemicontinuousOn f s) (hne : s.Nonempty) (hs : IsSeqCompact s)
    (hbdd : BddBelow (f '' s)) : ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨y, -, hy_lim, hy_mem⟩ := exists_seq_tendsto_sInf (hne.image f) hbdd
  choose u hu hfu using hy_mem
  obtain ⟨x, hx, φ, hφ, hux⟩ := hs hu
  have hmin : Tendsto (f ∘ (u ∘ φ)) atTop (𝓝 (sInf (f '' s))) := by
    have : f ∘ (u ∘ φ) = y ∘ φ := funext fun n ↦ hfu (φ n)
    rw [this]
    exact hy_lim.comp hφ.tendsto_atTop
  exact ⟨x, hx, hf.isMinOn_of_tendsto_sInf hbdd (fun n ↦ hu (φ n)) hx hux hmin⟩

/-- **Sequential extreme value theorem for real-valued functions.** A sequentially lower
semicontinuous real-valued function on a nonempty sequentially compact set attains its minimum
there, without an a priori lower bound. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact
    {f : X → ℝ} {s : Set X} (hf : SeqLowerSemicontinuousOn f s)
    (hne : s.Nonempty) (hs : IsSeqCompact s) : ∃ x ∈ s, IsMinOn f s x := by
  have hf' : SeqLowerSemicontinuousOn (fun x ↦ (f x : EReal)) s :=
    seqLowerSemicontinuousOn_coe_ereal_iff.2 hf
  obtain ⟨x, hx, hmin⟩ :=
    hf'.exists_isMinOn_of_isSeqCompact_of_bddBelow hne hs (OrderBot.bddBelow _)
  exact ⟨x, hx, fun y hy ↦ EReal.coe_le_coe_iff.1 (hmin hy)⟩

/-- A sequentially lower semicontinuous real-valued function is bounded below on every
sequentially compact set. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact
    {f : X → ℝ} {s : Set X} (hf : SeqLowerSemicontinuousOn f s)
    (hs : IsSeqCompact s) : BddBelow (f '' s) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨_, _, hmin⟩ := hf.exists_isMinOn_of_isSeqCompact hne hs
    exact hmin.bddBelow

end Minimization

end TauCeti
