/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import TauCeti.Topology.Order.IsLUB
import TauCeti.Topology.Semicontinuity.ENat

/-!
# Sequential lower semicontinuity

A function `f : X → β` from a topological space to a preordered type is *sequentially lower
semicontinuous* within `s` at `x` (`TauCeti.SeqLowerSemicontinuousWithinAt f s x`) if for every
sequence `u : ℕ → X` in `s` converging to `x` and every strict lower bound `y < f x`, eventually
`y < f (u n)`. As with `LowerSemicontinuousWithinAt`, the definition requires no topology or
completeness on `β`; specialized variants (`SeqLowerSemicontinuousAt`, `SeqLowerSemicontinuousOn`,
`SeqLowerSemicontinuous`) restrict to the ambient space or to every point of `s`.

Every lower semicontinuous function is sequentially lower semicontinuous. For any preordered
codomain, sequential lower semicontinuity is equivalent to sequential closedness of all complements
`(f ⁻¹' Ioi y)ᶜ` (without any countability hypothesis on `β`, via subsequence extraction), and on a
sequential space it agrees with topological lower semicontinuity. When `β` is a linear order,
`(f ⁻¹' Ioi b)ᶜ` simplifies to the sublevel set `f ⁻¹' Iic b`.

When `β` is a complete linear order, sequential lower semicontinuity is equivalent to the lower
limit inequality `f x ≤ liminf (f ∘ u) atTop` along convergent sequences; for `ℝ`-valued functions
the same holds after coercion to `EReal`, accommodating sequences unbounded above, while sequences
with a finite limit `f (u n) → r` satisfy `f x ≤ r`. Finally, on a nonempty sequentially compact
set, a sequentially lower semicontinuous function taking values in a first-countable conditionally
complete linear order attains its minimum whenever bounded below (and automatically when `atBot` is
countably generated, as for `ℝ`).
-/

public section

open Filter Function Set Topology

namespace TauCeti

section Preorder

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Preorder β]
  {f g : X → β} {s t : Set X} {x : X}

/-- `f : X → β` is sequentially lower semicontinuous within `s` at `x` if every sequence in `s`
converging to `x` eventually exceeds any strict lower bound `y < f x`. -/
def SeqLowerSemicontinuousWithinAt (f : X → β) (s : Set X) (x : X) : Prop :=
  ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- `f : X → β` is sequentially lower semicontinuous at `x` if every sequence converging to `x`
eventually exceeds any strict lower bound `y < f x`. -/
def SeqLowerSemicontinuousAt (f : X → β) (x : X) : Prop :=
  ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n)

/-- `f : X → β` is sequentially lower semicontinuous on `s` if it is sequentially lower
semicontinuous within `s` at every point of `s`. -/
def SeqLowerSemicontinuousOn (f : X → β) (s : Set X) : Prop :=
  ∀ x ∈ s, SeqLowerSemicontinuousWithinAt f s x

/-- `f : X → β` is sequentially lower semicontinuous if it is sequentially lower semicontinuous at
every point. -/
def SeqLowerSemicontinuous (f : X → β) : Prop :=
  ∀ x, SeqLowerSemicontinuousAt f x

/-- Unfolded characterization of `SeqLowerSemicontinuousWithinAt`. -/
theorem seqLowerSemicontinuousWithinAt_iff :
    SeqLowerSemicontinuousWithinAt f s x ↔
      ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Unfolded characterization of `SeqLowerSemicontinuousAt`. -/
theorem seqLowerSemicontinuousAt_iff :
    SeqLowerSemicontinuousAt f x ↔
      ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → ∀ y < f x, ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Unfolded characterization of `SeqLowerSemicontinuousOn`. -/
theorem seqLowerSemicontinuousOn_iff :
    SeqLowerSemicontinuousOn f s ↔ ∀ x ∈ s, SeqLowerSemicontinuousWithinAt f s x :=
  Iff.rfl

/-- Unfolded characterization of `SeqLowerSemicontinuous`. -/
theorem seqLowerSemicontinuous_iff :
    SeqLowerSemicontinuous f ↔ ∀ x, SeqLowerSemicontinuousAt f x :=
  Iff.rfl

/-- Along a sequence in `s` converging to `x`, a function sequentially lower semicontinuous within
`s` at `x` eventually exceeds any strict lower bound `y < f x`. -/
theorem SeqLowerSemicontinuousWithinAt.eventually_lt (hf : SeqLowerSemicontinuousWithinAt f s x)
    {u : ℕ → X} (hu : ∀ n, u n ∈ s) (hlim : Tendsto u atTop (𝓝 x)) {y : β} (hy : y < f x) :
    ∀ᶠ n in atTop, y < f (u n) :=
  hf hu hlim y hy

/-- Along a sequence converging to `x`, a function sequentially lower semicontinuous at `x`
eventually exceeds any strict lower bound `y < f x`. -/
theorem SeqLowerSemicontinuousAt.eventually_lt (hf : SeqLowerSemicontinuousAt f x)
    {u : ℕ → X} (hlim : Tendsto u atTop (𝓝 x)) {y : β} (hy : y < f x) :
    ∀ᶠ n in atTop, y < f (u n) :=
  hf hlim y hy

/-- Along a sequence in `s` converging to `x ∈ s`, a function sequentially lower semicontinuous on
`s` eventually exceeds any strict lower bound `y < f x`. -/
theorem SeqLowerSemicontinuousOn.eventually_lt (hf : SeqLowerSemicontinuousOn f s)
    (hx : x ∈ s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) (hlim : Tendsto u atTop (𝓝 x))
    {y : β} (hy : y < f x) : ∀ᶠ n in atTop, y < f (u n) :=
  hf x hx hu hlim y hy

/-- Along a sequence converging to `x`, a sequentially lower semicontinuous function eventually
exceeds any strict lower bound `y < f x`. -/
theorem SeqLowerSemicontinuous.eventually_lt (hf : SeqLowerSemicontinuous f)
    {u : ℕ → X} (hlim : Tendsto u atTop (𝓝 x)) {y : β} (hy : y < f x) :
    ∀ᶠ n in atTop, y < f (u n) :=
  hf x hlim y hy

/-- Sequential lower semicontinuity within `univ` is sequential lower semicontinuity at a point. -/
@[simp]
theorem seqLowerSemicontinuousWithinAt_univ_iff :
    SeqLowerSemicontinuousWithinAt f univ x ↔ SeqLowerSemicontinuousAt f x := by
  simp [SeqLowerSemicontinuousWithinAt, SeqLowerSemicontinuousAt]

/-- Sequential lower semicontinuity on `univ` is global sequential lower semicontinuity. -/
@[simp]
theorem seqLowerSemicontinuousOn_univ_iff :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f := by
  simp [SeqLowerSemicontinuousOn, SeqLowerSemicontinuous]

/-- Sequential lower semicontinuity on `s` is equivalent to sequential lower semicontinuity of the
restriction `s.domRestrict f` on the subtype `s`. -/
@[simp]
theorem seqLowerSemicontinuous_restrict_iff :
    SeqLowerSemicontinuous (s.domRestrict f) ↔ SeqLowerSemicontinuousOn f s := by
  refine ⟨fun h x hx u hu hlim y hy ↦ ?_, fun h ⟨x, hx⟩ v hlim y hy ↦ ?_⟩
  · have hv : Tendsto (fun n ↦ (⟨u n, hu n⟩ : s)) atTop (𝓝 ⟨x, hx⟩) :=
      tendsto_subtype_rng.2 hlim
    exact h ⟨x, hx⟩ hv y hy
  · exact h x hx (fun n ↦ (v n).2) ((continuous_subtype_val.tendsto _).comp hlim) y hy

/-- Every function is sequentially lower semicontinuous on the empty set. -/
@[simp]
theorem seqLowerSemicontinuousOn_empty : SeqLowerSemicontinuousOn f ∅ := by
  simp [SeqLowerSemicontinuousOn]

/-- Sequential lower semicontinuity within a set is inherited by subsets. -/
theorem SeqLowerSemicontinuousWithinAt.mono (hf : SeqLowerSemicontinuousWithinAt f s x)
    (hts : t ⊆ s) : SeqLowerSemicontinuousWithinAt f t x :=
  fun _ hu ↦ hf fun n ↦ hts (hu n)

/-- Sequential lower semicontinuity at `x` implies sequential lower semicontinuity within any set
at `x`. -/
theorem SeqLowerSemicontinuousAt.seqLowerSemicontinuousWithinAt
    (hf : SeqLowerSemicontinuousAt f x) (s : Set X) :
    SeqLowerSemicontinuousWithinAt f s x :=
  fun _ _ hlim ↦ hf hlim

/-- Sequential lower semicontinuity on `s` gives sequential lower semicontinuity within `s` at each
point of `s`. -/
theorem SeqLowerSemicontinuousOn.seqLowerSemicontinuousWithinAt
    (hf : SeqLowerSemicontinuousOn f s) (hx : x ∈ s) :
    SeqLowerSemicontinuousWithinAt f s x :=
  hf x hx

/-- Sequential lower semicontinuity on `s` is inherited by subsets of `s`. -/
theorem SeqLowerSemicontinuousOn.mono (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) :
    SeqLowerSemicontinuousOn f t :=
  fun x hx ↦ (hf x (hts hx)).mono hts

/-- Sequential lower semicontinuity on `s` depends only on the values of `f` on `s`. -/
theorem seqLowerSemicontinuousOn_congr (hfg : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s := by
  refine ⟨fun hf x hx u hu hlim y hy ↦ ?_, fun hg x hx u hu hlim y hy ↦ ?_⟩
  · rw [← hfg hx] at hy
    exact (hf x hx hu hlim y hy).mono fun n hn ↦ by rwa [← hfg (hu n)]
  · rw [hfg hx] at hy
    exact (hg x hx hu hlim y hy).mono fun n hn ↦ by rwa [hfg (hu n)]

/-- Global sequential lower semicontinuity gives sequential lower semicontinuity at each point. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousAt
    (hf : SeqLowerSemicontinuous f) (x : X) : SeqLowerSemicontinuousAt f x :=
  hf x

/-- Global sequential lower semicontinuity gives sequential lower semicontinuity within any set. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousWithinAt
    (hf : SeqLowerSemicontinuous f) (s : Set X) (x : X) :
    SeqLowerSemicontinuousWithinAt f s x :=
  (hf x).seqLowerSemicontinuousWithinAt s

/-- Global sequential lower semicontinuity gives sequential lower semicontinuity on any set. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousOn
    (hf : SeqLowerSemicontinuous f) (s : Set X) : SeqLowerSemicontinuousOn f s :=
  fun x _ ↦ hf.seqLowerSemicontinuousWithinAt s x

/-- Constant functions are sequentially lower semicontinuous within any set. -/
theorem seqLowerSemicontinuousWithinAt_const {b : β} :
    SeqLowerSemicontinuousWithinAt (fun _ : X ↦ b) s x :=
  fun _ _ _ _ hy ↦ Eventually.of_forall fun _ ↦ hy

/-- Constant functions are sequentially lower semicontinuous at any point. -/
theorem seqLowerSemicontinuousAt_const {b : β} :
    SeqLowerSemicontinuousAt (fun _ : X ↦ b) x :=
  fun _ _ _ hy ↦ Eventually.of_forall fun _ ↦ hy

/-- Constant functions are sequentially lower semicontinuous on any set. -/
theorem seqLowerSemicontinuousOn_const {b : β} :
    SeqLowerSemicontinuousOn (fun _ : X ↦ b) s :=
  fun _ _ ↦ seqLowerSemicontinuousWithinAt_const

/-- Constant functions are sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_const {b : β} :
    SeqLowerSemicontinuous (fun _ : X ↦ b) :=
  fun _ ↦ seqLowerSemicontinuousAt_const

/-- Precomposing a sequentially lower semicontinuous function within `s` at `g y` with a map
continuous within `t` at `y` mapping `t` into `s` preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuousWithinAt.comp {g : Y → X} {t : Set Y} {y : Y}
    (hf : SeqLowerSemicontinuousWithinAt f s (g y)) (hg : ContinuousWithinAt g t y)
    (hgt : MapsTo g t s) : SeqLowerSemicontinuousWithinAt (f ∘ g) t y :=
  fun _ hu hlim ↦ hf (fun n ↦ hgt (hu n))
    (hg.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hu⟩))

/-- Precomposing a sequentially lower semicontinuous function at `g y` with a map continuous at `y`
preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuousAt.comp {g : Y → X} {y : Y}
    (hf : SeqLowerSemicontinuousAt f (g y)) (hg : ContinuousAt g y) :
    SeqLowerSemicontinuousAt (f ∘ g) y :=
  fun _ hlim ↦ hf (hg.tendsto.comp hlim)

/-- Precomposing a sequentially lower semicontinuous function on `s` with a map continuous on `t`
mapping `t` into `s` preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuousOn.comp {g : Y → X} {t : Set Y}
    (hf : SeqLowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hgt : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun y hy ↦ (hf (g y) (hgt hy)).comp (hg y hy) hgt

/-- Precomposing a sequentially lower semicontinuous function with a continuous map preserves
sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.comp {g : Y → X} (hf : SeqLowerSemicontinuous f)
    (hg : Continuous g) : SeqLowerSemicontinuous (f ∘ g) :=
  fun y ↦ (hf (g y)).comp hg.continuousAt

/-- Precomposing a sequentially lower semicontinuous function within `s` at `g y` with a
sequentially continuous map mapping `t` into `s` preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuousWithinAt.comp_seqContinuous {g : Y → X} {t : Set Y} {y : Y}
    (hf : SeqLowerSemicontinuousWithinAt f s (g y)) (hg : SeqContinuous g) (hgt : MapsTo g t s) :
    SeqLowerSemicontinuousWithinAt (f ∘ g) t y :=
  fun _ hu hlim ↦ hf (fun n ↦ hgt (hu n)) (hg hlim)

/-- Precomposing a sequentially lower semicontinuous function at `g y` with a sequentially
continuous map preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuousAt.comp_seqContinuous {g : Y → X} {y : Y}
    (hf : SeqLowerSemicontinuousAt f (g y)) (hg : SeqContinuous g) :
    SeqLowerSemicontinuousAt (f ∘ g) y :=
  fun _ hlim ↦ hf (hg hlim)

/-- Precomposing a sequentially lower semicontinuous function on `s` with a sequentially continuous
map mapping `t` into `s` preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuousOn.comp_seqContinuous {g : Y → X} {t : Set Y}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqContinuous g) (hgt : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun y hy ↦ (hf (g y) (hgt hy)).comp_seqContinuous hg hgt

/-- Precomposing a sequentially lower semicontinuous function with a sequentially continuous map
preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.comp_seqContinuous {g : Y → X} (hf : SeqLowerSemicontinuous f)
    (hg : SeqContinuous g) : SeqLowerSemicontinuous (f ∘ g) :=
  fun _ _ hlim ↦ hf _ (hg hlim)

/-- Lower semicontinuity within `s` at `x` implies sequential lower semicontinuity within `s`
at `x`. -/
theorem _root_.LowerSemicontinuousWithinAt.seqLowerSemicontinuousWithinAt
    (hf : LowerSemicontinuousWithinAt f s x) : SeqLowerSemicontinuousWithinAt f s x :=
  fun _ hu hlim y hy ↦
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hu⟩).eventually (hf y hy)

/-- Lower semicontinuity at `x` implies sequential lower semicontinuity at `x`. -/
theorem _root_.LowerSemicontinuousAt.seqLowerSemicontinuousAt
    (hf : LowerSemicontinuousAt f x) : SeqLowerSemicontinuousAt f x :=
  fun _ hlim y hy ↦ hlim.eventually (hf y hy)

/-- Lower semicontinuity on `s` implies sequential lower semicontinuity on `s`. -/
theorem _root_.LowerSemicontinuousOn.seqLowerSemicontinuousOn
    (hf : LowerSemicontinuousOn f s) : SeqLowerSemicontinuousOn f s :=
  fun _ hx ↦ (hf.lowerSemicontinuousWithinAt hx).seqLowerSemicontinuousWithinAt

/-- Lower semicontinuity implies sequential lower semicontinuity. -/
theorem _root_.LowerSemicontinuous.seqLowerSemicontinuous
    (hf : LowerSemicontinuous f) : SeqLowerSemicontinuous f :=
  fun x ↦ (hf.lowerSemicontinuousAt x).seqLowerSemicontinuousAt

/-- Sequential lower semicontinuity is equivalent to sequential closedness of `(f ⁻¹' Ioi y)ᶜ`
for every `y : β`. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage :
    SeqLowerSemicontinuous f ↔ ∀ y, IsSeqClosed (f ⁻¹' Ioi y)ᶜ := by
  refine ⟨fun hf y u z hu hlim hy ↦ ?_, fun h z u hlim y hy ↦ ?_⟩
  · obtain ⟨n, hn⟩ := (hf z hlim y hy).exists
    exact hu n hn
  · by_contra hnot
    rw [not_eventually] at hnot
    obtain ⟨φ, hφ, hφy⟩ := extraction_of_frequently_atTop hnot
    exact h y hφy (hlim.comp hφ.tendsto_atTop) hy

/-- For a sequentially lower semicontinuous function, `(f ⁻¹' Ioi y)ᶜ` is sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_compl_preimage (hf : SeqLowerSemicontinuous f)
    (y : β) : IsSeqClosed (f ⁻¹' Ioi y)ᶜ :=
  seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage.1 hf y

/-- On a sequential space, sequential lower semicontinuity is equivalent to topological lower
semicontinuity. -/
theorem seqLowerSemicontinuous_iff_lowerSemicontinuous [SequentialSpace X] :
    SeqLowerSemicontinuous f ↔ LowerSemicontinuous f := by
  simp only [seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage, isSeqClosed_iff_isClosed,
    isClosed_compl_iff, lowerSemicontinuous_iff_isOpen_preimage]

/-- On a sequential space, a sequentially lower semicontinuous function is lower semicontinuous. -/
theorem SeqLowerSemicontinuous.lowerSemicontinuous [SequentialSpace X]
    (hf : SeqLowerSemicontinuous f) : LowerSemicontinuous f :=
  seqLowerSemicontinuous_iff_lowerSemicontinuous.1 hf

/-- When the subtype `s` is a sequential space, sequential lower semicontinuity on `s` is
equivalent to topological lower semicontinuity on `s`. -/
theorem seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn [SequentialSpace s] :
    SeqLowerSemicontinuousOn f s ↔ LowerSemicontinuousOn f s := by
  rw [← seqLowerSemicontinuous_restrict_iff, ← lowerSemicontinuous_restrict_iff,
    seqLowerSemicontinuous_iff_lowerSemicontinuous]

/-- When the subtype `s` is a sequential space, a sequentially lower semicontinuous function on `s`
is lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.lowerSemicontinuousOn [SequentialSpace s]
    (hf : SeqLowerSemicontinuousOn f s) : LowerSemicontinuousOn f s :=
  seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn.1 hf

end Preorder

section LinearOrder

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] {f : X → β} {s : Set X} {x : X}

/-- A sequentially continuous function into a linearly ordered space with closed lower rays is
sequentially lower semicontinuous. -/
theorem _root_.SeqContinuous.seqLowerSemicontinuous [TopologicalSpace β] [ClosedIicTopology β]
    (hf : SeqContinuous f) : SeqLowerSemicontinuous f :=
  fun _ _ hlim _ hy ↦ (hf hlim).eventually (eventually_gt_nhds hy)

/-- For a linearly ordered codomain, sequential lower semicontinuity is equivalent to sequential
closedness of all sublevels `f ⁻¹' Iic b`. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage :
    SeqLowerSemicontinuous f ↔ ∀ b, IsSeqClosed (f ⁻¹' Iic b) := by
  simp only [seqLowerSemicontinuous_iff_isSeqClosed_compl_preimage, ← preimage_compl, compl_Ioi]

/-- Sublevels of a sequentially lower semicontinuous function are sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_preimage (hf : SeqLowerSemicontinuous f) (b : β) :
    IsSeqClosed (f ⁻¹' Iic b) :=
  seqLowerSemicontinuous_iff_isSeqClosed_preimage.1 hf b

/-- Sequential lower semicontinuity on `s` is equivalent to sequential closedness of each sublevel
in the subtype `s`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_subtype :
    SeqLowerSemicontinuousOn f s ↔ ∀ b, IsSeqClosed (((↑) : s → X) ⁻¹' (f ⁻¹' Iic b)) := by
  rw [← seqLowerSemicontinuous_restrict_iff, seqLowerSemicontinuous_iff_isSeqClosed_preimage]
  rfl

/-- On a sequentially closed set `s`, sequential lower semicontinuity of `f` on `s` is equivalent
to sequential closedness of every relative sublevel `{x ∈ s | f x ≤ b}` in the ambient space. -/
theorem _root_.IsSeqClosed.seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b, IsSeqClosed {x ∈ s | f x ≤ b} := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_subtype]
  refine forall_congr' fun b ↦ ⟨fun hb u z hu hlim ↦ ?_, fun hb v ⟨z, hz⟩ hv hlim ↦ ?_⟩
  · have hz : z ∈ s := hs (fun n ↦ (hu n).1) hlim
    refine ⟨hz, ?_⟩
    have hv : Tendsto (fun n ↦ (⟨u n, (hu n).1⟩ : s)) atTop (𝓝 ⟨z, hz⟩) :=
      tendsto_subtype_rng.2 hlim
    exact hb (fun n ↦ (hu n).2) hv
  · exact (hb (fun n ↦ ⟨(v n).2, hv n⟩) ((continuous_subtype_val.tendsto _).comp hlim)).2

/-- On a sequentially closed set `s`, each relative sublevel `{x ∈ s | f x ≤ b}` of a sequentially
lower semicontinuous function is sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_sublevel (hf : SeqLowerSemicontinuousOn f s)
    (hs : IsSeqClosed s) (b : β) : IsSeqClosed {x ∈ s | f x ≤ b} :=
  (hs.seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel.1 hf) b

end LinearOrder

section Liminf

variable {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}

section CompleteLinearOrder

variable {β : Type*} [CompleteLinearOrder β] {f : X → β}

/-- For a complete linear order, sequential lower semicontinuity within `s` at `x` is equivalent to
the `liminf` inequality `f x ≤ liminf (f ∘ u) atTop` along sequences in `s` converging to `x`. -/
theorem seqLowerSemicontinuousWithinAt_iff_le_liminf :
    SeqLowerSemicontinuousWithinAt f s x ↔
      ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  refine forall_congr' fun u ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  rw [le_liminf_iff]
  rfl

alias ⟨SeqLowerSemicontinuousWithinAt.le_liminf, _⟩ := seqLowerSemicontinuousWithinAt_iff_le_liminf

/-- For a complete linear order, sequential lower semicontinuity at `x` is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along sequences converging to `x`. -/
theorem seqLowerSemicontinuousAt_iff_le_liminf :
    SeqLowerSemicontinuousAt f x ↔
      ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  rw [← seqLowerSemicontinuousWithinAt_univ_iff, seqLowerSemicontinuousWithinAt_iff_le_liminf]
  simp

alias ⟨SeqLowerSemicontinuousAt.le_liminf, _⟩ := seqLowerSemicontinuousAt_iff_le_liminf

/-- For a complete linear order, sequential lower semicontinuity on `s` is equivalent to
`f x ≤ liminf (f ∘ u) atTop` for all `x ∈ s` and sequences in `s` converging to `x`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        f x ≤ liminf (f ∘ u) atTop := by
  simp only [seqLowerSemicontinuousOn_iff, seqLowerSemicontinuousWithinAt_iff_le_liminf]

alias ⟨SeqLowerSemicontinuousOn.le_liminf, _⟩ := seqLowerSemicontinuousOn_iff_le_liminf

/-- For a complete linear order, sequential lower semicontinuity is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along all convergent sequences. -/
theorem seqLowerSemicontinuous_iff_le_liminf :
    SeqLowerSemicontinuous f ↔
      ∀ x, ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  simp only [seqLowerSemicontinuous_iff, seqLowerSemicontinuousAt_iff_le_liminf]

alias ⟨SeqLowerSemicontinuous.le_liminf, _⟩ := seqLowerSemicontinuous_iff_le_liminf

end CompleteLinearOrder

section RealEReal

variable {f : X → ℝ}

/-- For a real-valued function, sequential lower semicontinuity within `s` at `x` is equivalent to
the `EReal`-valued `liminf` inequality `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`
along sequences in `s` converging to `x`, including sequences unbounded above. -/
theorem seqLowerSemicontinuousWithinAt_real_iff_le_liminf_ereal :
    SeqLowerSemicontinuousWithinAt f s x ↔
      ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  refine forall_congr' fun u ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  rw [le_liminf_iff, EReal.forall]
  simp

alias ⟨SeqLowerSemicontinuousWithinAt.coe_ereal_le_liminf, _⟩ :=
  seqLowerSemicontinuousWithinAt_real_iff_le_liminf_ereal

/-- For a real-valued function, sequential lower semicontinuity at `x` is equivalent to the
`EReal`-valued `liminf` inequality along every sequence converging to `x`. -/
theorem seqLowerSemicontinuousAt_real_iff_le_liminf_ereal :
    SeqLowerSemicontinuousAt f x ↔
      ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousWithinAt_univ_iff,
    seqLowerSemicontinuousWithinAt_real_iff_le_liminf_ereal]
  simp

alias ⟨SeqLowerSemicontinuousAt.coe_ereal_le_liminf, _⟩ :=
  seqLowerSemicontinuousAt_real_iff_le_liminf_ereal

/-- For a real-valued function, sequential lower semicontinuity on `s` is equivalent to the
`EReal`-valued `liminf` inequality along every sequence in `s` converging to a point of `s`. -/
theorem seqLowerSemicontinuousOn_real_iff_le_liminf_ereal :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ ⦃u : ℕ → X⦄, (∀ n, u n ∈ s) → Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  simp only [seqLowerSemicontinuousOn_iff, seqLowerSemicontinuousWithinAt_real_iff_le_liminf_ereal]

alias ⟨SeqLowerSemicontinuousOn.coe_ereal_le_liminf, _⟩ :=
  seqLowerSemicontinuousOn_real_iff_le_liminf_ereal

/-- For a real-valued function, sequential lower semicontinuity is equivalent to the
`EReal`-valued `liminf` inequality along all convergent sequences. -/
theorem seqLowerSemicontinuous_real_iff_le_liminf_ereal :
    SeqLowerSemicontinuous f ↔
      ∀ x, ∀ ⦃u : ℕ → X⦄, Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  simp only [seqLowerSemicontinuous_iff, seqLowerSemicontinuousAt_real_iff_le_liminf_ereal]

alias ⟨SeqLowerSemicontinuous.coe_ereal_le_liminf, _⟩ :=
  seqLowerSemicontinuous_real_iff_le_liminf_ereal

end RealEReal

end Liminf

section AlgebraAndLimits

variable {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}

/-- Along a sequence in `s` converging to `x` whose values under `f` converge to `r`, sequential
lower semicontinuity within `s` at `x` gives `f x ≤ r`. -/
theorem SeqLowerSemicontinuousWithinAt.le_of_tendsto {β : Type*} [LinearOrder β]
    [TopologicalSpace β] [ClosedIciTopology β] {f : X → β}
    (hf : SeqLowerSemicontinuousWithinAt f s x) {u : ℕ → X} {r : β}
    (hu : ∀ n, u n ∈ s) (hlim : Tendsto u atTop (𝓝 x))
    (hflim : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) : f x ≤ r := by
  by_contra! hlt
  obtain ⟨y', hy', z, hz, hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
  obtain ⟨n, hn₁, hn₂⟩ := ((hflim.eventually (eventually_lt_nhds hy')).and (hf hu hlim z hz)).exists
  exact (hdisj _ hn₁ _ hn₂).false

/-- Along a sequence converging to `x` whose values under `f` converge to `r`, sequential lower
semicontinuity at `x` gives `f x ≤ r`. -/
theorem SeqLowerSemicontinuousAt.le_of_tendsto {β : Type*} [LinearOrder β]
    [TopologicalSpace β] [ClosedIciTopology β] {f : X → β}
    (hf : SeqLowerSemicontinuousAt f x) {u : ℕ → X} {r : β}
    (hlim : Tendsto u atTop (𝓝 x)) (hflim : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) :
    f x ≤ r :=
  (hf.seqLowerSemicontinuousWithinAt univ).le_of_tendsto (fun _ ↦ mem_univ _) hlim hflim

/-- Along a sequence in `s` converging to `x ∈ s` whose values under `f` converge to `r`,
sequential lower semicontinuity on `s` gives `f x ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto {β : Type*} [LinearOrder β]
    [TopologicalSpace β] [ClosedIciTopology β] {f : X → β}
    (hf : SeqLowerSemicontinuousOn f s) (hx : x ∈ s) {u : ℕ → X} {r : β}
    (hu : ∀ n, u n ∈ s) (hlim : Tendsto u atTop (𝓝 x))
    (hflim : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) : f x ≤ r :=
  (hf x hx).le_of_tendsto hu hlim hflim

/-- Along a sequence converging to `x` whose values under `f` converge to `r`, sequential lower
semicontinuity gives `f x ≤ r`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto {β : Type*} [LinearOrder β]
    [TopologicalSpace β] [ClosedIciTopology β] {f : X → β}
    (hf : SeqLowerSemicontinuous f) {u : ℕ → X} {r : β}
    (hlim : Tendsto u atTop (𝓝 x)) (hflim : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) :
    f x ≤ r :=
  (hf x).le_of_tendsto hlim hflim

/-- Postcomposing with a monotone function continuous at `f x` preserves sequential lower
semicontinuity within `s` at `x`. -/
theorem _root_.ContinuousAt.comp_seqLowerSemicontinuousWithinAt {γ δ : Type*}
    [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
    {g : γ → δ} {f : X → γ} (hg : ContinuousAt g (f x))
    (hf : SeqLowerSemicontinuousWithinAt f s x) (hmono : Monotone g) :
    SeqLowerSemicontinuousWithinAt (g ∘ f) s x := by
  intro u hu hlim
  let F : ℕ∞ → γ := ENat.recTopCoe (f x) (f ∘ u)
  have hF : LowerSemicontinuousAt F ⊤ :=
    ENat.lowerSemicontinuousAt_top_iff.2 (hf hu hlim)
  have hgF : ContinuousAt g (F ⊤) := hg
  simpa only [F, ENat.recTopCoe_top, ENat.recTopCoe_natCast, Function.comp_apply] using
    ENat.lowerSemicontinuousAt_top_iff.1 (hgF.comp_lowerSemicontinuousAt hF hmono)

/-- Postcomposing with a monotone function continuous at `f x` preserves sequential lower
semicontinuity at `x`. -/
theorem _root_.ContinuousAt.comp_seqLowerSemicontinuousAt {γ δ : Type*}
    [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
    {g : γ → δ} {f : X → γ} (hg : ContinuousAt g (f x))
    (hf : SeqLowerSemicontinuousAt f x) (hmono : Monotone g) :
    SeqLowerSemicontinuousAt (g ∘ f) x := by
  rw [← seqLowerSemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hg.comp_seqLowerSemicontinuousWithinAt hf hmono

/-- Postcomposing with a monotone continuous function preserves sequential lower semicontinuity
on `s`. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuousOn {γ δ : Type*}
    [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
    {g : γ → δ} {f : X → γ} (hg : Continuous g)
    (hf : SeqLowerSemicontinuousOn f s) (hmono : Monotone g) :
    SeqLowerSemicontinuousOn (g ∘ f) s :=
  fun x hx ↦ hg.continuousAt.comp_seqLowerSemicontinuousWithinAt (hf x hx) hmono

/-- Postcomposing with a monotone continuous function preserves sequential lower semicontinuity. -/
theorem _root_.Continuous.comp_seqLowerSemicontinuous {γ δ : Type*}
    [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
    {g : γ → δ} {f : X → γ} (hg : Continuous g)
    (hf : SeqLowerSemicontinuous f) (hmono : Monotone g) :
    SeqLowerSemicontinuous (g ∘ f) :=
  fun x ↦ hg.continuousAt.comp_seqLowerSemicontinuousAt (hf x) hmono

/-- The sum of two sequentially lower semicontinuous functions within `s` at `x` is sequentially
lower semicontinuous, assuming continuity of addition at `(f x, g x)`. -/
theorem SeqLowerSemicontinuousWithinAt.add' {γ : Type*} [AddCommMonoid γ] [LinearOrder γ]
    [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuousWithinAt f s x) (hg : SeqLowerSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuousWithinAt (fun z ↦ f z + g z) s x := by
  intro u hu hlim
  let F : ℕ∞ → γ := ENat.recTopCoe (f x) (f ∘ u)
  let G : ℕ∞ → γ := ENat.recTopCoe (g x) (g ∘ u)
  have hF : LowerSemicontinuousAt F ⊤ := ENat.lowerSemicontinuousAt_top_iff.2 (hf hu hlim)
  have hG : LowerSemicontinuousAt G ⊤ := ENat.lowerSemicontinuousAt_top_iff.2 (hg hu hlim)
  simpa only [F, G, ENat.recTopCoe_top, ENat.recTopCoe_natCast, Function.comp_apply] using
    ENat.lowerSemicontinuousAt_top_iff.1 (hF.add' hG hcont)

/-- The sum of two sequentially lower semicontinuous functions at `x` is sequentially lower
semicontinuous, assuming continuity of addition at `(f x, g x)`. -/
theorem SeqLowerSemicontinuousAt.add' {γ : Type*} [AddCommMonoid γ] [LinearOrder γ]
    [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuousAt f x) (hg : SeqLowerSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuousAt (fun z ↦ f z + g z) x := by
  rw [← seqLowerSemicontinuousWithinAt_univ_iff] at hf hg ⊢
  exact hf.add' hg hcont

/-- The sum of two sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`, assuming pointwise continuity of addition on `s`. -/
theorem SeqLowerSemicontinuousOn.add' {γ : Type*} [AddCommMonoid γ] [LinearOrder γ]
    [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuousOn (fun z ↦ f z + g z) s :=
  fun x hx ↦ (hf x hx).add' (hg x hx) (hcont x hx)

/-- The sum of two sequentially lower semicontinuous functions is sequentially lower
semicontinuous, assuming pointwise continuity of addition. -/
theorem SeqLowerSemicontinuous.add' {γ : Type*} [AddCommMonoid γ] [LinearOrder γ]
    [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ ↦ p.1 + p.2) (f x, g x)) :
    SeqLowerSemicontinuous (fun z ↦ f z + g z) :=
  fun x ↦ (hf x).add' (hg x) (hcont x)

/-- The sum of two sequentially lower semicontinuous functions within `s` at `x` is sequentially
lower semicontinuous when addition is continuous. -/
theorem SeqLowerSemicontinuousWithinAt.add {γ : Type*} [AddCommMonoid γ] [LinearOrder γ]
    [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuousWithinAt f s x) (hg : SeqLowerSemicontinuousWithinAt g s x) :
    SeqLowerSemicontinuousWithinAt (fun z ↦ f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two sequentially lower semicontinuous functions at `x` is sequentially lower
semicontinuous when addition is continuous. -/
theorem SeqLowerSemicontinuousAt.add {γ : Type*} [AddCommMonoid γ] [LinearOrder γ]
    [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuousAt f x) (hg : SeqLowerSemicontinuousAt g x) :
    SeqLowerSemicontinuousAt (fun z ↦ f z + g z) x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two sequentially lower semicontinuous functions on `s` is sequentially lower
semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.add {γ : Type*} [AddCommMonoid γ] [LinearOrder γ]
    [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun z ↦ f z + g z) s :=
  hf.add' hg fun _ _ ↦ continuous_add.continuousAt

/-- The sum of two sequentially lower semicontinuous functions is sequentially lower
semicontinuous. -/
theorem SeqLowerSemicontinuous.add {γ : Type*} [AddCommMonoid γ] [LinearOrder γ]
    [IsOrderedAddMonoid γ] [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ] {f g : X → γ}
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous (fun z ↦ f z + g z) :=
  hf.add' hg fun _ ↦ continuous_add.continuousAt

end AlgebraAndLimits

/-- Along a sequence in `s` whose images under an equivalence `e : X ≃ Y` converge to `e x` with
`x ∈ s` and whose values under `f` converge to `r`, sequential lower semicontinuity of `f ∘ e.symm`
on `e '' s` gives `f x ≤ r`. -/
theorem _root_.Equiv.le_of_seqLowerSemicontinuousOn_image {X Y β : Type*} [TopologicalSpace Y]
    [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β] (e : X ≃ Y) {f : X → β}
    {s : Set X} (hf : SeqLowerSemicontinuousOn (fun y ↦ f (e.symm y)) (e '' s))
    {x : X} (hx : x ∈ s) {u : ℕ → X} {r : β} (hu : ∀ n, u n ∈ s)
    (hlim : Tendsto (fun n ↦ e (u n)) atTop (𝓝 (e x)))
    (hflim : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) : f x ≤ r := by
  simpa only [Equiv.symm_apply_apply] using
    hf.le_of_tendsto (mem_image_of_mem e hx) (fun n ↦ mem_image_of_mem e (hu n)) hlim
      (by simpa only [Equiv.symm_apply_apply] using hflim)

section SeqCompact

variable {X β : Type*} [TopologicalSpace X] {f : X → β} {s : Set X}

/-- A sequentially lower semicontinuous function into a nonempty linear order with countably
generated `atBot` is bounded below on every sequentially compact set. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact [LinearOrder β] [Nonempty β]
    [(atBot : Filter β).IsCountablyGenerated] (hs : IsSeqCompact s)
    (hf : SeqLowerSemicontinuousOn f s) : BddBelow (f '' s) := by
  by_contra hnot
  obtain ⟨b, -, hb_lim⟩ := exists_seq_antitone_tendsto_atTop_atBot β
  have hex (n : ℕ) : ∃ x ∈ s, f x < b n := by
    by_contra! hle
    exact hnot ⟨b n, forall_mem_image.2 hle⟩
  choose u hu hfu using hex
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hs hu
  have hnot_min : ¬ IsMin (f a) := fun hmin ↦
    hnot ⟨f a, forall_mem_image.2 fun x _ ↦ le_of_not_gt hmin.not_lt⟩
  obtain ⟨y, hy⟩ := not_isMin_iff.1 hnot_min
  have hev₁ := hf a ha (fun k ↦ hu (φ k)) hlim y hy
  have hev₂ := (hb_lim.comp hφ.tendsto_atTop).eventually (eventually_le_atBot y)
  obtain ⟨k, hk₁, hk₂⟩ := (hev₁.and hev₂).exists
  exact hk₁.not_ge ((hfu (φ k)).le.trans hk₂)

/-- On a nonempty sequentially compact set, a sequentially lower semicontinuous function into a
first-countable conditionally complete linear order that is bounded below attains its minimum. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact_of_bddBelow
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] (hne : s.Nonempty) (hs : IsSeqCompact s)
    (hf : SeqLowerSemicontinuousOn f s) (hbdd : BddBelow (f '' s)) :
    ∃ a ∈ s, IsMinOn f s a := by
  obtain ⟨u, hu, -, hy_lim⟩ := exists_seq_forall_mem_and_tendsto_sInf hne hbdd
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hs hu
  refine ⟨a, ha, fun x hx ↦ ?_⟩
  exact (hf.le_of_tendsto ha (fun k ↦ hu (φ k)) hlim (hy_lim.comp hφ.tendsto_atTop)).trans
    (csInf_le hbdd (mem_image_of_mem f hx))

/-- On a nonempty sequentially compact set, a sequentially lower semicontinuous function into a
first-countable conditionally complete linear order with countably generated `atBot` attains its
minimum without a separate lower-bound assumption. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] [(atBot : Filter β).IsCountablyGenerated]
    (hne : s.Nonempty) (hs : IsSeqCompact s) (hf : SeqLowerSemicontinuousOn f s) :
    ∃ a ∈ s, IsMinOn f s a :=
  have : Nonempty β := ⟨f hne.some⟩
  hf.exists_isMinOn_of_isSeqCompact_of_bddBelow hne hs (hf.bddBelow_of_isSeqCompact hs)

end SeqCompact

end TauCeti
