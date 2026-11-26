/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Cofinal
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Bounds in ordered topological spaces

An estimate proved by a limiting argument typically arrives with an error term attached: one shows
`v ≤ K + e i` for every `i` far enough along a filter, where `e i` vanishes in the limit.  The
result below discharges that error term in one step, turning the eventual approximate bound into
the exact bound `v ≤ K`, so that a proof need not repeat the limit argument at each estimate it
establishes.

In a linearly ordered space with closed lower (or upper) rays, clamping a convergent family `g → a`
against a family escaping to `atBot` via `max` (or to `atTop` via `min`) leaves the limit
unchanged, since the escaping branch is eventually dominated by the convergent one.

## Main results

* `Filter.Tendsto.le_of_eventually_le_add`: if `v ≤ K + e i` eventually along `l` and `e` tends to
  `0` along `l`, then `v ≤ K`.
* `ContinuousWithinAt.le_of_forall_gt_le`: a lower bound `X ≤ g ζ` holding for every `ζ > a`
  passes to `ζ = a` when `g` is continuous from the right at `a`.
* `Filter.Tendsto.exists_forall_le_of_le`: a function tending to `b` along `cofinite` that is at
  least `b` somewhere attains its supremum.
* `Filter.Tendsto.atBot_max` and `Filter.Tendsto.max_atBot`: if one branch tends to `atBot` and the
  other tends to `𝓝 a`, their pointwise `max` tends to `𝓝 a` (with dual versions
  `Filter.Tendsto.atTop_min` and `Filter.Tendsto.min_atTop`).
* `MapClusterPt.ge_of_monotone_atTop` and `MapClusterPt.le_of_monotone_atBot`: a monotone family
  is bounded above by its cluster points at `atTop` and below by its cluster points at `atBot`.
* `ContinuousAt.mem_interior_strict_epigraph`: above a point where `g` is continuous, the strict
  epigraph `{p | g p.1 < p.2}` is a neighbourhood.
* `TauCeti.eq_of_tendsto_section`, `TauCeti.monotone_of_tendsto_section`: uniqueness and
  monotonicity of an index map matching boundary limits of sections on `C` along a set `B`
  meeting `closure C` to pointwise distinct or strictly monotone boundary sections on `B`.
* `TauCeti.exists_mem_Ioo_of_Ioo_subset_closure_range`: a family whose values are dense in a
  nonempty open interval of a densely ordered space takes a value in it.
* `TauCeti.not_tendsto_nhds_of_forall_exists_le`: an unbounded-above sequence `ℕ → α` converges to
  no limit in `α`.
* `TauCeti.not_tendsto_nhds_of_continuousAt_comp_eq`: a sequence `ℕ → β` whose image under a
  continuous map `β → α` is unbounded above converges to no limit in `β`.
* `TauCeti.inter_closure_subset_setOf_le`: if, inside an open set `U`, a set `Ω` is the strict
  sublevel set `{z | f z < g z}` of two functions continuous on `U`, then inside `U` the closure of
  `Ω` lies in `{z | f z ≤ g z}`. This is the local form of Mathlib's `closure_lt_subset_le`.
-/

public section

open Filter Topology

/-- **A bound holding up to a vanishing correction holds outright.**  If `v ≤ K + e i` for all `i`
in some set of the filter `l`, and `e` tends to `0` along `l`, then `v ≤ K`.

No sign condition on `v`, `K` or `e` is required, and addition need only be continuous in each
argument separately. -/
theorem Filter.Tendsto.le_of_eventually_le_add {ι α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] [AddZeroClass α] [SeparatelyContinuousAdd α] {l : Filter ι} [l.NeBot]
    {e : ι → α}
    (he : Tendsto e l (𝓝 0)) {v K : α} (h : ∀ᶠ i in l, v ≤ K + e i) : v ≤ K :=
  ge_of_tendsto (by simpa using he.const_add K) h

/-- A lower bound `X ≤ g ζ` holding for every `ζ > a` passes to `ζ = a` when `g` is continuous
from the right at `a` and `a` is approached from the right. -/
theorem ContinuousWithinAt.le_of_forall_gt_le {α β : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] [TopologicalSpace β] [Preorder β] {a : β} [(𝓝[>] a).NeBot] {X : α}
    {g : β → α} (hg : ContinuousWithinAt g (Set.Ioi a) a) (h : ∀ ζ, a < ζ → X ≤ g ζ) :
    X ≤ g a :=
  ge_of_tendsto hg (eventually_nhdsWithin_of_forall h)

/-- A function to a linearly ordered topological space that tends to `b` along `cofinite` and
is at least `b` somewhere attains its supremum. -/
theorem Filter.Tendsto.exists_forall_le_of_le {α β : Type*} [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] {v : α → β} {b : β} (hv : Tendsto v cofinite (𝓝 b)) {a : α}
    (ha : b ≤ v a) : ∃ t, ∀ s, v s ≤ v t := by
  by_cases h : ∀ s, v s ≤ v a
  · exact ⟨a, h⟩
  obtain ⟨s₁, hs₁⟩ := not_forall.mp h
  have hfin : {s | v s₁ ≤ v s}.Finite := by
    simpa [eventually_cofinite] using
      hv.eventually (eventually_lt_nhds (ha.trans_lt (not_le.mp hs₁)))
  obtain ⟨t, ht, htmax⟩ := hfin.toFinset.exists_max_image v ⟨s₁, by simp⟩
  refine ⟨t, fun s ↦ ?_⟩
  by_cases hs : v s₁ ≤ v s
  · exact htmax s (by simpa using hs)
  · exact (not_le.mp hs).le.trans (by simpa using ht)

/-- If `f` tends to `atBot` and `g` tends to `𝓝 a`, then `fun i ↦ max (f i) (g i)` tends to
`𝓝 a`. -/
@[to_dual /-- If `f` tends to `atTop` and `g` tends to `𝓝 a`, then `fun i ↦ min (f i) (g i)` tends
to `𝓝 a`. -/]
theorem Filter.Tendsto.atBot_max {ι β : Type*} [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] {l : Filter ι} {f g : ι → β} {a : β} (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 a)) : Tendsto (fun i ↦ max (f i) (g i)) l (𝓝 a) := by
  refine hg.congr' ?_
  by_cases hbot : ∃ b, b < a
  · obtain ⟨b, hba⟩ := hbot
    filter_upwards [hf.eventually_le_atBot b, hg.eventually_const_lt hba] with i hfi hgi
    exact (max_eq_right (hfi.trans hgi.le)).symm
  · filter_upwards [hf.eventually_le_atBot a] with i hfi
    exact (max_eq_right (hfi.trans (not_lt.1 fun hgi ↦ hbot ⟨g i, hgi⟩))).symm

/-- If `f` tends to `𝓝 a` and `g` tends to `atBot`, then `fun i ↦ max (f i) (g i)` tends to
`𝓝 a`. -/
@[to_dual /-- If `f` tends to `𝓝 a` and `g` tends to `atTop`, then `fun i ↦ min (f i) (g i)` tends
to `𝓝 a`. -/]
theorem Filter.Tendsto.max_atBot {ι β : Type*} [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] {l : Filter ι} {f g : ι → β} {a : β} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l atBot) : Tendsto (fun i ↦ max (f i) (g i)) l (𝓝 a) := by
  simp_rw [max_comm (f _) (g _)]
  exact hg.atBot_max hf

/-- **A monotone family lies below its cluster points at `atTop`.** If `f` is monotone and `a` is a
cluster point of `f` along `atTop`, then `f i ≤ a` for every `i`. This is `Monotone.ge_of_tendsto`
for a cluster point instead of a limit. -/
theorem MapClusterPt.ge_of_monotone_atTop {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [Preorder α] [ClosedIciTopology α] {f : ι → α} {a : α} (ha : MapClusterPt a atTop f)
    (hf : Monotone f) (i : ι) : f i ≤ a :=
  isClosed_Ici.mem_of_mapClusterPt ha <| (eventually_ge_atTop i).mono fun _ hj ↦ hf hj

/-- **A monotone family lies above its cluster points at `atBot`.** If `f` is monotone and `a` is a
cluster point of `f` along `atBot`, then `a ≤ f i` for every `i`. This is `Monotone.le_of_tendsto`
for a cluster point instead of a limit. -/
theorem MapClusterPt.le_of_monotone_atBot {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [Preorder α] [ClosedIicTopology α] {f : ι → α} {a : α} (ha : MapClusterPt a atBot f)
    (hf : Monotone f) (i : ι) : a ≤ f i :=
  isClosed_Iic.mem_of_mapClusterPt ha <| (eventually_le_atBot i).mono fun _ hj ↦ hf hj

/-- **The strict epigraph is open above a point of continuity.** If `g` is continuous at `x₀` and
`g x₀ < t`, then `(x₀, t)` is an interior point of the strict epigraph `{p | g p.1 < p.2}`. -/
theorem ContinuousAt.mem_interior_strict_epigraph {X α : Type*} [TopologicalSpace X]
    [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] {g : X → α} {x₀ : X}
    (hg : ContinuousAt g x₀) {t : α} (ht : g x₀ < t) :
    (x₀, t) ∈ interior {p : X × α | g p.1 < p.2} :=
  mem_interior_iff_mem_nhds.2 <|
    (hg.comp continuousAt_fst).eventually_lt continuousAt_snd ht

namespace TauCeti

section BoundarySection

variable {X α ι κ : Type*} [TopologicalSpace X] [TopologicalSpace α]
  {C B : Set X} {θ : ι → C → α} {η : κ → B → α} {σ σ' : ι → κ}

/-- Over a boundary set `B` meeting `closure C` on which the sections `η` are pointwise distinct,
at most one index map `σ` can match the limits of `θ` along `C` to `η`. -/
theorem eq_of_tendsto_section [T2Space α] (hBC : (B ∩ closure C).Nonempty)
    (hη : ∀ x : B, Function.Injective fun l ↦ η l x)
    (hσ : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x)))
    (hσ' : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ' i) x))) :
    σ = σ' := by
  obtain ⟨x₀, hx₀B, hx₀C⟩ := hBC
  have : (comap (Subtype.val : C → X) (𝓝 x₀)).NeBot :=
    mem_closure_iff_comap_neBot.mp hx₀C
  funext i
  exact hη ⟨x₀, hx₀B⟩ (tendsto_nhds_unique (hσ i ⟨x₀, hx₀B⟩) (hσ' i ⟨x₀, hx₀B⟩))

/-- If pointwise monotone sections `θ` on `C` converge along `C` at a set `B` meeting
`closure C` to pointwise strictly monotone sections `η` on `B`, the matching index map `σ` is
monotone. -/
theorem monotone_of_tendsto_section [Preorder ι] [LinearOrder κ] [Preorder α]
    [OrderClosedTopology α] (hBC : (B ∩ closure C).Nonempty)
    (hθ : ∀ y : C, Monotone fun i ↦ θ i y) (hη : ∀ x : B, StrictMono fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.val)) (𝓝 (η (σ i) x))) :
    Monotone σ := by
  obtain ⟨x₀, hx₀B, hx₀C⟩ := hBC
  have : (comap (Subtype.val : C → X) (𝓝 x₀)).NeBot :=
    mem_closure_iff_comap_neBot.mp hx₀C
  intro i j hij
  exact (hη ⟨x₀, hx₀B⟩).le_iff_le.mp <|
    le_of_tendsto_of_tendsto (hlim i ⟨x₀, hx₀B⟩) (hlim j ⟨x₀, hx₀B⟩)
      (Eventually.of_forall fun y ↦ hθ y hij)

end BoundarySection

/-- A family whose values are dense in a nonempty open interval of a densely ordered space takes a
value in that interval. -/
theorem exists_mem_Ioo_of_Ioo_subset_closure_range {α ι : Type*} [LinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderClosedTopology α] {c : ι → α} {a b : α} (hab : a < b)
    (h : Set.Ioo a b ⊆ closure (Set.range c)) : ∃ i, c i ∈ Set.Ioo a b := by
  obtain ⟨y, hy⟩ := Set.nonempty_Ioo.2 hab
  obtain ⟨_, hy', i, rfl⟩ := mem_closure_iff.1 (h hy) _ isOpen_Ioo hy
  exact ⟨i, hy'⟩

/-- An unbounded-above sequence `ℕ → α` converges to no limit in `α`. -/
theorem not_tendsto_nhds_of_forall_exists_le {α : Type*} [LinearOrder α] [NoMaxOrder α]
    [TopologicalSpace α] [ClosedIciTopology α] {u : ℕ → α}
    (hu : ∀ B : α, ∃ n : ℕ, B ≤ u n) (a : α) : ¬ Tendsto u atTop (𝓝 a) := by
  intro h
  have hc : IsCofinal (Set.range u) := fun B ↦ by
    obtain ⟨n, hn⟩ := hu B
    exact ⟨u n, ⟨n, rfl⟩, hn⟩
  exact hc.not_bddAbove h.bddAbove_range

/-- If `g : β → α` is continuous at `b` and `g (v n) = u n` is unbounded above in `α`, then `v`
converges to no limit `b` in `β`. -/
theorem not_tendsto_nhds_of_continuousAt_comp_eq {α β : Type*}
    [LinearOrder α] [NoMaxOrder α] [TopologicalSpace α] [ClosedIciTopology α]
    [TopologicalSpace β] {g : β → α} {b : β} (hg : ContinuousAt g b) {v : ℕ → β} {u : ℕ → α}
    (huv : ∀ n, g (v n) = u n) (hu : ∀ B : α, ∃ n : ℕ, B ≤ u n) :
    ¬ Tendsto v atTop (𝓝 b) :=
  fun h ↦ not_tendsto_nhds_of_forall_exists_le hu (g b) ((hg.tendsto.comp h).congr huv)

/-- If `Ω` agrees with `{z | f z < g z}` on an open set `U` where `f` and `g` are continuous, then
the points of `U` in the closure of `Ω` satisfy `f z ≤ g z`. This is the local form of Mathlib's
`closure_lt_subset_le`, as used for a domain described near a boundary point by a defining
inequality. -/
theorem inter_closure_subset_setOf_le {X α : Type*} [TopologicalSpace X] [TopologicalSpace α]
    [Preorder α] [OrderClosedTopology α] {U Ω : Set X} {f g : X → α} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) (hΩ : U ∩ Ω = U ∩ {z | f z < g z}) :
    U ∩ closure Ω ⊆ {z | f z ≤ g z} := fun y hy => by
  have hcl : y ∈ closure (U ∩ {z | f z < g z}) := hΩ ▸ hU.inter_closure hy
  exact ((hf y hy.1).mono Set.inter_subset_left).closure_le hcl
    ((hg y hy.1).mono Set.inter_subset_left) fun z hz => le_of_lt hz.2

end TauCeti
