/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Elementary frontier lemmas

Facts about `frontier` that carry no structure of their own: straddling, splitting a domain in
two, clinging to it from inside, and the frontier of an image.
Each is the topological core of a step that a boundary argument would otherwise carry out inside
a concrete space. The list is open-ended; nothing below depends on how many entries it has.

Also recorded here is the sublevel-set lemma `TauCeti.exists_isOpen_subset_pos_forall_frontier_le`:
if `u` and `w` are continuous on the closure of an open set `Ω`, `w` lies below `u` on the frontier
of `Ω` and above it at a point of `Ω`, then `Ω ∩ {u < w}` is an open subset of `Ω` whose closure
lies in `Ω` and on whose frontier `w ≤ u`.

## A connected set that straddles a set meets its frontier

A preconnected set that meets both a set `V` and its complement must meet `frontier V`: it cannot
cross from the inside of `V` to the outside without touching the boundary. This is the
intermediate-value principle in its purely topological form, and it is the mechanism by which a
*path* leaving a set produces a *boundary point* of that set.

Mathlib records the two extreme cases — `frontier_eq_empty_iff` and `nonempty_frontier_iff` say
that in a preconnected *space* the frontier of `V` is empty exactly when `V` is `∅` or `univ` — but
not this relative form, which is the one an argument along a segment or a path needs. No hypothesis
is placed on `V`; only preconnectedness of the straddling set is used.

The proof is the standard clopen argument: the complement of `frontier V` is the disjoint union of
the two open sets `interior V` and `interior Vᶜ` (`compl_frontier_eq_union_interior`), so a
preconnected set avoiding the frontier lies inside one of them, and then it misses `V` entirely or
is contained in `V` entirely.

## Where the boundary of the image of one side of a split domain can lie

Split a set `U` into two pieces `s` and `t` that a map `f` sends to *disjoint open* sets, plus a
remainder `u`. Then `frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`
(`TauCeti.frontier_image_subset_image_union_frontier_image`): the boundary of the image of one side
consists of images of the remainder — the cut — and of boundary points of the whole image, and of
nothing else.

The proof is a three-way case split. A point `p` of `frontier (f '' s)` lies in `closure (f '' U)`,
so if it is not on `frontier (f '' U)` it is a value `f w` with `w` in one of the three covering
sets. It cannot come from `s`, since `f '' s` is open and therefore disjoint from its own frontier;
and it cannot come from `t`, since `f '' t` is then an open neighbourhood of `p`, which must meet
`f '' s`, contradicting disjointness of the two images. So `w ∈ u`.

The source carries no topology; the sides enter topologically only through their images, which are
asked to be open and disjoint, and that is all the argument uses of them. What is asked of the
sides themselves is purely set-theoretic: `s ⊆ U` and the covering `U ⊆ s ∪ t ∪ u`. In particular
`t` need not lie in `U`, and neither side need be open or disjoint from the other. A consumer whose
map is open and injective on two disjoint open sides supplies both image hypotheses, as the
conformal one below does through the open mapping theorem and `Disjoint.image`.

## What a set's frontier sees of a subset

A subset `A` of a set `V` cannot reach `frontier V` except through its own frontier:

> `frontier V ∩ closure A = frontier V ∩ frontier A`

(`TauCeti.frontier_inter_closure_eq_frontier_inter_frontier`). The reason is that `closure A` is
`A ∪ frontier A`, and a point of `A` on `frontier V` is already on `frontier A`: it is adherent to
`A` and, since `interior A ⊆ interior V`, it is not interior to `A`. So the part of `frontier V`
that `A` clings to has two interchangeable descriptions — as the reach of `closure A`, and as the
meeting of two frontiers. The first is the one an argument about limits of points of `A` produces;
the second is the one a diameter estimate consumes, `frontier` being where the estimates of a
domain-splitting argument live.

## A local defining function takes its boundary value on the frontier

If, on an open set `U`, a set `D` is the superlevel set `{a ≤ f}` of a function `f` with values in
a linear order with closed order topology, then `f x = a` at every frontier point `x ∈ U` of `D`
at which `f` is continuous (`TauCeti.eq_of_mem_frontier_of_mem_iff_le`). Where `a < f x`,
continuity puts a whole neighbourhood of `x` in `D`, so `x` is interior to `D`; where `f x < a`, it
puts a whole neighbourhood of `x` outside `D`, so `x` is not adherent to `D`. Neither `D` nor `f`
needs any further hypothesis: `D` need not be closed, and `f` need only be continuous at `x`.

## The frontier of a set between an open and a closed interval

A set `Ω` with `Ioo a b ⊆ Ω ⊆ Icc a b` has its frontier inside `{a, b}`: its closure lies in
`Icc a b` and its interior contains `Ioo a b`. So every set avoiding `a` and `b` is disjoint from
`frontier Ω` (`TauCeti.disjoint_frontier_of_Ioo_subset_of_subset_Icc`), whichever endpoints `Ω`
contains. This is the form in which spectral projections onto intervals are shown to be continuous
functions of a self-adjoint operator whose spectrum avoids the endpoints.

## Consumers

The straddling, splitting and clinging lemmas serve Carathéodory's boundary correspondence for
conformal maps. The first does so through `TauCeti/Analysis/Normed/Module/DiamFrontier.lean`: a
ray leaving a bounded set crosses its frontier, which is what makes the frontier of such a set as
wide as the set itself. The second is the splitting step of
`TauCeti/Analysis/Complex/Conformal/CutDiameter.lean`, where `s` and `t` are the two sides of a
circular crosscut of a domain and `u` is the crosscut arc. The third is what lets
`TauCeti/Analysis/Complex/Conformal/ClusterSet.lean` identify the boundary piece that one side of
such a crosscut cuts off, whose description as a union of cluster sets is naturally a statement
about a closure. The image lemma is used quite differently, for a partial homeomorphism of a real
coordinate space. Nothing here is specific to any of those uses; no lemma mentions a metric,
let alone a holomorphic map.

## Main results

* `IsPreconnected.inter_frontier_nonempty` — a preconnected set meeting both a set and its
  complement meets the frontier of that set.
* `IsPreconnected.subset_of_disjoint_frontier` — a preconnected set that meets a set and misses its
  frontier lies in that set.
* `TauCeti.frontier_image_subset_image_union_frontier_image` — for a set split into two sides with
  disjoint open images plus a remainder, the frontier of the image of the side lying in that set
  lies on the image of the remainder and on the frontier of the image of the whole.
* `TauCeti.frontier_inter_closure_eq_frontier_inter_frontier` — the frontier of a set meets the
  closure of a subset exactly where it meets that subset's frontier.
* `TauCeti.frontier_image_subset_of_closure_subset` — for an open map whose image closure adds at
  most a set `t`, the frontier of an image lies on the image of the frontier, together with `t`.
* `TauCeti.eq_of_mem_frontier_of_mem_iff_le` — a function whose superlevel set `{a ≤ f}` agrees
  with a set on an open set takes the value `a` at the frontier points of the set in that open
  set where it is continuous.
* `TauCeti.disjoint_frontier_of_Ioo_subset_of_subset_Icc` — a set avoiding `a` and `b` is disjoint
  from the frontier of every set between `Ioo a b` and `Icc a b`.
* `TauCeti.nonneg_of_forall_abs_le_frontier` — a bound for the absolute value of a function on the
  frontier of a nonempty compact set in a preconnected noncompact space is nonnegative.
-/

public section

namespace TauCeti

open Set

section Straddle

variable {X : Type*} [TopologicalSpace X] {S V : Set X}

/-- **A preconnected set missing the frontier lies in the interior or in the exterior.** If `S` is
preconnected and disjoint from `frontier V`, then `S ⊆ interior V` or `S ⊆ (closure V)ᶜ`. -/
theorem _root_.IsPreconnected.subset_interior_or_subset_compl_closure (hS : IsPreconnected S)
    (h : Disjoint S (frontier V)) : S ⊆ interior V ∨ S ⊆ (closure V)ᶜ := by
  have hsub : S ⊆ interior V ∪ interior Vᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact fun x hx hxf => h.le_bot ⟨hx, hxf⟩
  rw [interior_compl] at hsub
  exact hS.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left (interior_subset.trans subset_closure)) hsub

/-- **A preconnected set that meets both a set and its complement meets its frontier.** If `S` is
preconnected and contains a point of `V` and a point outside `V`, then `S` meets `frontier V`.

Nothing is assumed about `V`; a preconnected set missing the frontier is confined to the interior
or to the exterior of `V` and therefore cannot straddle `V`. -/
theorem _root_.IsPreconnected.inter_frontier_nonempty (hS : IsPreconnected S)
    (h₁ : (S ∩ V).Nonempty) (h₂ : (S \ V).Nonempty) : (S ∩ frontier V).Nonempty := by
  by_contra hcon
  rcases hS.subset_interior_or_subset_compl_closure
    (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hcon)) with h | h
  · obtain ⟨x, hxS, hxV⟩ := h₂
    exact hxV (interior_subset (h hxS))
  · obtain ⟨x, hxS, hxV⟩ := h₁
    exact h hxS (subset_closure hxV)

/-- A preconnected set that meets `V` and misses its frontier lies in `V`: otherwise it would
straddle `V` and so meet `frontier V`. -/
theorem _root_.IsPreconnected.subset_of_disjoint_frontier (hS : IsPreconnected S)
    (hdisj : Disjoint S (frontier V)) (hmeet : (S ∩ V).Nonempty) : S ⊆ V := by
  by_contra h
  obtain ⟨p, hpS, hpf⟩ := hS.inter_frontier_nonempty hmeet (Set.not_subset.mp h)
  exact hdisj.le_bot ⟨hpS, hpf⟩

/-- **The connected component of a point in the complement of a set `F` stays inside any set
containing the point whose frontier lies in `F`.** Otherwise the component, being preconnected,
would meet both the set and its complement, hence its frontier, which lies in `F`. No hypothesis
places the point outside `F`: for a point of `F` the component is empty. -/
theorem connectedComponentIn_subset_of_frontier_subset {F : Set X} {x₀ : X} (hs : x₀ ∈ V)
    (hfr : frontier V ⊆ F) : connectedComponentIn Fᶜ x₀ ⊆ V := by
  by_contra h
  have hout := nonempty_of_not_subset h
  -- the component is nonempty, so `x₀` lies outside `F` and hence in its own component
  have hx₀ := mem_connectedComponentIn (connectedComponentIn_nonempty_iff.mp
    (hout.mono sdiff_subset))
  obtain ⟨p, hpC, hpf⟩ :=
    isPreconnected_connectedComponentIn.inter_frontier_nonempty ⟨x₀, hx₀, hs⟩ hout
  exact connectedComponentIn_subset _ _ hpC (hfr hpf)

end Straddle

section ImageSplit

variable {X Y : Type*} [TopologicalSpace Y] {f : X → Y} {U s t u : Set X}

/-- **The boundary of the image of one side of a split domain lies on the image of the remainder
and on the boundary of the image of the domain.** If `U` is covered by two sets `s`, `t` with
disjoint open images together with a third set `u`, and `s ⊆ U`, then
`frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`.

The conclusion is about `s`, the side that is asked to lie in `U`. The argument treats the two
sides alike apart from that, so a consumer with `t ⊆ U` in hand bounds `t` as well by swapping
their roles.

A frontier point of `f '' s` lies in `closure (f '' U)`, so if it is not a frontier point of
`f '' U` it is a value `f w` with `w` in one of the three covering sets: `w ∈ s` would place it
inside the open set `f '' s`, which is disjoint from its own frontier, and `w ∈ t` inside the open
set `f '' t`, which meets `f '' s` because the point is in its closure, contradicting disjointness
of the two images. So `w ∈ u`.

The source carries no topology at all: `U` and the three sets covering it are constrained only by
the two set-theoretic hypotheses `hsU : s ⊆ U` and `hcov : U ⊆ s ∪ t ∪ u`, while every topological
hypothesis, and the conclusion, lives in the target. In particular `t` need not lie in `U`, and
the two sides need be neither open nor disjoint nor separated by injectivity — only their images
need be open and disjoint, which is what the argument uses and what an injective open map on two
disjoint open sides supplies. -/
theorem frontier_image_subset_image_union_frontier_image (hfs : IsOpen (f '' s))
    (hft : IsOpen (f '' t)) (hst : Disjoint (f '' s) (f '' t)) (hsU : s ⊆ U)
    (hcov : U ⊆ s ∪ t ∪ u) :
    frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U) := by
  intro p hp
  have hpΩ : p ∈ closure (f '' U) := closure_mono (image_mono hsU) hp.1
  rw [closure_eq_self_union_frontier] at hpΩ
  rcases hpΩ with hpin | hpfr
  · obtain ⟨w, hw, rfl⟩ := hpin
    rcases hcov hw with (hws | hwt) | hwu
    · exact (hfs.inter_frontier_eq.subset ⟨mem_image_of_mem f hws, hp⟩).elim
    · obtain ⟨q, hqt, hqs⟩ := mem_closure_iff.mp hp.1 _ hft (mem_image_of_mem f hwt)
      exact absurd hqs (disjoint_right.mp hst hqt)
    · exact Or.inl (mem_image_of_mem f hwu)
  · exact Or.inr hpfr

end ImageSplit

section Inside

variable {X : Type*} [TopologicalSpace X] {A V : Set X}

/-- **The frontier of a set meets the closure of a subset exactly where it meets that subset's
frontier.** For any `A ⊆ V`,

> `frontier V ∩ closure A = frontier V ∩ frontier A`.

Writing `closure A` as `A ∪ frontier A`, the first piece brings nothing new: a point of `A` on
`frontier V` is adherent to `A` and is kept out of `interior A` by `interior A ⊆ interior V`, so it
already lies on `frontier A`. Only the inclusion `A ⊆ V` is used — `V` need be neither open nor
closed, and `A` is arbitrary.

So the part of `frontier V` that `A` clings to may be described either as its meeting with
`closure A` or as its meeting with `frontier A`. An argument about limits of points of `A` produces
the first; a diameter estimate obtained by splitting `V` into pieces consumes the second. -/
theorem frontier_inter_closure_eq_frontier_inter_frontier (hAV : A ⊆ V) :
    frontier V ∩ closure A = frontier V ∩ frontier A := by
  rw [closure_eq_self_union_frontier, inter_union_distrib_left]
  refine union_eq_right.mpr fun x hx =>
    ⟨hx.1, (mem_frontier_iff_notMem_interior hx.2).mpr fun hint => ?_⟩
  exact (mem_frontier_iff_notMem_interior (hAV hx.2)).mp hx.1 (interior_mono hAV hint)

end Inside

section OpenImage

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s : Set X}
  {t : Set Y}

/-- **The frontier of an image lies on the image of the frontier, plus whatever the closure adds.**
For an open map `f` whose image closure satisfies `closure (f '' s) ⊆ f '' closure s ∪ t`,

> `frontier (f '' s) ⊆ f '' frontier s ∪ t`.

The extra set `t` absorbs whatever an unbounded direction of `s` escapes to: without it the
inclusion would say that the frontier of an image is the image of a frontier, which fails as soon
as `f` sends a divergent sequence somewhere convergent. A consumer supplies `t` together with the
closure hypothesis, typically from a compactness statement about the image; it is often a single
point, but nothing in the argument needs that.

Openness is what the argument uses: it keeps the image of the interior inside the interior of
the image, and it cannot be dropped, as the inclusion of `[0, 1]` into `ℝ` with `s = univ` and
`t = ∅` shows. No injectivity is needed, since a difference of images always lies in the image of
the difference. -/
theorem frontier_image_subset_of_closure_subset (hf : IsOpenMap f)
    (hcl : closure (f '' s) ⊆ f '' closure s ∪ t) :
    frontier (f '' s) ⊆ f '' frontier s ∪ t := by
  refine (Set.sdiff_subset_sdiff hcl (hf.image_interior_subset s)).trans ?_
  rw [Set.union_sdiff_distrib]
  exact Set.union_subset_union (Set.subset_image_sdiff f _ _) Set.sdiff_subset

end OpenImage

section SublevelBetween

variable {X : Type*} [TopologicalSpace X] {Ω : Set X} {u : X → ℝ}

/-- Let `u` and `w` be continuous on the closure of an open set `Ω` with `w < u` on its frontier,
and `u x₀ < w x₀` at some `x₀ ∈ Ω`. Then `G = Ω ∩ {u < w}` is an open subset of `Ω` containing `x₀`,
and the closure of `G` lies in `Ω` and `w ≤ u` on the frontier of `G`. -/
theorem exists_isOpen_subset_pos_forall_frontier_le (hΩo : IsOpen Ω) {w : X → ℝ}
    (huc : ContinuousOn u (closure Ω)) (hwc : ContinuousOn w (closure Ω))
    (hfrw : ∀ y ∈ frontier Ω, w y < u y) {x₀ : X} (hx₀ : x₀ ∈ Ω) (hlt : u x₀ < w x₀) :
    ∃ G, IsOpen G ∧ G ⊆ Ω ∧ closure G ⊆ Ω ∧ x₀ ∈ G ∧ (∀ y ∈ G, 0 < w y - u y) ∧
      ∀ y ∈ frontier G, w y ≤ u y := by
  set G := Ω ∩ (fun y => w y - u y) ⁻¹' Ioi 0
  have hGo : IsOpen G := ((hwc.sub huc).mono subset_closure).isOpen_inter_preimage hΩo isOpen_Ioi
  have hGc : closure G ⊆ Ω := by
    have hT : closure G ⊆ closure Ω ∩ (fun y => w y - u y) ⁻¹' Ici 0 :=
      closure_minimal (fun y hy => ⟨subset_closure hy.1, le_of_lt hy.2⟩)
        ((hwc.sub huc).preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici)
    intro y hy
    obtain ⟨hy₁, hy₂⟩ := hT hy
    by_contra hyΩ
    have := hfrw y (by rw [hΩo.frontier_eq]; exact ⟨hy₁, hyΩ⟩)
    simp only [mem_preimage, mem_Ici] at hy₂
    linarith
  refine ⟨G, hGo, inter_subset_left, hGc, ⟨hx₀, sub_pos.2 hlt⟩, fun y hy => hy.2,
    fun y hy => ?_⟩
  rw [hGo.frontier_eq] at hy
  have : ¬0 < w y - u y := fun h => hy.2 ⟨hGc hy.1, h⟩
  linarith [not_lt.1 this]

end SublevelBetween

section DefiningFunction

open Filter Topology

variable {X α : Type*} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α] {D U : Set X} {f : X → α} {a : α} {x : X}

/-- **A local defining function takes its boundary value on the frontier.** If, on an open set
`U`, the set `D` is the superlevel set `{a ≤ f}` of a function `f` with values in a linear order
with closed order topology, then `f x = a` at every point `x ∈ U` of `frontier D` at which `f` is
continuous. -/
theorem eq_of_mem_frontier_of_mem_iff_le (hU : IsOpen U) (hD : ∀ y ∈ U, y ∈ D ↔ a ≤ f y)
    (hxU : x ∈ U) (hf : ContinuousAt f x) (hx : x ∈ frontier D) : f x = a := by
  refine le_antisymm (not_lt.1 fun h ↦ hx.2 (mem_interior_iff_mem_nhds.2 ?_)) (not_lt.1 fun h ↦ ?_)
  · filter_upwards [hU.mem_nhds hxU, hf (isOpen_Ioi.mem_nhds h)] with y hyU hy
    exact (hD y hyU).2 (le_of_lt hy)
  · have hDc : Dᶜ ∈ 𝓝 x := by
      filter_upwards [hU.mem_nhds hxU, hf (isOpen_Iio.mem_nhds h)] with y hyU hy hyD
      exact not_le.2 hy ((hD y hyU).1 hyD)
    obtain ⟨y, hyD, hy⟩ := mem_closure_iff_nhds.1 hx.1 _ hDc
    exact hyD hy

end DefiningFunction

section Interval

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] {s Ω : Set α}
  {a b : α}

/-- The frontier of a set `Ω` between `Ioo a b` and `Icc a b` lies in `{a, b}`, so every set `s`
avoiding `a` and `b` is disjoint from it. -/
theorem disjoint_frontier_of_Ioo_subset_of_subset_Icc (h₁ : Ioo a b ⊆ Ω) (h₂ : Ω ⊆ Icc a b)
    (ha : a ∉ s) (hb : b ∉ s) : Disjoint s (frontier Ω) := by
  refine disjoint_left.2 fun x hx ⟨hcl, hint⟩ ↦ ?_
  obtain ⟨hax, hxb⟩ := closure_minimal h₂ isClosed_Icc hcl
  rcases hax.eq_or_lt with rfl | hax
  · exact ha hx
  rcases hxb.eq_or_lt with rfl | hxb
  · exact hb hx
  exact hint (interior_maximal h₁ isOpen_Ioo ⟨hax, hxb⟩)

end Interval

section Bound

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [NoncompactSpace X]

/-- A nonempty compact set `K` in a preconnected noncompact space has a nonempty frontier, so a
bound `M` for the absolute value of a function on `frontier K` is nonnegative. -/
theorem nonneg_of_forall_abs_le_frontier {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {f : X → ℝ} {M : ℝ} (hbdry : ∀ ⦃x⦄, x ∈ frontier K → |f x| ≤ M) : 0 ≤ M := by
  obtain ⟨y, hy⟩ := nonempty_frontier_iff.2 ⟨hne, hK.ne_univ⟩
  exact (abs_nonneg _).trans (hbdry hy)

end Bound

end TauCeti
