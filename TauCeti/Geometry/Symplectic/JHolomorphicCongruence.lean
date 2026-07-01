/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import TauCeti.Geometry.Symplectic.JHolomorphic

/-!
# Congruence lemmas for `J`-holomorphic maps

This file records the locality API for the normed-vector-space `J`-holomorphic predicates used
by the analytic Heegaard Floer roadmap. A `J`-holomorphic condition depends only on a local
representative of the map near the point or within the source set, because the underlying
Frechet derivative has the same locality property.

These lemmas are the chart-level bookkeeping needed before the roadmap upgrades the local
Cauchy--Riemann equation to almost complex manifolds, where maps are constantly replaced by
equal local representatives in overlapping charts and restricted domains.

## Main declarations

* `TauCeti.IsJHolomorphicAt.congr_of_eventuallyEq`: pointwise locality under equality in a
  neighborhood.
* `TauCeti.IsJHolomorphicWithinAt.congr_of_eventuallyEq` and
  `TauCeti.IsJHolomorphicWithinAt.congr_mono`: within-set locality under equality in the
  source filter or on a smaller source set.
* `TauCeti.isJHolomorphicWithinAt_congr_set`: changing the source set near the base point.
* `TauCeti.IsJHolomorphicOn.congr_mono`, `IsJHolomorphicOn.congr`, and
  `isJHolomorphicOn_congr`: setwise congruence API.

The proofs are thin wrappers around Mathlib's Frechet-derivative congruence lemmas in
`Mathlib.Analysis.Calculus.FDeriv.Congr`.
-/

public section

namespace TauCeti

open Filter
open scoped Topology

variable {V W : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f g : V → W} {s t : Set V} {x : V}

/-- Pointwise `J`-holomorphicity is unchanged after replacing a map by one equal to it in a
neighborhood of the point. -/
lemma IsJHolomorphicAt.congr_of_eventuallyEq (hf : IsJHolomorphicAt J J' f x)
    (hfg : g =ᶠ[𝓝 x] f) : IsJHolomorphicAt J J' g x :=
  ⟨hf.choose, hf.hasFDerivAt.congr_of_eventuallyEq hfg, hf.derivative_isComplexLinear⟩

/-- Pointwise `J`-holomorphicity is unchanged under local equality near the point. -/
lemma Filter.EventuallyEq.isJHolomorphicAt_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsJHolomorphicAt J J' f x ↔ IsJHolomorphicAt J J' g x :=
  ⟨fun hf => hf.congr_of_eventuallyEq hfg.symm,
    fun hg => hg.congr_of_eventuallyEq hfg⟩

/-- A pointwise `J`-holomorphic map may be replaced by a map equal to it everywhere. -/
lemma IsJHolomorphicAt.congr (hf : IsJHolomorphicAt J J' f x)
    (hfg : ∀ y, g y = f y) : IsJHolomorphicAt J J' g x :=
  hf.congr_of_eventuallyEq (Filter.Eventually.of_forall hfg)

/-- Pointwise `J`-holomorphicity is invariant under pointwise equality of maps. -/
lemma isJHolomorphicAt_congr (hfg : ∀ y, f y = g y) :
    IsJHolomorphicAt J J' f x ↔ IsJHolomorphicAt J J' g x :=
  (Filter.EventuallyEq.isJHolomorphicAt_iff (Filter.Eventually.of_forall hfg))

/-- Within-set `J`-holomorphicity is unchanged after replacing a map by one equal to it in the
source-set neighborhood filter, provided the values also agree at the base point. -/
lemma IsJHolomorphicWithinAt.congr_of_eventuallyEq
    (hf : IsJHolomorphicWithinAt J J' f s x) (hfg : g =ᶠ[𝓝[s] x] f)
    (hx : g x = f x) : IsJHolomorphicWithinAt J J' g s x :=
  ⟨hf.choose, hf.hasFDerivWithinAt.congr_of_eventuallyEq hfg hx,
    hf.derivative_isComplexLinear⟩

/-- Within-set `J`-holomorphicity is unchanged after replacing a map by one equal to it in the
source-set neighborhood filter, when the base point belongs to the source set. -/
lemma IsJHolomorphicWithinAt.congr_of_eventuallyEq_of_mem
    (hf : IsJHolomorphicWithinAt J J' f s x) (hfg : g =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    IsJHolomorphicWithinAt J J' g s x :=
  hf.congr_of_eventuallyEq hfg (hfg.eq_of_nhdsWithin hx)

/-- Within-set `J`-holomorphicity is unchanged under local equality in the source-set
neighborhood filter, provided the values agree at the base point. -/
lemma Filter.EventuallyEq.isJHolomorphicWithinAt_iff (hfg : f =ᶠ[𝓝[s] x] g)
    (hx : f x = g x) :
    IsJHolomorphicWithinAt J J' f s x ↔ IsJHolomorphicWithinAt J J' g s x :=
  ⟨fun hf => hf.congr_of_eventuallyEq hfg.symm hx.symm,
    fun hg => hg.congr_of_eventuallyEq hfg hx⟩

/-- Within-set `J`-holomorphicity is unchanged under local equality in the source-set
neighborhood filter, when the base point belongs to the source set. -/
lemma Filter.EventuallyEq.isJHolomorphicWithinAt_iff_of_mem (hfg : f =ᶠ[𝓝[s] x] g)
    (hx : x ∈ s) :
    IsJHolomorphicWithinAt J J' f s x ↔ IsJHolomorphicWithinAt J J' g s x :=
  Filter.EventuallyEq.isJHolomorphicWithinAt_iff hfg (hfg.eq_of_nhdsWithin hx)

/-- Within-set `J`-holomorphicity is unchanged after replacing a map by an equal map on the
source set and at the base point. -/
lemma IsJHolomorphicWithinAt.congr (hf : IsJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f s) (hx : g x = f x) : IsJHolomorphicWithinAt J J' g s x :=
  hf.congr_of_eventuallyEq hfg.eventuallyEq_nhdsWithin hx

/-- Within-set `J`-holomorphicity is unchanged after replacing a map by an equal map on the
source set, when the base point belongs to the source set. -/
lemma IsJHolomorphicWithinAt.congr' (hf : IsJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f s) (hx : x ∈ s) : IsJHolomorphicWithinAt J J' g s x :=
  hf.congr hfg (hfg hx)

/-- Restrict the source set and replace a within-set `J`-holomorphic map by one equal to it on
the smaller source set and at the base point. -/
lemma IsJHolomorphicWithinAt.congr_mono (hf : IsJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f t) (hx : g x = f x) (hts : t ⊆ s) :
    IsJHolomorphicWithinAt J J' g t x :=
  ⟨hf.choose, hf.hasFDerivWithinAt.congr_mono hfg hx hts, hf.derivative_isComplexLinear⟩

/-- Restrict the source set and replace a within-set `J`-holomorphic map by one equal to it on
the smaller source set, when the base point belongs to that smaller source set. -/
lemma IsJHolomorphicWithinAt.congr_mono' (hf : IsJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f t) (hx : x ∈ t) (hts : t ⊆ s) :
    IsJHolomorphicWithinAt J J' g t x :=
  hf.congr_mono hfg (hfg hx) hts

/-- Within-set `J`-holomorphicity is invariant under changing the source set in a neighborhood
of the base point. -/
lemma isJHolomorphicWithinAt_congr_set (hst : s =ᶠ[𝓝 x] t) :
    IsJHolomorphicWithinAt J J' f s x ↔ IsJHolomorphicWithinAt J J' f t x := by
  constructor
  · rintro ⟨f', hf', hlin⟩
    exact ⟨f', (hasFDerivWithinAt_congr_set hst).mp hf', hlin⟩
  · rintro ⟨f', hf', hlin⟩
    exact ⟨f', (hasFDerivWithinAt_congr_set hst).mpr hf', hlin⟩

/-- Setwise `J`-holomorphicity on a smaller source set is unchanged after replacing a map by
one equal to it on that smaller source set. -/
lemma IsJHolomorphicOn.congr_mono (hf : IsJHolomorphicOn J J' f s)
    (hfg : Set.EqOn g f t) (hts : t ⊆ s) : IsJHolomorphicOn J J' g t :=
  fun x hx => (hf x (hts hx)).congr_mono hfg (hfg hx) hts

/-- Setwise `J`-holomorphicity is unchanged after replacing a map by one equal to it on the
source set. -/
lemma IsJHolomorphicOn.congr (hf : IsJHolomorphicOn J J' f s)
    (hfg : Set.EqOn g f s) : IsJHolomorphicOn J J' g s :=
  hf.congr_mono hfg (fun _ hx => hx)

/-- Setwise `J`-holomorphicity is invariant under equality of maps on the source set. -/
lemma isJHolomorphicOn_congr (hfg : Set.EqOn f g s) :
    IsJHolomorphicOn J J' f s ↔ IsJHolomorphicOn J J' g s :=
  ⟨fun hf => hf.congr fun _ hx => (hfg hx).symm,
    fun hg => hg.congr hfg⟩

/-- A globally `J`-holomorphic map may be replaced by a pointwise equal map. -/
lemma IsJHolomorphic.congr (hf : IsJHolomorphic J J' f) (hfg : ∀ x, g x = f x) :
    IsJHolomorphic J J' g :=
  fun x => (hf x).congr hfg

/-- Global `J`-holomorphicity is invariant under pointwise equality of maps. -/
lemma isJHolomorphic_congr (hfg : ∀ x, f x = g x) :
    IsJHolomorphic J J' f ↔ IsJHolomorphic J J' g :=
  ⟨fun hf => hf.congr fun x => (hfg x).symm,
    fun hg => hg.congr hfg⟩

end TauCeti
