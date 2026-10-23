/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Finset.Sort

/-!
# Locally ordering the distinct values of a finite family

A finite family of continuous functions into a linearly ordered space can be ordered near
a parameter by selecting one fixed label for each distinct value at that parameter, provided
labels coinciding there continue to coincide nearby. The selected labels enumerate all distinct
values in strictly increasing order on one common neighborhood. Empty families are included.

This keeps the original functions, rather than sorting their values independently at each
parameter, so any additional regularity of the functions survives the selection. In particular,
it is useful for turning analytic root labellings with persistent collisions into distinct
ordered root sections.

Over a preconnected space, finitely many continuous functions whose values never coincide are
ordered globally: their order at one point is their order everywhere. They can then be listed as
a stack strictly increasing at every point.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- A finite continuous family with persistent central collisions admits a fixed selection
of labels whose values enumerate its range in strictly increasing order near the central
parameter. Only pairs equal at the central parameter need an equality hypothesis. -/
theorem exists_eventually_strictMono_range_eq {B Y ι : Type*} [TopologicalSpace B]
    [LinearOrder Y] [TopologicalSpace Y] [OrderClosedTopology Y] [Finite ι]
    {f : ι → B → Y} {x₀ : B} (hf : ∀ i, ContinuousAt (f i) x₀)
    (heq : ∀ i j, f i x₀ = f j x₀ → f i =ᶠ[𝓝 x₀] f j) :
    ∃ k : ℕ, ∃ e : Fin k ↪ ι, ∀ᶠ x in 𝓝 x₀,
      StrictMono (fun i ↦ f (e i) x) ∧
        range (fun i ↦ f (e i) x) = range (fun i ↦ f i x) := by
  classical
  let := Fintype.ofFinite ι
  let S := Finset.univ.image (fun i ↦ f i x₀)
  let v := S.orderEmbOfFin rfl
  have hlabel (i : Fin S.card) : ∃ j, f j x₀ = v i := by
    have hi := S.orderEmbOfFin_mem rfl i
    simpa only [S, Finset.mem_image, Finset.mem_univ, true_and] using hi
  choose e he using hlabel
  have hinj : Function.Injective e := by
    intro i j hij
    apply v.injective
    rw [← he i, ← he j, hij]
  have hmono : StrictMono (fun i ↦ f (e i) x₀) := by
    simpa only [he] using v.strictMono
  have hcover (j : ι) : ∃ i, f (e i) x₀ = f j x₀ := by
    have hj : f j x₀ ∈ (S : Set Y) := Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    have hrange : range v = (S : Set Y) := S.range_orderEmbOfFin rfl
    obtain ⟨i, hi⟩ := hrange.symm ▸ hj
    exact ⟨i, (he i).trans hi⟩
  have hlt : ∀ᶠ x in 𝓝 x₀, ∀ i j, i < j → f (e i) x < f (e j) x := by
    refine eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ ?_
    by_cases hij : i < j
    · exact ((hf (e i)).eventually_lt (hf (e j)) (hmono hij)).mono fun _ h ↦ fun _ ↦ h
    · exact Eventually.of_forall fun _ h ↦ (hij h).elim
  have hmem : ∀ᶠ x in 𝓝 x₀, ∀ j, ∃ i, f (e i) x = f j x := by
    refine eventually_all.2 fun j ↦ ?_
    obtain ⟨i, hi⟩ := hcover j
    exact (heq (e i) j hi).mono fun _ h ↦ ⟨i, h⟩
  refine ⟨S.card, ⟨e, hinj⟩, ?_⟩
  filter_upwards [hlt, hmem] with x hx hm
  refine ⟨fun _ _ hij ↦ hx _ _ hij, ?_⟩
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact mem_range_self (e i)
  · rintro ⟨j, rfl⟩
    exact hm j

/-- On a nonempty preconnected space, a finite set `G` of continuous functions into a linear
order, no two of which take the same value at any point, can be listed as `θ₀, θ₁, …, θₖ₋₁`
with `θ₀ x < θ₁ x < ⋯ < θₖ₋₁ x` at every point `x`. -/
theorem exists_strictMono_range_eq {B Y : Type*} [TopologicalSpace B] [PreconnectedSpace B]
    [Nonempty B] [LinearOrder Y] [TopologicalSpace Y] [OrderClosedTopology Y] {G : Set (B → Y)}
    (hG : G.Finite) (hc : ∀ g ∈ G, Continuous g) (hne : G.Pairwise fun f g ↦ ∀ x, f x ≠ g x) :
    ∃ k, ∃ θ : Fin k → B → Y, range θ = G ∧ ∀ x, StrictMono fun i ↦ θ i x := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty B›
  -- Two members are ordered everywhere as they are at `x₀`.
  have hlt {f g : B → Y} (hf : f ∈ G) (hg : g ∈ G) (h : f x₀ < g x₀) (x : B) : f x < g x := by
    have hfg : f ≠ g := by
      rintro rfl
      exact h.false
    refine ((isPreconnected_univ.subset_or_subset (isOpen_lt (hc f hf) (hc g hg))
      (isOpen_lt (hc g hg) (hc f hf)) (disjoint_left.2 fun _ h₁ h₂ ↦ lt_asymm h₁ h₂)
      fun x _ ↦ (hne hf hg hfg x).lt_or_gt).resolve_right fun h' ↦ ?_) (mem_univ x)
    exact lt_asymm h (h' (mem_univ x₀))
  -- List the members in increasing order of their values at `x₀`.
  set V := hG.toFinset.image fun g ↦ g x₀
  set v := V.orderEmbOfFin rfl
  have hV (i : Fin V.card) : ∃ g ∈ G, g x₀ = v i := by
    have h := V.orderEmbOfFin_mem rfl i
    simpa only [V, Finset.mem_image, Set.Finite.mem_toFinset] using h
  choose θ hθG hθv using hV
  refine ⟨V.card, θ, Subset.antisymm (range_subset_iff.2 hθG) fun g hg ↦ ?_,
    fun x i j hij ↦ hlt (hθG i) (hθG j) (by simpa only [hθv] using v.strictMono hij) x⟩
  obtain ⟨i, hi⟩ : g x₀ ∈ range v := by
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_image.2 ⟨g, hG.mem_toFinset.2 hg, rfl⟩
  by_contra hgi
  exact hne (hθG i) hg (fun h ↦ hgi ⟨i, h⟩) x₀ ((hθv i).trans hi)

end TauCeti
