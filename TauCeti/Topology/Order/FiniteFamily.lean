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

A finite family of functions into a linearly ordered space, each converging along a filter, can
be ordered eventually along that filter by selecting one fixed label for each distinct limit,
provided labels with equal limits eventually coincide. The selected labels then eventually
enumerate all distinct values in strictly increasing order. For a family continuous at a
parameter and the neighborhood filter there, this happens on one common neighborhood. Empty
families are included.

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

/-- A finite family converging along a filter `l`, whose members with equal limits eventually
coincide along `l`, admits a fixed selection of labels whose values eventually enumerate its
range in strictly increasing order. Only pairs with equal limits need an equality hypothesis.
For `l = 𝓝 x₀` and a family continuous at `x₀`, the limits are the central values. -/
theorem exists_eventually_strictMono_range_eq {B Y ι : Type*} [LinearOrder Y]
    [TopologicalSpace Y] [OrderClosedTopology Y] [Finite ι] {f : ι → B → Y} {l : Filter B}
    {a : ι → Y} (hf : ∀ i, Tendsto (f i) l (𝓝 (a i)))
    (heq : ∀ i j, a i = a j → f i =ᶠ[l] f j) :
    ∃ k : ℕ, ∃ e : Fin k ↪ ι, ∀ᶠ x in l,
      StrictMono (fun i ↦ f (e i) x) ∧
        range (fun i ↦ f (e i) x) = range (fun i ↦ f i x) := by
  let := Fintype.ofFinite ι
  -- Label the distinct limits in increasing order, each by one index attaining it.
  let S := Finset.univ.image a
  let v := S.orderEmbOfFin rfl
  have hlabel (i : Fin S.card) : ∃ j, a j = v i := by
    have hi := S.orderEmbOfFin_mem rfl i
    simpa only [S, Finset.mem_image, Finset.mem_univ, true_and] using hi
  choose e he using hlabel
  have hmono : StrictMono (a ∘ e) := by
    simpa only [Function.comp_def, he] using v.strictMono
  have hcover (j : ι) : ∃ i, a (e i) = a j := by
    obtain ⟨i, hi⟩ : a j ∈ range v := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem a (Finset.mem_univ j))
    exact ⟨i, (he i).trans hi⟩
  have hlt : ∀ᶠ x in l, ∀ i j, i < j → f (e i) x < f (e j) x :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ eventually_imp_distrib_left.2 fun hij ↦
      (hf (e i)).eventually_lt (hf (e j)) (hmono hij)
  have hmem : ∀ᶠ x in l, ∀ j, ∃ i, f (e i) x = f j x :=
    eventually_all.2 fun j ↦ (hcover j).elim fun i hi ↦ (heq (e i) j hi).mono fun _ h ↦ ⟨i, h⟩
  refine ⟨S.card, ⟨e, hmono.injective.of_comp⟩, ?_⟩
  filter_upwards [hlt, hmem] with x hx hm
  exact ⟨fun _ _ hij ↦ hx _ _ hij,
    Subset.antisymm (range_subset_iff.2 fun i ↦ mem_range_self (e i)) (range_subset_iff.2 hm)⟩

/-- On a preconnected space, a finite set `G` of continuous functions into a linear
order, no two of which take the same value at any point, can be listed as `θ₀, θ₁, …, θₖ₋₁`
with `θ₀ x < θ₁ x < ⋯ < θₖ₋₁ x` at every point `x`. -/
theorem exists_strictMono_range_eq {B Y : Type*} [TopologicalSpace B] [PreconnectedSpace B]
    [LinearOrder Y] [TopologicalSpace Y] [OrderClosedTopology Y] {G : Set (B → Y)}
    (hG : G.Finite) (hc : ∀ g ∈ G, Continuous g) (hne : G.Pairwise fun f g ↦ ∀ x, f x ≠ g x) :
    ∃ k, ∃ θ : Fin k → B → Y, range θ = G ∧ ∀ x, StrictMono fun i ↦ θ i x := by
  classical
  -- Over an empty base there is a single function, so `G` has at most one member.
  rcases isEmpty_or_nonempty B with hB | ⟨⟨x₀⟩⟩
  · rcases G.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
    · exact ⟨0, Fin.elim0, by simp, fun x ↦ (hB.false x).elim⟩
    · refine ⟨1, fun _ ↦ g, ?_, fun x ↦ (hB.false x).elim⟩
      ext f
      simp [Subsingleton.elim f g, hg]
  -- Two members are ordered everywhere as they are at `x₀`.
  have hlt {f g : B → Y} (hf : f ∈ G) (hg : g ∈ G) (h : f x₀ < g x₀) (x : B) : f x < g x := by
    have hfg : f ≠ g := by
      rintro rfl
      exact h.false
    refine ((isPreconnected_univ.subset_or_subset (isOpen_lt (hc f hf) (hc g hg))
      (isOpen_lt (hc g hg) (hc f hf)) (disjoint_left.2 fun _ h₁ h₂ ↦ lt_asymm h₁ h₂)
      fun x _ ↦ (hne hf hg hfg x).lt_or_gt).resolve_right fun h' ↦ ?_) (mem_univ x)
    exact lt_asymm h (h' (mem_univ x₀))
  -- List the members in increasing order of their values at `x₀`: this is the local ordering
  -- above along the principal filter `pure x₀`, where every pair with equal values coincides.
  have := hG.to_subtype
  obtain ⟨k, e, he⟩ := exists_eventually_strictMono_range_eq (f := fun g : G ↦ (g : B → Y))
    (fun g ↦ tendsto_pure_nhds _ x₀) fun _ _ h ↦ eventually_pure.2 h
  obtain ⟨hmono, hrange⟩ := eventually_pure.1 he
  refine ⟨k, fun i ↦ e i, Subset.antisymm (range_subset_iff.2 fun i ↦ (e i).2) fun g hg ↦ ?_,
    fun x i j hij ↦ hlt (e i).2 (e j).2 (hmono hij) x⟩
  obtain ⟨i, hi⟩ : g x₀ ∈ range fun i ↦ (e i : B → Y) x₀ := hrange ▸ mem_range_self (⟨g, hg⟩ : G)
  by_contra hgi
  exact hne (e i).2 hg (fun h ↦ hgi ⟨i, h⟩) x₀ hi

end TauCeti
