/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Closures, closed images, and pointwise quotients

Mathlib relates `closure` to a pointwise product when one factor is *open* — `IsOpen.mul_closure`
and its neighbours in `Mathlib/Topology/Algebra/Group/Pointwise.lean` — and to a pointwise scalar
product when the action is jointly continuous, in `smul_set_closure_subset`. The containment for
division, which needs neither openness nor a group structure, is not there.

It is what a Baire argument needs. Such an argument produces a set whose *closure* has interior,
and the step from there to a neighbourhood of the identity runs through `D / D` for that closure
`D`; without this containment there is no way back from `closure s / closure t` to a closure.

Multiplication and addition carry a closed relation to a closed set if its second coordinate
lies in a compact set. This applies to bounded displacements in proper normed spaces, even when
the first coordinate ranges over a noncompact set.

In a weakly locally compact topological group, intersecting a compact identity neighbourhood with
Mathlib's `exists_closed_nhds_one_inv_eq_mul_subset` yields a closed, compact, symmetric identity
neighbourhood inside any given identity neighbourhood.

## Main results

* `TauCeti.closure_div_closure_subset`, with its additive form
  `TauCeti.closure_sub_closure_subset`.
* `TauCeti.exists_mem_nhds_one_isClosed_isCompact_inv_eq_subset`, with its additive form
  `TauCeti.exists_mem_nhds_zero_isClosed_isCompact_neg_eq_subset`.
* `IsClosed.image_mul_of_snd_subset`, with its additive form
  `IsClosed.image_add_of_snd_subset`.
* `IsCompact.exists_isOpen_superset_mul_subset`, with its additive form
  `IsCompact.exists_isOpen_superset_add_subset`: an open set containing `A * K` with `K` compact
  contains `V * K` for an open superset `V` of `A`. Outer regularity arguments use it to thicken
  an arbitrary set to an open one.
* `IsClosed.div_right_of_isCompact`, with its additive form `IsClosed.sub_right_of_isCompact`.
-/

public section

open Set Pointwise
open scoped Topology

namespace TauCeti

section Div

variable {G : Type*} [TopologicalSpace G] [Div G] [ContinuousDiv G]

/-- **Division carries closures into the closure of the quotient.** Neither set need be open,
unlike in the `IsOpen.mul_closure` family, and `G` need only carry a continuous division — no
group structure, and in particular no inverse. -/
@[to_additive /-- **Subtraction carries closures into the closure of the difference.** Neither set
need be open, and `G` need only carry a continuous subtraction — no group structure, and in
particular no negation. -/]
theorem closure_div_closure_subset (s t : Set G) : closure s / closure t ⊆ closure (s / t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    map_mem_closure₂ continuous_div' ha hb fun _ hx _ hy ↦ div_mem_div hx hy

end Div

/-- Every identity neighbourhood in a weakly locally compact topological group contains a closed,
compact, symmetric identity neighbourhood. -/
@[to_additive /-- Every neighbourhood of zero in a weakly locally compact topological additive
group contains a closed, compact, symmetric neighbourhood of zero. -/]
theorem exists_mem_nhds_one_isClosed_isCompact_inv_eq_subset {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] {U : Set G}
    (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), IsClosed V ∧ IsCompact V ∧ V⁻¹ = V ∧ V ⊆ U := by
  obtain ⟨K₀, hK₀_comp, hK₀_mem⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV_mem, hV_closed, hV_inv, hVV⟩ :=
    exists_closed_nhds_one_inv_eq_mul_subset (Filter.inter_mem hU hK₀_mem)
  have hV_sub : V ⊆ U ∩ K₀ :=
    (subset_mul_left V (mem_of_mem_nhds hV_mem)).trans hVV
  exact ⟨V, hV_mem, hV_closed,
    hK₀_comp.of_isClosed_subset hV_closed (hV_sub.trans inter_subset_right), hV_inv,
    hV_sub.trans inter_subset_left⟩

end TauCeti

/-- The products of a closed relation form a closed set if the second coordinate is contained
in a compact set. -/
@[to_additive /-- The sums of a closed relation form a closed set if the second coordinate is
contained in a compact set. -/]
theorem IsClosed.image_mul_of_snd_subset {G : Type*} [TopologicalSpace G]
    [Group G] [ContinuousDiv G] {s : Set (G × G)} (hs : IsClosed s)
    {C : Set G} (hC : IsCompact C) (hsub : Prod.snd '' s ⊆ C) :
    IsClosed ((fun p : G × G ↦ p.1 * p.2) '' s) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  convert isClosedMap_fst_of_compactSpace _
    (hs.preimage (f := fun p : G × C ↦ (p.1 / p.2, (p.2 : G))) (by fun_prop)) using 1
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1 * p.2, ⟨p.2, hsub ⟨p, hp, rfl⟩⟩), by simpa, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1 / p.2, p.2), hp, by simp⟩

/-- If `A * K` lies in an open set `U` and `K` is compact, then so does `V * K` for an open
superset `V` of `A`, namely the complement of the closed set `Uᶜ * K⁻¹`. The set `A` is
arbitrary. -/
@[to_additive /-- If `A + K` lies in an open set `U` and `K` is compact, then so does `V + K` for
an open superset `V` of `A`, namely the complement of the closed set `Uᶜ + -K`. The set `A` is
arbitrary. -/]
theorem IsCompact.exists_isOpen_superset_mul_subset {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {A K U : Set G} (hK : IsCompact K) (hU : IsOpen U) (h : A * K ⊆ U) :
    ∃ V, IsOpen V ∧ A ⊆ V ∧ V * K ⊆ U := by
  refine ⟨(Uᶜ * K⁻¹)ᶜ, (hU.isClosed_compl.mul_right_of_isCompact hK.inv).isOpen_compl, ?_, ?_⟩
  · -- If `x = u * k` with `u ∉ U` and `k⁻¹ ∈ K`, then `u = x * k⁻¹ ∈ A * K ⊆ U`.
    rintro x hx ⟨u, hu, k, hk, rfl⟩
    exact hu (h ⟨u * k, hx, k⁻¹, hk, mul_inv_cancel_right u k⟩)
  · -- If `v * k ∉ U`, then `v = (v * k) * k⁻¹ ∈ Uᶜ * K⁻¹`.
    rintro _ ⟨v, hv, k, hk, rfl⟩
    by_contra hvk
    exact hv ⟨v * k, hvk, k⁻¹, inv_mem_inv.2 hk, mul_inv_cancel_right v k⟩

/-- The quotient `t / s` of a closed set `t` by a compact set `s` is closed. -/
@[to_additive /-- The difference `t - s` of a closed set `t` and a compact set `s` is closed. -/]
theorem IsClosed.div_right_of_isCompact {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {s t : Set G} (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (t / s) := by
  rw [div_eq_mul_inv]
  exact ht.mul_right_of_isCompact hs.inv

end
