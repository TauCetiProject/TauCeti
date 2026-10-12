/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# The compact-open topology: discreteness, and pairing maps into a product

A continuous map `f` from a compact space to a discrete space has finite image, and each of its
fibres is closed, hence compact. Prescribing the value of a map on each of those finitely many
fibres is therefore a finite intersection of compact-open subbasic sets, so it is an open
condition, and it pins the map down to `f` itself. Consequently `C(X, Y)` is discrete.

Compactness of `X` is used and not merely convenient: for `X = ℕ` discrete and `Y = Bool` the
compact subsets of `X` are the finite ones, so the compact-open topology on `C(ℕ, Bool)` is the
product topology, which is not discrete.

The file also records when pairing two maps into a product, `(f, g) ↦ (x ↦ (f x, g x))`, is
continuous for the compact-open topologies. Mathlib's `ContinuousMap.continuous_prodMk_const` is
the case where the first map is constant. The case where the second map is constant follows by
swapping the factors, and the general case holds for every regular source: a compact set on which
`(f, g)` lands in an open set `U` is covered by finitely many compact pieces on each of which
`(f, g)` lands in a box inside `U`, and the pieces exist because every point has a closed
neighbourhood inside any given open one. Regularity is used and not merely convenient: for the
one-point compactification of `ℚ` as source and the Sierpiński space as both targets, the maps
`(f, g)` with `f ⁻¹' {⊤} ∪ g ⁻¹' {⊤} = univ` do not form an open set. Topological groups are
regular, so these are the continuity statements behind the pointwise operations on the iterated
function spaces `C(G, C(G, …))` of the coinduced resolution of a topological representation.
-/

public section

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The compact-open topology on the continuous maps from a compact space to a discrete space is
discrete. -/
instance discreteTopology [CompactSpace X] [DiscreteTopology Y] :
    DiscreteTopology C(X, Y) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro f
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have hset : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨?_, fun h ↦ ext fun x ↦ h (f x) ⟨x, rfl⟩ rfl⟩
    rintro rfl _ _ _ hx
    exact hx
  rw [hset]
  exact hfin.isOpen_biInter fun y _ ↦ isOpen_setOfPred_mapsTo
    (isClosed_singleton.preimage f.continuous).isCompact (isOpen_discrete _)

/-- Pairing a map with a constant in the right component of a product is continuous, the mirror
image of Mathlib's `ContinuousMap.continuous_prodMk_const`, whose constant is the left component. -/
theorem continuous_prodMk_const_right {Z : Type*} [TopologicalSpace Z] :
    Continuous fun p : C(X, Y) × Z ↦ p.1.prodMk (const X p.2) := by
  have : (fun p : C(X, Y) × Z ↦ p.1.prodMk (const X p.2)) =
      fun p ↦ ContinuousMap.prodSwap.comp ((const X p.2).prodMk p.1) := by
    ext p x <;> rfl
  rw [this]
  exact (continuous_postcomp _).comp (continuous_prodMk_const.comp continuous_swap)

/-- Pairing two maps into a product is continuous for a regular source, in particular for a
topological group. -/
theorem continuous_prodMk {Z : Type*} [TopologicalSpace Z] [RegularSpace X] :
    Continuous fun p : C(X, Y) × C(X, Z) ↦ p.1.prodMk p.2 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, ContinuousMap.tendsto_nhds_compactOpen]
  rintro ⟨f, g⟩ K hK U hU H
  -- around each point of `K`, a closed neighbourhood on which `(f, g)` lands in a box inside `U`
  have key : ∀ x ∈ K, ∃ C : Set X, IsClosed C ∧ C ∈ nhds x ∧ ∃ V : Set Y, ∃ W : Set Z,
      IsOpen V ∧ IsOpen W ∧ V ×ˢ W ⊆ U ∧ Set.MapsTo f C V ∧ Set.MapsTo g C W := by
    intro x hx
    obtain ⟨V, W, hV, hW, hfx, hgx, hVW⟩ := isOpen_prod_iff.mp hU (f x) (g x) (H hx)
    obtain ⟨C, hCmem, hC, hCsub⟩ := exists_mem_nhds_isClosed_subset (Filter.inter_mem
      (f.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hfx))
      (g.continuous.continuousAt.preimage_mem_nhds (hW.mem_nhds hgx)))
    exact ⟨C, hC, hCmem, V, W, hV, hW, hVW, fun y hy ↦ (hCsub hy).1, fun y hy ↦ (hCsub hy).2⟩
  choose! C hCclosed hCnhds V W hV hW hVW hfC hgC using key
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover C fun x hx ↦ hCnhds x hx
  have hf : ∀ᶠ f' : C(X, Y) in nhds f, ∀ x ∈ t, Set.MapsTo f' (K ∩ C x) (V x) :=
    t.eventually_all.mpr fun x hx ↦ eventually_mapsTo (hK.inter_right (hCclosed x (htK x hx)))
      (hV x (htK x hx)) ((hfC x (htK x hx)).mono_left Set.inter_subset_right)
  have hg : ∀ᶠ g' : C(X, Z) in nhds g, ∀ x ∈ t, Set.MapsTo g' (K ∩ C x) (W x) :=
    t.eventually_all.mpr fun x hx ↦ eventually_mapsTo (hK.inter_right (hCclosed x (htK x hx)))
      (hW x (htK x hx)) ((hgC x (htK x hx)).mono_left Set.inter_subset_right)
  rw [nhds_prod_eq]
  filter_upwards [hf.prod_mk hg] with p hp y hy
  obtain ⟨x, hxt, hyC⟩ := Set.mem_iUnion₂.mp (hKt hy)
  exact hVW x (htK x hxt) ⟨hp.1 x hxt ⟨hy, hyC⟩, hp.2 x hxt ⟨hy, hyC⟩⟩

end ContinuousMap
