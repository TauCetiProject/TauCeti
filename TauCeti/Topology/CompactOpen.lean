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
swapping the factors. The general case, for every R₁ source and in particular for every regular
or Hausdorff one, is Mathlib's `ContinuousMap.continuous_prodMk'`. Topological groups are regular,
so these are the continuity statements behind the pointwise operations on the iterated function
spaces `C(G, C(G, …))` of the coinduced resolution of a topological representation.

Finally, the constant maps embed `Y` in `C(X, Y)` whenever `X` is nonempty
(`ContinuousMap.isEmbedding_const`): evaluation at any point is a continuous left inverse.
Postcomposition with a closed embedding `g` is a closed embedding
(`ContinuousMap.isClosedEmbedding_postcomp`): its range consists of the maps with values in the
closed range of `g`, a condition closed under pointwise limits.
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

/-- Constant maps embed the target in the compact-open mapping space whenever the source is
nonempty. Evaluation at any point is a continuous left inverse. -/
theorem isEmbedding_const [Nonempty X] : Topology.IsEmbedding (const X : Y → C(X, Y)) :=
  Function.LeftInverse.isEmbedding (f := fun f : C(X, Y) ↦ f (Classical.arbitrary X))
    (fun _ ↦ rfl) (continuous_eval_const _) continuous_const'

variable {Z : Type*} [TopologicalSpace Z]

/-- The maps obtained by postcomposition with a topology inducing map `g` are exactly the maps
with values in the range of `g`. -/
theorem range_postcomp (g : C(Y, Z)) (hg : Topology.IsInducing g) :
    Set.range (g.comp : C(X, Y) → C(X, Z)) = {f | ∀ x, f x ∈ Set.range g} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f x ↦ ⟨f x, rfl⟩) fun f hf ↦ ?_
  choose k hk using hf
  refine ⟨⟨k, hg.continuous_iff.2 ?_⟩, ext hk⟩
  simpa [Function.comp_def, hk] using f.continuous

/-- If `g : C(Y, Z)` is a closed embedding, then the composition
`ContinuousMap.comp g : C(X, Y) → C(X, Z)` is a closed embedding too. -/
theorem isClosedEmbedding_postcomp (g : C(Y, Z)) (hg : Topology.IsClosedEmbedding g) :
    Topology.IsClosedEmbedding (g.comp : C(X, Y) → C(X, Z)) := by
  refine ⟨isEmbedding_postcomp g hg.isEmbedding, ?_⟩
  simp only [range_postcomp g hg.isInducing, Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ hg.isClosed_range.preimage (continuous_eval_const x)

end ContinuousMap
