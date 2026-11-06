/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Square
public import TauCeti.Geometry.Manifold.Morse.Stable.SequentialCompactness
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Dynamics.Flow.LevelCrossing
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice

/-!
# The compactified space of index-two trajectories

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `r` critical points with
`ind p = ind r + 2`. This file constructs the compactification of the space of unparametrized
trajectories from `p` to `r` by the broken trajectories, as a compact subset of `M × M`.

Choose two levels `f r < b < a < f p` such that every critical value strictly between `f r` and
`f p` lies strictly between `b` and `a` (they exist by
`TauCeti.IsMorse.exists_lt_lt_lt_forall_mem_Ioo`). Every trajectory from `p` to `r` crosses the
*entrance level* `a` and the *exit level* `b` once, and every trajectory broken at a critical point
`q` of the intermediate index crosses `a` on its component from `p` to `q` and `b` on its component
from `q` to `r`. Recording the two crossing points gives

* the **unbroken pairs** `TauCeti.IsAdaptedPseudoGradient.morseUnbrokenPairs`: pairs `(x, y)` with
  `x` on a trajectory from `p` to `r` at the level `a` and `y` the point of its orbit at the
  level `b`;
* the **broken pairs** `TauCeti.IsAdaptedPseudoGradient.morseBrokenPairs`: pairs `(x, y)` with `x`
  on a trajectory from `p` to `q` at the level `a` and `y` on a trajectory from `q` to `r` at the
  level `b`;
* their union `TauCeti.IsAdaptedPseudoGradient.morseCompactifiedPairs`, the compactified space of
  trajectories with the subspace topology of `M × M`.

Two pairs are close when the trajectories they record enter and leave the region between the two
levels at nearby points; for a family of unbroken trajectories approaching a broken one, the
entrance points converge to the entrance point of the first component and the exit points to the
exit point of the second. So convergence in this topology is convergence up to breaking, and the
space is Hausdorff because `M × M` is.

The main result is compactness
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isCompact_morseCompactifiedPairs`). Limits of
unbroken pairs are unbroken or broken pairs, by the index-two sequential compactness theorem
`IsMorseSmale.exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two` in the namespace
`TauCeti.IsAdaptedPseudoGradient` and the continuity of level-crossing times; and there are only
finitely many broken pairs. The unbroken pairs form a copy of the level slice
`W^u(p) ∩ W^s(r) ∩ {f = a}` with its topology
(`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseUnbrokenPairs`), a one-dimensional
manifold under the Morse–Smale condition, and the broken pairs are as many as the broken index-two
trajectories counted by the square of the mod-two Morse boundary
(`TauCeti.IsAdaptedPseudoGradient.ncard_morseBrokenPairs`). Hence the Morse boundary squares to
zero exactly when every such space has an even number of broken pairs
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_iff_even`).
This is the parity that a compact one-dimensional manifold whose boundary is the set of broken
pairs provides; the neighbourhoods of the broken pairs, which come from gluing, are not
constructed here.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseUnbrokenPairs`, `morseBrokenPairs`, `morseCompactifiedPairs`: unbroken, broken and all
  trajectories from `p` to `r`, recorded by their crossings of an entrance and an exit level.

## Main results

* `TauCeti.IsMorse.exists_lt_lt_lt_forall_mem_Ioo`: suitable entrance and exit levels exist.
* `disjoint_morseUnbrokenPairs_morseBrokenPairs`: no pair is both broken and unbroken.
* `exists_homeomorph_morseUnbrokenPairs`: the unbroken pairs are homeomorphic to the level slice
  of trajectories at the entrance level, by the first projection.
* `ncard_morseBrokenPairs`: the broken pairs are as many as the broken index-two trajectories.
* `IsMorseSmale.finite_morseBrokenPairs`: there are finitely many broken pairs.
* `IsMorseSmale.closure_morseUnbrokenPairs_subset`: limits of unbroken pairs are unbroken or
  broken pairs.
* `IsMorseSmale.isCompact_morseCompactifiedPairs`: the compactified space is compact.
* `IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_iff_even`: `∂ ∘ ∂ = 0` exactly when every
  compactified space of index-two trajectories has an even number of broken pairs.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories) and Chapter 4 (the proof that `∂ ∘ ∂ = 0`).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (compactified spaces of trajectories, whose topology is
  convergence up to breaking).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p r : M} {a b : ℝ}

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Entrance and exit levels.** For critical points `p` and `r` of a Morse function on a compact
manifold with `f r < f p`, there are levels `f r < b < a < f p` such that every critical value
strictly between `f r` and `f p` lies strictly between `b` and `a`. -/
theorem IsMorse.exists_lt_lt_lt_forall_mem_Ioo (hf : IsMorse 𝓘(ℝ, E) f) (hrp : f r < f p) :
    ∃ a b, f r < b ∧ b < a ∧ a < f p ∧
      ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f q ∈ Ioo (f r) (f p) → f q ∈ Ioo b a := by
  -- The critical values in `(f r, f p)`, together with the midpoint, form a finite nonempty set.
  set S : Set ℝ := insert ((f r + f p) / 2)
    (f '' (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ioo (f r) (f p)))
  have hfin : S.Finite := ((hf.finite_criticalPoints.subset inter_subset_left).image f).insert _
  have hsub : S ⊆ Ioo (f r) (f p) := by
    rintro x (rfl | ⟨q, hq, rfl⟩)
    · exact ⟨by linarith, by linarith⟩
    · exact hq.2
  have hmid : (f r + f p) / 2 ∈ S := mem_insert _ _
  obtain ⟨m₀, hm₀, hmin⟩ := exists_min_image S id hfin ⟨_, hmid⟩
  obtain ⟨m₁, hm₁, hmax⟩ := exists_max_image S id hfin ⟨_, hmid⟩
  have h₀ := hsub hm₀
  have h₁ := hsub hm₁
  have hle₀ : m₀ ≤ (f r + f p) / 2 := hmin _ hmid
  have hle₁ : (f r + f p) / 2 ≤ m₁ := hmax _ hmid
  refine ⟨(m₁ + f p) / 2, (f r + m₀) / 2, by linarith [h₀.1], by linarith, by linarith [h₁.2],
    fun q hq hqI ↦ ?_⟩
  have hqS : f q ∈ S :=
    mem_insert_of_mem _ ⟨q, ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hq, hqI⟩, rfl⟩
  have hq₀ : m₀ ≤ f q := hmin _ hqS
  have hq₁ : f q ≤ m₁ := hmax _ hqS
  exact ⟨by linarith [h₀.1], by linarith [h₁.2]⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Points whose Morse indices differ by one are distinct. -/
private theorem ne_of_index_eq_add_one {x x' : M}
    (h : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f x' + 1) : x ≠ x' := by
  rintro rfl
  omega

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The **unbroken pairs**: a trajectory from `p` to `r` is recorded by its point `x` on the
entrance level `a` and the point `y` of its orbit on the exit level `b`. -/
def morseUnbrokenPairs (p r : M) (a b : ℝ) : Set (M × M) :=
  {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ f w.1 = a ∧ f w.2 = b ∧
    ∃ t, hX.flow t w.1 = w.2}

/-- Membership in the unbroken pairs. -/
@[simp]
theorem mem_morseUnbrokenPairs {w : M × M} :
    w ∈ hX.morseUnbrokenPairs p r a b ↔
      w.1 ∈ hX.flow.unstableSet p ∧ w.1 ∈ hX.flow.stableSet r ∧ f w.1 = a ∧ f w.2 = b ∧
        ∃ t, hX.flow t w.1 = w.2 := by
  simp only [morseUnbrokenPairs, mem_ofPred_eq, mem_inter_iff, and_assoc]

/-- The **broken pairs**: a trajectory from `p` to `r` broken at a critical point `q` with
`ind p = ind q + 1 = ind r + 2` is recorded by the point `x` of its component from `p` to `q` on
the entrance level `a` and the point `y` of its component from `q` to `r` on the exit level `b`.
-/
def morseBrokenPairs (p r : M) (a b : ℝ) : Set (M × M) :=
  {w | ∃ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
    w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {x | f x = a} ∧
    w.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∩ {x | f x = b}}

/-- Membership in the broken pairs. -/
@[simp]
theorem mem_morseBrokenPairs {w : M × M} :
    w ∈ hX.morseBrokenPairs p r a b ↔
      ∃ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
        w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {x | f x = a} ∧
        w.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∩ {x | f x = b} :=
  Iff.rfl

/-- The **compactified space of trajectories** from `p` to `r`, recorded by their crossings of the
entrance level `a` and the exit level `b`: the unbroken and the broken pairs. Its topology is the
subspace topology of `M × M`. -/
def morseCompactifiedPairs (p r : M) (a b : ℝ) : Set (M × M) :=
  hX.morseUnbrokenPairs p r a b ∪ hX.morseBrokenPairs p r a b

theorem morseCompactifiedPairs_def :
    hX.morseCompactifiedPairs p r a b =
      hX.morseUnbrokenPairs p r a b ∪ hX.morseBrokenPairs p r a b :=
  (rfl)

/-- A pair of the compactified space is unbroken or broken. -/
@[simp]
theorem mem_morseCompactifiedPairs {w : M × M} :
    w ∈ hX.morseCompactifiedPairs p r a b ↔
      w ∈ hX.morseUnbrokenPairs p r a b ∨ w ∈ hX.morseBrokenPairs p r a b :=
  Iff.rfl

/-- **No pair is both unbroken and broken.** The entrance point of an unbroken pair flows to `r`,
and that of a broken pair to a critical point of a different index. -/
theorem disjoint_morseUnbrokenPairs_morseBrokenPairs :
    Disjoint (hX.morseUnbrokenPairs p r a b) (hX.morseBrokenPairs p r a b) := by
  refine disjoint_left.2 fun w hU hB ↦ ?_
  obtain ⟨q, -, -, hqr, hw₁, -⟩ := hX.mem_morseBrokenPairs.1 hB
  have hqr' : q ≠ r := by
    rintro rfl
    omega
  exact (Flow.disjoint_stableSet hqr').ne_of_mem hw₁.1.2 hU.1.2 rfl

/-- The unbroken pairs are the compactified space with the broken pairs removed. -/
theorem morseCompactifiedPairs_sdiff_morseBrokenPairs :
    hX.morseCompactifiedPairs p r a b \ hX.morseBrokenPairs p r a b =
      hX.morseUnbrokenPairs p r a b :=
  union_sdiff_cancel_right (Set.disjoint_iff.1 hX.disjoint_morseUnbrokenPairs_morseBrokenPairs)

/-! ### Level crossings -/

/-- **Points of one orbit on one level coincide.** If `y` lies on a trajectory from a critical
point `x` to a different critical point `x'`, a point of its orbit on the level of `y` is `y`. -/
private theorem flow_eq_self_of_value_eq (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {x x' y : M}
    (hxx' : x ≠ x') (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x') {t : ℝ}
    (ht : f (hX.flow t y) = f y) : hX.flow t y = y := by
  have h0 : t = 0 := (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hxx' hy).injective
    (by simpa only [Flow.map_zero_apply] using ht)
  rw [h0, Flow.map_zero_apply]

/-- The point where the orbit of `y` crosses the level `c`. -/
private noncomputable def levelCrossing (c : ℝ) (y : M) : M :=
  hX.flow (Flow.levelCrossingTime hX.flow f c y) y

/-- The crossing of the level `c` by a trajectory from `x` to `x'`, for `f x' < c < f x`, lies on
the same trajectory and on the level `c`. -/
private theorem levelCrossing_mem (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {x x' y : M} {c : ℝ}
    (hxx' : x ≠ x') (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x') (hc : f x' < c)
    (hc' : c < f x) :
    hX.levelCrossing c y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x' ∩ {z | f z = c} :=
  ⟨hX.flow.isInvariant_unstableSet_inter_stableSet x x' _ hy,
    Flow.apply_flow_levelCrossingTime
      (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hxx' hy hc hc').exists⟩

/-- A point of the orbit of `y` on the level `c` is the crossing of that level. -/
private theorem levelCrossing_eq (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {x x' y : M} {c t : ℝ}
    (hxx' : x ≠ x') (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x')
    (ht : f (hX.flow t y) = c) : hX.levelCrossing c y = hX.flow t y := by
  rw [levelCrossing, ← (Flow.eq_levelCrossingTime_iff
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hxx' hy) ⟨t, ht⟩).2 ht]

/-- The crossing of the level of `y` by an orbit through a point of the orbit of `y` is `y`. -/
private theorem levelCrossing_flow (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {x x' y : M}
    (hxx' : x ≠ x') (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x') (t : ℝ) :
    hX.levelCrossing (f y) (hX.flow t y) = y := by
  have hy' := hX.flow.isInvariant_unstableSet_inter_stableSet x x' t hy
  have h := hX.levelCrossing_eq hf hxx' hy' (t := -t) (by rw [← Flow.map_add, neg_add_cancel,
    Flow.map_zero_apply])
  rwa [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at h

/-- **Crossings of a level converge along convergent orbits.** Let the points `φ (s i) (u i)` of
the orbits of `u i` tend to a point `z` of a trajectory from `x` to a different critical point
`x'`. If the orbit of each `u i` meets the level of `φ T z` at the time `τ i`, then these crossing
points tend to `φ T z`. -/
private theorem tendsto_flow_of_value_eq {ι : Type*} {l : Filter ι}
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {x x' z : M} (hxx' : x ≠ x')
    (hz : z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x') {u : ι → M} {s : ι → ℝ}
    (hu : Tendsto (fun i ↦ hX.flow (s i) (u i)) l (𝓝 z)) (T : ℝ) {τ : ι → ℝ}
    (hτ : ∀ i, f (hX.flow (τ i) (u i)) = f (hX.flow T z)) :
    Tendsto (fun i ↦ hX.flow (τ i) (u i)) l (𝓝 (hX.flow T z)) := by
  have hz' := hX.flow.isInvariant_unstableSet_inter_stableSet x x' T hz
  have hw : Tendsto (fun i ↦ hX.flow T (hX.flow (s i) (u i))) l (𝓝 (hX.flow T z)) :=
    ((hX.contMDiff_flow_apply T).continuous.tendsto z).comp hu
  have hflow (i : ι) :
      hX.flow (τ i - s i - T) (hX.flow T (hX.flow (s i) (u i))) = hX.flow (τ i) (u i) := by
    rw [← Flow.map_add, ← Flow.map_add, sub_add_cancel, sub_add_cancel]
  -- The crossing times of the orbits of `φ T (φ (s i) (u i))` tend to `0`, that of `φ T z`.
  have hσ := hX.tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet hf hxx' hz' hw
    (σ := fun i ↦ τ i - s i - T) fun i ↦ by rw [hflow, hτ]
  have hlim := (hX.contMDiff_flow_uncurry.continuous.tendsto ((0 : ℝ), hX.flow T z)).comp
    (hσ.prodMk_nhds hw)
  simp only [Flow.map_zero_apply] at hlim
  exact hlim.congr hflow

/-- Crossings of levels by trajectories ending at different critical points are different. -/
private theorem eq_of_levelCrossing_eq_of_mem_stableSet {q q' y y' : M} {c c' : ℝ}
    (hy : y ∈ hX.flow.stableSet q) (hy' : y' ∈ hX.flow.stableSet q')
    (h : hX.levelCrossing c y = hX.levelCrossing c' y') : q = q' := by
  by_contra hqq'
  exact (Flow.disjoint_stableSet hqq').ne_of_mem
    ((Flow.apply_mem_stableSet_iff _ _).2 hy) ((Flow.apply_mem_stableSet_iff _ _).2 hy') h

/-- Two points of one level of a trajectory space whose orbits cross another level at the same
point coincide. -/
private theorem eq_of_levelCrossing_eq (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {x x' y y' : M}
    {c : ℝ} (hxx' : x ≠ x') (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x')
    (hfy : f y' = f y) (h : hX.levelCrossing c y = hX.levelCrossing c y') : y = y' := by
  simp only [levelCrossing] at h
  have h' : hX.flow (Flow.levelCrossingTime hX.flow f c y -
      Flow.levelCrossingTime hX.flow f c y') y = y' := by
    rw [sub_eq_neg_add, Flow.map_add, h, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  exact (hX.flow_eq_self_of_value_eq hf hxx' hy (by rw [h', hfy])).symm.trans h'

/-! ### Unbroken pairs -/

/-- **The unbroken pairs are a level slice.** For distinct `p` and `r` and an exit level
`f r < b < f p`, the first projection identifies the unbroken pairs with the level slice of
trajectories from `p` to `r` at the entrance level `a`. -/
theorem exists_homeomorph_morseUnbrokenPairs (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hpr : p ≠ r) (hb : f r < b) (hbp : b < f p) :
    ∃ e : ↥(hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {x | f x = a}) ≃ₜ
        ↥(hX.morseUnbrokenPairs p r a b), ∀ y, (e y : M × M).1 = y := by
  have hanti (y : M) (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r) :=
    hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hpr hy
  have hex (y : M) (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r) :=
    (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hpr hy hb hbp).exists
  have hτ := Flow.continuousOn_levelCrossingTime hf.continuous.continuousOn hanti hex
  have hmem (y : ↥(hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {x | f x = a})) :
      ((y : M), hX.levelCrossing b y) ∈ hX.morseUnbrokenPairs p r a b :=
    ⟨y.2.1, y.2.2, Flow.apply_flow_levelCrossingTime (hex y y.2.1), _, rfl⟩
  refine ⟨{ toFun := fun y ↦ ⟨(y, hX.levelCrossing b y), hmem y⟩
            invFun := fun w ↦ ⟨w.1.1, w.2.1, w.2.2.1⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun w ↦ ?_
            continuous_toFun := ?_
            continuous_invFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _ },
    fun _ ↦ rfl⟩
  · obtain ⟨-, -, hw₂, t, ht⟩ := w.2
    refine Subtype.ext (Prod.ext rfl ?_)
    dsimp only
    rw [hX.levelCrossing_eq hf hpr w.2.1 (t := t) (by rw [ht, hw₂]), ht]
  · exact (continuous_subtype_val.prodMk (hX.flow.continuous
      (hτ.comp_continuous continuous_subtype_val fun y ↦ y.2.1)
      continuous_subtype_val)).subtype_mk _

/-! ### Broken pairs -/

/-- **Broken pairs count broken trajectories.** If every critical value strictly between `f r`
and `f p` lies strictly between the levels `b < a`, then the broken pairs are as many as the broken
index-two trajectories `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySet`, which record the
same trajectories by their points on the middle levels of their two components. -/
theorem ncard_morseBrokenPairs (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (hb : f r < b)
    (ha : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f q ∈ Ioo (f r) (f p) → f q ∈ Ioo b a) :
    (hX.morseBrokenPairs p r a b).ncard = (hX.morseBrokenTrajectorySet p r).ncard := by
  -- For a broken trajectory through `q`, the critical value `f q` lies between `b` and `a`.
  have hlev {q y z : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) (hpq : p ≠ q) (hqr : q ≠ r)
      (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
      (hz : z ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) : f q ∈ Ioo b a := by
    have hyI := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hpq hy
    have hzI := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hqr hz
    exact hcrit q hq ⟨hzI.1.trans hzI.2, hyI.1.trans hyI.2⟩
  symm
  refine ncard_congr (fun x _ ↦ (hX.levelCrossing a x.2.1, hX.levelCrossing b x.2.2))
    (fun x hx ↦ ?_) (fun x x' hx hx' hxx' ↦ ?_) (fun w hw ↦ ?_)
  · -- A broken trajectory gives a broken pair.
    obtain ⟨hpq, hqr, hy, hz⟩ := (hX.mem_morseBrokenTrajectorySet).1 hx
    rw [mem_morseTrajectorySlice] at hy hz
    have hpq' := ne_of_index_eq_add_one hpq
    have hqr' := ne_of_index_eq_add_one hqr
    have hq := mem_criticalPoints_iff_mfderiv_eq_zero.1 x.1.2
    have hqI := hlev hq hpq' hqr' ⟨hy.1, hy.2.1⟩ ⟨hz.1, hz.2.1⟩
    exact ⟨x.1, hq, hpq, hqr, hX.levelCrossing_mem hf hpq' ⟨hy.1, hy.2.1⟩ hqI.2 ha,
      hX.levelCrossing_mem hf hqr' ⟨hz.1, hz.2.1⟩ hb hqI.1⟩
  · -- The crossings determine the intermediate critical point and both components.
    obtain ⟨hpq, hqr, hy, hz⟩ := (hX.mem_morseBrokenTrajectorySet).1 hx
    obtain ⟨-, -, hy', hz'⟩ := (hX.mem_morseBrokenTrajectorySet).1 hx'
    rw [mem_morseTrajectorySlice] at hy hz hy' hz'
    obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 hxx'
    -- The entrance crossing determines the intermediate critical point, then both components.
    have hq' : (x.1 : M) = x'.1 := hX.eq_of_levelCrossing_eq_of_mem_stableSet hy.2.1 hy'.2.1 h₁
    refine Prod.ext (Subtype.ext hq') (Prod.ext ?_ ?_)
    · exact hX.eq_of_levelCrossing_eq hf (ne_of_index_eq_add_one hpq) ⟨hy.1, hy.2.1⟩
        (by rw [hy.2.2, hy'.2.2, hq']) h₁
    · exact hX.eq_of_levelCrossing_eq hf (ne_of_index_eq_add_one hqr) ⟨hz.1, hz.2.1⟩
        (by rw [hz.2.2, hz'.2.2, hq']) h₂
  · -- A broken pair comes from the broken trajectory through its middle-level points.
    obtain ⟨q, hq, hpq, hqr, hw₁, hw₂⟩ := hX.mem_morseBrokenPairs.1 hw
    have hpq' := ne_of_index_eq_add_one hpq
    have hqr' := ne_of_index_eq_add_one hqr
    have hyI := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hpq' hw₁.1
    have hzI := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hqr' hw₂.1
    have hy := hX.levelCrossing_mem hf hpq' hw₁.1 (c := (f p + f q) / 2)
      (by linarith [hyI.1, hyI.2]) (by linarith [hyI.1, hyI.2])
    have hz := hX.levelCrossing_mem hf hqr' hw₂.1 (c := (f q + f r) / 2)
      (by linarith [hzI.1, hzI.2]) (by linarith [hzI.1, hzI.2])
    refine ⟨(⟨q, mem_criticalPoints_iff_mfderiv_eq_zero.2 hq⟩, hX.levelCrossing ((f p + f q) / 2)
      w.1, hX.levelCrossing ((f q + f r) / 2) w.2), (hX.mem_morseBrokenTrajectorySet).2 ⟨hpq, hqr,
      (mem_morseTrajectorySlice _).2 ⟨hy.1.1, hy.1.2, hy.2⟩,
      (mem_morseTrajectorySlice _).2 ⟨hz.1.1, hz.1.2, hz.2⟩⟩, ?_⟩
    -- Crossing the level of `w.1` from a point of its orbit returns `w.1`, and likewise for `w.2`.
    have h₁ := hX.levelCrossing_flow hf hpq' hw₁.1
      (Flow.levelCrossingTime hX.flow f ((f p + f q) / 2) w.1)
    have h₂ := hX.levelCrossing_flow hf hqr' hw₂.1
      (Flow.levelCrossingTime hX.flow f ((f q + f r) / 2) w.2)
    rw [hw₁.2] at h₁
    rw [hw₂.2] at h₂
    exact Prod.ext h₁ h₂

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- **Finitely many broken pairs.** Under the Morse–Smale condition, a compactified space of
trajectories between critical points has finitely many broken pairs. -/
theorem finite_morseBrokenPairs (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) : (hX.morseBrokenPairs p r a b).Finite := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  -- Index-one level slices are finite, including the empty ones outside the range of values.
  have hslice {x x' : M} (c : ℝ) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
      (hx' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x' = 0)
      (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f x' + 1) :
      (hX.flow.unstableSet x ∩ hX.flow.stableSet x' ∩ {z | f z = c}).Finite := by
    by_cases hc : f x' < c ∧ c < f x
    · exact h.finite_unstableSet_inter_stableSet_inter_level hf hx hx' hind hc
    · refine finite_empty.subset fun z hz ↦ hc ?_
      have hzI :=
        hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf (ne_of_index_eq_add_one hind) hz.1
      rw [hz.2] at hzI
      exact hzI
  -- Sort the broken pairs by their intermediate critical point `q`.
  have hS : {q | q ∈ criticalPoints 𝓘(ℝ, E) f ∧
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1}.Finite :=
    hf.finite_criticalPoints.subset fun q hq ↦ hq.1
  refine (hS.biUnion fun q hq ↦
    (hslice a hp (mem_criticalPoints_iff_mfderiv_eq_zero.1 hq.1) hq.2.1).prod
      (hslice b (mem_criticalPoints_iff_mfderiv_eq_zero.1 hq.1) hr hq.2.2)).subset fun w hw ↦ ?_
  obtain ⟨q, hq, hpq, hqr, hw₁, hw₂⟩ := hX.mem_morseBrokenPairs.1 hw
  exact mem_biUnion (x := q) ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hq, hpq, hqr⟩ ⟨hw₁, hw₂⟩

/-- **Limits of unbroken pairs.** Let `ind p = ind r + 2`, and let the levels `f r < b < a < f p`
separate the ends from every critical value strictly between `f r` and `f p`. Then a limit of
unbroken pairs from `p` to `r` is an unbroken pair or a broken pair. -/
theorem closure_morseUnbrokenPairs_subset (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2)
    (hb : f r < b) (hba : b < a) (ha : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f q ∈ Ioo (f r) (f p) → f q ∈ Ioo b a) :
    closure (hX.morseUnbrokenPairs p r a b) ⊆ hX.morseCompactifiedPairs p r a b := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  intro w hw
  obtain ⟨v, hv, hvw⟩ := mem_closure_iff_seq_limit.1 hw
  simp only [mem_morseUnbrokenPairs] at hv
  choose hvp hvr hva hvb τ hτ using hv
  have hreg (y : M) (hy : f y = a) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := fun hy0 ↦
    (hcrit y hy0 (hy ▸ ⟨hb.trans hba, ha⟩)).2.ne hy
  obtain ⟨n, y, hn, hya, hy, hcase⟩ :=
    h.exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two hf hp hr hind hreg
      (fun k ↦ (v k).1) fun k ↦ ⟨⟨hvp k, hvr k⟩, hva k⟩
  have hvn := hvw.comp hn.tendsto_atTop
  have hw₁ : w.1 = y := tendsto_nhds_unique ((continuous_fst.tendsto w).comp hvn) hy
  -- If orbit points of the entrance points tend to a point `z` of a trajectory crossing the exit
  -- level, then the exit points tend to the crossing of the exit level by the orbit of `z`.
  have hw₂ {x x' z : M} (s : ℕ → ℝ) (hxx' : x ≠ x')
      (hz : z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x') (hx'b : f x' < b) (hbx : b < f x)
      (hs : Tendsto (fun k ↦ hX.flow (s k) (v (n k)).1) atTop (𝓝 z)) :
      ∃ T, w.2 = hX.flow T z ∧ f (hX.flow T z) = b := by
    obtain ⟨T, hT⟩ :=
      (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf hxx' hz hx'b hbx).exists
    have hlim := hX.tendsto_flow_of_value_eq hdf hxx' hz hs T (τ := fun k ↦ τ (n k))
      fun k ↦ by rw [hτ, hvb, hT]
    exact ⟨T, tendsto_nhds_unique ((continuous_snd.tendsto w).comp hvn)
      (hlim.congr fun k ↦ hτ (n k)), hT⟩
  rcases hcase with hyU | ⟨q, z, t, hq, hpq, hqr, hz, ⟨hyq, hzq, -⟩ | ⟨hyq, hzq, -⟩⟩
  · -- The limit is unbroken.
    have hpr : p ≠ r := by
      rintro rfl
      omega
    obtain ⟨T, hT, hTb⟩ := hw₂ (fun _ ↦ 0) hpr hyU hb (hba.trans ha)
      (by simpa only [Flow.map_zero_apply] using hy)
    refine Or.inl ((mem_morseUnbrokenPairs _).2 ?_)
    rw [hw₁, hT]
    exact ⟨hyU.1, hyU.2, hya, hTb, T, rfl⟩
  · -- The limit breaks at `q`, and the entrance level is crossed by the component from `p` to `q`.
    have hyI := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf (ne_of_index_eq_add_one hpq) hyq
    have hzI := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf (ne_of_index_eq_add_one hqr) hzq
    have hqI := hcrit q hq ⟨hzI.1.trans hzI.2, hyI.1.trans hyI.2⟩
    obtain ⟨T, hT, hTb⟩ := hw₂ t (ne_of_index_eq_add_one hqr) hzq hb hqI.1 hz
    refine Or.inr (hX.mem_morseBrokenPairs.2 ⟨q, hq, hpq, hqr, ?_, ?_⟩)
    · rw [hw₁]
      exact ⟨hyq, hya⟩
    · rw [hT]
      exact ⟨hX.flow.isInvariant_unstableSet_inter_stableSet q r T hzq, hTb⟩
  · -- The entrance level lies above `f q`, so it is not crossed by the component from `q` to `r`.
    have hyI := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf (ne_of_index_eq_add_one hqr) hyq
    have hzI := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf (ne_of_index_eq_add_one hpq) hzq
    have hqI := hcrit q hq ⟨hyI.1.trans hyI.2, hzI.1.trans hzI.2⟩
    exfalso
    linarith [hyI.2, hqI.2]

/-- **The compactified space of index-two trajectories is compact.** Let `ind p = ind r + 2`, and
let the levels `f r < b < a < f p` separate the ends from every critical value strictly between
`f r` and `f p`. Then the unbroken and broken pairs from `p` to `r` form a compact subset of
`M × M`. -/
theorem isCompact_morseCompactifiedPairs (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2)
    (hb : f r < b) (hba : b < a) (ha : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f q ∈ Ioo (f r) (f p) → f q ∈ Ioo b a) :
    IsCompact (hX.morseCompactifiedPairs p r a b) := by
  refine (isClosed_of_closure_subset ?_).isCompact
  rw [morseCompactifiedPairs_def, closure_union,
    (h.finite_morseBrokenPairs hf hp hr).isClosed.closure_eq]
  exact union_subset (h.closure_morseUnbrokenPairs_subset hf hp hr hind hb hba ha hcrit)
    subset_union_right

/-- **`∂² = 0` reduces to the parity of broken pairs.** The mod-two Morse boundary squares to zero
exactly when, for any two critical points `p` and `r` and any levels `f r < b < a < f p`
separating the ends from the critical values strictly between `f r` and `f p`, the compactified
space of trajectories from `p` to `r` has an even number of broken pairs. -/
theorem morseBoundary_comp_morseBoundary_eq_zero_iff_even :
    h.morseBoundary hf ∘ₗ h.morseBoundary hf = 0 ↔
      ∀ (p r : criticalPoints 𝓘(ℝ, E) f) (a b : ℝ), f r < b → b < a → a < f p →
        (∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f q ∈ Ioo (f r) (f p) → f q ∈ Ioo b a) →
        Even (hX.morseBrokenPairs p r a b).ncard := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  rw [h.morseBoundary_comp_morseBoundary_eq_zero_iff hf]
  refine ⟨fun h0 p r a b hb _ ha hcrit ↦ hX.ncard_morseBrokenPairs hdf hb ha hcrit ▸ h0 p r,
    fun h0 p r ↦ ?_⟩
  by_cases hrp : f r < f p
  · obtain ⟨a, b, hb, hba, ha, hcrit⟩ := hf.exists_lt_lt_lt_forall_mem_Ioo hrp
    exact hX.ncard_morseBrokenPairs hdf hb ha hcrit ▸ h0 p r a b hb hba ha hcrit
  · -- Without a drop in value there are no broken trajectories.
    have hempty : hX.morseBrokenTrajectorySet p r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ by
        obtain ⟨hpq, hqr, hy, hz⟩ := (hX.mem_morseBrokenTrajectorySet).1 hx
        exact hrp
          ((hX.value_lt_of_mem_morseTrajectorySlice hdf (ne_of_index_eq_add_one hqr) hz).trans
            (hX.value_lt_of_mem_morseTrajectorySlice hdf (ne_of_index_eq_add_one hpq) hy))
    rw [hempty, ncard_empty]
    exact Even.zero

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
