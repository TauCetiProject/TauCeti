/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Square
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.Geometry.Manifold.Morse.Stable.SequentialCompactness

/-!
# The compactified space of index-two trajectories

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `r` critical points with
`ind p = ind r + 2`. This file embeds the one-dimensional space of trajectories from `p` to `r`
in the compact space `M × M` and studies its closure there. It shows that the closure adds only
trajectories broken once, at a critical point `q` of intermediate index, that it adds finitely many
points, and that it is one-dimensional at the unbroken trajectories. That every broken trajectory
is a limit of unbroken ones is proved in `TauCeti.Geometry.Manifold.Morse.Boundary.Gluing`.

A trajectory is recorded by its points on two levels `c₁` and `c₂` with
`f r < c₂ < c₁ < f p`, chosen so that every critical value strictly between `f r` and `f p` lies
strictly between `c₂` and `c₁`; such levels exist by
`TauCeti.IsMorse.exists_lt_lt_forall_mem_Ioo`. A single level does not suffice: a trajectory
broken at `q` meets a level above `f q` only along its first component, so all broken trajectories
sharing that component would be recorded by the same point. With two levels, an unbroken
trajectory gives a pair in `morseTrajectoryPairs p r c₁ c₂`, and a broken one gives a pair in
`morseBrokenTrajectoryPairs p r c₁ c₂`, its first point on the component from `p` to `q` and its
second on the component from `q` to `r`. The compactified space is the closure of the unbroken
pairs in `M × M`; it is compact as a closed subset of the compact space `M × M`
(`isClosed_closure.isCompact`), which needs no separate statement. The main facts are:

* its points are unbroken or broken trajectory pairs (the sequential compactness of index-two
  trajectories, `IsMorseSmale.exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two`,
  together with the convergence of level crossings);
* there are finitely many broken pairs, and they are as many as the broken trajectories
  `morseBrokenTrajectorySet p r` counted by the square of the mod-two Morse boundary;
* the unbroken pairs form an open subset, homeomorphic to the level slice
  `W^u(p) ∩ W^s(r) ∩ {f = c₁}`, so each of them has a neighbourhood homeomorphic to an open
  subset of `ℝ`.

The converse inclusion, that every broken trajectory is a limit of unbroken ones, is
`IsMorseSmale.morseBrokenTrajectoryPairs_subset_closure`. Each broken trajectory moreover has a
neighbourhood homeomorphic to a half-open interval, by
`IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`. Together with
`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico` this would show that the broken trajectories
are even in number, which is `∂ ∘ ∂ = 0` by
`IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_iff`.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseTrajectoryPairs`, `morseBrokenTrajectoryPairs`: unbroken and broken trajectories from `p`
  to `r`, recorded by their points on two levels.
* `exists_homeomorph_morseTrajectoryPairs`: the unbroken pairs are homeomorphic to a level slice.
* `ncard_morseBrokenTrajectoryPairs`: the broken pairs are as many as the broken trajectories.
* `IsMorseSmale.closure_morseTrajectoryPairs_subset`: the limits of unbroken pairs are unbroken or
  broken pairs.
* `IsMorseSmale.finite_morseBrokenTrajectoryPairs`: there are finitely many broken pairs.
* `IsMorseSmale.isOpen_preimage_val_morseTrajectoryPairs`: the unbroken pairs are open in the
  compactified space.
* `IsMorseSmale.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs`: the compactified space is
  locally homeomorphic to open subsets of `ℝ` at unbroken pairs.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories, and the compactified space of index-two
  trajectories as a manifold with boundary).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The trajectories from `p` to `r` recorded by their points on the two levels `c₁` and `c₂`:
the pairs `(y, z)` with `y` on a trajectory from `p` to `r`, `f y = c₁`, `f z = c₂`, and `z` on
the orbit of `y`. -/
def morseTrajectoryPairs (p r : M) (c₁ c₂ : ℝ) : Set (M × M) :=
  {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ f w.1 = c₁ ∧ f w.2 = c₂ ∧
    ∃ t, hX.flow t w.1 = w.2}

/-- The trajectories from `p` to `r` broken once, at a critical point `q` of intermediate index,
recorded by their points on the two levels `c₁` and `c₂`: the pairs `(y, z)` with `y` on a
trajectory from `p` to `q` with `f y = c₁` and `z` on a trajectory from `q` to `r` with
`f z = c₂`. -/
def morseBrokenTrajectoryPairs (p r : M) (c₁ c₂ : ℝ) : Set (M × M) :=
  {w | ∃ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
    w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ f w.1 = c₁ ∧
    w.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧ f w.2 = c₂}

/-- Membership in the set of trajectory pairs. -/
@[simp]
theorem mem_morseTrajectoryPairs {p r : M} {c₁ c₂ : ℝ} {w : M × M} :
    w ∈ hX.morseTrajectoryPairs p r c₁ c₂ ↔
      w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ f w.1 = c₁ ∧ f w.2 = c₂ ∧
        ∃ t, hX.flow t w.1 = w.2 :=
  Iff.rfl

/-- Membership in the set of broken trajectory pairs. -/
@[simp]
theorem mem_morseBrokenTrajectoryPairs {p r : M} {c₁ c₂ : ℝ} {w : M × M} :
    w ∈ hX.morseBrokenTrajectoryPairs p r c₁ c₂ ↔
      ∃ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
        w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ f w.1 = c₁ ∧
        w.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧ f w.2 = c₂ :=
  Iff.rfl

/-- No pair of points of an unbroken trajectory is the pair of points of a broken one. -/
theorem disjoint_morseTrajectoryPairs_morseBrokenTrajectoryPairs (p r : M) (c₁ c₂ : ℝ) :
    Disjoint (hX.morseTrajectoryPairs p r c₁ c₂) (hX.morseBrokenTrajectoryPairs p r c₁ c₂) := by
  refine disjoint_left.2 fun w hw hw' ↦ ?_
  obtain ⟨q, -, -, hqr, hy, -⟩ := hw'
  have hqr' : q ≠ r := by rintro rfl; omega
  exact (Flow.disjoint_stableSet hqr').notMem_of_mem_left hy.2 hw.1.2

/-- **The unbroken trajectories form a copy of a level slice.** Recording a trajectory from `p`
to `r` by its point on the level `c₁` identifies the pairs of its points on the levels `c₁` and
`c₂`, for `f r < c₂ < f p`, with the level slice `W^u(p) ∩ W^s(r) ∩ {f = c₁}`. -/
theorem exists_homeomorph_morseTrajectoryPairs (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p r : M}
    (hpr : p ≠ r) {c₁ c₂ : ℝ} (hr₂ : f r < c₂) (h₂p : c₂ < f p) :
    ∃ Φ : hX.morseTrajectoryPairs p r c₁ c₂ ≃ₜ
        ↥(hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {y | f y = c₁}),
      ∀ w, (Φ w : M) = (w : M × M).1 := by
  -- The orbit of each point of the slice meets the level `c₂` at a unique time `τ y`.
  have hτ (y : ↥(hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {y | f y = c₁})) :
      ∃! t, f (hX.flow t y) = c₂ :=
    hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hpr y.2.1 hr₂ h₂p
  choose τ hτ' using fun y ↦ (hτ y).exists
  -- The point of the level `c₂` depends continuously on the point of the level `c₁`.
  have hg : Continuous fun y ↦ hX.flow (τ y) (y : M) := by
    refine continuous_iff_continuousAt.2 fun y ↦ ?_
    obtain ⟨σ, hσ, hlim⟩ := hX.exists_tendsto_flow_of_tendsto hf y.2.1 hr₂ h₂p
      (continuous_subtype_val.tendsto y) (s := τ) hτ'
    rwa [(hτ y).unique hσ (hτ' y)] at hlim
  refine ⟨
    { toFun w := ⟨w.1.1, w.2.1, w.2.2.1⟩
      invFun y := ⟨(y.1, hX.flow (τ y) y.1), y.2.1, y.2.2, hτ' y, τ y, rfl⟩
      left_inv := ?_
      right_inv y := rfl
      continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.prodMk hg).subtype_mk _ }, fun w ↦ rfl⟩
  rintro ⟨⟨y, z⟩, hy, hyc, hzc, t, ht⟩
  obtain rfl : hX.flow t y = z := ht
  have := (hτ ⟨y, hy, hyc⟩).unique (hτ' ⟨y, hy, hyc⟩) hzc
  exact Subtype.ext (Prod.ext rfl (congrArg (hX.flow · y) this))

omit hX in
/-- Membership in the set of broken trajectories, with the trajectory slices unfolded. The sets
`morseBrokenTrajectorySet` and `morseTrajectorySlice` are not exposed outside their modules, so
this combines `mem_morseBrokenTrajectorySet` with `mem_morseTrajectorySlice`. -/
private theorem mem_morseBrokenTrajectorySet' {hX : IsAdaptedPseudoGradient f X}
    {p r : M} {x : criticalPoints 𝓘(ℝ, E) f × M × M} :
    x ∈ hX.morseBrokenTrajectorySet p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
      (x.2.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet x.1 ∧ f x.2.1 = (f p + f x.1) / 2) ∧
      (x.2.2 ∈ hX.flow.unstableSet x.1 ∩ hX.flow.stableSet r ∧ f x.2.2 = (f x.1 + f r) / 2) := by
  simp [mem_morseBrokenTrajectorySet, mem_morseTrajectorySlice, and_assoc]

/-- Every broken trajectory pair lies on the orbits of the two components of a broken
trajectory. -/
private theorem exists_mem_morseBrokenTrajectorySet_of_mem_morseBrokenTrajectoryPairs
    (hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p r : M} {c₁ c₂ : ℝ} {w : M × M}
    (hw : w ∈ hX.morseBrokenTrajectoryPairs p r c₁ c₂) :
    ∃ x ∈ hX.morseBrokenTrajectorySet p r, ∃ t₁ t₂ : ℝ,
      hX.flow t₁ w.1 = x.2.1 ∧ hX.flow t₂ w.2 = x.2.2 := by
  obtain ⟨q, hq, hpq, hqr, hy, -, hz, -⟩ := hw
  have hpq' : p ≠ q := by rintro rfl; omega
  have hqr' : q ≠ r := by rintro rfl; omega
  have hy' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hpq' hy
  have hz' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hqr' hz
  -- Move the two points to the middle levels of their components.
  obtain ⟨t₁, ht₁⟩ := (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf hpq' hy
    (c := (f p + f q) / 2) (by linarith [hy'.1, hy'.2]) (by linarith [hy'.1, hy'.2])).exists
  obtain ⟨t₂, ht₂⟩ := (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf hqr' hz
    (c := (f q + f r) / 2) (by linarith [hz'.1, hz'.2]) (by linarith [hz'.1, hz'.2])).exists
  exact ⟨(⟨q, mem_criticalPoints_iff_mfderiv_eq_zero.2 hq⟩, hX.flow t₁ w.1, hX.flow t₂ w.2),
    mem_morseBrokenTrajectorySet'.2 ⟨hpq, hqr,
      ⟨hX.flow.isInvariant_unstableSet_inter_stableSet _ _ _ hy, ht₁⟩,
      ⟨hX.flow.isInvariant_unstableSet_inter_stableSet _ _ _ hz, ht₂⟩⟩, t₁, t₂, rfl, rfl⟩

/-- **The broken trajectory pairs count the broken trajectories.** Recording a broken index-two
trajectory by its points on the levels `c₁` and `c₂`, rather than by the points of its two
components on their middle levels, does not change the number of broken trajectories. -/
theorem ncard_morseBrokenTrajectoryPairs (hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (p r : criticalPoints 𝓘(ℝ, E) f) {c₁ c₂ : ℝ} (hr₂ : f r < c₂) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    (hX.morseBrokenTrajectoryPairs p r c₁ c₂).ncard = (hX.morseBrokenTrajectorySet p r).ncard := by
  have hne {a b : M} (h : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1) :
      a ≠ b := by
    rintro rfl; omega
  -- The two components of every broken trajectory cross the levels `c₁` and `c₂`.
  have hcross : ∀ x ∈ hX.morseBrokenTrajectorySet p r,
      (∃ t, f (hX.flow t x.2.1) = c₁) ∧ ∃ t, f (hX.flow t x.2.2) = c₂ := by
    rintro ⟨q, z₁, z₂⟩ hx
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := mem_morseBrokenTrajectorySet'.1 hx
    have h₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf (hne hpq) hz₁.1
    have h₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf (hne hqr) hz₂.1
    have hq := hgap q q.2
      ⟨h₂.1.trans h₂.2, h₁.1.trans h₁.2⟩
    exact ⟨(hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf (hne hpq) hz₁.1 hq.2
      h₁p).exists, (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf (hne hqr)
      hz₂.1 hr₂ hq.1).exists⟩
  choose! τ₁ hτ₁ using fun x hx ↦ (hcross x hx).1
  choose! τ₂ hτ₂ using fun x hx ↦ (hcross x hx).2
  symm
  refine ncard_congr (fun x _ ↦ (hX.flow (τ₁ x) x.2.1, hX.flow (τ₂ x) x.2.2)) ?_ ?_ ?_
  · rintro x hx
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := mem_morseBrokenTrajectorySet'.1 hx
    exact ⟨x.1, mem_criticalPoints_iff_mfderiv_eq_zero.1 x.1.2, hpq, hqr,
      hX.flow.isInvariant_unstableSet_inter_stableSet _ _ _ hz₁.1, hτ₁ x hx,
      hX.flow.isInvariant_unstableSet_inter_stableSet _ _ _ hz₂.1, hτ₂ x hx⟩
  · rintro ⟨q, z₁, z₂⟩ ⟨q', z₁', z₂'⟩ hx hx' heq
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := mem_morseBrokenTrajectorySet'.1 hx
    obtain ⟨-, -, hz₁', hz₂'⟩ := mem_morseBrokenTrajectorySet'.1 hx'
    simp only [Prod.mk.injEq] at heq
    -- The intermediate critical point is the limit of the first component.
    obtain rfl : q = q' := Subtype.ext <| by
      by_contra hqq
      refine (Flow.disjoint_stableSet hqq).notMem_of_mem_left
        ((hX.flow.apply_mem_stableSet_iff (τ₁ (q, z₁, z₂))).2 hz₁.1.2) ?_
      rw [heq.1]
      exact (hX.flow.apply_mem_stableSet_iff _).2 hz₁'.1.2
    exact Prod.ext rfl (Prod.ext
      (hX.eq_of_flow_eq_of_value_eq (hne hpq) hz₁.1 heq.1 (hz₁.2.trans hz₁'.2.symm))
      (hX.eq_of_flow_eq_of_value_eq (hne hqr) hz₂.1 heq.2 (hz₂.2.trans hz₂'.2.symm)))
  · intro w hw
    obtain ⟨x, hx, t₁, t₂, ht₁, ht₂⟩ :=
      hX.exists_mem_morseBrokenTrajectorySet_of_mem_morseBrokenTrajectoryPairs hdf hw
    obtain ⟨q, hq, hpq, hqr, -, hyc, -, hzc⟩ := hw
    obtain ⟨hpq', hqr', hz₁, hz₂⟩ := mem_morseBrokenTrajectorySet'.1 hx
    -- The level points of the two components are the given pair.
    refine ⟨x, hx, Prod.ext ?_ ?_⟩
    · refine hX.eq_of_flow_eq_of_value_eq (hne hpq')
        (hX.flow.isInvariant_unstableSet_inter_stableSet _ _ _ hz₁.1) (t := -τ₁ x) (t' := t₁)
        ?_ ((hτ₁ x hx).trans hyc.symm)
      rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply, ht₁]
    · refine hX.eq_of_flow_eq_of_value_eq (hne hqr')
        (hX.flow.isInvariant_unstableSet_inter_stableSet _ _ _ hz₂.1) (t := -τ₂ x) (t' := t₂)
        ?_ ((hτ₂ x hx).trans hzc.symm)
      rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply, ht₂]

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Finitely many broken trajectories.** Under the Morse–Smale condition, the pairs of points of
broken index-two trajectories on two levels form a finite set. -/
theorem finite_morseBrokenTrajectoryPairs {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (c₁ c₂ : ℝ) :
    (hX.morseBrokenTrajectoryPairs p r c₁ c₂).Finite := by
  have hcrit {q : M} : q ∈ criticalPoints 𝓘(ℝ, E) f ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 :=
    mem_criticalPoints_iff_mfderiv_eq_zero
  -- Sort the broken trajectories by their intermediate critical point `q`.
  refine ((hf.finite_criticalPoints.inter_of_left {q |
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1}).biUnion
    fun q hq ↦
      (h.finite_unstableSet_inter_stableSet_inter_level hf hp (hcrit.1 hq.1) hq.2.1 c₁).prod
        (h.finite_unstableSet_inter_stableSet_inter_level hf (hcrit.1 hq.1) hr hq.2.2 c₂)).subset ?_
  rintro w ⟨q, hq, hpq, hqr, hy, hyc, hz, hzc⟩
  exact mem_biUnion ⟨hcrit.2 hq, hpq, hqr⟩ ⟨⟨hy, hyc⟩, hz, hzc⟩

include h hf in
/-- **The limits of trajectories are trajectories or broken trajectories.** Let `p` and `r` be
critical points with `ind p = ind r + 2`, and let the levels `f r < c₂ < c₁ < f p` separate every
critical value strictly between `f r` and `f p` from `f r` and `f p`. Then every limit of pairs of
points of trajectories from `p` to `r` on the levels `c₁` and `c₂` is the pair of points of a
trajectory from `p` to `r`, or of a trajectory broken once at a critical point of intermediate
index. -/
theorem closure_morseTrajectoryPairs_subset {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    closure (hX.morseTrajectoryPairs p r c₁ c₂) ⊆
      hX.morseTrajectoryPairs p r c₁ c₂ ∪ hX.morseBrokenTrajectoryPairs p r c₁ c₂ := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  intro w hw
  obtain ⟨v, hvP, hvw⟩ := mem_closure_iff_seq_limit.1 hw
  choose hvpr hv₁ hv₂ s hs using hvP
  have hv₁w := (continuous_fst.tendsto w).comp hvw
  have hv₂w := (continuous_snd.tendsto w).comp hvw
  -- A level `c₁` point is never critical.
  have hreg : ∀ y, f y = c₁ → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := fun y hy hy0 ↦ by
    have := hgap y (mem_criticalPoints_iff_mfderiv_eq_zero.2 hy0) (hy ▸ ⟨hr₂.trans h₂₁, h₁p⟩)
    exact (hy ▸ this).2.false
  obtain ⟨n, y, hn, hyc, hyv, hcases⟩ :=
    h.exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two hf hp hr hind hreg
      (fun k ↦ (v k).1) fun k ↦ ⟨hvpr k, hv₁ k⟩
  obtain rfl : y = w.1 := tendsto_nhds_unique hyv (hv₁w.comp hn.tendsto_atTop)
  rcases hcases with hy | ⟨q, z, t, hq, hpq, hqr, hz, hcases⟩
  · -- The limit is unbroken; its second point is where its orbit meets the level `c₂`.
    obtain ⟨σ, hσ, hlim⟩ := hX.exists_tendsto_flow_of_tendsto hdf hy hr₂
      (h₂₁.trans h₁p) hyv (s := fun k ↦ s (n k)) fun k ↦ (hs (n k)).symm ▸ hv₂ (n k)
    have hw₂ : hX.flow σ w.1 = w.2 := tendsto_nhds_unique hlim (by
      simpa only [Function.comp_def, hs] using hv₂w.comp hn.tendsto_atTop)
    exact Or.inl ⟨hy, hyc, hw₂ ▸ hσ, σ, hw₂⟩
  have hpq' : p ≠ q := by rintro rfl; omega
  have hqr' : q ≠ r := by rintro rfl; omega
  have hqc : q ∈ criticalPoints 𝓘(ℝ, E) f := mem_criticalPoints_iff_mfderiv_eq_zero.2 hq
  rcases hcases with ⟨hy, hz', -⟩ | ⟨hy, hz', -⟩
  · -- The level `c₁` is crossed before the break at `q`, and the level `c₂` after it.
    have hfy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hpq' hy
    have hfz := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hqr' hz'
    have hq₂ := (hgap q hqc ⟨hfz.1.trans hfz.2, hfy.2.trans' hfy.1⟩).1
    obtain ⟨σ, hσ, hlim⟩ := hX.exists_tendsto_flow_of_tendsto hdf hz' hr₂ hq₂ hz
      (s := fun k ↦ s (n k) - t k) fun k ↦ by
        rw [← Flow.map_add, sub_add_cancel, hs, hv₂]
    have hw₂ : hX.flow σ z = w.2 := tendsto_nhds_unique hlim (by
      simpa only [Function.comp_def, ← Flow.map_add, sub_add_cancel, hs] using
        hv₂w.comp hn.tendsto_atTop)
    exact Or.inr ⟨q, hq, hpq, hqr, hy, hyc,
      hw₂ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet q r σ hz', hw₂ ▸ hσ⟩
  · -- A point of the level `c₁` cannot lie after the break at `q`, which is below `c₁`.
    have hfy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hqr' hy
    have hfz := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hpq' hz'
    have hq₁ := (hgap q hqc ⟨hfy.1.trans hfy.2, hfz.2.trans' hfz.1⟩).2
    linarith [hfy.2]

include h hf in
/-- Only finitely many points of the compactified space are not unbroken trajectories. -/
theorem finite_closure_diff_morseTrajectoryPairs {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    (closure (hX.morseTrajectoryPairs p r c₁ c₂) \ hX.morseTrajectoryPairs p r c₁ c₂).Finite :=
  (h.finite_morseBrokenTrajectoryPairs hf hp hr c₁ c₂).subset fun _ hw ↦
    (h.closure_morseTrajectoryPairs_subset hf hp hr hind hr₂ h₂₁ h₁p hgap hw.1).resolve_left hw.2

include h hf in
/-- **The unbroken trajectories are open in the compactified space.** -/
theorem isOpen_preimage_val_morseTrajectoryPairs {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    IsOpen ((↑) ⁻¹' hX.morseTrajectoryPairs p r c₁ c₂ :
      Set (closure (hX.morseTrajectoryPairs p r c₁ c₂))) := by
  -- Its complement is the preimage of a finite, hence closed, set.
  have hc : IsClosed ((↑) ⁻¹' (closure (hX.morseTrajectoryPairs p r c₁ c₂) \
      hX.morseTrajectoryPairs p r c₁ c₂) : Set (closure (hX.morseTrajectoryPairs p r c₁ c₂))) :=
    (h.finite_closure_diff_morseTrajectoryPairs hf hp hr hind hr₂ h₂₁ h₁p
      hgap).isClosed.preimage continuous_subtype_val
  convert hc.isOpen_compl using 1
  ext x
  simp only [mem_preimage, mem_compl_iff, Set.mem_sdiff, Subtype.coe_prop, true_and, not_not]

include h hf in
/-- **The compactified space is one-dimensional at unbroken trajectories.** Every unbroken
trajectory has a neighbourhood in the compactified space homeomorphic to an open subset of `ℝ`. -/
theorem exists_nhds_homeomorph_of_mem_morseTrajectoryPairs {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁)
    {w : M × M} (hw : w ∈ closure (hX.morseTrajectoryPairs p r c₁ c₂))
    (hwP : w ∈ hX.morseTrajectoryPairs p r c₁ c₂) :
    ∃ N ∈ 𝓝 (⟨w, hw⟩ : closure (hX.morseTrajectoryPairs p r c₁ c₂)),
      ∃ V : Set ℝ, IsOpen V ∧ Nonempty (V ≃ₜ N) := by
  have hpr : p ≠ r := by rintro rfl; omega
  obtain ⟨Φ, hΦ⟩ := hX.exists_homeomorph_morseTrajectoryPairs
    (hf.contMDiff.mdifferentiable (by simp)) hpr hr₂ (h₂₁.trans h₁p)
  -- The level slice is a manifold modelled on a line `L`.
  obtain ⟨L, hL, C, -, -⟩ := h.exists_unstableSet_inter_stableSet_level_isManifold hf hp hr hpr
    ⟨w.1, hwP.1, hwP.2.1⟩
  let _ := C
  have hL1 : Module.finrank ℝ L = Module.finrank ℝ ℝ := by rw [Module.finrank_self]; omega
  -- The unbroken trajectories sit openly in the compactified space.
  let ι : hX.morseTrajectoryPairs p r c₁ c₂ → closure (hX.morseTrajectoryPairs p r c₁ c₂) :=
    fun x ↦ ⟨x.1, subset_closure x.2⟩
  have hι : IsOpenEmbedding ι := by
    refine ⟨(IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).1 IsEmbedding.subtypeVal, ?_⟩
    convert h.isOpen_preimage_val_morseTrajectoryPairs hf hp hr hind hr₂ h₂₁ h₁p hgap
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have : Nonempty (hX.morseTrajectoryPairs p r c₁ c₂) := ⟨⟨w, hwP⟩⟩
  let G := ((hι.toOpenPartialHomeomorph ι).symm.trans Φ.toOpenPartialHomeomorph).trans
    ((chartAt L (Φ ⟨w, hwP⟩)).trans
      (ContinuousLinearEquiv.ofFinrankEq hL1).toHomeomorph.toOpenPartialHomeomorph)
  refine ⟨G.source, G.open_source.mem_nhds ?_, G.target, G.open_target,
    ⟨G.toHomeomorphSourceTarget.symm⟩⟩
  have hιw : ι ⟨w, hwP⟩ = ⟨w, hw⟩ := rfl
  simp [G, ← hιw, hι.toOpenPartialHomeomorph_left_inv]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
