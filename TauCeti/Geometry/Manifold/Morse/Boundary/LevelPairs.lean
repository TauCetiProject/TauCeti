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
# Index-two trajectories recorded on two levels, and their broken limits

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` an adapted pseudo-gradient
satisfying the Morse–Smale condition, and `p`, `r` critical points with `ind p = ind r + 2`. To
show that the mod-two Morse boundary squares to zero, the trajectories from `p` to `r` are
compactified by broken trajectories, which must appear as the boundary points of a compact
one-dimensional manifold. Representing a trajectory by its single point on one level does not
give that compactification: two broken trajectories sharing their first component have the same
point on any level that the first component crosses.

Here a trajectory is recorded by the pair of its points on two levels `c₁ > c₂`, chosen so that
every critical point `q` of the intermediate index with `f r < f q < f p` lies strictly between
them (`TauCeti.SeparatesIntermediateLevels`, provided by
`TauCeti.IsMorse.exists_separating_levels`). A broken trajectory through
such a `q` is then recorded by the point of its first component on the level `c₁` and the point
of its second component on the level `c₂`, which determine both components. The pairs of the
unbroken trajectories form `TauCeti.IsAdaptedPseudoGradient.trajectoryLevelPairs`, those of the
broken ones `TauCeti.IsAdaptedPseudoGradient.brokenLevelPairs`. These two sets are disjoint, and
sequential compactness of index-two trajectories shows that every limit of unbroken pairs is
either unbroken or broken. Moreover the broken pairs are in bijection with the broken trajectories
`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySet` counted by the square of the Morse
boundary.

The closure of the unbroken pairs in `M × M` is compact and Hausdorff. What it still needs to be
a one-dimensional manifold whose boundary is exactly the broken pairs is the gluing step: each
broken pair is a limit of unbroken pairs, with a neighbourhood homeomorphic to a half-open interval
(compare `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_homeomorph_closure_splitGluingPairs`).
This is not proved here.

## Main declarations

* `TauCeti.SeparatesIntermediateLevels`: every critical value of the intermediate index strictly
  between `f r` and `f p` lies strictly between `c₂` and `c₁`.
* `TauCeti.SeparatesIntermediateLevels.value_mem_Ioo_of_mem_unstableSet_inter_stableSet`: along
  a broken trajectory from `p` through `q` to `r`, separating levels satisfy `c₂ < f q < c₁`.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `trajectoryLevelPairs`: the trajectories from `p` to `r`, recorded by their points on two
  levels.
* `brokenLevelPairs`: the broken index-two trajectories from `p` to `r`, recorded in the same way.
* `disjoint_trajectoryLevelPairs_brokenLevelPairs`: no pair is both unbroken and broken.
* `bijOn_brokenLevelPairs`, `ncard_brokenLevelPairs`: following the flow from the middle levels
  to the levels `c₁` and `c₂` is a bijection from the broken trajectories onto the broken pairs.
* `IsMorseSmale.finite_brokenLevelPairs`: there are finitely many broken pairs.
* `IsMorseSmale.closure_trajectoryLevelPairs_subset_union_brokenLevelPairs`: limits of unbroken
  pairs are unbroken or broken.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories) and Chapter 4 (the proof that
  `∂ ∘ ∂ = 0`).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section SeparatesIntermediateLevels

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

/-- The levels `c₂` and `c₁` separate the critical values of the intermediate index between `p`
and `r`: every critical point `q` with `ind p = ind q + 1` and `ind q = ind r + 1` whose value
lies strictly between `f r` and `f p` satisfies `c₂ < f q < c₁`. -/
def SeparatesIntermediateLevels (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p r : M) (c₁ c₂ : ℝ) :
    Prop :=
  ∀ q, mfderiv I 𝓘(ℝ) f q = 0 →
    manifoldMorseIndex I f p = manifoldMorseIndex I f q + 1 →
    manifoldMorseIndex I f q = manifoldMorseIndex I f r + 1 →
    f r < f q → f q < f p → c₂ < f q ∧ f q < c₁

/-- Levels separating every critical value strictly between `f r` and `f p`, as provided by
`TauCeti.IsMorse.exists_separating_levels`, separate those of the intermediate index. -/
theorem SeparatesIntermediateLevels.of_forall_mem_criticalPoints {I : ModelWithCorners ℝ E H}
    {f : M → ℝ} {p r : M} {c₁ c₂ : ℝ}
    (h : ∀ q ∈ criticalPoints I f, f r < f q → f q < f p → c₂ < f q ∧ f q < c₁) :
    SeparatesIntermediateLevels I f p r c₁ c₂ :=
  fun q hq _ _ ↦ h q (mem_criticalPoints_iff_mfderiv_eq_zero.2 hq)

/-- Separating levels bound every critical value of the intermediate index strictly between `f r`
and `f p`. -/
theorem SeparatesIntermediateLevels.mem_Ioo {I : ModelWithCorners ℝ E H} {f : M → ℝ}
    {p q r : M} {c₁ c₂ : ℝ} (h : SeparatesIntermediateLevels I f p r c₁ c₂)
    (hq : mfderiv I 𝓘(ℝ) f q = 0)
    (hpq : manifoldMorseIndex I f p = manifoldMorseIndex I f q + 1)
    (hqr : manifoldMorseIndex I f q = manifoldMorseIndex I f r + 1)
    (hrq : f r < f q) (hqp : f q < f p) :
    f q ∈ Ioo c₂ c₁ :=
  h q hq hpq hqr hrq hqp

end SeparatesIntermediateLevels

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Points of different Morse indices are different. -/
private theorem ne_of_manifoldMorseIndex_eq_add {a b : M} {k : ℕ} (hk : 0 < k)
    (h : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + k) : a ≠ b :=
  ne_of_apply_ne (manifoldMorseIndex 𝓘(ℝ, E) f) (by omega)

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The trajectories from `p` to `r`, each recorded by the pair of its points on the levels `c₁`
and `c₂`. -/
def trajectoryLevelPairs (p r : M) (c₁ c₂ : ℝ) : Set (M × M) :=
  {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ f w.1 = c₁ ∧ f w.2 = c₂ ∧
    ∃ t, hX.flow t w.1 = w.2}

/-- Membership in the set of level pairs of trajectories. -/
@[simp]
theorem mem_trajectoryLevelPairs {p r : M} {c₁ c₂ : ℝ} {w : M × M} :
    w ∈ hX.trajectoryLevelPairs p r c₁ c₂ ↔
      w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ f w.1 = c₁ ∧ f w.2 = c₂ ∧
        ∃ t, hX.flow t w.1 = w.2 :=
  Iff.rfl

/-- The broken index-two trajectories from `p` to `r`, each recorded by the point on the level
`c₁` of its component from `p` to the intermediate critical point `q`, and the point on the level
`c₂` of its component from `q` to `r`. -/
def brokenLevelPairs (p r : M) (c₁ c₂ : ℝ) : Set (M × M) :=
  {w | ∃ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
    (w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ f w.1 = c₁) ∧
    w.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧ f w.2 = c₂}

/-- Membership in the set of level pairs of broken trajectories. -/
@[simp]
theorem mem_brokenLevelPairs {p r : M} {c₁ c₂ : ℝ} {w : M × M} :
    w ∈ hX.brokenLevelPairs p r c₁ c₂ ↔
      ∃ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
        (w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ f w.1 = c₁) ∧
        w.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧ f w.2 = c₂ :=
  Iff.rfl

/-- **Unbroken and broken pairs are distinct.** The first point of an unbroken pair flows to `r`,
while the first point of a broken pair flows to a critical point of index `ind r + 1`. -/
theorem disjoint_trajectoryLevelPairs_brokenLevelPairs (p r : M) (c₁ c₂ : ℝ) :
    Disjoint (hX.trajectoryLevelPairs p r c₁ c₂) (hX.brokenLevelPairs p r c₁ c₂) := by
  refine disjoint_left.2 fun w hT hB ↦ ?_
  obtain ⟨q, -, -, hqr, ⟨hq, -⟩, -⟩ := hB
  exact (Flow.disjoint_stableSet (ne_of_manifoldMorseIndex_eq_add one_pos hqr)).notMem_of_mem_left
    hq.2 hT.1.2

variable {hX}

/-- Along a broken trajectory from `p` through `q` to `r`, the critical value `f q` lies between
levels `c₂` and `c₁` separating the critical values of the intermediate index. -/
theorem _root_.TauCeti.SeparatesIntermediateLevels.value_mem_Ioo_of_mem_unstableSet_inter_stableSet
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    {p q r y z : M} {c₁ c₂ : ℝ}
    (hsep : SeparatesIntermediateLevels 𝓘(ℝ, E) f p r c₁ c₂)
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hz : z ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    f q ∈ Ioo c₂ c₁ := by
  have hy' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf
    (ne_of_manifoldMorseIndex_eq_add one_pos hpq) hy
  have hz' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf
    (ne_of_manifoldMorseIndex_eq_add one_pos hqr) hz
  exact hsep.mem_Ioo hq hpq hqr (hz'.1.trans hz'.2) (hy'.1.trans hy'.2)

/-- Along a broken trajectory from `p` through `q` to `r`, following the flow from the middle levels
to the levels `c₁` and `c₂` is a bijection between the level slices of each component. -/
private theorem bijOn_flow_levelCrossingTime_components (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    {p q r y z : M} {c₁ c₂ : ℝ} (hc₁ : c₁ < f p) (hc₂ : f r < c₂)
    (hsep : SeparatesIntermediateLevels 𝓘(ℝ, E) f p r c₁ c₂)
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hz : z ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    BijOn (fun z ↦ hX.flow (Flow.levelCrossingTime hX.flow f c₁ z) z)
        ((hX.flow.unstableSet p ∩ hX.flow.stableSet q) ∩ {z | f z = (f p + f q) / 2})
        ((hX.flow.unstableSet p ∩ hX.flow.stableSet q) ∩ {z | f z = c₁}) ∧
      BijOn (fun z ↦ hX.flow (Flow.levelCrossingTime hX.flow f c₂ z) z)
        ((hX.flow.unstableSet q ∩ hX.flow.stableSet r) ∩ {z | f z = (f q + f r) / 2})
        ((hX.flow.unstableSet q ∩ hX.flow.stableSet r) ∩ {z | f z = c₂}) := by
  have hcq := hsep.value_mem_Ioo_of_mem_unstableSet_inter_stableSet hf hq hpq hqr hy hz
  exact ⟨hX.bijOn_flow_levelCrossingTime_midpoint hf (ne_of_manifoldMorseIndex_eq_add one_pos hpq)
      hcq.2 hc₁,
    hX.bijOn_flow_levelCrossingTime_midpoint hf (ne_of_manifoldMorseIndex_eq_add one_pos hqr) hc₂
      hcq.1⟩

/-- **Broken trajectories correspond to broken pairs.** Let the levels `c₂ > f r` and `c₁ < f p`
separate the critical values of the intermediate index strictly between `f r` and `f p`. Sending a
broken trajectory `(q, z₁, z₂)`, recorded by points on the middle levels, to the point of the orbit
of `z₁` on the level `c₁` and the point of the orbit of `z₂` on the level `c₂` is a bijection onto
the broken pairs. -/
theorem bijOn_brokenLevelPairs (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p r : M} {c₁ c₂ : ℝ}
    (hc₁ : c₁ < f p) (hc₂ : f r < c₂)
    (hsep : SeparatesIntermediateLevels 𝓘(ℝ, E) f p r c₁ c₂) :
    BijOn (fun x : criticalPoints 𝓘(ℝ, E) f × M × M ↦
        (hX.flow (Flow.levelCrossingTime hX.flow f c₁ x.2.1) x.2.1,
          hX.flow (Flow.levelCrossingTime hX.flow f c₂ x.2.2) x.2.2))
      (hX.morseBrokenTrajectorySet p r) (hX.brokenLevelPairs p r c₁ c₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨q, z₁, z₂⟩ hx
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := (mem_morseBrokenTrajectorySet hX).1 hx
    simp only [mem_morseTrajectorySlice, ← and_assoc] at hz₁ hz₂
    have hq := mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2
    obtain ⟨hb₁, hb₂⟩ :=
      bijOn_flow_levelCrossingTime_components hf hc₁ hc₂ hsep hq hpq hqr hz₁.1 hz₂.1
    exact ⟨q, hq, hpq, hqr, hb₁.mapsTo hz₁, hb₂.mapsTo hz₂⟩
  · rintro ⟨q, z₁, z₂⟩ hx ⟨q', z₁', z₂'⟩ hx' heq
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := (mem_morseBrokenTrajectorySet hX).1 hx
    obtain ⟨-, -, hz₁', hz₂'⟩ := (mem_morseBrokenTrajectorySet hX).1 hx'
    simp only [mem_morseTrajectorySlice, ← and_assoc] at hz₁ hz₂ hz₁' hz₂'
    simp only [Prod.mk.injEq] at heq
    -- The first level point flows to both `q` and `q'`.
    have hqq : q = q' := by
      by_contra hqq
      have h₁ := (Flow.apply_mem_stableSet_iff hX.flow
        (Flow.levelCrossingTime hX.flow f c₁ z₁)).2 hz₁.1.2
      have h₂ := (Flow.apply_mem_stableSet_iff hX.flow
        (Flow.levelCrossingTime hX.flow f c₁ z₁')).2 hz₁'.1.2
      rw [← heq.1] at h₂
      exact (Flow.disjoint_stableSet (Subtype.coe_ne_coe.2 hqq)).notMem_of_mem_left h₁ h₂
    subst hqq
    obtain ⟨hb₁, hb₂⟩ := bijOn_flow_levelCrossingTime_components hf hc₁ hc₂ hsep
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2) hpq hqr hz₁.1 hz₂.1
    obtain rfl := hb₁.injOn hz₁ hz₁' heq.1
    obtain rfl := hb₂.injOn hz₂ hz₂' heq.2
    rfl
  · rintro ⟨w₁, w₂⟩ ⟨q, hq, hpq, hqr, hw₁, hw₂⟩
    -- Follow each component of the broken pair back to its middle level.
    obtain ⟨hb₁, hb₂⟩ :=
      bijOn_flow_levelCrossingTime_components hf hc₁ hc₂ hsep hq hpq hqr hw₁.1 hw₂.1
    obtain ⟨z₁, hz₁, rfl⟩ := hb₁.surjOn hw₁
    obtain ⟨z₂, hz₂, rfl⟩ := hb₂.surjOn hw₂
    exact ⟨(⟨q, mem_criticalPoints_iff_mfderiv_eq_zero.2 hq⟩, z₁, z₂),
      (mem_morseBrokenTrajectorySet hX).2 ⟨hpq, hqr, (mem_morseTrajectorySlice hX).2
        ⟨hz₁.1.1, hz₁.1.2, hz₁.2⟩, (mem_morseTrajectorySlice hX).2 ⟨hz₂.1.1, hz₂.1.2, hz₂.2⟩⟩,
      rfl⟩

/-- **Counting broken pairs.** Under the separation hypotheses of
`TauCeti.IsAdaptedPseudoGradient.bijOn_brokenLevelPairs`, there are as many broken pairs as broken
trajectories. -/
theorem ncard_brokenLevelPairs (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p r : M} {c₁ c₂ : ℝ}
    (hc₁ : c₁ < f p) (hc₂ : f r < c₂)
    (hsep : SeparatesIntermediateLevels 𝓘(ℝ, E) f p r c₁ c₂) :
    (hX.brokenLevelPairs p r c₁ c₂).ncard = (hX.morseBrokenTrajectorySet p r).ncard :=
  (bijOn_brokenLevelPairs hf hc₁ hc₂ hsep).ncard_eq.symm

namespace IsMorseSmale

/-- **Finitely many broken pairs.** Under the Morse–Smale condition and the separation hypotheses
of `TauCeti.IsAdaptedPseudoGradient.bijOn_brokenLevelPairs`, there are finitely many broken pairs
between two critical points. -/
theorem finite_brokenLevelPairs (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (p r : criticalPoints 𝓘(ℝ, E) f) {c₁ c₂ : ℝ} (hc₁ : c₁ < f p) (hc₂ : f r < c₂)
    (hsep : SeparatesIntermediateLevels 𝓘(ℝ, E) f p r c₁ c₂) :
    (hX.brokenLevelPairs p r c₁ c₂).Finite :=
  (bijOn_brokenLevelPairs (hf.contMDiff.mdifferentiable (by simp)) hc₁ hc₂
    hsep).finite_iff_finite.1 (h.finite_morseBrokenTrajectorySet hf p r)

/-- **Limits of unbroken pairs are unbroken or broken.** Let `p` and `r` be critical points with
`ind p = ind r + 2`, let no critical point lie on the level `c₁`, and let every critical value of
the intermediate index strictly between `f r` and `f p` lie strictly between `c₂` and `c₁`. Then
every limit in `M × M` of level pairs of trajectories from `p` to `r` is either such a pair or the
level pair of a broken trajectory. -/
theorem closure_trajectoryLevelPairs_subset_union_brokenLevelPairs (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f)
    {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hreg : ∀ y, f y = c₁ → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0)
    (hsep : SeparatesIntermediateLevels 𝓘(ℝ, E) f p r c₁ c₂) :
    closure (hX.trajectoryLevelPairs p r c₁ c₂) ⊆
      hX.trajectoryLevelPairs p r c₁ c₂ ∪ hX.brokenLevelPairs p r c₁ c₂ := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have hpr : p ≠ r := ne_of_manifoldMorseIndex_eq_add two_pos hind
  rintro ⟨y₁, y₂⟩ hy
  obtain ⟨w, hwT, hw⟩ := mem_closure_iff_seq_limit.1 hy
  choose hw₁ hwc₁ hwc₂ s hs using fun k ↦ (mem_trajectoryLevelPairs hX).1 (hwT k)
  obtain ⟨hw₁lim, hw₂lim⟩ := (Prod.tendsto_iff _ _).1 hw
  -- The level `c₂` lies strictly between `f r` and `f p`, being crossed by a trajectory.
  have hc₂ : f r < c₂ ∧ c₂ < f p := by
    have := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hpr
      (hX.flow.isInvariant_unstableSet_inter_stableSet p r (s 0) (hw₁ 0))
    rwa [hs, hwc₂] at this
  obtain ⟨n, y, hn, hyc, hlim, hcase⟩ :=
    h.exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two hf hp hr hind hreg
      (fun k ↦ (w k).1) fun k ↦ ⟨hw₁ k, hwc₁ k⟩
  obtain rfl : y = y₁ := tendsto_nhds_unique hlim (hw₁lim.comp hn.tendsto_atTop)
  -- The second points of the subsequence are its level points on `c₂`.
  have h₂ : Tendsto (fun k ↦ hX.flow (s (n k)) (w (n k)).1) atTop (𝓝 y₂) :=
    (hw₂lim.comp hn.tendsto_atTop).congr fun k ↦ (hs (n k)).symm
  have hsc (k : ℕ) : f (hX.flow (s (n k)) (w (n k)).1) = c₂ := by rw [hs, hwc₂]
  rcases hcase with hyT | ⟨q, z, t, hq, hpq, hqr, hzlim, ⟨hyq, hzq, -⟩ | ⟨hyq, hzq, -⟩⟩
  · -- An unbroken limit: its point on the level `c₂` is the limit of the second points.
    obtain ⟨σ, hσ, -⟩ :=
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd hpr hyT hc₂.1 hc₂.2
    obtain rfl := tendsto_nhds_unique h₂
      (hX.tendsto_flow_of_flow_eq_of_mem_unstableSet_inter_stableSet hfd hpr hyT hσ hlim hsc)
    exact Or.inl ⟨hyT, hyc, hσ, σ, rfl⟩
  · -- A limit broken after the level `c₁`: the second points converge on the second component.
    have hqr' := ne_of_manifoldMorseIndex_eq_add one_pos hqr
    obtain ⟨σ, hσ, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd hqr' hzq
      hc₂.1 (hsep.value_mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hq hpq hqr hyq hzq).1
    have hlim₂ := hX.tendsto_flow_of_flow_eq_of_mem_unstableSet_inter_stableSet hfd hqr' hzq hσ
      hzlim (s := fun k ↦ s (n k) - t k)
      fun k ↦ by rw [← Flow.map_add, sub_add_cancel, hsc]
    simp only [← Flow.map_add, sub_add_cancel] at hlim₂
    obtain rfl := tendsto_nhds_unique h₂ hlim₂
    exact Or.inr ⟨q, hq, hpq, hqr, ⟨hyq, hyc⟩,
      hX.flow.isInvariant_unstableSet_inter_stableSet q r σ hzq, hσ⟩
  · -- A limit broken before the level `c₁` would put `f q` both above and below `c₁`.
    have hyq' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd
      (ne_of_manifoldMorseIndex_eq_add one_pos hqr) hyq
    exact absurd (hsep.value_mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hq hpq hqr hzq hyq).2
      (hyc ▸ hyq'.2).not_gt

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
