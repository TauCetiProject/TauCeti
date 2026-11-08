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
them (`TauCeti.IsMorse.exists_separating_levels`). A broken trajectory through
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

* `TauCeti.IsMorse.exists_separating_levels`: levels separating the intermediate critical values
  exist.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `trajectoryLevelPairs`: the trajectories from `p` to `r`, recorded by their points on two
  levels.
* `brokenLevelPairs`: the broken index-two trajectories from `p` to `r`, recorded in the same way.
* `disjoint_trajectoryLevelPairs_brokenLevelPairs`: no pair is both unbroken and broken.
* `bijOn_brokenLevelPairs`, `ncard_brokenLevelPairs`: following the flow from the middle levels
  to the levels `c₁` and `c₂` is a bijection from the broken trajectories onto the broken pairs.
* `IsMorseSmale.finite_brokenLevelPairs`: there are finitely many broken pairs.
* `IsMorseSmale.closure_trajectoryLevelPairs_subset`: limits of unbroken pairs are unbroken or
  broken.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories) and Chapter 4 (the proof that
  `∂ ∘ ∂ = 0`).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Separating levels exist.** For a Morse function on a compact manifold and critical points `p`
and `r`, there are levels `c₂` above `f r` and `c₁` below `f p` such that every critical value
strictly between `f r` and `f p` lies strictly between `c₂` and `c₁`, and no critical point lies on
the level `c₁`. -/
theorem IsMorse.exists_separating_levels (hf : IsMorse 𝓘(ℝ, E) f) (p r : M) :
    ∃ c₁ c₂ : ℝ, c₁ < f p ∧ f r < c₂ ∧ (∀ y, f y = c₁ → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0) ∧
      ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f r < f q → f q < f p → c₂ < f q ∧ f q < c₁ := by
  have hcrit := hf.finite_criticalPoints
  -- Levels close enough to `f p` from below, and to `f r` from above, separate the finitely many
  -- critical values.
  have h₁ : ∀ᶠ c in 𝓝[<] (f p), c < f p ∧
      ∀ q ∈ criticalPoints 𝓘(ℝ, E) f, f q < f p → f q < c :=
    (eventually_nhdsWithin_of_forall fun _ h ↦ h).and <| (eventually_all_finite hcrit).2
      fun q _ ↦ by
        by_cases hq : f q < f p
        · filter_upwards [Ioo_mem_nhdsLT hq] with c hc _ using hc.1
        · exact Eventually.of_forall fun _ h ↦ absurd h hq
  have h₂ : ∀ᶠ c in 𝓝[>] (f r), f r < c ∧
      ∀ q ∈ criticalPoints 𝓘(ℝ, E) f, f r < f q → c < f q :=
    (eventually_nhdsWithin_of_forall fun _ h ↦ h).and <| (eventually_all_finite hcrit).2
      fun q _ ↦ by
        by_cases hq : f r < f q
        · filter_upwards [Ioo_mem_nhdsGT hq] with c hc _ using hc.2
        · exact Eventually.of_forall fun _ h ↦ absurd h hq
  obtain ⟨c₁, hc₁p, hc₁⟩ := h₁.exists
  obtain ⟨c₂, hc₂r, hc₂⟩ := h₂.exists
  refine ⟨c₁, c₂, hc₁p, hc₂r, fun y hy h0 ↦ ?_, fun q hq hrq hqp ↦ ?_⟩
  · have hy' := hc₁ y (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) (hy ▸ hc₁p)
    exact hy'.ne hy
  · exact ⟨hc₂ q (mem_criticalPoints_iff_mfderiv_eq_zero.2 hq) hrq,
      hc₁ q (mem_criticalPoints_iff_mfderiv_eq_zero.2 hq) hqp⟩

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
  have hne : q ≠ r := by
    rintro rfl
    omega
  exact (Flow.disjoint_stableSet hne).notMem_of_mem_left hq.2 hT.1.2

variable {hX}

/-- Following a trajectory from `a` to `b` to its point on a level `c` strictly between `f b` and
`f a` stays on the trajectory and lands on the level. -/
private theorem flow_levelCrossingTime_mem (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {a b z : M}
    (hab : a ≠ b) (hz : z ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {c : ℝ}
    (hc : f b < c ∧ c < f a) :
    hX.flow (Flow.levelCrossingTime hX.flow f c z) z ∈
        hX.flow.unstableSet a ∩ hX.flow.stableSet b ∧
      f (hX.flow (Flow.levelCrossingTime hX.flow f c z) z) = c :=
  ⟨hX.flow.isInvariant_unstableSet_inter_stableSet a b _ hz, Flow.apply_flow_levelCrossingTime
    (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hab hz hc.1 hc.2).exists⟩

/-- A point `w` of a trajectory from `a` to `b` lying on the level `c` is the point on that level of
the orbit of any `φ s w`. -/
private theorem flow_levelCrossingTime_flow (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {a b w : M}
    (hab : a ≠ b) (hw : w ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {c : ℝ}
    (hwc : f w = c) (s : ℝ) :
    hX.flow (Flow.levelCrossingTime hX.flow f c (hX.flow s w)) (hX.flow s w) = w := by
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hab hw
  rw [Flow.levelCrossingTime_flow hanti ⟨0, by rwa [Flow.map_zero_apply]⟩,
    (Flow.levelCrossingTime_eq_zero_iff hanti ⟨0, by rwa [Flow.map_zero_apply]⟩).2 hwc,
    ← Flow.map_add, zero_sub, neg_add_cancel, Flow.map_zero_apply]

/-- Two points of trajectories from `a` to `b` on the same level and on the same orbit are equal.
-/
private theorem eq_of_flow_eq (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {a b z z' : M} (hab : a ≠ b)
    (hz : z ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) (hzz' : f z = f z') {t t' : ℝ}
    (ht : hX.flow t z = hX.flow t' z') : z = z' := by
  have hz' : z' = hX.flow (t - t') z := by
    rw [sub_eq_neg_add, Flow.map_add, ht, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have h0 : t - t' = 0 :=
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hab hz).injective
      (by rw [← hz', Flow.map_zero_apply, hzz'])
  rw [hz', h0, Flow.map_zero_apply]

/-- **Broken trajectories correspond to broken pairs.** Let the levels `c₂ > f r` and `c₁ < f p`
separate the critical values of the intermediate index strictly between `f r` and `f p`. Sending a
broken trajectory `(q, z₁, z₂)`, recorded by points on the middle levels, to the point of the orbit
of `z₁` on the level `c₁` and the point of the orbit of `z₂` on the level `c₂` is a bijection onto
the broken pairs. -/
theorem bijOn_brokenLevelPairs (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p r : M} {c₁ c₂ : ℝ}
    (hc₁ : c₁ < f p) (hc₂ : f r < c₂)
    (hsep : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 →
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 →
      f r < f q → f q < f p → c₂ < f q ∧ f q < c₁) :
    BijOn (fun x : criticalPoints 𝓘(ℝ, E) f × M × M ↦
        (hX.flow (Flow.levelCrossingTime hX.flow f c₁ x.2.1) x.2.1,
          hX.flow (Flow.levelCrossingTime hX.flow f c₂ x.2.2) x.2.2))
      (hX.morseBrokenTrajectorySet p r) (hX.brokenLevelPairs p r c₁ c₂) := by
  have hne {a b : M} (h : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1) :
      a ≠ b := by
    rintro rfl
    omega
  -- The critical values along a broken trajectory through `q` are ordered, so `q` is separated.
  have hlev {q y z : M} (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
      (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
      (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
      (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
      (hz : z ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
      (f q < c₁ ∧ c₁ < f p) ∧ f r < c₂ ∧ c₂ < f q := by
    have hy' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf (hne hpq) hy
    have hz' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf (hne hqr) hz
    have hs := hsep q hq hpq hqr (hz'.1.trans hz'.2) (hy'.1.trans hy'.2)
    exact ⟨⟨hs.2, hc₁⟩, hc₂, hs.1⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨q, z₁, z₂⟩ hx
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := (mem_morseBrokenTrajectorySet hX).1 hx
    rw [mem_morseTrajectorySlice] at hz₁ hz₂
    have hq := mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2
    obtain ⟨hc₁q, hc₂q⟩ := hlev hpq hqr hq ⟨hz₁.1, hz₁.2.1⟩ ⟨hz₂.1, hz₂.2.1⟩
    exact ⟨q, hq, hpq, hqr, flow_levelCrossingTime_mem hf (hne hpq) ⟨hz₁.1, hz₁.2.1⟩ hc₁q,
      flow_levelCrossingTime_mem hf (hne hqr) ⟨hz₂.1, hz₂.2.1⟩ hc₂q⟩
  · rintro ⟨q, z₁, z₂⟩ hx ⟨q', z₁', z₂'⟩ hx' heq
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := (mem_morseBrokenTrajectorySet hX).1 hx
    obtain ⟨-, -, hz₁', hz₂'⟩ := (mem_morseBrokenTrajectorySet hX).1 hx'
    rw [mem_morseTrajectorySlice] at hz₁ hz₂ hz₁' hz₂'
    simp only [Prod.mk.injEq] at heq
    -- The first level point flows to both `q` and `q'`.
    have hqq : q = q' := by
      by_contra hqq
      have h₁ := (Flow.apply_mem_stableSet_iff hX.flow
        (Flow.levelCrossingTime hX.flow f c₁ z₁)).2 hz₁.2.1
      have h₂ := (Flow.apply_mem_stableSet_iff hX.flow
        (Flow.levelCrossingTime hX.flow f c₁ z₁')).2 hz₁'.2.1
      rw [← heq.1] at h₂
      exact (Flow.disjoint_stableSet (Subtype.coe_ne_coe.2 hqq)).notMem_of_mem_left h₁ h₂
    subst hqq
    obtain rfl := eq_of_flow_eq hf (hne hpq) ⟨hz₁.1, hz₁.2.1⟩ (hz₁.2.2.trans hz₁'.2.2.symm) heq.1
    obtain rfl := eq_of_flow_eq hf (hne hqr) ⟨hz₂.1, hz₂.2.1⟩ (hz₂.2.2.trans hz₂'.2.2.symm) heq.2
    rfl
  · rintro ⟨w₁, w₂⟩ ⟨q, hq, hpq, hqr, ⟨hw₁, hw₁c⟩, hw₂, hw₂c⟩
    -- Follow each component of the broken pair back to its middle level.
    obtain ⟨-, hc₁q⟩ := hlev hpq hqr hq hw₁ hw₂
    have hmid {a b w : M} (hab : a ≠ b) (hw : w ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :=
      flow_levelCrossingTime_mem (c := (f a + f b) / 2) hf hab hw
        (by have := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hab hw
            constructor <;> linarith [this.1, this.2])
    refine ⟨(⟨q, mem_criticalPoints_iff_mfderiv_eq_zero.2 hq⟩,
      hX.flow (Flow.levelCrossingTime hX.flow f ((f p + f q) / 2) w₁) w₁,
      hX.flow (Flow.levelCrossingTime hX.flow f ((f q + f r) / 2) w₂) w₂),
      (mem_morseBrokenTrajectorySet hX).2 ⟨hpq, hqr, ?_, ?_⟩, ?_⟩
    · exact (mem_morseTrajectorySlice hX).2
        ⟨(hmid (hne hpq) hw₁).1.1, (hmid (hne hpq) hw₁).1.2, (hmid (hne hpq) hw₁).2⟩
    · exact (mem_morseTrajectorySlice hX).2
        ⟨(hmid (hne hqr) hw₂).1.1, (hmid (hne hqr) hw₂).1.2, (hmid (hne hqr) hw₂).2⟩
    · simp only [flow_levelCrossingTime_flow hf (hne hpq) hw₁ hw₁c,
        flow_levelCrossingTime_flow hf (hne hqr) hw₂ hw₂c]

/-- **Counting broken pairs.** Under the separation hypotheses of
`TauCeti.IsAdaptedPseudoGradient.bijOn_brokenLevelPairs`, there are as many broken pairs as broken
trajectories. -/
theorem ncard_brokenLevelPairs (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p r : M} {c₁ c₂ : ℝ}
    (hc₁ : c₁ < f p) (hc₂ : f r < c₂)
    (hsep : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 →
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 →
      f r < f q → f q < f p → c₂ < f q ∧ f q < c₁) :
    (hX.brokenLevelPairs p r c₁ c₂).ncard = (hX.morseBrokenTrajectorySet p r).ncard := by
  have hbij := bijOn_brokenLevelPairs (hX := hX) hf hc₁ hc₂ hsep
  rw [← hbij.image_eq, hbij.injOn.ncard_image]

namespace IsMorseSmale

/-- **Finitely many broken pairs.** Under the Morse–Smale condition and the separation hypotheses
of `TauCeti.IsAdaptedPseudoGradient.bijOn_brokenLevelPairs`, there are finitely many broken pairs
between two critical points. -/
theorem finite_brokenLevelPairs (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (p r : criticalPoints 𝓘(ℝ, E) f) {c₁ c₂ : ℝ} (hc₁ : c₁ < f p) (hc₂ : f r < c₂)
    (hsep : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 →
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 →
      f r < f q → f q < f p → c₂ < f q ∧ f q < c₁) :
    (hX.brokenLevelPairs p r c₁ c₂).Finite := by
  rw [← (bijOn_brokenLevelPairs (hf.contMDiff.mdifferentiable (by simp)) hc₁ hc₂ hsep).image_eq]
  exact (h.finite_morseBrokenTrajectorySet hf p r).image _

/-- **Limits of unbroken pairs are unbroken or broken.** Let `p` and `r` be critical points with
`ind p = ind r + 2`, let no critical point lie on the level `c₁`, and let every critical value of
the intermediate index strictly between `f r` and `f p` lie strictly between `c₂` and `c₁`. Then
every limit in `M × M` of level pairs of trajectories from `p` to `r` is either such a pair or the
level pair of a broken trajectory. -/
theorem closure_trajectoryLevelPairs_subset (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hreg : ∀ y, f y = c₁ → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0)
    (hsep : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 →
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 →
      f r < f q → f q < f p → c₂ < f q ∧ f q < c₁) :
    closure (hX.trajectoryLevelPairs p r c₁ c₂) ⊆
      hX.trajectoryLevelPairs p r c₁ c₂ ∪ hX.brokenLevelPairs p r c₁ c₂ := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have hpr : p ≠ r := by
    rintro rfl
    omega
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
  all_goals
    have hpq' : p ≠ q := by
      rintro rfl
      omega
    have hqr' : q ≠ r := by
      rintro rfl
      omega
  · -- A limit broken after the level `c₁`: the second points converge on the second component.
    have hyq' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hpq' hyq
    have hzq' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hqr' hzq
    have hsepq := hsep q hq hpq hqr (hzq'.1.trans hzq'.2) (hyq'.1.trans hyq'.2)
    obtain ⟨σ, hσ, -⟩ :=
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd hqr' hzq hc₂.1 hsepq.1
    have hlim₂ := hX.tendsto_flow_of_flow_eq_of_mem_unstableSet_inter_stableSet hfd hqr' hzq hσ
      hzlim (s := fun k ↦ s (n k) - t k)
      fun k ↦ by rw [← Flow.map_add, sub_add_cancel, hsc]
    simp only [← Flow.map_add, sub_add_cancel] at hlim₂
    obtain rfl := tendsto_nhds_unique h₂ hlim₂
    exact Or.inr ⟨q, hq, hpq, hqr, ⟨hyq, hyc⟩,
      hX.flow.isInvariant_unstableSet_inter_stableSet q r σ hzq, hσ⟩
  · -- A limit broken before the level `c₁` would put `f q` both above and below `c₁`.
    have hyq' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hqr' hyq
    have hzq' := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hpq' hzq
    have hsepq := hsep q hq hpq hqr (hyq'.1.trans hyq'.2) (hzq'.1.trans hzq'.2)
    exact absurd hsepq.2 (hyc ▸ hyq'.2).not_gt

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
