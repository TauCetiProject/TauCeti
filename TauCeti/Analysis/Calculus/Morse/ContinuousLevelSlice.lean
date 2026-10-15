/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.LevelSlice
import Mathlib.Topology.Order.Basic

/-!
# Continuous normalization of connecting gradient trajectories

An intermediate value of a Morse function selects one time on every connecting orbit. The
selected time varies continuously with the initial point, so shifting each point to that time
gives a continuous map into the level slice. This supplies the topological part of the
unparametrized trajectory-space construction; smooth manifold charts require further work.

The level-slice viewpoint follows Audin--Damian, *Morse Theory and Floer Homology*, Chapter 2.
-/

public section

open Filter Set Topology

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q : E}

/-- The unique time at which a connecting trajectory meets an intermediate level depends
continuously on its initial point. -/
theorem IsNegativeGradient.exists_continuous_levelCrossingTime
    (hφ : IsNegativeGradient φ f)
    (hf : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, DifferentiableAt ℝ f x)
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    {c : ℝ} (hc : f q < c ∧ c < f p) :
    ∃ t : ↥(unstableSet φ p ∩ stableSet φ q) → ℝ,
      Continuous t ∧ ∀ x, f (φ (t x) x.1) = c := by
  let C : Set E := unstableSet φ p ∩ stableSet φ q
  have hforbit (x : C) (u : ℝ) : DifferentiableAt ℝ f (φ u x.1) :=
    hf _ ⟨isInvariant_unstableSet φ p u x.2.1,
      isInvariant_stableSet φ q u x.2.2⟩
  have hpq : p ≠ q := by
    intro heq
    subst q
    exact (lt_asymm hc.1 hc.2)
  have hC : ContinuousOn f C := by
    intro x hx
    exact (hf x hx).continuousAt.continuousWithinAt
  let crossing (x : C) :=
    hφ.existsUnique_time_value_of_mem_unstableSet_inter_stableSet
      (hforbit x) hfp hfq x.2 hc
  let t : C → ℝ := fun x ↦ Classical.choose (crossing x)
  have ht (x : C) : f (φ (t x) x.1) = c := (Classical.choose_spec (crossing x)).1
  have hstrict (x : C) : StrictAnti (fun u : ℝ ↦ f (φ u x.1)) :=
    hφ.orbit_strictAnti_of_mem_unstableSet_inter_stableSet (hforbit x) hpq x.2
  have hvalue (u : ℝ) : Continuous (fun x : C ↦ f (φ u x.1)) := by
    have horbit : Continuous (fun x : C ↦ φ u x.1) :=
      φ.continuous continuous_const continuous_subtype_val
    have hmem (x : C) : φ u x.1 ∈ C :=
      ⟨isInvariant_unstableSet φ p u x.2.1, isInvariant_stableSet φ q u x.2.2⟩
    exact (continuousOn_iff_continuous_domRestrict.mp hC).comp (horbit.subtype_mk hmem)
  refine ⟨t, continuous_iff_continuousAt.mpr (fun x ↦ ?_), ht⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hval : c < f (φ a x.1) := by
      rw [← ht x]
      exact hstrict x ha
    filter_upwards [(hvalue a).continuousAt.eventually (eventually_gt_nhds hval)] with y hy
    by_contra hnot
    have hle : t y ≤ a := le_of_not_gt hnot
    have hmono := (hstrict y).antitone hle
    rw [ht y] at hmono
    exact (not_lt_of_ge hmono) hy
  · intro b hb
    have hval : f (φ b x.1) < c := by
      rw [← ht x]
      exact hstrict x hb
    filter_upwards [(hvalue b).continuousAt.eventually (eventually_lt_nhds hval)] with y hy
    by_contra hnot
    have hle : b ≤ t y := le_of_not_gt hnot
    have hmono := (hstrict y).antitone hle
    rw [ht y] at hmono
    exact (not_lt_of_ge hmono) hy

/-- Moving each connecting point to its unique intersection with an intermediate level is
continuous, fixes points already on that level, and is invariant under time translation. -/
theorem IsNegativeGradient.exists_continuous_levelSlice
    (hφ : IsNegativeGradient φ f)
    (hf : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, DifferentiableAt ℝ f x)
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    {c : ℝ} (hc : f q < c ∧ c < f p) :
    ∃ s : ↥(unstableSet φ p ∩ stableSet φ q) →
        ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}),
      Continuous s ∧ (∀ x, (s x).1 ∈ φ.orbit x.1) ∧
        (∀ x, f x.1 = c → (s x).1 = x.1) ∧
        ∀ (x : ↥(unstableSet φ p ∩ stableSet φ q)) (u : ℝ),
          s ⟨φ u x.1, ⟨isInvariant_unstableSet φ p u x.2.1,
            isInvariant_stableSet φ q u x.2.2⟩⟩ = s x := by
  obtain ⟨t, htcont, ht⟩ :=
    hφ.exists_continuous_levelCrossingTime hf hfp hfq hc
  let s (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
      ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) :=
    ⟨φ (t x) x.1,
      ⟨⟨isInvariant_unstableSet φ p (t x) x.2.1,
        isInvariant_stableSet φ q (t x) x.2.2⟩, ht x⟩⟩
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · exact (φ.continuous htcont continuous_subtype_val).subtype_mk _
  · intro x
    exact φ.mem_orbit_iff.mpr ⟨t x, rfl⟩
  · intro x hx
    have hpq : p ≠ q := by
      intro heq
      subst q
      exact (lt_asymm hc.1 hc.2)
    have hstrict := hφ.orbit_strictAnti_of_mem_unstableSet_inter_stableSet
      (fun u ↦ hf _ ⟨isInvariant_unstableSet φ p u x.2.1,
        isInvariant_stableSet φ q u x.2.2⟩) hpq x.2
    have hzero : t x = 0 := hstrict.injective (by
      simpa only [_root_.Flow.map_zero_apply] using (ht x).trans hx.symm)
    simp only [s, hzero, _root_.Flow.map_zero_apply]
  · intro x u
    apply Subtype.ext
    have hpq : p ≠ q := by
      intro heq
      subst q
      exact (lt_asymm hc.1 hc.2)
    have hstrict := hφ.orbit_strictAnti_of_mem_unstableSet_inter_stableSet
      (fun v ↦ hf _ ⟨isInvariant_unstableSet φ p v x.2.1,
        isInvariant_stableSet φ q v x.2.2⟩) hpq x.2
    have heq : t ⟨φ u x.1, ⟨isInvariant_unstableSet φ p u x.2.1,
        isInvariant_stableSet φ q u x.2.2⟩⟩ + u = t x := by
      apply hstrict.injective
      -- Unfold the orbit function in the injectivity goal to expose the flow composition.
      change f (φ (t ⟨φ u x.1, ⟨isInvariant_unstableSet φ p u x.2.1,
        isInvariant_stableSet φ q u x.2.2⟩⟩ + u) x.1) = f (φ (t x) x.1)
      rw [φ.map_add]
      exact (ht ⟨φ u x.1, ⟨isInvariant_unstableSet φ p u x.2.1,
        isInvariant_stableSet φ q u x.2.2⟩⟩).trans (ht x).symm
    simpa only [s, ← φ.map_add] using congrArg (fun v ↦ φ v x.1) heq

end Flow
