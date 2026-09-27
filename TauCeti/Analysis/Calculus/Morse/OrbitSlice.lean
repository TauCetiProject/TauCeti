/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.LevelSlice
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Connecting orbits and intermediate level sets

For a negative-gradient flow, every orbit connecting two distinct limiting points meets an
intermediate level exactly once. Consequently the quotient map from connecting points to their
time-translation orbits restricts to a bijection on that level. This identifies the underlying
points of an unparametrized Morse trajectory space with a level slice, before any smooth
structure or compactification is constructed.

The use of an intermediate level as a slice follows Audin--Damian,
*Morse Theory and Floer Homology*, Chapter 2.
-/

public section

open Set Topology

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q : E}

/-- The quotient map is bijective from an intermediate level of the connecting set onto
the orbit classes containing connecting points. -/
theorem IsNegativeGradient.bijOn_quotient_connecting_level
    (hφ : IsNegativeGradient φ f)
    (hf : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, ∀ t,
      DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    {c : ℝ} (hc : f q < c ∧ c < f p) :
    letI : AddAction ℝ E := φ.toAddAction
    Set.BijOn (fun x : E ↦ (Quotient.mk'' x : AddAction.orbitRel.Quotient ℝ E))
      ((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})
      {a | ∃ x ∈ unstableSet φ p ∩ stableSet φ q,
        (Quotient.mk'' x : AddAction.orbitRel.Quotient ℝ E) = a} := by
  have hpq : p ≠ q := by
    intro heq
    subst q
    exact (lt_asymm hc.1 hc.2)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hx.1, rfl⟩
  · intro x hx y hy hxy
    obtain ⟨t, ht'⟩ := Quotient.exact hxy
    have ht : φ t y = x := ht'
    have hstrict := hφ.orbit_strictAnti_of_mem_unstableSet_inter_stableSet
      (hf y hy.1) hpq hy.1
    have hzero : t = 0 := hstrict.injective (by
      simpa only [ht, φ.map_zero_apply] using (hx.2.trans hy.2.symm))
    simpa only [hzero, φ.map_zero_apply] using ht.symm
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨t, ht, _⟩ := hφ.existsUnique_time_value_of_mem_unstableSet_inter_stableSet
      (hf x hx) hfp hfq hx hc
    refine ⟨φ t x, ⟨⟨(isInvariant_unstableSet φ p t hx.1),
      (isInvariant_stableSet φ q t hx.2)⟩, ht⟩, ?_⟩
    exact Quotient.sound ⟨t, rfl⟩

end Flow
