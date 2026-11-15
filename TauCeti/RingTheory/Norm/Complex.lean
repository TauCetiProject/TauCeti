/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.Units
public import Mathlib.Algebra.Order.Ring.Units
public import Mathlib.RingTheory.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Norm

/-!
# The norm group of the complex extension of the reals

The complex norm is the squared modulus. Its image on units is therefore exactly the positive
real units. This identifies the norm quotient used in cyclic Galois cohomology with the real
sign quotient, supplying the arithmetic input for the real Brauer invariant.
-/

public section

namespace TauCeti

/-- The norms of nonzero complex numbers are precisely the positive real units. -/
theorem normGroup_real_complex : normGroup ℝ ℂ = Units.posSubgroup ℝ := by
  ext a
  rw [mem_normGroup_iff, Units.mem_posSubgroup]
  constructor
  · rintro ⟨z, hz⟩
    rw [Algebra.norm_complex_apply] at hz
    exact hz ▸ Complex.normSq_pos.mpr z.ne_zero
  · intro ha
    have ha0 : (a : ℝ) ∈ Set.range Complex.normSq := by
      rw [Complex.range_normSq]
      exact ha.le
    obtain ⟨z, hz⟩ := ha0
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact a.ne_zero (by simpa using hz.symm)
    exact ⟨Units.mk0 z hz0, by simpa [Algebra.norm_complex_apply] using hz⟩

end TauCeti
