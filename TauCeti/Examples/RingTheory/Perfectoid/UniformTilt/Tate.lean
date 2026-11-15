/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Tate
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# The Tate tilt of the p-adic complex numbers

These checks construct the Tate and perfectoid structures on the tilt of `ℂ_p` using existence
of compatible roots, test the zeroth-coordinate power-boundedness criterion, and exhibit a
pseudouniformiser and a unit outside the integral tilt.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltTate

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

local instance : IsTateRing (uniformTilt p ℂ_[p]) := by
  obtain ⟨ϖ⟩ := nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p)
  apply uniformTilt.isTateRing_of_sharp (ϖ := uniformTilt.mk ϖ.root ϖ.root_succ_pow)
  simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero

example : IsPerfectoidTateRing p (uniformTilt p ℂ_[p]) := by
  obtain ⟨ϖ⟩ := nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p)
  apply uniformTilt.isPerfectoidTateRing_of_sharp (ϖ := uniformTilt.mk ϖ.root ϖ.root_succ_pow)
  simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero

example (x : uniformTilt p ℂ_[p]) :
    x ∈ powerBoundedSubring (uniformTilt p ℂ_[p]) ↔ ‖uniformTilt.coeff p ℂ_[p] 0 x‖ ≤ 1 := by
  obtain ⟨ϖ⟩ := nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p)
  have hϖ : IsPseudoUniformizer
      (uniformTilt.coeff p ℂ_[p] 0 (uniformTilt.mk ϖ.root ϖ.root_succ_pow)) := by
    simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero
  rw [uniformTilt.mem_powerBoundedSubring_iff hϖ, mem_powerBoundedSubring,
    isPowerBounded_iff_norm_le_one]

example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    IsPseudoUniformizer (uniformTilt.mk ϖ.root ϖ.root_succ_pow) := by
  rw [isPseudoUniformizer_iff, uniformTilt.isUnit_iff_coeff_zero,
    uniformTilt.isTopologicallyNilpotent_iff_coeff_zero, uniformTilt.coeff_mk]
  exact isPseudoUniformizer_iff.mp ϖ.isPseudoUniformizer_root_zero

example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    let x := uniformTilt.mk (fun n ↦ (ϖ.root n)⁻¹)
      (fun n ↦ by rw [inv_pow, ϖ.root_succ_pow])
    IsUnit x ∧ x ∉ powerBoundedSubring (uniformTilt p ℂ_[p]) := by
  dsimp only
  have hϖ : IsPseudoUniformizer
      (uniformTilt.coeff p ℂ_[p] 0 (uniformTilt.mk ϖ.root ϖ.root_succ_pow)) := by
    simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero
  constructor
  · rw [uniformTilt.isUnit_iff_coeff_zero, uniformTilt.coeff_mk]
    exact ϖ.isPseudoUniformizer_root_zero.isUnit.inv
  · rw [uniformTilt.mem_powerBoundedSubring_iff hϖ, uniformTilt.coeff_mk,
      mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, norm_inv, not_le]
    obtain ⟨h0, h1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
    exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1

end TauCeti.Examples.UniformTiltTate
