/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Coordinate lemmas for the complex `skewSwap`

This file records coordinate consequences of the standard complex structure on `ℂ × ℂ`, given by
`LinearEquiv.skewSwap ℂ ℂ ℂ`. These facts are useful when calculating with its eigenspaces and the
associated alternating coordinate form.
-/

public section

namespace TauCeti

open scoped ComplexOrder

/-- An `i`-eigenvector of the standard complex structure on `ℂ × ℂ` has second coordinate
`-i` times its first coordinate. -/
theorem skewSwap_snd_eq_neg_I_mul_fst_of_mem_I {E : Type*} [AddCommGroup E] [Module ℂ E]
    {x : E × E}
    (hx : x ∈ Module.End.eigenspace
        (LinearEquiv.skewSwap ℂ E E).toLinearMap Complex.I) :
    x.2 = -Complex.I • x.1 := by
  rw [Module.End.mem_eigenspace_iff] at hx
  have h := congrArg Prod.fst hx
  have h' : -x.2 = Complex.I • x.1 := by
    simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.skewSwap_apply, Prod.fst,
      Prod.smul_fst] using h
  calc
    x.2 = -(-x.2) := by simp
    _ = -(Complex.I • x.1) := congrArg Neg.neg h'
    _ = -Complex.I • x.1 := by rw [neg_smul]

/-- A `-i`-eigenvector of the standard complex structure on `ℂ × ℂ` has second coordinate
`i` times its first coordinate. -/
theorem skewSwap_snd_eq_I_mul_fst_of_mem_neg_I {E : Type*} [AddCommGroup E] [Module ℂ E]
    {x : E × E}
    (hx : x ∈ Module.End.eigenspace
        (LinearEquiv.skewSwap ℂ E E).toLinearMap (-Complex.I)) :
    x.2 = Complex.I • x.1 := by
  rw [Module.End.mem_eigenspace_iff] at hx
  have h := congrArg Prod.fst hx
  have h' : -x.2 = (-Complex.I) • x.1 := by
    simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.skewSwap_apply, Prod.fst,
      Prod.smul_fst] using h
  calc
    x.2 = -(-x.2) := by simp
    _ = -((-Complex.I) • x.1) := congrArg Neg.neg h'
    _ = Complex.I • x.1 := by rw [neg_smul, neg_neg]

namespace Complex

/-- For a nonzero `z : ℂ`, the standard positive expression associated with the `i`-eigenvector
coordinate relation is positive. -/
theorem I_mul_coordinate_form_pos (z : ℂ) (hz : z ≠ 0) :
    0 < Complex.I *
      ((-Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (-Complex.I * z)) := by
  have hcalc : Complex.I *
      ((-Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (-Complex.I * z)) = (2 * Complex.normSq z : ℝ) := by
    rw [map_mul, map_neg]
    norm_num
    rw [Complex.normSq_eq_conj_mul_self]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hcalc]
  exact Complex.zero_lt_real.mpr (mul_pos (by norm_num) (Complex.normSq_pos.mpr hz))

/-- For a nonzero `z : ℂ`, the standard positive expression associated with the `-i`-eigenvector
coordinate relation is positive. -/
theorem neg_I_mul_coordinate_form_pos (z : ℂ) (hz : z ≠ 0) :
    0 < (-Complex.I) *
      ((Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (Complex.I * z)) := by
  have heq : (-Complex.I) *
      ((Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (Complex.I * z)) = Complex.I *
      ((-Complex.I * z) * starRingEnd ℂ z -
        z * starRingEnd ℂ (-Complex.I * z)) := by
    rw [map_mul]
    norm_num
    ring
  rw [heq]
  exact I_mul_coordinate_form_pos z hz

end Complex

end TauCeti
