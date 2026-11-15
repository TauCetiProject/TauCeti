/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Entrywise exponentials of positive-semidefinite matrices

A matrix, read as a kernel on its (possibly infinite) index type, stays positive semidefinite
after applying the complex exponential to every entry. The entrywise exponential is the sum of
the Schur powers `K ^ k / k!`, each of which is positive semidefinite by the Schur product
theorem. This is the analytic input to Schoenberg's theorem on conditionally negative
semidefinite kernels.

## Main declarations

* `Matrix.PosSemidef.map_cexp`: the entrywise exponential of a positive-semidefinite kernel is
  positive semidefinite.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3, §1.
-/

public section

open scoped ComplexOrder Nat

namespace Matrix

variable {n : Type*}

/-- The entrywise exponential of a positive-semidefinite kernel is positive semidefinite: it is
the sum of the Schur powers `K ^ k / k!`. -/
theorem PosSemidef.map_cexp {K : Matrix n n ℂ} (hK : K.PosSemidef) :
    (K.map Complex.exp).PosSemidef := by
  have hsum : HasSum (fun k : ℕ ↦ (k ! : ℂ)⁻¹ • (of fun a b ↦ K a b ^ k)) (K.map Complex.exp) := by
    refine Pi.hasSum.mpr fun a ↦ Pi.hasSum.mpr fun b ↦ ?_
    simpa [Complex.exp_eq_exp_ℂ, div_eq_inv_mul] using
      NormedSpace.expSeries_div_hasSum_exp (K a b)
  refine PosSemidef.of_hasSum hsum fun k ↦ PosSemidef.smul ?_ (by positivity)
  exact hK.hadamard_pow k

end Matrix
