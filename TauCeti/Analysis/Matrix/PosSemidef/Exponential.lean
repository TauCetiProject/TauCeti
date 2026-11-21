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
* `TauCeti.posSemidef_cexp_sum_sub`, `TauCeti.posSemidef_cexp_of_hasSum_sub`,
  `TauCeti.posSemidef_cexp_tsum_sub`: the entrywise exponential of a finite sum or pointwise
  convergent series of positive-semidefinite complex kernels shifted by real constants is positive
  semidefinite.

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

namespace TauCeti

open Filter

/-- The entrywise exponential of a finite sum of positive-semidefinite complex kernels shifted by
real constants `c i` is positive semidefinite. -/
theorem posSemidef_cexp_sum_sub {ι n : Type*} {s : Finset ι} {K : ι → Matrix n n ℂ}
    (hK : ∀ i ∈ s, (K i).PosSemidef) (c : ι → ℝ) :
    (Matrix.of fun a b : n ↦ Complex.exp (∑ i ∈ s, (K i a b - (c i : ℂ)))).PosSemidef := by
  have hS : (∑ i ∈ s, K i).PosSemidef := Matrix.posSemidef_sum s hK
  have hc : (0 : ℂ) ≤ (Real.exp (-∑ i ∈ s, c i) : ℂ) := by
    exact_mod_cast (Real.exp_pos _).le
  refine (congrArg Matrix.PosSemidef ?_).mp (hS.map_cexp.smul hc)
  ext a b
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.of_apply,
    smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_sum, ← Complex.exp_add]
  congr 1
  rw [Finset.sum_sub_distrib, add_comm, sub_eq_add_neg]

/-- The entrywise exponential of the pointwise limit of a series of positive-semidefinite complex
kernels shifted by real constants `c i` is positive semidefinite, for any nontrivial summation
filter `L`. -/
theorem posSemidef_cexp_of_hasSum_sub {ι n : Type*} {L : SummationFilter ι} [L.NeBot]
    {K : ι → Matrix n n ℂ} (hK : ∀ i, (K i).PosSemidef) {c : ι → ℝ} {S : Matrix n n ℂ}
    (hS : ∀ a b, HasSum (fun i ↦ K i a b - (c i : ℂ)) (S a b) L) :
    (S.map Complex.exp).PosSemidef :=
  isClosed_setOfPred_posSemidef.mem_of_tendsto
    (f := fun s : Finset ι ↦
      Matrix.of fun a b : n ↦ Complex.exp (∑ i ∈ s, (K i a b - (c i : ℂ))))
    (tendsto_pi_nhds.mpr fun a ↦ tendsto_pi_nhds.mpr fun b ↦
      Complex.continuous_exp.continuousAt.tendsto.comp (hS a b))
    (Eventually.of_forall fun _ ↦ posSemidef_cexp_sum_sub (fun i _ ↦ hK i) c)

/-- The entrywise exponential of a pointwise summable series of positive-semidefinite complex
kernels shifted by real constants `c i` is positive semidefinite. -/
theorem posSemidef_cexp_tsum_sub {ι n : Type*} {K : ι → Matrix n n ℂ}
    (hK : ∀ i, (K i).PosSemidef) {c : ι → ℝ}
    (hsumm : ∀ a b, Summable fun i ↦ K i a b - (c i : ℂ)) :
    (Matrix.of fun a b : n ↦ Complex.exp (∑' i, (K i a b - (c i : ℂ)))).PosSemidef :=
  posSemidef_cexp_of_hasSum_sub hK fun a b ↦ (hsumm a b).hasSum

end TauCeti
