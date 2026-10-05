/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Enhancement
public import Mathlib.LinearAlgebra.Trace

/-!
# The weighted trace of the Jimbo braid representation

The weighted trace is `tr (ρ(b) * μ^{⊗n})`, where `ρ` is the Jimbo representation
and `μ` is Turaev's diagonal enhancement. It is invariant under braid conjugation
and satisfies the unnormalized HOMFLY skein relation. On the identity braid it is
the `n`-th power of the quantum dimension `∑ a, q ^ (N - 1 - 2 * a)`.

The coefficient formula makes the trace computable in the canonical word basis.
The two single-crossing values check both signs of the enhancement against the
one-strand value. The weighted trace itself still changes under stabilization;
the writhe normalization and the general stabilization laws are separate results.

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527-553 (weighted traces of enhanced Yang-Baxter operators).
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335-388 (the trace construction of HOMFLY).

The trace uses Mathlib's basis-independent `LinearMap.trace`; the representation
and enhancement are constructed in the companion modules.
-/

public section

open Finsupp
open scoped BigOperators

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {N n : ℕ}

/-- Turaev's weighted trace of a braid in the Jimbo representation with `N` colours.
No division by the quantum dimension or by `q - q⁻¹` is required. -/
noncomputable def jimboWeightedTrace (q : Rˣ) (b : BraidGroup n) : R :=
  LinearMap.trace R ((Fin n → Fin N) →₀ R)
    ((jimbo (Fin N) q b : Module.End R ((Fin n → Fin N) →₀ R)) * jimboEnhancement q)

/-- The defining equation of the weighted braid trace. -/
theorem jimboWeightedTrace_def (q : Rˣ) (b : BraidGroup n) :
    jimboWeightedTrace (N := N) q b =
      LinearMap.trace R ((Fin n → Fin N) →₀ R)
        ((jimbo (Fin N) q b : Module.End R ((Fin n → Fin N) →₀ R)) *
          jimboEnhancement q) := (rfl)

/-- The weighted trace is the sum of diagonal coefficients times their word weights. -/
theorem jimboWeightedTrace_eq_sum (q : Rˣ) (b : BraidGroup n) :
    jimboWeightedTrace (N := N) q b =
      ∑ w : Fin n → Fin N,
        (jimbo (Fin N) q b : Module.End R ((Fin n → Fin N) →₀ R)) (single w 1) w *
          ∏ i, jimboWeight q (w i) := by
  classical
  rw [jimboWeightedTrace_def, LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Module.End.mul_apply, Finsupp.coe_basisSingleOne, jimboEnhancement_single_one, map_smul]
  simp [mul_comm]

/-- The trace of the identity braid, whose closure is the `n`-component unlink. -/
@[simp]
theorem jimboWeightedTrace_one (q : Rˣ) :
    jimboWeightedTrace (N := N) q (1 : BraidGroup n) =
      (∑ a : Fin N, jimboWeight q a) ^ n := by
  classical
  rw [jimboWeightedTrace_eq_sum]
  simp only [map_one, Units.val_one, Module.End.one_apply, single_eq_same, one_mul]
  rw [← Fintype.prod_sum]
  simp

/-- The weighted trace has the cyclic property on products of braids. -/
theorem jimboWeightedTrace_mul_comm (q : Rˣ) (b c : BraidGroup n) :
    jimboWeightedTrace (N := N) q (b * c) = jimboWeightedTrace (N := N) q (c * b) := by
  simp only [jimboWeightedTrace_def, map_mul, Units.val_mul]
  rw [mul_assoc, (jimboEnhancement_commute (N := N) q c).eq.symm, ← mul_assoc,
    LinearMap.trace_mul_cycle]

/-- Conjugation, the first Markov move, preserves the weighted trace. -/
@[simp]
theorem jimboWeightedTrace_conj (q : Rˣ) (b c : BraidGroup n) :
    jimboWeightedTrace (N := N) q (c * b * c⁻¹) = jimboWeightedTrace (N := N) q b := by
  rw [jimboWeightedTrace_mul_comm q (c * b) c⁻¹]
  simp [← mul_assoc]

/-- Changing one crossing gives the unnormalized HOMFLY skein relation, in any braid context. -/
theorem jimboWeightedTrace_skein (q : Rˣ) (b c : BraidGroup n) (i : Fin (n - 1)) :
    jimboWeightedTrace (N := N) q (b * BraidGroup.sigma i * c) =
      jimboWeightedTrace (N := N) q (b * (BraidGroup.sigma i)⁻¹ * c) +
        ((q : R) - ↑(q⁻¹)) * jimboWeightedTrace (N := N) q (b * c) := by
  simp only [jimboWeightedTrace_def, map_mul, map_inv, Units.val_mul]
  rw [val_jimbo_sigma_eq_val_inv_add, mul_add, add_mul, add_mul, map_add]
  simp

/-- The positive crossing on two strands has trace `q ^ N` times the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_sigma_two (q : Rˣ) :
    jimboWeightedTrace (N := N) q (BraidGroup.sigma (0 : Fin (2 - 1))) =
      ↑(q ^ N) * ∑ a : Fin N, jimboWeight q a := by
  classical
  rw [jimboWeightedTrace_eq_sum, jimbo_sigma, jimboUnit_val]
  have hstrand : BraidGroup.strand (0 : Fin (2 - 1)) = 0 := by ext; simp
  have hsucc : BraidGroup.strandSucc (0 : Fin (2 - 1)) = 1 := by ext; simp
  rw [hstrand, hsucc, ← (finTwoArrowEquiv (Fin N)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, finTwoArrowEquiv_symm_apply,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = (∑ c : Fin N,
        (jimboGenerator q (0 : Fin 2) 1 (single ![a, c] 1)) ![a, c] *
          jimboWeight q c) * jimboWeight q a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by rw [sum_jimboGenerator_coeff_mul_weight, ite_eq_left rfl]

/-- The negative crossing on two strands has trace `q ^ (-N)` times the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_sigma_two_inv (q : Rˣ) :
    jimboWeightedTrace (N := N) q ((BraidGroup.sigma (0 : Fin (2 - 1)))⁻¹) =
      ↑((q⁻¹) ^ N) * ∑ a : Fin N, jimboWeight q a := by
  have h := jimboWeightedTrace_skein (N := N) q (1 : BraidGroup 2) 1 0
  simp only [one_mul, mul_one, jimboWeightedTrace_sigma_two, jimboWeightedTrace_one] at h
  have hs := jimboWeight_sum (N := N) q
  linear_combination -h - (∑ a : Fin N, jimboWeight q a) * hs

/-- At `q = 1`, the trace counts colourings fixed by the underlying strand permutation. -/
@[simp]
theorem jimboWeightedTrace_one_parameter (b : BraidGroup n) :
    jimboWeightedTrace (N := N) (1 : Rˣ) b =
      ((Finset.univ.filter fun w : Fin n → Fin N =>
        w ∘ ⇑(BraidGroup.permHom n b)⁻¹ = w).card : R) := by
  classical
  rw [jimboWeightedTrace_eq_sum]
  simp [single_apply, Finset.sum_boole]

end TauCeti.KnotTheory
