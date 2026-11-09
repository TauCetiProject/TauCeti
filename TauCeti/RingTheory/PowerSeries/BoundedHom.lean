/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.Topology.Algebra.InfiniteSum.IntegralCoefficients
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bounded homomorphisms out of power series

A uniformly norm-bounded ring homomorphism from a power-series ring that sends the variable
inside the open unit ball is determined by its values on constants and the variable.
Consequently evaluation of integral series commutes with formal substitution at a series
with zero constant term. This permits evaluating integral compositional inverses in complete
non-archimedean rings, without imposing a linear topology on the target ring.
-/

public section

open PowerSeries Filter

namespace RingHom

/-- Uniformly bounded homomorphisms out of a power-series ring agree if they agree on constants
and send the variable to the same element of norm less than one. -/
theorem ext_powerSeries_of_bounded {R K : Type*} [Semiring R] [NormedRing K]
    (φ ψ : R⟦X⟧ →+* K) (hφ : ∃ M : ℝ, ∀ f, ‖φ f‖ ≤ M)
    (hψ : ∃ M : ℝ, ∀ f, ‖ψ f‖ ≤ M) (hC : ∀ r, φ (C r) = ψ (C r))
    (hX : φ X = ψ X) (hq : ‖φ X‖ < 1) : φ = ψ := by
  obtain ⟨M, hM⟩ := hφ
  obtain ⟨N, hN⟩ := hψ
  have hp (p : Polynomial R) : φ (p : R⟦X⟧) = ψ (p : R⟦X⟧) := by
    have h := Polynomial.ringHom_ext (f := φ.comp Polynomial.coeToPowerSeries.ringHom)
      (g := ψ.comp Polynomial.coeToPowerSeries.ringHom)
      (fun r ↦ by simpa using hC r) (by simpa using hX)
    exact RingHom.congr_fun h p
  ext f
  have hbound (n : ℕ) : ‖φ f - ψ f‖ ≤ ‖φ X‖ ^ (n + 1) * (M + N) := by
    conv_lhs => rw [f.eq_X_pow_mul_shift_add_trunc (n + 1)]
    simp only [map_add, map_mul, map_pow, hp, ← hX]
    calc
      _ = ‖φ X ^ (n + 1) * (φ (PowerSeries.mk fun i ↦ coeff (i + (n + 1)) f) -
          ψ (PowerSeries.mk fun i ↦ coeff (i + (n + 1)) f))‖ := by
        rw [add_sub_add_right_eq_sub, mul_sub]
      _ ≤ ‖φ X‖ ^ (n + 1) * (M + N) := by
        exact (norm_mul_le _ _).trans (mul_le_mul
          (norm_pow_le' _ (Nat.succ_pos n)) ((norm_sub_le _ _).trans (add_le_add (hM _) (hN _)))
          (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
  have hz := squeeze_zero (fun _ ↦ norm_nonneg (φ f - ψ f)) hbound
    (by simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq).comp
        (tendsto_add_atTop_nat 1)).mul_const (M + N))
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hz))

end RingHom

namespace TauCeti

variable {K : Type*} [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K]

/-- Evaluation of integral series commutes with substitution at a series with zero constant
term. Both evaluation parameters lie in the open unit ball. -/
theorem evalIntSeries_subst (q : K) (hq : ‖q‖ < 1) (f g : ℤ⟦X⟧)
    (hg : constantCoeff g = 0) :
    evalIntSeries q hq (f.subst g) =
      evalIntSeries (evalIntSeries q hq g)
        ((norm_evalIntSeries_le_of_constantCoeff_eq_zero q hq hg).trans_lt hq) f := by
  have hs : HasSubst g := .of_constantCoeff_zero hg
  have h := RingHom.ext_powerSeries_of_bounded
    ((evalIntSeries q hq).comp (substAlgHom hs).toRingHom)
    (evalIntSeries (evalIntSeries q hq g)
      ((norm_evalIntSeries_le_of_constantCoeff_eq_zero q hq hg).trans_lt hq))
    ⟨‖(1 : K)‖, fun _ ↦ norm_evalIntSeries_le_norm_one q hq _⟩
    ⟨‖(1 : K)‖, fun _ ↦ norm_evalIntSeries_le_norm_one _ _ _⟩
    (fun r ↦ by simp)
    (by simp [substAlgHom_X])
    (by simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      substAlgHom_X] using
      (norm_evalIntSeries_le_of_constantCoeff_eq_zero q hq hg).trans_lt hq)
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    coe_substAlgHom] using RingHom.congr_fun h f

end TauCeti
