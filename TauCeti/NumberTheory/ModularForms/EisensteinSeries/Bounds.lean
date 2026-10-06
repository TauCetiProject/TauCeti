/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Subspace
public import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
public import Mathlib.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Fourier coefficient bounds on Eisenstein subspaces

For weight `k ≥ 3`, the positive Fourier coefficients of each normalized raised character
Eisenstein series are bounded by `n^(k-1) ∑' d, d^(-(k-1))`. The constant is independent
of the characters and the raising parameter. Finite linear combinations consequently have
coefficients `O(n^(k-1))`, and their coefficient L-series have abscissa of absolute
convergence at most `k`.

The estimate applies to the entire fixed-nebentypus Eisenstein subspace, defined as the span
of the normalized raised character series. Membership means being a finite linear combination
of these generators and does not require a decomposition of the ambient modular-form space.
Extending the abscissa bound to arbitrary modular forms requires a cusp–Eisenstein decomposition
and the cusp-form coefficient bound. We do not assert this power bound in weight two, where
the untwisted divisor sum is not `O(n)`.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.norm_qExpansion_form_coeff_le`: a uniform bound for
  the generators at positive indices.
* `TauCeti.isBigO_qExpansion_coeff_of_mem_eisensteinSubspace`: the coefficient bound on
  the whole span.
* `TauCeti.abscissaOfAbsConv_qExpansion_coeff_le_of_mem_eisensteinSubspace`: absolute
  convergence of the coefficient L-series for `Re s > k`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §4.5 and Proposition 5.9.1.
-/

public noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped MatrixGroups

namespace TauCeti

namespace EisensteinSeries.CharIndex

variable {N k : ℕ} [NeZero N] (a : CharIndex N k)

/-- A normalized raised character Eisenstein series has positive Fourier coefficients
bounded by `n^(k-1)` times the reciprocal-power series, uniformly in its indexing data. -/
theorem norm_qExpansion_form_coeff_le (hk : 3 ≤ (k : ℤ)) {n : ℕ} (hn : n ≠ 0) :
    ‖(qExpansion 1 (a.form hk)).coeff n‖ ≤
      (n : ℝ) ^ (k - 1) * ∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹ := by
  have he : 1 < k - 1 := by omega
  rw [a.form_def,
    qExpansion_normalizedCharEisensteinSeriesMFRaise_coeff
      a.psi a.phi hk a.level_dvd a.parity a.phi_primitive hn]
  split_ifs
  · calc
      ‖DirichletCharacter.twistedDivisorSum (k - 1) a.psi a.phi (n / a.t)‖ ≤
          ∑ d ∈ (n / a.t).divisors, (d : ℝ) ^ (k - 1) :=
        norm_twistedDivisorSum_le _ _ _ _
      _ ≤ ((n / a.t : ℕ) : ℝ) ^ (k - 1) * ∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹ :=
        sum_divisors_pow_le _ he _
      _ ≤ (n : ℝ) ^ (k - 1) * ∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹ := by
        gcongr
        exact_mod_cast Nat.div_le_self n a.t
  · simpa using mul_nonneg (by positivity : 0 ≤ (n : ℝ) ^ (k - 1))
      (tsum_nonneg fun d ↦ by positivity : 0 ≤ ∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹)

/-- The coefficients of a normalized raised character Eisenstein series are `O(n^(k-1))`.
The constant coefficient does not affect the estimate at infinity. -/
theorem isBigO_qExpansion_form_coeff (hk : 3 ≤ (k : ℤ)) :
    (fun n ↦ (qExpansion 1 (a.form hk)).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (k - 1)) := by
  refine isBigO_iff.mpr ⟨∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹, ?_⟩
  filter_upwards [eventually_ne_atTop 0] with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ (k - 1)),
    mul_comm] using a.norm_qExpansion_form_coeff_le hk hn

end EisensteinSeries.CharIndex

variable {N k : ℕ} [NeZero N] {chi : (ZMod N)ˣ →* ℂˣ}

/-- Every form in the fixed-nebentypus Eisenstein subspace of weight `k ≥ 3` has Fourier
coefficients `O(n^(k-1))`. -/
theorem isBigO_qExpansion_coeff_of_mem_eisensteinSubspace (hk : 3 ≤ (k : ℤ))
    {f : modFormCharSpace (k : ℤ) chi} (hf : f ∈ eisensteinSubspace chi hk) :
    (fun n ↦ (qExpansion 1 (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ))).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (k - 1)) := by
  let Q : modFormCharSpace (k : ℤ) chi →ₗ[ℂ] PowerSeries ℂ :=
    (ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map N) (k : ℤ)).comp
      (modFormCharSpace (k : ℤ) chi).subtype
  have hQ (g : modFormCharSpace (k : ℤ) chi) :
      Q g = qExpansion 1 (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ)) := by
    simp [Q, ModularForm.qExpansionLinearMap_apply]
  rw [eisensteinSubspace_def] at hf
  suffices (fun n ↦ (Q f).coeff n) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (k - 1)) by
    simpa only [hQ] using this
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨⟨a, ha⟩, rfl⟩ := hg
      simpa only [hQ, EisensteinSeries.CharIndex.coe_inCharSpace]
        using a.isBigO_qExpansion_form_coeff hk
  | zero => simpa using (isBigO_zero (fun n : ℕ ↦ (n : ℝ) ^ (k - 1)) atTop)
  | add g h _ _ hg hh => simpa using hg.add hh
  | smul c g _ hg => simpa using hg.const_mul_left c

/-- The coefficient L-series of an Eisenstein form of weight `k ≥ 3` has abscissa of
absolute convergence at most `k`. -/
theorem abscissaOfAbsConv_qExpansion_coeff_le_of_mem_eisensteinSubspace
    (hk : 3 ≤ (k : ℤ)) {f : modFormCharSpace (k : ℤ) chi}
    (hf : f ∈ eisensteinSubspace chi hk) :
    LSeries.abscissaOfAbsConv
      (fun n ↦ (qExpansion 1 (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ))).coeff n) ≤
        (k : EReal) := by
  have hO := isBigO_qExpansion_coeff_of_mem_eisensteinSubspace hk hf
  have hO' :
      (fun n ↦
        (qExpansion 1 (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ))).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ((k - 1 : ℕ) : ℝ)) := by
    simpa only [Real.rpow_natCast] using hO
  have h := LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hO'
  have hk1 : 1 ≤ k := by omega
  have hweight : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hk1
  have heq : (((k - 1 : ℕ) : ℝ) : EReal) + 1 = (k : EReal) := by
    calc
      _ = ((((k - 1 : ℕ) : ℝ) + 1 : ℝ) : EReal) := (EReal.coe_add _ 1).symm
      _ = ((k : ℝ) : EReal) := congrArg (fun x : ℝ ↦ (x : EReal)) hweight
      _ = (k : EReal) := EReal.coe_natCast
  exact h.trans_eq heq

end TauCeti
