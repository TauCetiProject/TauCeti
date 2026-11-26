/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.Analysis.Asymptotics.Expansion.PowerSeries
public import TauCeti.RingTheory.PowerSeries.ComplexPower

import Mathlib.Analysis.Analytic.Binomial
import TauCeti.Analysis.Asymptotics.Expansion.Poincare
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Basic

/-!
# Principal complex powers and logarithms of asymptotic power series

This file establishes the closure of complex asymptotic power series in a small variable `w → 0`
under principal complex logarithms and principal complex powers when the constant coefficient lies
in `Complex.slitPlane` (NIST DLMF §2.1(iii)).

## Main results

* `Asymptotics.hasAsymptoticExpansion_pow_log`: principal complex logarithm `Complex.log ∘ f`
  for `constantCoeff P ∈ Complex.slitPlane`.
* `Asymptotics.hasAsymptoticExpansion_pow_cpow`: principal complex power `fun x => f x ^ r`
  using `PowerSeries.formalCpow (Complex.log (constantCoeff P)) r P`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.1(iii),
  <https://dlmf.nist.gov/2.1#iii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 1, §8.
-/

public section

open Filter Topology Finset PowerSeries

namespace Asymptotics

private lemma hasAsymptoticExpansion_pow_unit_sub_one {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {P : ℂ⟦X⟧} {f : α → ℂ} {ℓ : ℂ}
    (hP : constantCoeff P = Complex.exp ℓ)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (C (Complex.exp (-ℓ)) * P - 1))
      (fun x => Complex.exp (-ℓ) * f x - 1) ∧
    Tendsto (fun x => Complex.exp (-ℓ) * f x - 1) l (𝓝 0) := by
  have hu_exp : HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (C (Complex.exp (-ℓ)) * P - 1))
      (fun x => Complex.exp (-ℓ) * f x - 1) := by
    have hsub := hasAsymptoticExpansion_pow_sub
      (hasAsymptoticExpansion_pow_const_mul (Complex.exp (-ℓ)) hf)
      (hasAsymptoticExpansion_pow_const (l := l) (w := w) (1 : ℂ))
    exact (hsub.congr_coeff fun n => by simp only [map_one]).congr'
      (Eventually.of_forall fun _ => rfl)
  refine ⟨hu_exp, ?_⟩
  have hU0 : constantCoeff (C (Complex.exp (-ℓ)) * P - 1) = 0 :=
    constantCoeff_exp_neg_mul_sub_one hP
  simpa only [hU0] using hu_exp.tendsto_constantCoeff hw

/-- Principal logarithm of a complex asymptotic power series whose constant coefficient lies in
`Complex.slitPlane` (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_log {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {P : ℂ⟦X⟧} {f : α → ℂ}
    (hP : constantCoeff P ∈ Complex.slitPlane)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (C (Complex.log (constantCoeff P)) +
        PowerSeries.logOf (C (Complex.exp (-Complex.log (constantCoeff P))) * P)))
      fun x => Complex.log (f x) := by
  set p₀ : ℂ := constantCoeff P
  set ℓ : ℂ := Complex.log p₀
  have hp₀_ne : p₀ ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hP).2
  have hexpℓ : Complex.exp ℓ = p₀ := Complex.exp_log hp₀_ne
  obtain ⟨hu_exp, hu0⟩ := hasAsymptoticExpansion_pow_unit_sub_one hw hexpℓ.symm hf
  have hU0 : constantCoeff (C (Complex.exp (-ℓ)) * P - 1) = 0 :=
    constantCoeff_exp_neg_mul_sub_one hexpℓ.symm
  have hlog_at0 : HasAsymptoticExpansion (𝓝 (0 : ℂ)) (fun n z => z ^ n)
      (fun n => coeff n (PowerSeries.log ℂ)) (fun z => Complex.log (1 + z)) := by
    have hfp := hasFPowerSeriesAt_clog_one_add.hasAsymptoticExpansion
    refine (hfp.congr_scale fun n => Eventually.of_forall fun z => by
      dsimp only; rw [sub_zero]).congr_coeff fun n => ?_
    rw [FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_log]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, map_div₀, map_pow, map_neg, map_one, map_natCast]
      rw [pow_succ, pow_succ]
      ring
  have hcomp := hasAsymptoticExpansion_pow_subst hw hu0 hU0 hlog_at0 hu_exp
  have hadd := hasAsymptoticExpansion_pow_add (hasAsymptoticExpansion_pow_const (l := l) (w := w) ℓ)
    hcomp
  refine (hadd.congr_coeff fun n => by rw [PowerSeries.logOf_eq]).congr' ?_
  filter_upwards [Complex.eventually_log_mul_one_add hP hu0] with x hx
  have hfx : f x = p₀ * (1 + (Complex.exp (-ℓ) * f x - 1)) := by
    rw [Complex.exp_neg, hexpℓ]
    field_simp [hp₀_ne]
    ring
  dsimp only [Pi.add_apply]
  conv_rhs => rw [hfx, hx]

/-- Principal complex power of a complex asymptotic power series whose constant coefficient lies in
`Complex.slitPlane` (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_cpow {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {P : ℂ⟦X⟧} {f : α → ℂ}
    (hP : constantCoeff P ∈ Complex.slitPlane)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) (r : ℂ) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (formalCpow (Complex.log (constantCoeff P)) r P))
      fun x => f x ^ r := by
  set p₀ : ℂ := constantCoeff P
  set ℓ : ℂ := Complex.log p₀
  have hp₀_ne : p₀ ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hP).2
  have hexpℓ : Complex.exp ℓ = p₀ := Complex.exp_log hp₀_ne
  obtain ⟨hu_exp, hu0⟩ := hasAsymptoticExpansion_pow_unit_sub_one hw hexpℓ.symm hf
  have hU0 : constantCoeff (C (Complex.exp (-ℓ)) * P - 1) = 0 :=
    constantCoeff_exp_neg_mul_sub_one hexpℓ.symm
  have hbin_at0 : HasAsymptoticExpansion (𝓝 (0 : ℂ)) (fun n z => z ^ n)
      (fun n => coeff n (PowerSeries.binomialSeries ℂ r)) (fun z => (1 + z) ^ r) := by
    have hfp := (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := r)).hasAsymptoticExpansion
    refine (hfp.congr_scale fun n => Eventually.of_forall fun z => by
      dsimp only; rw [sub_zero]).congr_coeff fun n => ?_
    simp [_root_.binomialSeries, PowerSeries.binomialSeries_coeff]
  have hcomp := hasAsymptoticExpansion_pow_subst hw hu0 hU0 hbin_at0 hu_exp
  have hmul := hasAsymptoticExpansion_pow_const_mul (Complex.exp (r * ℓ)) hcomp
  refine (hmul.congr_coeff fun n => by rw [formalCpow_def, binomialPow_def]).congr' ?_
  have h1u : Tendsto (fun x => 1 + (Complex.exp (-ℓ) * f x - 1)) l (𝓝 (1 : ℂ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hu0
  filter_upwards [Complex.eventually_log_mul_one_add hP hu0, h1u.eventually_ne one_ne_zero]
    with x hx h1ne
  have hfx : f x = p₀ * (1 + (Complex.exp (-ℓ) * f x - 1)) := by
    rw [Complex.exp_neg, hexpℓ]
    field_simp [hp₀_ne]
    ring
  conv_rhs => rw [hfx, Complex.cpow_def_of_ne_zero (mul_ne_zero hp₀_ne h1ne), hx]
  rw [Complex.cpow_def_of_ne_zero h1ne, add_mul, Complex.exp_add, mul_comm ℓ r]

end Asymptotics
