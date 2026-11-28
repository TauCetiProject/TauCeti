/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Expansion.PowerSeries
public import TauCeti.RingTheory.PowerSeries.ComplexPower

import TauCeti.Analysis.Analytic.Binomial
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
  using `P.formalCpow (Complex.log (constantCoeff P)) r`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.1(iii),
  <https://dlmf.nist.gov/2.1#iii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 1, §8.
-/

public section

open Filter Topology Finset PowerSeries

namespace Asymptotics

private lemma constantCoeff_C_cexp_neg_log_mul_sub_one {P : ℂ⟦X⟧}
    (hP : constantCoeff P ∈ Complex.slitPlane) :
    constantCoeff (C (Complex.exp (-Complex.log (constantCoeff P))) * P - 1) = 0 := by
  rw [map_sub, map_one,
    constantCoeff_C_cexp_neg_mul (Complex.exp_log (Complex.mem_slitPlane_iff_arg.mp hP).2).symm,
    sub_self]

private lemma hasAsymptoticExpansion_pow_unit_sub_one {α : Type*} {l : Filter α} {w : α → ℂ}
    {P : ℂ⟦X⟧} {f : α → ℂ}
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (C (Complex.exp (-Complex.log (constantCoeff P))) * P - 1))
      (fun x => Complex.exp (-Complex.log (constantCoeff P)) * f x - 1) :=
  ((hasAsymptoticExpansion_pow_sub
    (hasAsymptoticExpansion_pow_const_mul (Complex.exp (-Complex.log (constantCoeff P))) hf)
    (hasAsymptoticExpansion_pow_const (l := l) (w := w) (1 : ℂ))).congr_coeff
    fun n => by simp only [map_one]).congr'
    (Eventually.of_forall fun _ => by simp only [Pi.sub_apply])

private lemma tendsto_C_cexp_neg_log_mul_sub_one {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {P : ℂ⟦X⟧} {f : α → ℂ}
    (hP : constantCoeff P ∈ Complex.slitPlane)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) :
    Tendsto (fun x => Complex.exp (-Complex.log (constantCoeff P)) * f x - 1) l (𝓝 0) := by
  simpa only [constantCoeff_C_cexp_neg_log_mul_sub_one hP] using
    (hasAsymptoticExpansion_pow_unit_sub_one hf).tendsto_constantCoeff hw

private lemma eq_mul_one_add_cexp_neg_log_mul_sub_one {p₀ : ℂ} (hp₀ : p₀ ≠ 0) (y : ℂ) :
    y = p₀ * (1 + (Complex.exp (-Complex.log p₀) * y - 1)) := by
  rw [Complex.exp_neg, Complex.exp_log hp₀]
  field_simp [hp₀]
  ring

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
  have hp₀_ne : constantCoeff P ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hP).2
  have hU0 := constantCoeff_C_cexp_neg_log_mul_sub_one hP
  have hu_exp := hasAsymptoticExpansion_pow_unit_sub_one hf
  have hu0 := tendsto_C_cexp_neg_log_mul_sub_one hw hP hf
  have hlog_at0 : HasAsymptoticExpansion (𝓝 (0 : ℂ)) (fun n z => z ^ n)
      (fun n => coeff n (PowerSeries.log ℂ)) (fun z => Complex.log (1 + z)) := by
    refine hasFPowerSeriesAt_clog_one_add.hasAsymptoticExpansion_zero.congr_coeff fun n => ?_
    rw [FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_log]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, map_div₀, map_pow, map_neg, map_one, map_natCast]
      rw [pow_succ, pow_succ]
      ring
  have hcomp := hasAsymptoticExpansion_pow_subst hw hu0 hU0 hlog_at0 hu_exp
  have hadd := hasAsymptoticExpansion_pow_add
    (hasAsymptoticExpansion_pow_const (l := l) (w := w) (Complex.log (constantCoeff P))) hcomp
  refine (hadd.congr_coeff fun n => by rw [PowerSeries.logOf_eq]).congr' ?_
  filter_upwards [Complex.eventually_log_mul_one_add hP hu0] with x hx
  dsimp only [Pi.add_apply]
  conv_rhs => rw [eq_mul_one_add_cexp_neg_log_mul_sub_one hp₀_ne (f x), hx]

/-- Principal complex power of a complex asymptotic power series whose constant coefficient lies in
`Complex.slitPlane` (DLMF §2.1(iii)). -/
theorem hasAsymptoticExpansion_pow_cpow {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) {P : ℂ⟦X⟧} {f : α → ℂ}
    (hP : constantCoeff P ∈ Complex.slitPlane)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f) (r : ℂ) :
    HasAsymptoticExpansion l (fun n x => w x ^ n)
      (fun n => coeff n (P.formalCpow (Complex.log (constantCoeff P)) r))
      fun x => f x ^ r := by
  set p₀ : ℂ := constantCoeff P
  set ℓ : ℂ := Complex.log p₀
  have hp₀_ne : p₀ ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hP).2
  have hU0 := constantCoeff_C_cexp_neg_log_mul_sub_one hP
  have hu_exp := hasAsymptoticExpansion_pow_unit_sub_one hf
  have hu0 := tendsto_C_cexp_neg_log_mul_sub_one hw hP hf
  have hbin_at0 : HasAsymptoticExpansion (𝓝 (0 : ℂ)) (fun n z => z ^ n)
      (fun n => coeff n (PowerSeries.binomialSeries ℂ r)) (fun z => (1 + z) ^ r) :=
    .of_isBigO fun N => (TauCeti.isBigO_one_add_cpow_sub_sum r N).congr_left fun z => by
      simp [PowerSeries.binomialSeries_coeff, mul_comm]
  have hcomp := hasAsymptoticExpansion_pow_subst hw hu0 hU0 hbin_at0 hu_exp
  have hmul := hasAsymptoticExpansion_pow_const_mul (Complex.exp (r * ℓ)) hcomp
  refine (hmul.congr_coeff fun n => by rw [formalCpow_def, binomialPow_def]).congr' ?_
  filter_upwards [Complex.eventually_log_mul_one_add hP hu0,
    (hf.tendsto_constantCoeff hw).eventually_ne hp₀_ne] with x hx hfne
  have hfx := eq_mul_one_add_cexp_neg_log_mul_sub_one hp₀_ne (f x)
  have h1ne : 1 + (Complex.exp (-ℓ) * f x - 1) ≠ 0 :=
    right_ne_zero_of_mul (hfx ▸ hfne)
  conv_rhs => rw [hfx, Complex.cpow_def_of_ne_zero (hfx ▸ hfne), hx]
  rw [Complex.cpow_def_of_ne_zero h1ne, add_mul, Complex.exp_add, mul_comm ℓ r]

end Asymptotics
