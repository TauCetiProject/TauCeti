/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Deleting finitely many Euler factors

Restricting Euler-product data away from a finite set `S` of primes, keeping only the
coefficients of the ideals prime to `S`, replaces the local Euler factors at `S` by `1` and leaves
the others untouched. On the half-plane of absolute convergence the two `L`-series therefore
differ by the finitely many deleted factors; for a completely multiplicative weight `χ` the
restriction `χ.restrict S` divides the `L`-series by `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))⁻¹`.

For the trivial weight the restriction is `ofBadPrimes S`, the indicator of the ideals prime to
`S`, and its `L`-series is the Dedekind zeta function with the Euler factors at `S` removed:

`L_S(s) = ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`  for `Re s > 1`.

The correction factor does not vanish on `Re s > 0`, because
`|N(𝔭) ^ s| = N(𝔭) ^ (Re s) > 1` there. Consequently `L_S` has the same kind of singularity at
`s = 1` as `ζ_K`: its residue from the right is that of `ζ_K` multiplied by the nonzero number
`∏ 𝔭 ∈ S, (1 - N(𝔭)⁻¹)`, and its logarithmic derivative differs from that of `ζ_K` by the finite
sum `∑ 𝔭 ∈ S, log N(𝔭) / (N(𝔭) ^ s - 1)`, which is holomorphic on `Re s > 0` and in particular
across the line `Re s = 1`. This is the form in which Dirichlet series whose Euler products omit
the ramified primes, such as the series of a Galois character, are compared with `ζ_K`.

## Main results

* `TauCeti.EulerProductData.eulerFactor_restrictAway_of_mem`,
  `TauCeti.EulerProductData.eulerFactor_restrictAway_of_notMem`: restricting away from `S`
  replaces the local factors at `S` by `1` and keeps the others.
* `TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor`: multiplying the `L`-series
  of the restriction by the deleted local factors recovers the original `L`-series.
* `TauCeti.MultiplicativeIdealWeight.LSeries_restrict`: the same for a completely multiplicative
  weight, with the deleted factors in closed form.
* `TauCeti.LSeries_ofBadPrimes`: the `L`-series of the indicator of the ideals prime to `S` is
  `ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))` on `Re s > 1`.
* `TauCeti.prod_one_sub_absNorm_cpow_neg_ne_zero`: the correction factor has no zero on
  `Re s > 0`.
* `TauCeti.tendsto_sub_one_mul_LSeries_ofBadPrimes`: the residue at `s = 1` from the right.
* `TauCeti.logDeriv_LSeries_ofBadPrimes`: the logarithmic derivative on `Re s > 1`, and
  `TauCeti.differentiableOn_sum_log_absNorm_div_cpow_sub_one`: the correction term in it is
  holomorphic on `Re s > 0`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace TauCeti

open Filter
open scoped nonZeroDivisors NumberField Topology
open IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

variable (D : EulerProductData K) {s : ℂ}

/-- Restricting away from a set of primes preserves absolute convergence of the ideal-indexed
Dirichlet series, since it only replaces some terms by `0`. -/
theorem summable_idealTerm_restrictAway (S : Set (HeightOneSpectrum (𝓞 K)))
    (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    Summable (idealTerm K (D.restrictAway S).toIdealArithmeticFunction s) := by
  classical
  refine hs.norm.of_norm_bounded fun I ↦ ?_
  rw [norm_idealTerm, norm_idealTerm]
  gcongr
  simp only [restrictAway_apply]
  split_ifs <;> simp

/-- Restricting away from `S` replaces the local Euler factor at a prime of `S` by `1`. -/
theorem eulerFactor_restrictAway_of_mem {S : Set (HeightOneSpectrum (𝓞 K))}
    {P : HeightOneSpectrum (𝓞 K)} (hP : P ∈ S) (s : ℂ) :
    (D.restrictAway S).eulerFactor P s = 1 := by
  classical
  rw [eulerFactor_eq_tsum, tsum_eq_single 0 fun e he ↦ ?_]
  · have h0 : P.primeIdealPow 0 = 1 := Subtype.ext (by simp)
    simp [idealTerm_def, h0, Ideal.one_eq_top, Ideal.isPrimeTo_top, D.isMultiplicative.map_one]
  · have hnot : ¬ Ideal.IsPrimeTo (P.asIdeal ^ e) S := by
      rw [Ideal.isPrimeTo_pow_iff he, Ideal.isPrimeTo_asIdeal_iff]
      exact not_not_intro hP
    simp [idealTerm_def, hnot]

/-- Restricting away from `S` leaves the local Euler factor at a prime outside `S` unchanged. -/
theorem eulerFactor_restrictAway_of_notMem {S : Set (HeightOneSpectrum (𝓞 K))}
    {P : HeightOneSpectrum (𝓞 K)} (hP : P ∉ S) (s : ℂ) :
    (D.restrictAway S).eulerFactor P s = D.eulerFactor P s := by
  classical
  rw [eulerFactor_eq_tsum, eulerFactor_eq_tsum]
  refine tsum_congr fun e ↦ ?_
  have hprime : Ideal.IsPrimeTo (P.asIdeal ^ e) S := (Ideal.isPrimeTo_asIdeal_iff.mpr hP).pow e
  simp [idealTerm_def, hprime]

/-- **Deleting finitely many Euler factors.** Where the ideal-indexed Dirichlet series of `D`
converges absolutely, restricting `D` away from a finite set `S` of primes divides its `L`-series
by the local Euler factors at `S`: multiplying them back recovers the `L`-series of `D`. -/
theorem LSeries_restrictAway_mul_prod_eulerFactor (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : Summable (idealTerm K D.toIdealArithmeticFunction s)) :
    LSeries (normCoeff K (D.restrictAway S).toIdealArithmeticFunction) s *
        ∏ P ∈ S, D.eulerFactor P s =
      LSeries (normCoeff K D.toIdealArithmeticFunction) s := by
  classical
  -- The Euler factors of the restriction are those of `D` off `S` and `1` on `S`, so multiplying
  -- them by the finitely many factors of `D` at `S` recovers the Euler product of `D`.
  have hS : HasProd (fun P ↦ if P ∈ S then D.eulerFactor P s else 1)
      (∏ P ∈ S, D.eulerFactor P s) := by
    have h := hasProd_prod_of_ne_finset_one (s := S) (L := SummationFilter.unconditional _)
      (f := fun P ↦ if P ∈ S then D.eulerFactor P s else 1) fun P hP ↦ by simp [hP]
    rwa [Finset.prod_ite_mem, Finset.inter_self] at h
  have hfun : ∀ P, D.eulerFactor P s =
      (D.restrictAway S).eulerFactor P s * if P ∈ S then D.eulerFactor P s else 1 := fun P ↦ by
    by_cases hP : P ∈ S
    · simp [hP, D.eulerFactor_restrictAway_of_mem (Finset.mem_coe.mpr hP)]
    · simp [hP, D.eulerFactor_restrictAway_of_notMem (mt Finset.mem_coe.mp hP)]
  exact ((D.hasProd_eulerFactor hs).unique (((D.restrictAway S).hasProd_eulerFactor
    (D.summable_idealTerm_restrictAway S hs)).mul hS |>.congr_fun hfun)).symm

end EulerProductData

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- **Deleting finitely many Euler factors of a completely multiplicative weight.** Where the
ideal-indexed Dirichlet series of `χ` converges absolutely, restricting `χ` away from a finite set
`S` of primes multiplies its `L`-series by `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))`, the reciprocal of the
deleted local factors. -/
theorem LSeries_restrict (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    LSeries (normCoeff K (χ.restrict S S.finite_toSet).toIdealArithmeticFunction) s =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s *
        ∏ P ∈ S, (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) := by
  classical
  have hdata : EulerProductData.ofMultiplicativeIdealWeight (χ.restrict S S.finite_toSet) =
      (EulerProductData.ofMultiplicativeIdealWeight χ).restrictAway S :=
    EulerProductData.ext fun I ↦ by simp
  have key := EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor
    (EulerProductData.ofMultiplicativeIdealWeight χ) S (by simpa using hs)
  rw [← hdata, Finset.prod_congr rfl fun P _ ↦ eulerFactor_ofMultiplicativeIdealWeight χ P
    (norm_div_lt_one_of_summable_idealTerm χ hs P)] at key
  simp only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] at key
  have hne : ∏ P ∈ S, (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun P _ ↦ χ.one_sub_div_ne_zero_of_summable_idealTerm hs P
  rw [← key, Finset.prod_inv_distrib, mul_assoc, inv_mul_cancel₀ hne, mul_one]

end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function with finitely many Euler factors deleted -/

private theorem natCast_absNorm_ne_zero (P : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (NumberField.HeightOneSpectrum.one_lt_absNorm P).ne_bot

/-- On `Re s > 0`, `N(𝔭) ^ s` lies outside the closed unit disc. -/
private theorem one_lt_norm_absNorm_cpow (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) : 1 < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ s‖ := by
  have hP := NumberField.HeightOneSpectrum.one_lt_absNorm P
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  exact Real.one_lt_rpow (by exact_mod_cast hP) hs

private theorem absNorm_cpow_sub_one_ne_zero (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) : (Ideal.absNorm P.asIdeal : ℂ) ^ s - 1 ≠ 0 := fun h ↦ by
  simpa [sub_eq_zero.mp h] using one_lt_norm_absNorm_cpow P hs

/-- **The deleted Euler factors do not vanish on `Re s > 0`.** In particular they do not vanish
at `s = 1`, so deleting them does not change the order of the pole there. -/
theorem prod_one_sub_absNorm_cpow_neg_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ}
    (hs : 0 < s.re) : ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun P _ h ↦ absNorm_cpow_sub_one_ne_zero P hs ?_
  rw [Complex.cpow_neg, sub_eq_zero, eq_comm, inv_eq_one] at h
  rw [h, sub_self]

/-- **The Dedekind zeta function with the Euler factors at `S` deleted.** For a finite set `S` of
primes and `Re s > 1`, the `L`-series of the indicator of the ideals prime to `S` is
`ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`. -/
theorem LSeries_ofBadPrimes (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
        S.finite_toSet).toIdealArithmeticFunction) s =
      NumberField.dedekindZeta K s * ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
  have hsum : Summable
      (idealTerm K (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction s) := by
    rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact summable_idealTerm_one_iff.mpr hs
  rw [← MultiplicativeIdealWeight.one_restrict, MultiplicativeIdealWeight.LSeries_restrict _ S hsum,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    ← dedekindZeta_eq_LSeries_normCoeff_one]
  congr 1
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  rw [MultiplicativeIdealWeight.one_apply, ite_eq_right P.ne_bot, Complex.cpow_neg, one_div]

/-- **The residue at `s = 1` after deleting Euler factors.** As `s → 1⁺`,
`(s - 1) L_S(s)` tends to the residue of `ζ_K` multiplied by `∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))`, which
is nonzero by `prod_one_sub_absNorm_cpow_neg_ne_zero`. -/
theorem tendsto_sub_one_mul_LSeries_ofBadPrimes (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (normCoeff K
        (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
          S.finite_toSet).toIdealArithmeticFunction) s) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K *
        ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ)))) := by
  have hcont : Continuous fun s : ℝ ↦ ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-(s : ℂ))) :=
    continuous_finsetProd _ fun P _ ↦ continuous_const.sub <|
      (Complex.continuous_ofReal.neg).const_cpow <| Or.inl <| natCast_absNorm_ne_zero P
  have hprod := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  rw [Complex.ofReal_one] at hprod
  refine ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).mul hprod).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [LSeries_ofBadPrimes S (by simpa using hs), mul_assoc]

/-- The logarithmic derivative of a deleted Euler factor `1 - N(𝔭) ^ (-s)`. -/
private theorem logDeriv_one_sub_absNorm_cpow_neg (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv (fun z : ℂ ↦ 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-z)) s =
      Complex.log (Ideal.absNorm P.asIdeal) / ((Ideal.absNorm P.asIdeal : ℂ) ^ s - 1) := by
  have h0 := natCast_absNorm_ne_zero P
  have hderiv := (((hasDerivAt_neg s).const_cpow (Or.inl h0)).const_sub 1).deriv
  have hpow : (Ideal.absNorm P.asIdeal : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h0)
  have hsub := absNorm_cpow_sub_one_ne_zero P hs
  rw [logDeriv_apply, hderiv, Complex.cpow_neg]
  field_simp

/-- **The logarithmic derivative after deleting Euler factors.** For a finite set `S` of primes
and `Re s > 1`, the logarithmic derivative of `L_S(s) = ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))` is
that of `ζ_K` plus `∑ 𝔭 ∈ S, log N(𝔭) / (N(𝔭) ^ s - 1)`. -/
theorem logDeriv_LSeries_ofBadPrimes (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (LSeries (normCoeff K
        (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
          S.finite_toSet).toIdealArithmeticFunction)) s =
      logDeriv (NumberField.dedekindZeta K) s + ∑ P ∈ S,
        Complex.log (Ideal.absNorm P.asIdeal) / ((Ideal.absNorm P.asIdeal : ℂ) ^ s - 1) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  -- `L_S` and `ζ_K * ∏ (1 - N(𝔭) ^ (-s))` agree on the open half-plane `Re s > 1`, hence near `s`
  have heq : LSeries (normCoeff K
      (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
        S.finite_toSet).toIdealArithmeticFunction) =ᶠ[𝓝 s]
      fun z ↦ NumberField.dedekindZeta K z *
        ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-z)) :=
    Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      fun z hz ↦ LSeries_ofBadPrimes S hz
  have hζ : DifferentiableAt ℂ (NumberField.dedekindZeta K) s := by
    rw [funext (dedekindZeta_eq_LSeries_dedekindZetaCoeff K)]
    exact (LSeries_hasDerivAt (by rw [abscissaOfAbsConv_dedekindZetaCoeff]; exact_mod_cast hs))
      |>.differentiableAt
  have hfac : ∀ P ∈ S, DifferentiableAt ℂ
      (fun z : ℂ ↦ 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-z)) s := fun P _ ↦
    (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow
      (Or.inl (natCast_absNorm_ne_zero P)) |>.const_sub 1
  rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply,
    logDeriv_fun_mul s (dedekindZeta_ne_zero_of_one_lt_re hs)
      (prod_one_sub_absNorm_cpow_neg_ne_zero S hs0) hζ (DifferentiableAt.fun_finsetProd hfac),
    logDeriv_fun_prod ?_ hfac]
  · exact congrArg _ (Finset.sum_congr rfl fun P _ ↦ logDeriv_one_sub_absNorm_cpow_neg P hs0)
  · exact fun P hP ↦ Finset.prod_ne_zero_iff.mp (prod_one_sub_absNorm_cpow_neg_ne_zero S hs0) P hP

/-- **The Euler-factor correction is holomorphic on `Re s > 0`.** The finite sum
`∑ 𝔭 ∈ S, log N(𝔭) / (N(𝔭) ^ s - 1)` by which `logDeriv_LSeries_ofBadPrimes` separates the
logarithmic derivatives of `L_S` and `ζ_K` extends holomorphically across the line `Re s = 1`. -/
theorem differentiableOn_sum_log_absNorm_div_cpow_sub_one (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∑ P ∈ S,
        Complex.log (Ideal.absNorm P.asIdeal) / ((Ideal.absNorm P.asIdeal : ℂ) ^ s - 1))
      {s | 0 < s.re} := fun _ hs ↦
  (DifferentiableAt.fun_sum fun P _ ↦ (differentiableAt_const _).div
    ((differentiableAt_id.const_cpow (Or.inl (natCast_absNorm_ne_zero P))).sub_const 1)
    (absNorm_cpow_sub_one_ne_zero P hs)).differentiableWithinAt

end TauCeti
