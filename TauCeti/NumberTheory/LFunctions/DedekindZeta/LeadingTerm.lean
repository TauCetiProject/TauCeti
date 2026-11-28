/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
public import TauCeti.NumberTheory.NumberField.TateEmbedding.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.LeadingCoefficient
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
import TauCeti.NumberTheory.LFunctions.DedekindZeta.TrivialZeros
import TauCeti.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.NumberTheory.NumberField.Units.Dirichlet
import TauCeti.NumberTheory.NumberField.Units.Regulator.Basic

/-!
# The Dedekind zeta leading term at nonpositive integers

For a number field `K` and `n ≥ 2`, the continued Dedekind zeta function has order of
vanishing `d` at `1 - n`, where `d` is the real dimension of the embedding Tate space in
twist `n - 1`. Its leading Taylor coefficient is a nonzero real number and is a nonzero
rational multiple of `√|discr K| * π ^ (d - [K : ℚ] * n) * ζ_K(n)`.

The functional equation identifies the nonvanishing completed factor at `1 - n` with
its value at `n`. The reciprocal archimedean factors account for the whole vanishing
order, and their leading coefficients give the power of `π`.

At `s = 0`, the simple pole of `Λ_K` with residue `-2 ^ (r₁ + r₂) h R / w` combines with the
order-`r₁ + r₂` zero of `|d_K| ^ (-s / 2) Γ_ℝ(s)⁻¹ ^ r₁ Γ_ℂ(s)⁻¹ ^ r₂` to give a zero of order
`Units.rank K` and leading coefficient `-(h R / w)` (`tendsto_dedekindZetaC_div_pow_rank_zero`,
`meromorphicTrailingCoeffAt_dedekindZetaC_zero`), specializing to `ζ_K(0) = -h / w` when
`Units.rank K = 0` (`dedekindZetaC_zero_of_rank_eq_zero`).

## References

* A. Borel, [*Cohomologie de SLₙ et valeurs de fonctions zêta aux points entiers*][Borel1977],
  §§1.4 and 6.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.

[Borel1977]: https://www.numdam.org/item/ASNSP_1977_4_4_4_613_0/
-/

public section

open Complex Filter Module _root_.NumberField NumberField.InfinitePlace NumberField.Units
open scoped Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

private theorem one_sub_natCast_ne_one {n : ℕ} (hn : 2 ≤ n) : (1 : ℂ) - n ≠ 1 := by
  have h : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact fun he ↦ h (sub_eq_self.mp he)

private theorem one_lt_re_natCast {n : ℕ} (hn : 2 ≤ n) : 1 < (n : ℂ).re := by
  rw [natCast_re]
  have hn_nat : 1 < n := by omega
  exact_mod_cast hn_nat

/-- The analytic factor left over after removing the reciprocal Gamma factors from the
functional equation. -/
private noncomputable def leadingTermFactor (s : ℂ) : ℂ :=
  ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * completedDedekindZeta K s

private theorem analyticAt_leadingTermFactor {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    AnalyticAt ℂ (leadingTermFactor K) s :=
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (abs_discr_pos K).ne'
  ((by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ -z / 2) s).const_cpow (.inl hd)).mul
    (analyticAt_completedDedekindZeta K h₀ h₁)

/-- The functional equation evaluates the analytic factor at `1 - n` using the convergent
Dedekind zeta value at `n`. -/
private theorem leadingTermFactor_one_sub_nat {n : ℕ} (hn : 2 ≤ n) :
    leadingTermFactor K (1 - n) =
      (((|discr K| : ℤ) : ℂ) ^ (-((1 : ℂ) - n) / 2) *
        ((|discr K| : ℤ) : ℂ) ^ ((n : ℂ) / 2)) *
        (Gammaℝ n ^ nrRealPlaces K * Gammaℂ n ^ nrComplexPlaces K) * dedekindZeta K n := by
  rw [leadingTermFactor, completedDedekindZeta_one_sub,
    completedDedekindZeta_eq_mul_dedekindZeta K (one_lt_re_natCast hn)]
  ring

private theorem leadingTermFactor_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    leadingTermFactor K (1 - n) ≠ 0 := by
  have hr : ((1 : ℂ) - n).re < 0 := by simpa [sub_re] using Nat.lt_of_succ_le hn
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (abs_discr_pos K).ne'
  rw [leadingTermFactor]
  exact mul_ne_zero (cpow_ne_zero_iff.mpr (.inl hd))
    (completedDedekindZeta_ne_zero_of_re_neg K hr)

private theorem eventuallyEq_dedekindZetaC_mul_reciprocalGamma {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    dedekindZetaC K =ᶠ[𝓝 s] fun z ↦
      leadingTermFactor K z *
        ((Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) := by
  filter_upwards [eventually_ne_nhds h₀, eventually_ne_nhds h₁] with z hz₀ hz₁
  rw [dedekindZetaC_eq_mul_completedDedekindZeta K hz₀ hz₁, leadingTermFactor]
  ring

/-- At `1 - n` for `n ≥ 2`, the vanishing order of the continued Dedekind zeta function
equals the dimension of the embedding Tate space in twist `n - 1`. -/
theorem analyticOrderAt_dedekindZetaC_one_sub_nat {n : ℕ} (hn : 2 ≤ n) :
    analyticOrderAt (dedekindZetaC K) (1 - n) =
      (finrank ℝ (TauCeti.NumberField.tateEmbeddingSpace K (n - 1)) : ℕ∞) := by
  apply ENat.map_natCast_injective (α := ℤ)
  rw [← (analyticAt_dedekindZetaC K (one_sub_natCast_ne_one hn)).meromorphicOrderAt_eq,
    meromorphicOrderAt_dedekindZetaC_one_sub_nat K hn,
    TauCeti.NumberField.finrank_tateEmbeddingSpace_pred K (by omega : 1 ≤ n), ENat.map_natCast]

private theorem discr_cpow_mul_one_sub {n : ℕ} (hn : 2 ≤ n) :
    ((|discr K| : ℤ) : ℂ) ^ (-((1 : ℂ) - n) / 2) * ((|discr K| : ℤ) : ℂ) ^ ((n : ℂ) / 2) =
      ((|discr K| : ℤ) : ℂ) ^ (n - 1 : ℕ) * (Real.sqrt (|discr K| : ℤ) : ℂ) := by
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (abs_discr_pos K).ne'
  have he : -((1 : ℂ) - n) / 2 + (n : ℂ) / 2 = ((n - 1 : ℕ) : ℂ) + 1 / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  rw [← cpow_add _ _ hd, he, cpow_add _ _ hd, cpow_natCast, Real.sqrt_eq_rpow,
    ofReal_cpow (by exact_mod_cast (abs_discr_pos K).le)]
  simp only [ofReal_div, ofReal_one, ofReal_ofNat, ofReal_intCast]

/-- At `1 - n` for `n ≥ 2`, the leading coefficient of the continued Dedekind zeta function is
a nonzero rational multiple of `√|discr K| * π ^ (d - [K : ℚ] * n) * ζ_K(n)`. -/
private theorem exists_rat_meromorphicTrailingCoeffAt_dedekindZetaC_one_sub_nat
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ q : ℚ, q ≠ 0 ∧
      meromorphicTrailingCoeffAt (dedekindZetaC K) (1 - n) =
        (q : ℂ) * (Real.sqrt (|discr K| : ℤ) : ℂ) *
          (Real.pi : ℂ) ^ ((finrank ℝ (TauCeti.NumberField.tateEmbeddingSpace K (n - 1)) : ℤ) -
            (finrank ℚ K : ℤ) * n) * dedekindZeta K n := by
  have h₀ : (1 : ℂ) - n ≠ 0 :=
    sub_ne_zero.mpr (Nat.cast_ne_one.mpr (Nat.ne_of_gt (Nat.lt_of_succ_le hn))).symm
  have h₁ := one_sub_natCast_ne_one hn
  have hf := analyticAt_leadingTermFactor K h₀ h₁
  have hg := TauCeti.analyticAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow
    (nrRealPlaces K) (nrComplexPlaces K) (1 - n)
  obtain ⟨q, hq, hgamma⟩ :=
    exists_rat_meromorphicTrailingCoeffAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub
      (nrRealPlaces K) (nrComplexPlaces K) (by omega : 1 ≤ n)
  refine ⟨q * (|discr K| : ℤ) ^ (n - 1 : ℕ), mul_ne_zero hq (pow_ne_zero _
    (by exact_mod_cast (abs_discr_pos K).ne')), ?_⟩
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      ((eventuallyEq_dedekindZetaC_mul_reciprocalGamma K h₀ h₁).filter_mono nhdsWithin_le_nhds),
    hf.meromorphicAt.meromorphicTrailingCoeffAt_fun_mul hg.meromorphicAt,
    hf.meromorphicTrailingCoeffAt_of_ne_zero (leadingTermFactor_ne_zero K hn),
    leadingTermFactor_one_sub_nat K hn,
    TauCeti.NumberField.finrank_tateEmbeddingSpace_pred K (by omega : 1 ≤ n),
    ← card_add_two_mul_card_eq_rank]
  calc
    _ = (((|discr K| : ℤ) : ℂ) ^ (-((1 : ℂ) - n) / 2) *
          ((|discr K| : ℤ) : ℂ) ^ ((n : ℂ) / 2)) *
        (meromorphicTrailingCoeffAt
          (fun z ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) (1 - n) *
          (Gammaℝ n ^ nrRealPlaces K * Gammaℂ n ^ nrComplexPlaces K)) * dedekindZeta K n := by ring
    _ = _ := by
      rw [discr_cpow_mul_one_sub K hn, hgamma]
      push_cast only [Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      ring

/-- The real part of the degree-`d` Taylor coefficient of the continued Dedekind zeta
function at `1 - n`, where `d` is the dimension of the embedding Tate space in twist `n - 1`.
For `n ≥ 2` this is its real, nonzero leading coefficient. -/
noncomputable def dedekindZetaCLeadingCoeff (n : ℕ) : ℝ :=
  let d := finrank ℝ (TauCeti.NumberField.tateEmbeddingSpace K (n - 1))
  (iteratedDeriv d (dedekindZetaC K) (1 - n) / (d.factorial : ℂ)).re

/-- The leading coefficient in terms of the normalized complex derivative. -/
theorem dedekindZetaCLeadingCoeff_def (n : ℕ) :
    dedekindZetaCLeadingCoeff K n =
      let d := finrank ℝ (TauCeti.NumberField.tateEmbeddingSpace K (n - 1))
      (iteratedDeriv d (dedekindZetaC K) (1 - n) / (d.factorial : ℂ)).re := (rfl)

/-- Let `Z` be a continuation of the Dedekind zeta series analytic away from `1`.
At `1 - n`, with `n ≥ 2`, its vanishing order is the dimension `d` of the embedding Tate space
in twist `n - 1`. The degree-`d` Taylor coefficient is real and nonzero, is the punctured limit
of the quotient by `(s - (1 - n)) ^ d`, and is a nonzero rational multiple of
`√|discr K| * π ^ (d - [K : ℚ] * n) * ζ_K(n)`. The convergent value `ζ_K(n)` is positive. -/
theorem dedekindZeta_continuation_leadingTerm {n : ℕ} (hn : 2 ≤ n) {Z : ℂ → ℂ}
    (hZ : ∀ z ≠ 1, AnalyticAt ℂ Z z)
    (hseries : Set.EqOn Z (dedekindZeta K) {z | 1 < z.re}) :
    let d := finrank ℝ (TauCeti.NumberField.tateEmbeddingSpace K (n - 1))
    let a : ℂ := 1 - n
    let c := dedekindZetaCLeadingCoeff K n
    analyticOrderAt Z a = (d : ℕ∞) ∧
      (c : ℂ) = iteratedDeriv d Z a / (d.factorial : ℂ) ∧ c ≠ 0 ∧
      Tendsto (fun s ↦ Z s / (s - a) ^ d) (𝓝[≠] a) (𝓝 (c : ℂ)) ∧
      (∃ q : ℚ, q ≠ 0 ∧ c = (q : ℝ) * Real.sqrt (|discr K| : ℤ) *
        Real.pi ^ ((d : ℤ) - (finrank ℚ K : ℤ) * n) * (dedekindZeta K n).re) ∧
      0 < (dedekindZeta K n).re := by
  dsimp only
  let d := finrank ℝ (TauCeti.NumberField.tateEmbeddingSpace K (n - 1))
  let a : ℂ := 1 - n
  have ha : a ≠ 1 := one_sub_natCast_ne_one hn
  have hagree : Z =ᶠ[𝓝 a] dedekindZetaC K := by
    filter_upwards [eventually_ne_nhds ha] with s hs using
      eqOn_dedekindZetaC_of_eqOn_dedekindZeta K hZ hseries
        (Set.mem_compl_singleton_iff.mpr hs)
  have hord : analyticOrderAt Z a = (d : ℕ∞) :=
    (analyticOrderAt_congr hagree).trans (analyticOrderAt_dedekindZetaC_one_sub_nat K hn)
  have hM := (hZ a ha).meromorphicAt
  have hMord : meromorphicOrderAt Z a = ((d : ℤ) : WithTop ℤ) := by
    rw [(hZ a ha).meromorphicOrderAt_eq, hord, ENat.map_natCast]
  have hc : meromorphicTrailingCoeffAt Z a = iteratedDeriv d Z a / (d.factorial : ℂ) := by
    rw [(hZ a ha).meromorphicTrailingCoeffAt_eq_inv_factorial_smul_iteratedDeriv hord,
      smul_eq_mul, div_eq_inv_mul]
  obtain ⟨q, hq, hvalue⟩ := exists_rat_meromorphicTrailingCoeffAt_dedekindZetaC_one_sub_nat K hn
  have hn_nat : 1 < n := by omega
  have hnat : (1 : ℝ) < n := by exact_mod_cast hn_nat
  have hζ : ((dedekindZeta K n).re : ℂ) = dedekindZeta K n := by
    simpa only [ofReal_natCast] using TauCeti.dedekindZeta_ofReal_re (K := K) (n : ℝ)
  have hformula :
      ((q * Real.sqrt (|discr K| : ℤ) *
        Real.pi ^ ((d : ℤ) - (finrank ℚ K : ℤ) * n) * (dedekindZeta K n).re : ℝ) : ℂ) =
      (q : ℂ) * (Real.sqrt (|discr K| : ℤ) : ℂ) *
        (Real.pi : ℂ) ^ ((d : ℤ) - (finrank ℚ K : ℤ) * n) * dedekindZeta K n := by
    push_cast
    rw [hζ]
  rw [← meromorphicTrailingCoeffAt_congr_nhdsNE (hagree.filter_mono nhdsWithin_le_nhds), hc,
    ← hformula] at hvalue
  have hcoeff : (iteratedDeriv d Z a / (d.factorial : ℂ)).re = dedekindZetaCLeadingCoeff K n := by
    rw [hagree.iteratedDeriv_eq, dedekindZetaCLeadingCoeff_def]
  have hreal := congrArg re hvalue
  rw [hcoeff, ofReal_re] at hreal
  have hcast := (congrArg ofReal hreal).trans hvalue.symm
  refine ⟨hord, hcast, ?_, ?_, ⟨q, hq, hreal⟩, ?_⟩
  · exact fun h ↦ hM.meromorphicTrailingCoeffAt_ne_zero (hMord.trans_ne WithTop.coe_ne_top)
      (by rw [hc, ← hcast, h, ofReal_zero])
  · simpa only [smul_eq_mul, ← div_eq_inv_mul, hc, ← hcast] using
      (hZ a ha).tendsto_inv_pow_smul_meromorphicTrailingCoeffAt hord
  · simpa only [ofReal_natCast] using dedekindZeta_re_pos (K := K) hnat

private theorem dedekindZetaC_zero_limit_coeff :
    -((2 ^ (nrRealPlaces K + nrComplexPlaces K) * classNumber K * regulator K /
        torsionOrder K : ℝ) : ℂ) * 1 *
        ((2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K) =
      (-((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
  push_cast
  rw [pow_add, inv_pow, inv_pow]
  field_simp

private theorem dedekindZetaC_zero_factor_identity {z : ℂ} (hz0 : z ≠ 0)
    (hz : dedekindZetaC K z =
      invDedekindZetaCompletionFactor K z * completedDedekindZeta K z) :
    z * completedDedekindZeta K z * ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        ((z * Gammaℝ z)⁻¹ ^ nrRealPlaces K * (z * Gammaℂ z)⁻¹ ^ nrComplexPlaces K) =
      dedekindZetaC K z / z ^ Units.rank K := by
  have hrank := Units.rank_add_one_eq_nrRealPlaces_add_nrComplexPlaces K
  rw [hz, invDedekindZetaCompletionFactor_def]
  simp only [mul_inv, mul_pow]
  have hzpow : z * (z⁻¹ ^ nrRealPlaces K * z⁻¹ ^ nrComplexPlaces K) = (z ^ Units.rank K)⁻¹ := by
    rw [← pow_add, ← hrank, pow_succ', inv_pow]
    field_simp
  rw [div_eq_mul_inv _ (z ^ Units.rank K), ← hzpow]
  ring

/-- **Leading term of `ζ_K` at `s = 0`** (Neukirch VII (5.11)):
`dedekindZetaC K s / s ^ Units.rank K → -(h R / w)` as `s → 0`, `s ≠ 0`. -/
theorem tendsto_dedekindZetaC_div_pow_rank_zero :
    Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ Units.rank K) (𝓝[≠] 0)
      (𝓝 (-((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ)) := by
  have hdiscr :
      Tendsto (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) (𝓝[≠] 0) (𝓝 1) := by
    have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (abs_discr_pos K).ne'
    simpa using ((by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ -z / 2) 0).const_cpow
      (.inl hd)).continuousAt.mono_left nhdsWithin_le_nhds
  have hGℝ : Tendsto (fun z : ℂ ↦ (z * Gammaℝ z)⁻¹ ^ nrRealPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrRealPlaces K)) :=
    (Gammaℝ_residue_zero.inv₀ two_ne_zero).pow _
  have hGℂ : Tendsto (fun z : ℂ ↦ (z * Gammaℂ z)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrComplexPlaces K)) :=
    (Gammaℂ_residue_zero.inv₀ two_ne_zero).pow _
  have hprod :=
    ((tendsto_mul_completedDedekindZeta_zero K).mul hdiscr).mul (hGℝ.mul hGℂ)
  rw [dedekindZetaC_zero_limit_coeff K] at hprod
  refine hprod.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_invDedekindZetaCompletionFactor_mul K 0,
      self_mem_nhdsWithin]
    with z hz (hz0 : z ≠ 0)
  exact dedekindZetaC_zero_factor_identity K hz0 hz

/-- **Trailing coefficient of `ζ_K` at `s = 0`** (Neukirch VII (5.11)):
`meromorphicTrailingCoeffAt (dedekindZetaC K) 0 = -(h R / w)`. -/
theorem meromorphicTrailingCoeffAt_dedekindZetaC_zero :
    meromorphicTrailingCoeffAt (dedekindZetaC K) 0 =
      (-((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
  have hM : MeromorphicAt (dedekindZetaC K) 0 :=
    (analyticAt_dedekindZetaC K zero_ne_one).meromorphicAt
  have hlim : Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ Units.rank K) (𝓝[≠] 0)
      (𝓝 (meromorphicTrailingCoeffAt (dedekindZetaC K) 0)) := by
    refine hM.tendsto_nhds_meromorphicTrailingCoeffAt.congr fun s ↦ ?_
    simp [meromorphicOrderAt_dedekindZetaC_zero, zpow_neg, div_eq_inv_mul]
  exact tendsto_nhds_unique hlim (tendsto_dedekindZetaC_div_pow_rank_zero K)

/-- **Value of `ζ_K` at `s = 0` in unit rank zero** (such as `ℚ` and imaginary quadratic
fields): `ζ_K(0) = -h / w`. -/
@[simp]
theorem dedekindZetaC_zero_of_rank_eq_zero (hr : Units.rank K = 0) :
    dedekindZetaC K 0 = (-((classNumber K : ℝ) / torsionOrder K : ℝ) : ℂ) := by
  have hlim : Tendsto (dedekindZetaC K) (𝓝[≠] 0)
      (𝓝 (-((classNumber K : ℝ) / torsionOrder K : ℝ) : ℂ)) := by
    simpa [hr, Units.regulator_eq_one_of_rank_eq_zero K hr] using
      tendsto_dedekindZetaC_div_pow_rank_zero K
  have hcont : Tendsto (dedekindZetaC K) (𝓝[≠] 0) (𝓝 (dedekindZetaC K 0)) :=
    (analyticAt_dedekindZetaC K zero_ne_one).continuousAt.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hcont hlim

end TauCeti.LFunctions
