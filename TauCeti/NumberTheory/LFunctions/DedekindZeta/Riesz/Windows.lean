/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.Analysis.SpecialFunctions.Pow.Windows
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder
import TauCeti.Analysis.MellinTransform.WindowedLandau
import TauCeti.Analysis.SpecialFunctions.Pow.Windows.Bounds
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Growth
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Nonvanishing
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Riesz.ExplicitFormula
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Riesz.Poles

/-!
# Power windows for the Dedekind zeta Riesz remainder

The explicit formula bounds the first Riesz remainder of the trivial ray class character
when its Dedekind zeta function is zero-free in a right half-plane. Conversely, a one-sided
upper bound on arbitrarily far-out power windows rules out zeros, by the Mellin form of
windowed Landau. A pole of the Mellin expression at a real zero has positive leading
coefficient and hence cannot be the rightmost pole required by that criterion.

The window criterion for Dirichlet families follows Levent Alpöge's
`Deduction.zeroFree_of_rpow_window` in `DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean`
of his [formalization](https://github.com/leanprover-community/riemann-hypothesis)). Here the prime and
zero sums are those of the Dedekind zeta function of an arbitrary number field.
-/

public section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace Set

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- A zero-free half-plane for Dedekind zeta bounds the norm of its first Riesz remainder by
`C * y ^ σ` for `y ≥ 1` and `σ ≥ 1/2`, with a constant independent of `σ`. -/
theorem exists_norm_dedekindZeta_rieszRemainder_le_of_zeroFreeRightOf :
    ∃ C : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → ZeroFreeRightOf σ (dedekindZetaC K) → ∀ y ≥ 1,
      ‖(1 : PrimitiveRayClassCharacter K).rieszRemainder y‖ ≤ C * y ^ σ := by
  let Ξ := toMeromorphicNFOn (fun z : ℂ ↦ z * (z - 1) * completedDedekindZeta K z) univ
  let A := ∑' ρ : (MeromorphicOn.divisor Ξ univ).support,
    ‖((MeromorphicOn.divisor Ξ univ ρ).toNat : ℂ) / (ρ * (1 - ρ))‖
  let m : ℂ := (nrRealPlaces K : ℂ) + nrComplexPlaces K - 1
  let a := logDerivFinitePart (dedekindZetaC K) 0
  obtain ⟨B, hB⟩ := exists_norm_dedekindZetaRieszGammaCorrection_le K
  refine ⟨A + |B| + (‖a‖ + 3 * ‖m‖), fun σ hσ hz y hy ↦ ?_⟩
  have hzero (ρ : ℂ) (hρ : Ξ ρ = 0) : ρ.re ≤ σ := by
    by_contra! hlt
    have h0 := ne_zero_of_re_pos (by linarith : 0 < ρ.re)
    have hre := re_lt_one_of_toMeromorphicNFOn_mul_completedDedekindZeta_eq_zero K hρ
    have h1 : ρ ≠ 1 := ne_of_apply_ne re (ne_of_lt (by simpa only [one_re] using hre))
    dsimp only [Ξ] at hρ
    rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq K h0 h1] at hρ
    have hc : completedDedekindZeta K ρ = 0 :=
      (mul_eq_zero.mp hρ).resolve_left (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    have hζ : dedekindZetaC K ρ = 0 := by
      simp [dedekindZetaC_eq_mul_completedDedekindZeta K h0 h1, hc]
    exact ((zeroFreeRightOf_iff.mp hz) ρ hlt).not_gt
      ((analyticAt_dedekindZetaC K h1).meromorphicOrderAt_pos_iff_eq_zero.mpr hζ)
  have hZ := (orderLE_toMeromorphicNFOn_mul_completedDedekindZeta K).norm_rieszZeroSeries_le
    (differentiable_toMeromorphicNFOn_mul_completedDedekindZeta K) (by norm_num) hzero hy
  have hyσ : 1 ≤ y ^ σ := Real.one_le_rpow hy (by linarith)
  have hlog : Real.log y ≤ 2 * y ^ σ := by
    calc
      Real.log y ≤ y ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div (zero_le_one.trans hy) (by norm_num)
      _ ≤ 2 * y ^ σ := by
        rw [div_eq_mul_inv, mul_comm]
        norm_num only [inv_div, div_one]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy hσ) (by norm_num)
  have hO : ‖a + m * (1 + (Real.log y : ℂ))‖ ≤ (‖a‖ + 3 * ‖m‖) * y ^ σ := by
    calc
      _ ≤ ‖a‖ + ‖m‖ * (1 + Real.log y) := by
        exact (norm_add_le ..).trans (by
          rw [norm_mul, ← ofReal_one, ← ofReal_add, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [Real.log_nonneg hy])])
      _ ≤ ‖a‖ * y ^ σ + ‖m‖ * (3 * y ^ σ) :=
        add_le_add (le_mul_of_one_le_right (norm_nonneg a) hyσ)
          (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg m))
      _ = _ := by ring
  have hG : ‖dedekindZetaRieszGammaCorrection K y‖ ≤ |B| * y ^ σ :=
    (hB y hy).trans (mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hy (by linarith))
      (Real.rpow_nonneg (zero_le_one.trans hy) _) (abs_nonneg _))
  rw [PrimitiveRayClassCharacter.rieszRemainder_one_eq_dedekindZetaRieszZeroSide K hy,
    dedekindZetaRieszZeroSide_def]
  calc
    _ ≤ A * y ^ σ + |B| * y ^ σ + (‖a‖ + 3 * ‖m‖) * y ^ σ :=
      (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hZ hG)) hO)
    _ = _ := by ring

/-- A one-sided upper bound for the first Dedekind zeta Riesz remainder on arbitrarily
far-out power windows excludes zeros to the right of the exponent. -/
theorem zeroFreeRightOf_dedekindZetaC_of_hasWindows_rieszRemainder_one
    {θ L C : ℝ} (hθ : 0 ≤ θ) (hL : 1 < L)
    (hwin : HasWindows
      {y | ((1 : PrimitiveRayClassCharacter K).rieszRemainder y).re ≤ C * y ^ θ} L) :
    ZeroFreeRightOf θ (dedekindZetaC K) := by
  let ψ := (1 : PrimitiveRayClassCharacter K)
  let F := rieszRemainderMellin (dedekindZetaC K)
  have hreal (y : ℝ) : ((ψ.rieszRemainder y).re : ℂ) = ψ.rieszRemainder y := by
    apply conj_eq_iff_re.mp
    simpa only [ψ, PrimitiveRayClassCharacter.inv_one] using (ψ.rieszRemainder_inv y).symm
  have hF : MeromorphicOn F {z | θ < z.re} := fun z _ ↦
    meromorphicAt_rieszRemainderMellin (dedekindZetaC K) z
  have hM (z : ℂ) (hz : 1 < z.re) :
      IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(z + 1)) * ((ψ.rieszRemainder y).re : ℂ)) (Ioi 1) ∧
      (∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (-(z + 1)) * ((ψ.rieszRemainder y).re : ℂ)) = F z := by
    simp only [hreal]
    simp only [neg_add', mul_comm (_ ^ _), ψ,
      PrimitiveRayClassCharacter.rieszRemainder_one, ofReal_sub, ofReal_mul, ofReal_add, ofReal_one,
      mul_comm (_ : ℂ) (1 + (eulerKroneckerConstant K : ℂ)), F]
    exact integrableOn_and_integral_rieszSum_normCoeff_vonMangoldt_add_mul_cpow K hz
  have hno : ∀ z : ℂ, θ < z.re → 0 ≤ meromorphicOrderAt F z := by
    rcases meromorphicOrderAt_nonneg_or_exists_rightmost_real_pole_of_mellin_hasWindows
      hL hF hM hwin with h | ⟨β, hβ, hp, _, hneg, _⟩
    · exact h
    · obtain ⟨c, hc, he⟩ :=
        exists_pos_meromorphicTrailingCoeffAt_rieszRemainderMellin_dedekindZetaC K
          (hθ.trans_lt hβ.1) hp
      exact False.elim (hc.not_gt (by simpa only [F, he, ofReal_re] using hneg))
  refine zeroFreeRightOf_iff.mpr fun z hz ↦ le_of_not_gt fun hpos ↦ (hno z hz).not_gt ?_
  exact (meromorphicOrderAt_rieszRemainderMellin_dedekindZetaC_neg_iff K
    (ne_zero_of_re_pos (hθ.trans_lt hz))).mpr hpos

/-- For `σ ≥ 1/2`, the absence of Dedekind zeta zeros to the right of `σ` is equivalent to
one-sided bounds at each exponent `σ + ε` on arbitrarily far-out power windows. The ratio
may depend on `ε`; in the forward direction any fixed ratio greater than one works. -/
theorem zeroFreeRightOf_dedekindZetaC_iff_forall_exists_hasWindows_rieszRemainder_one
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) : ZeroFreeRightOf σ (dedekindZetaC K) ↔
      ∀ ε > (0 : ℝ), ∃ L > 1, HasWindows
        {y | ((1 : PrimitiveRayClassCharacter K).rieszRemainder y).re ≤ y ^ (σ + ε)} L := by
  constructor
  · intro hz ε hε
    obtain ⟨C, hC⟩ := exists_norm_dedekindZeta_rieszRemainder_le_of_zeroFreeRightOf K
    refine ⟨2, by norm_num,
      hasWindows_rpow_bound_of_eventually_le (C := C) ?_ (lt_add_of_pos_right _ hε) 2⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact (re_le_norm _).trans (hC σ hσ hz y hy)
  · rw [zeroFreeRightOf_iff_forall_gt]
    intro h θ hθ
    obtain ⟨L, hL, hwin⟩ := h (θ - σ) (sub_pos.mpr hθ)
    rw [add_sub_cancel] at hwin
    exact zeroFreeRightOf_dedekindZetaC_of_hasWindows_rieszRemainder_one K (C := 1)
      (by linarith) hL (by simpa only [one_mul] using hwin)

end TauCeti.LFunctions
