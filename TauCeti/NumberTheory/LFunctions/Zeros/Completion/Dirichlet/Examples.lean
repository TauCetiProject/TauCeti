/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.Analysis.SpecialFunctions.Log.SumLogDivSq
import Mathlib.Tactic.NormNum

/-!
# Examples for the Dirichlet completion and the retained-zero inequalities

* The native quadratic character modulo five is even. At zero its ordinary L-function vanishes,
  whereas its entire completion does not. Thus the positive-real-part hypothesis in the comparison
  of ordinary and completed zero multiplicities cannot be extended to include the origin.
  Its L-function also vanishes at every `-2n`, and admitting all these trivial zeros in the
  finite-sum inequality would add the divergent series `∑ₙ 1 / (σ + 2n)` to its left side.
* For a quartic character `χ` modulo five (odd, so its gamma shift is `κ = 1`), the right side of
  the retained-zero inequalities at `σ = 2` is at least `1.807`. Only the residues `n ≡ 1 mod 5`
  contribute positively to `-Re (L'/L)(2, χ) = ∑ₙ Λ(n) Re χ(n) / n²`, and the first of those with
  `Λ(n) ≠ 0` is `n = 11`, so `-Re (L'/L)(2, χ) ≤ ∑_{n ≥ 11} log n / n² ≤ (1 + log 10) / 10`.
* The one-zero inequality for the odd character `χ_{-4}` modulo four at `σ = 2`: its gamma term
  is `logDeriv Gammaℝ 3`, negative and inside `[-C_Γ, C_Γ]`, and its conductor term is `½ log 4`.
-/

public section

open Complex DirichletCharacter ArithmeticFunction LSeries

open scoped LSeries.notation

namespace TauCeti.LFunctions

/-- The quadratic character modulo five witnesses the origin boundary of the order comparison. -/
example :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let χ : DirichletCharacter ℂ 5 :=
      (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)
    ∃ hχ : χ.IsPrimitive, χ.Even ∧ χ ≠ 1 ∧ χ.LFunction 0 = 0 ∧
      (dirichletData χ hχ).entireCompletion 0 ≠ 0 ∧
      analyticOrderAt χ.LFunction 0 ≠
        analyticOrderAt (dirichletData χ hχ).entireCompletion 0 := by
  intro _ χ
  have he : χ.Even := by
    have hneg : (quadraticChar (ZMod 5)) (-1) = 1 := by
      rw [quadraticChar_neg_one (F := ZMod 5) (by norm_num [ZMod.ringChar_zmod_n]), ZMod.card]
      exact ZMod.χ₄_nat_one_mod_four (by norm_num)
    simp only [χ, DirichletCharacter.Even, MulChar.ringHomComp_apply, hneg, map_one]
  have hne : χ ≠ 1 := quadraticChar_ringHomComp_ne_one
    (by simp [ringChar.eq_zero]) (by norm_num)
  have hprim : χ.IsPrimitive := by
    simpa [χ, isPrimitive_def] using conductor_changeLevel_quadraticChar
      (R := ℂ) (p := 5) (by simp [ringChar.eq_zero]) (by norm_num) (dvd_refl 5)
  have hzero : χ.LFunction 0 = 0 := by
    simpa [DirichletCharacter.LFunction, χ.map_zero' (by decide : 5 ≠ 1)] using
      ZMod.LFunction_apply_zero_of_even he.to_fun
  have hc := dirichletData_entireCompletion_zero_ne_zero χ hprim
  refine ⟨hprim, he, hne, hzero, hc, ?_⟩
  rw [((dirichletData_hasMeromorphicContinuation χ hprim).analyticAt_entireCompletion 0)
    |>.analyticOrderAt_eq_zero.mpr hc]
  exact ((DirichletCharacter.differentiable_LFunction hne).analyticAt 0)
    |>.analyticOrderAt_ne_zero.mpr hzero

/-- The trivial zeros cannot be admitted in the finite-sum inequality: the even quadratic character
modulo five has `L(-2n, χ) = 0` for every `n ≥ 1`, while at every real `σ` the summands
`Re (1 / (σ - (-2n))) = 1 / (σ + 2n)` of these zeros are not summable. -/
example :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let χ : DirichletCharacter ℂ 5 :=
      (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)
    (∀ n : ℕ, 0 < n → χ.LFunction (-(2 * n)) = 0) ∧
      ∀ σ : ℝ, ¬Summable fun n : ℕ ↦ (1 / ((σ : ℂ) - (-(2 * n)))).re := by
  intro _ χ
  have he : χ.Even := by
    have hneg : (quadraticChar (ZMod 5)) (-1) = 1 := by
      rw [quadraticChar_neg_one (F := ZMod 5) (by norm_num [ZMod.ringChar_zmod_n]), ZMod.card]
      exact ZMod.χ₄_nat_one_mod_four (by norm_num)
    simp only [χ, DirichletCharacter.Even, MulChar.ringHomComp_apply, hneg, map_one]
  refine ⟨fun n hn ↦ ?_, fun σ hsum ↦ ?_⟩
  · have : NeZero n := ⟨hn.ne'⟩
    exact he.LFunction_neg_two_mul_nat n
  · have hre (n : ℕ) : (1 / ((σ : ℂ) - (-(2 * n)))).re = 1 / (σ + 2 * n) := by
      rw [sub_neg_eq_add, show (σ : ℂ) + 2 * n = ((σ + 2 * n : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_one, ← ofReal_div, ofReal_re]
    simp only [hre] at hsum
    -- With `K = ⌈|σ|⌉ + 1`, `1 / (n + 1) ≤ (3|σ| + 4) / (σ + 2(n + K))` would make the harmonic
    -- series summable.
    set K := ⌈|σ|⌉₊ + 1
    have hK : |σ| + 1 ≤ (K : ℝ) ∧ (K : ℝ) < |σ| + 2 := by
      have h₁ := Nat.le_ceil |σ|
      have h₂ := Nat.ceil_lt_add_one (abs_nonneg σ)
      push_cast [K]
      constructor <;> linarith
    have hσ := neg_abs_le σ
    have hσ' := le_abs_self σ
    have hpos (n : ℕ) : 0 < σ + 2 * ((n + K : ℕ) : ℝ) := by
      push_cast
      nlinarith [n.cast_nonneg (α := ℝ)]
    refine Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp ?_)
    refine (((summable_nat_add_iff K).mpr hsum).mul_left (3 * |σ| + 4)).of_nonneg_of_le
      (fun n ↦ by positivity) fun n ↦ ?_
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (hpos n)]
    push_cast
    nlinarith [n.cast_nonneg (α := ℝ)]

/-- A nonreal character: every character `χ` modulo `5` of order `4` (one exists) satisfies
`χ⁻¹ ≠ χ`, is primitive and odd, so its gamma shift is `κ = 1`, and the right side of the
finite-sum inequality at `σ = 2`, where `S = ∅` makes the left side `0`, is at least `1.807`.
A statement restricted to real characters would say nothing here.

Only the residues `n ≡ 1 mod 5` contribute positively to
`-Re (L'/L)(2, χ) = ∑ₙ Λ(n) Re χ(n) / n²`, and the first of those with `Λ(n) ≠ 0` is `n = 11`;
the tail `∑_{n ≥ 11} log n / n²` is at most `(1 + log 10) / 10 < 0.34`
(`Real.tsum_log_div_sq_of_lt_le`). -/
example :
    (∃ χ : DirichletCharacter ℂ 5, orderOf χ = 4) ∧
      ∀ χ : DirichletCharacter ℂ 5, orderOf χ = 4 →
        χ⁻¹ ≠ χ ∧ χ.IsPrimitive ∧ χ.Odd ∧
          logDeriv χ.gammaFactor 2 = logDeriv Gammaℝ 3 ∧
          (1.807 : ℝ) ≤ (logDeriv χ.LFunction 2).re + Real.log 5 / 2 + gammaLogDerivBound := by
  have : Fact (1 < 5) := ⟨by norm_num⟩
  refine ⟨?_, fun χ hχ ↦ ?_⟩
  · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact MulChar.exists_mulChar_orderOf (ZMod 5) (by rw [ZMod.card]) isPrimitiveRoot_I
  have hne : χ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hχ
    exact absurd hχ (by norm_num)
  have hprim : χ.IsPrimitive := by
    rcases Nat.prime_five.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level χ) with
      h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) hne
    · exact (DirichletCharacter.isPrimitive_def χ).mpr h
  -- An even `χ` would have `χ(a)² = χ(a²) = 1` on all units, since `a² ∈ {1, 4 = -1}`.
  have ho : χ.Odd := by
    refine χ.even_or_odd.resolve_left fun he ↦ ?_
    have h4 : χ 4 = 1 := by rw [show (4 : ZMod 5) = -1 by decide]; exact he
    have hsq : χ ^ 2 = 1 := MulChar.ext fun u ↦ by
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow]
      have hu : (u : ZMod 5) ≠ 0 := u.ne_zero
      rcases (by revert hu; generalize (u : ZMod 5) = a; revert a; decide :
          (u : ZMod 5) ^ 2 = 1 ∨ (u : ZMod 5) ^ 2 = 4) with h | h <;>
        simp [h, h4]
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hχ] at this
    exact absurd this (by decide)
  -- Off the residue class `1`, `χ` takes the values `0`, `±χ(2)` and `-1`, with `χ(2)² = -1`.
  have hre {a : ZMod 5} (ha : a ≠ 1) : (χ a).re ≤ 0 := by
    have h4 : χ 4 = -1 := by rw [show (4 : ZMod 5) = -1 by decide]; exact ho
    have h2 : χ 2 ^ 2 = -1 := by rw [← map_pow, show (2 : ZMod 5) ^ 2 = 4 by decide, h4]
    have h2re : (χ 2).re = 0 := by
      have hre := congrArg Complex.re h2
      have him := congrArg Complex.im h2
      simp only [pow_two, mul_re, mul_im, neg_re, neg_im, one_re, one_im] at hre him
      nlinarith [sq_nonneg (χ 2).re, sq_nonneg (χ 2).im]
    rcases (by revert a; decide : ∀ a : ZMod 5, a ≠ 1 → a = 0 ∨ a = 2 ∨ a = 3 ∨ a = 4) a ha with
      rfl | rfl | rfl | rfl
    · rw [MulChar.map_zero, zero_re]
    · exact h2re.le
    · rw [show (3 : ZMod 5) = 2 * 4 by decide, map_mul, h4, mul_neg_one, neg_re, h2re, neg_zero]
    · simp [h4]
  -- `-Re (L'/L)(2, χ) ≤ (1 + log 10) / 10`.
  have hL : -(logDeriv χ.LFunction 2).re ≤ (1 + Real.log 10) / 10 := by
    have hs : 1 < (2 : ℂ).re := by norm_num
    have hsum := LSeriesSummable_twist_vonMangoldt χ hs
    rw [logDeriv_LFunction_eq_neg_LSeries χ hs, neg_re, neg_neg, LSeries, re_tsum hsum]
    set g : ℕ → ℝ := fun n ↦ if 10 < n then Real.log n / (n : ℝ) ^ 2 else 0
    have hfg (n : ℕ) : (term (↗χ * ↗Λ) 2 n).re ≤ g n := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [g]
      have hterm : term (↗χ * ↗Λ) 2 n = χ n * ((Λ n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
        rw [term_of_ne_zero hn, cpow_ofNat, Pi.mul_apply]
        push_cast
        ring
      rw [hterm, re_mul_ofReal]
      have hΛ : 0 ≤ Λ n / (n : ℝ) ^ 2 := by positivity
      simp only [g]
      split_ifs with h11
      · calc (χ n).re * (Λ n / (n : ℝ) ^ 2) ≤ 1 * (Λ n / (n : ℝ) ^ 2) := by
              gcongr
              exact (re_le_norm _).trans (χ.norm_le_one _)
          _ ≤ Real.log n / (n : ℝ) ^ 2 := by
              rw [one_mul]
              gcongr
              exact vonMangoldt_le_log
      · by_cases h1 : (n : ZMod 5) = 1
        · have hΛ0 : Λ n = 0 := by
            have : n = 1 ∨ n = 6 := by
              have h5 := (ZMod.natCast_eq_natCast_iff' n 1 5).mp (by simpa using h1)
              omega
            rcases this with rfl | rfl
            · simp
            · rw [vonMangoldt_eq_zero_iff]
              decide
          simp [hΛ0]
        · exact mul_nonpos_of_nonpos_of_nonneg (hre h1) hΛ
    refine (Complex.reCLM.summable hsum).tsum_le_of_sum_range_le fun N ↦ ?_
    calc ∑ n ∈ Finset.range N, (term (↗χ * ↗Λ) 2 n).re ≤ ∑ n ∈ Finset.range N, g n :=
          Finset.sum_le_sum fun n _ ↦ hfg n
      _ ≤ ∑' n, g n := by
          have hg (n : ℕ) : 0 ≤ g n := by
            have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
            simp only [g]; split_ifs <;> positivity
          refine (Real.summable_log_div_sq.of_nonneg_of_le hg fun n ↦ ?_).sum_le_tsum _
            fun n _ ↦ hg n
          have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
          simp only [g]
          split_ifs
          · exact le_rfl
          · positivity
      _ ≤ (1 + Real.log 10) / 10 := by
          simpa using Real.tsum_log_div_sq_of_lt_le (N := 10) (by norm_num)
  refine ⟨fun hinv ↦ ?_, hprim, ho, ?_, ?_⟩
  · have horder : orderOf χ ≤ 2 :=
      (isSelfInv_iff_isOfFinOrder_and_orderOf_le_two.mp (isSelfInv_iff.mpr hinv)).2
    norm_num [hχ] at horder
  · rw [ho.logDeriv_gammaFactor]
    norm_num
  · have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have hlog5 : 2 * Real.log 2 ≤ Real.log 5 := by
      rw [← Real.log_rpow two_pos]
      exact Real.log_le_log (by positivity) (by norm_num)
    have hπ : 1 < Real.log Real.pi := by
      rw [Real.lt_log_iff_exp_lt Real.pi_pos]
      linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
    have h2 := Real.log_two_gt_d9
    rw [gammaLogDerivBound_eq]
    norm_num at h2 ⊢
    linarith

/-- The one-zero inequality for the odd character `χ_{-4}` modulo four at `σ = 2`: its gamma term
is `logDeriv Gammaℝ 3`, which is negative and lies in `[-C_Γ, C_Γ]`, and its conductor term is
`½ log 4`. -/
example :
    let χ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
    χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.Odd ∧ logDeriv χ.gammaFactor 2 = logDeriv Gammaℝ 3 ∧
      (logDeriv Gammaℝ 3).re < 0 ∧ ‖logDeriv Gammaℝ 3‖ ≤ gammaLogDerivBound ∧
      ∀ β : ℝ, 0 < β → χ.LFunction β = 0 →
        1 / (2 - β) ≤ (logDeriv χ.LFunction 2).re + Real.log 4 / 2 + gammaLogDerivBound := by
  intro χ
  have hprim : χ.IsPrimitive := (isPrimitive_def χ).mpr conductor_χ₄_ringHomComp
  have ho : χ.Odd := by
    have hneg : ZMod.χ₄ (-1) = -1 := by
      simpa only [Int.cast_neg, Int.cast_one] using
        (ZMod.χ₄_int_three_mod_four (n := -1) (by decide))
    simp only [χ, DirichletCharacter.Odd, MulChar.ringHomComp_apply, hneg, map_neg, map_one]
  have hne : χ ≠ 1 := fun h ↦ by
    have := ho
    rw [h, DirichletCharacter.Odd, MulChar.one_apply (isUnit_one.neg)] at this
    norm_num at this
  have h3pos : (0 : ℝ) < 3 := three_pos
  refine ⟨hprim, hne, ho, by rw [ho.logDeriv_gammaFactor]; norm_num, ?_, ?_, ?_⟩
  · simpa using re_logDeriv_Gammaℝ_ofReal_neg h3pos (by linarith [Real.two_le_pi])
  · simpa using norm_logDeriv_Gammaℝ_ofReal_le (s := 3) ⟨by norm_num, le_rfl⟩
  · intro β hβ hzero
    simpa using χ.one_div_sub_le_re_logDeriv_LFunction_add hprim hne hβ hzero
      (σ := 2) ⟨by norm_num, le_rfl⟩

end TauCeti.LFunctions
