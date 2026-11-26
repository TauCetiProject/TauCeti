/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz

/-!
# Trailing coefficients of analytic germs, under scaling, and on the real axis

At an analytic germ of order `n`, the trailing coefficient is the `n`-th Taylor coefficient
(`AnalyticAt.meromorphicTrailingCoeffAt_eq_inv_factorial_smul_iteratedDeriv`).
Dividing the germ by the corresponding power of the displacement tends to this coefficient
(`AnalyticAt.tendsto_inv_pow_smul_meromorphicTrailingCoeffAt`).

Mathlib's `meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt` shows that the
trailing coefficient is invariant under translation of the variable. Scaling the variable by a
nonzero constant `c` instead multiplies it by `c ^ n`, where `n` is the meromorphic order:
`TauCeti.meromorphicTrailingCoeffAt_comp_mul_const`. Both are special cases of Mathlib's
`MeromorphicAt.meromorphicTrailingCoeffAt_comp`.

At a real pole, real values bounded below to its right imply a positive real trailing
coefficient: multiplication by the positive power cancelling the pole sends the lower bound to
zero.
-/

public section

open Filter Topology

/-- Dividing an analytic germ of finite order `n` by the `n`-th power of the displacement
tends to its trailing coefficient, also for vector-valued germs. -/
theorem AnalyticAt.tendsto_inv_pow_smul_meromorphicTrailingCoeffAt
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜} {n : ℕ}
    (hf : AnalyticAt 𝕜 f x) (hn : analyticOrderAt f x = n) :
    Tendsto (fun z ↦ ((z - x) ^ n)⁻¹ • f z) (𝓝[≠] x)
      (𝓝 (meromorphicTrailingCoeffAt f x)) := by
  have hord : meromorphicOrderAt f x = ((n : ℤ) : WithTop ℤ) := by
    rw [hf.meromorphicOrderAt_eq, hn, ENat.map_natCast]
  have hnormalized : ((· - x) ^ (-(n : ℤ)) • f) =
      fun z ↦ ((z - x) ^ n)⁻¹ • f z := by
    funext z
    simp [zpow_neg]
  simpa only [hord, WithTop.untop₀_coe, hnormalized] using
    hf.meromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt

/-- At an analytic point of finite order `n`, the trailing coefficient is the Taylor
coefficient of degree `n`. -/
theorem AnalyticAt.meromorphicTrailingCoeffAt_eq_inv_factorial_smul_iteratedDeriv
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} {n : ℕ}
    (hf : AnalyticAt 𝕜 f x) (hn : analyticOrderAt f x = n) :
    meromorphicTrailingCoeffAt f x = (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f x := by
  obtain ⟨g, hg, hg₀, heq⟩ := hf.analyticOrderAt_eq_natCast.mp hn
  have hlocal : f =ᶠ[𝓝 x] fun z ↦ (z - x) ^ n • g z := heq
  have hpunct : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ (n : ℤ) • g z := by
    simpa only [zpow_natCast] using hlocal.filter_mono nhdsWithin_le_nhds
  rw [hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hg₀ hpunct,
    hlocal.iteratedDeriv_eq n,
    TauCeti.iteratedDeriv_pow_sub_smul_self hg.contDiffAt,
    ← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)]

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Scaling the variable by a nonzero constant `c` multiplies the trailing coefficient by
`c ^ n`, where `n` is the meromorphic order at the scaled point. -/
theorem meromorphicTrailingCoeffAt_comp_mul_const {f : 𝕜 → E} {x c : 𝕜} (hc : c ≠ 0) :
    meromorphicTrailingCoeffAt (f ∘ (· * c)) x =
      c ^ (meromorphicOrderAt f (x * c)).untop₀ • meromorphicTrailingCoeffAt f (x * c) := by
  classical
  by_cases hf : MeromorphicAt f (x * c)
  · have hlin : (fun z ↦ z * c - x * c) = (fun _ ↦ c) * (· - x) := by
      funext z
      simp only [Pi.mul_apply]
      ring
    have hnc : ¬EventuallyConst (· * c) (𝓝 x) := by
      have hg : AnalyticAt 𝕜 (· * c) x := by fun_prop
      simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top,
        hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by simp [hc])]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (g := (· * c)) hf (by fun_prop) hnc, hlin,
      analyticAt_const.meromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop),
      meromorphicTrailingCoeffAt_const, meromorphicTrailingCoeffAt_id_sub_const]
    simp
  · have hcomp : ¬MeromorphicAt (f ∘ (· * c)) x := fun h ↦ hf <| by
      simpa [Function.comp_def, mul_assoc, hc] using
        (show MeromorphicAt (f ∘ (· * c)) ((x * c) * c⁻¹) by simpa [hc] using h).comp_analyticAt
          (g := (· * c⁻¹)) (by fun_prop)
    simp [hf, hcomp]

/-- At a pole `x` of `F`, subtracting `F` from a function analytic at `x` negates the trailing
coefficient. -/
theorem _root_.AnalyticAt.meromorphicTrailingCoeffAt_fun_sub_of_neg {P F : 𝕜 → E} {x : 𝕜}
    (hP : AnalyticAt 𝕜 P x) (hF : meromorphicOrderAt F x < 0) :
    meromorphicTrailingCoeffAt (fun z ↦ P z - F z) x = -meromorphicTrailingCoeffAt F x := by
  have hlt : meromorphicOrderAt (fun z ↦ -F z) x < meromorphicOrderAt P x := by
    rw [← meromorphicOrderAt_fun_neg]
    exact hF.trans_le hP.meromorphicOrderAt_nonneg
  simpa only [meromorphicTrailingCoeffAt_fun_neg, sub_eq_add_neg, add_comm (P _)] using
    hP.meromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt hlt

/-- At a real pole of `F`, the trailing coefficient is positive real if the values just to its
right on the real axis are real and bounded below. -/
theorem meromorphicTrailingCoeffAt_pos_of_eventually_real_bddBelow
    {F : ℂ → ℂ} {β M : ℝ} (hp : meromorphicOrderAt F (β : ℂ) < 0)
    (h : ∀ᶠ (t : ℝ) in 𝓝[>] β, (F (t : ℂ)).im = 0 ∧ M ≤ (F (t : ℂ)).re) :
    0 < (meromorphicTrailingCoeffAt F (β : ℂ)).re ∧
      (meromorphicTrailingCoeffAt F (β : ℂ)).im = 0 := by
  have hF := meromorphicAt_of_meromorphicOrderAt_ne_zero hp.ne
  have hfin : meromorphicOrderAt F (β : ℂ) ≠ ⊤ := hp.ne_top
  let m := -(meromorphicOrderAt F (β : ℂ)).untop₀
  have hm : 0 < m := by
    apply neg_pos.mpr
    exact WithTop.coe_lt_coe.mp (by rwa [WithTop.coe_untop₀_of_ne_top hfin])
  have ht : Tendsto Complex.ofReal (𝓝[>] β) (𝓝[≠] (β : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi β)] with t ht
    simpa using (Set.mem_Ioi.mp ht).ne'
  have hlim : Tendsto (fun t : ℝ ↦ (↑((t - β) ^ m) : ℂ) * F t) (𝓝[>] β)
      (𝓝 (meromorphicTrailingCoeffAt F (β : ℂ))) := by
    refine (hF.tendsto_nhds_meromorphicTrailingCoeffAt.comp ht).congr fun t ↦ ?_
    simp only [Function.comp_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply, m,
      Complex.ofReal_zpow, Complex.ofReal_sub]
  have hIm : (meromorphicTrailingCoeffAt F (β : ℂ)).im = 0 := by
    apply tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp hlim)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h] with t ht
    simp only [Function.comp_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      ht.1, mul_zero, zero_mul, add_zero]
  have hM : Tendsto (fun t : ℝ ↦ (t - β) ^ m * M) (𝓝[>] β) (𝓝 0) := by
    lift m to ℕ using hm.le with n hn
    have hc : ContinuousAt (fun t : ℝ ↦ (t - β) ^ n * M) β := by fun_prop
    have hzero : n ≠ 0 := by exact_mod_cast hm.ne'
    simpa [hzero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi β))
  have hRe : 0 ≤ (meromorphicTrailingCoeffAt F (β : ℂ)).re := by
    refine le_of_tendsto_of_tendsto hM (Complex.continuous_re.continuousAt.tendsto.comp hlim) ?_
    filter_upwards [h, self_mem_nhdsWithin (s := Set.Ioi β)] with t ht htβ
    simpa only [Function.comp_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left ht.2 (zpow_nonneg (sub_nonneg.mpr (Set.mem_Ioi.mp htβ).le) m)
  refine ⟨hRe.lt_of_ne ?_, hIm⟩
  intro he
  exact hF.meromorphicTrailingCoeffAt_ne_zero hfin (Complex.ext he.symm hIm)

end TauCeti
