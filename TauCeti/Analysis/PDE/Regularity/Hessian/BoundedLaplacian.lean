/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.PlaneWave
import TauCeti.Analysis.InnerProductSpace.Laplacian.Projection
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# A bounded Laplacian does not bound the Hessian

For `1 < p < ∞` the Calderón–Zygmund estimate `‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}` holds for every
Schwartz function `u` on a finite-dimensional real inner product space
(`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`). This file proves that it
fails at the endpoint `p = ∞` in every dimension `n ≥ 2`, even with the supremum of `|u|` added to
the right-hand side and even for smooth compactly supported functions: for every `C` there is a
smooth compactly supported `u` with `|Δu| ≤ 1` and `|u| ≤ 1` everywhere and `‖D²u(0)‖ > C`
(`TauCeti.exists_abs_laplacian_le_one_and_lt_norm_iteratedFDeriv_two`). Hence no estimate
`‖D²u‖_{L^∞} ≤ C (‖Δu‖_{L^∞} + ‖u‖_{L^∞})` holds on smooth compactly supported functions
(`TauCeti.not_exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_add_eLpNorm_top`), and the
estimate `‖D²u‖_{L^∞} ≤ C ‖Δu‖_{L^∞}` fails on Schwartz functions
(`TauCeti.not_exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_top`). Correspondingly, the
`W^{2,p}` theory of strong solutions stops short of `p = ∞`: a bounded Laplacian gives `W^{2,p}`
for every finite `p`, but not `C^{1,1}`.

The dimension hypothesis is necessary. In dimension one `‖D²u(x)‖ = |u''(x)| = |Δu(x)|`, so the
estimate holds with `C = 1`, and in dimension zero every Hessian vanishes.

## The construction

Let `q` be a smooth harmonic function with `D²q(0) ≠ 0`; in dimension at least two,
`q(x) = ⟪v, x⟫² - ⟪w, x⟫²` for orthonormal `v, w` has `Δq = 2 ‖v‖² - 2 ‖w‖² = 0` and
`D²q(0)(v, v) = 2`. Let `χ` be a smooth bump equal to `1` on the closed unit ball and vanishing
outside the ball of radius `2`, and put `φ = χ q`. Then `Δφ` vanishes on the open unit ball,
where `φ = q`, and outside the closed ball of radius `2`. Rescale by the factors `cₖ = 4ᵏ`:

`φₖ(x) = cₖ⁻² φ(cₖ x)`, so that `Δφₖ(x) = (Δφ)(cₖ x)` and `D²φₖ(0) = D²q(0)`.

The Laplacians `Δφₖ` are supported in the disjoint annuli `4⁻ᵏ ≤ ‖x‖ ≤ 2 · 4⁻ᵏ`, so the sum
`u_N = ∑_{k < N} φₖ` has `|Δu_N| ≤ sup |Δφ|`, and `|u_N| ≤ ∑ₖ 16⁻ᵏ sup |φ| ≤ 2 sup |φ|`, while
`D²u_N(0) = N D²q(0)` grows without bound. Normalizing `u_N` gives the counterexamples.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 9 (the `Lᵖ` theory and its failure at the endpoints).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II
  (singular integrals are not bounded on `L^∞`).
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Filter Topology Set Finset
open scoped ENNReal NNReal Laplacian ContDiff SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The cut-off.** A smooth harmonic function `q`, multiplied by a bump equal to `1` on the closed
unit ball and vanishing outside the ball of radius `2`, gives a smooth function `φ` vanishing
outside the ball of radius `2`, with the Hessian of `q` at the origin and with `Δφ` supported in the
closed annulus `1 ≤ ‖x‖ ≤ 2`. -/
private theorem exists_cutoff_of_harmonic {q : V → ℝ} (hq : ContDiff ℝ ∞ q)
    (hΔq : ∀ x, Δ q x = 0) :
    ∃ φ : V → ℝ, ContDiff ℝ ∞ φ ∧ (∀ x, 2 ≤ ‖x‖ → φ x = 0) ∧
      (∀ x, Δ φ x ≠ 0 → 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2) ∧
      iteratedFDeriv ℝ 2 φ 0 = iteratedFDeriv ℝ 2 q 0 := by
  let χ : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have hφq : ∀ x : V, ‖x‖ < 1 → (fun y ↦ χ y * q y) =ᶠ[𝓝 x] q := fun x hx ↦ by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  refine ⟨fun y ↦ χ y * q y, χ.contDiff.mul hq, fun x hx ↦ ?_, fun x hx ↦ ?_,
    ((hφq 0 (by simp)).iteratedFDeriv ℝ 2).eq_of_nhds⟩
  · have : χ x = 0 := Function.notMem_support.1 fun h ↦ by
      rw [χ.support_eq, mem_ball_zero_iff] at h
      exact (lt_irrefl (2 : ℝ)) (hx.trans_lt h)
    simp only [this, zero_mul]
  · refine ⟨not_lt.1 fun h ↦ hx ?_, not_lt.1 fun h ↦ hx ?_⟩
    · rw [(laplacian_congr_nhds (hφq x h)).eq_of_nhds, hΔq]
    · refine laplacian_of_notMem_tsupport fun hx' ↦ ?_
      have : x ∈ tsupport χ := tsupport_mul_subset_left hx'
      rw [χ.tsupport_eq, mem_closedBall_zero_iff] at this
      exact (lt_irrefl (2 : ℝ)) (h.trans_le this)

omit [FiniteDimensional ℝ V] in
/-- **Disjoint annuli.** If `g` is supported in the closed annulus `1 ≤ ‖y‖ ≤ 2` and bounded by `M`,
then every sum of its rescalings `y ↦ g (4ᵏ y)` over distinct `k` is bounded by `M`: the rescaled
annuli `4⁻ᵏ ≤ ‖y‖ ≤ 2 · 4⁻ᵏ` are pairwise disjoint, so at most one term is nonzero. -/
private theorem abs_sum_comp_four_pow_smul_le {g : V → ℝ}
    (hg : ∀ y, g y ≠ 0 → 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 2) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, |g y| ≤ M)
    (s : Finset ℕ) (x : V) : |∑ k ∈ s, g ((4 : ℝ) ^ k • x)| ≤ M := by
  have key : ∀ j k, j < k → g ((4 : ℝ) ^ j • x) ≠ 0 → g ((4 : ℝ) ^ k • x) = 0 := by
    intro j k hjk hj
    by_contra hk
    have hj' := (hg _ hj).1
    have hk' := (hg _ hk).2
    rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hj' hk'
    have h4 : 4 * (4 : ℝ) ^ j ≤ 4 ^ k := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) hjk
    nlinarith [norm_nonneg x]
  by_cases h : ∃ j ∈ s, g ((4 : ℝ) ^ j • x) ≠ 0
  · obtain ⟨j, hj, hj0⟩ := h
    rw [Finset.sum_eq_single_of_mem j hj fun k _ hkj ↦ by
      rcases lt_or_gt_of_ne hkj with h | h
      · exact not_not.1 fun hk ↦ hj0 (key k j h hk)
      · exact key j k h hj0]
    exact hM _
  · push Not at h
    rw [Finset.sum_eq_zero h, abs_zero]
    exact hM0

/-- **The lacunary sum.** Let `φ` be smooth, vanishing outside the ball of radius `2`, with `Δφ`
supported in the closed annulus `1 ≤ ‖x‖ ≤ 2`, `|Δφ| ≤ M` and `|φ| ≤ P`. Then
`u = ∑_{k < N} 16⁻ᵏ φ(4ᵏ ·)` is smooth and compactly supported, with `|Δu| ≤ M`, `|u| ≤ 2 P` and
`D²u(0) = N D²φ(0)`. -/
private theorem exists_lacunary_sum {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : ∀ x, 2 ≤ ‖x‖ → φ x = 0) (hΔφ : ∀ x, Δ φ x ≠ 0 → 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2) {M P : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x, |Δ φ x| ≤ M) (hP : ∀ x, |φ x| ≤ P) (N : ℕ) :
    ∃ u : V → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ (∀ x, |Δ u x| ≤ M) ∧
      (∀ x, |u x| ≤ 2 * P) ∧ iteratedFDeriv ℝ 2 u 0 = (N : ℝ) • iteratedFDeriv ℝ 2 φ 0 := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hc0 : ∀ k, (4 : ℝ) ^ k ≠ 0 := fun k ↦ pow_ne_zero _ (by norm_num)
  set ψ : ℕ → V → ℝ := fun k ↦ (((4 : ℝ) ^ k) ^ 2)⁻¹ • fun y ↦ φ ((4 : ℝ) ^ k • y) with hψ_def
  have hφk : ∀ k, ContDiff ℝ ∞ fun y ↦ φ ((4 : ℝ) ^ k • y) := fun k ↦
    hφ.comp (contDiff_const_smul _)
  have hψ : ∀ k, ContDiff ℝ ∞ (ψ k) := fun k ↦ (hφk k).const_smul (((4 : ℝ) ^ k) ^ 2)⁻¹
  have hψ2 : ∀ k ∈ range N, ContDiff ℝ 2 (ψ k) := fun k _ ↦ (hψ k).of_le (by simp)
  refine ⟨fun x ↦ ∑ k ∈ range N, ψ k x, ContDiff.sum fun k _ ↦ hψ k,
    HasCompactSupport.intro (isCompact_closedBall 0 2) fun x hx ↦ ?_, fun x ↦ ?_, fun x ↦ ?_, ?_⟩
  · -- Every piece vanishes outside the ball of radius `2`, since `4ᵏ ≥ 1`.
    rw [mem_closedBall_zero_iff, not_le] at hx
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have hck : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have : 2 ≤ ‖(4 : ℝ) ^ k • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hck)]
      nlinarith [norm_nonneg x]
    simp [hψ_def, hφ0 _ this]
  · rw [laplacian_fun_sum fun k hk ↦ (hψ2 k hk).contDiffAt]
    simp only [hψ_def, laplacian_smul_comp_smul_right (hc0 _) hφ2.contDiffAt]
    exact abs_sum_comp_four_pow_smul_le hΔφ hM0 hM _ x
  · calc |∑ k ∈ range N, ψ k x| ≤ ∑ k ∈ range N, |ψ k x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range N, (1 / 2 : ℝ) ^ k * P := Finset.sum_le_sum fun k _ ↦ by
          simp only [hψ_def, Pi.smul_apply, smul_eq_mul, abs_mul]
          refine mul_le_mul ?_ (hP _) (abs_nonneg _) (by positivity)
          -- `16⁻ᵏ ≤ 2⁻ᵏ`.
          rw [abs_of_pos (by positivity), one_div, inv_pow]
          gcongr
          calc (2 : ℝ) ^ k ≤ 4 ^ k := by gcongr; norm_num
            _ ≤ (4 ^ k) ^ 2 := le_self_pow₀ (one_le_pow₀ (by norm_num)) two_ne_zero
      _ = (∑ k ∈ range N, (1 / 2 : ℝ) ^ k) * P := by rw [Finset.sum_mul]
      _ ≤ 2 * P := mul_le_mul_of_nonneg_right (sum_geometric_two_le N)
          ((abs_nonneg _).trans (hP 0))
  · -- Each rescaling `ψ k` has the Hessian of `φ` at the origin.
    have hD : ∀ k, iteratedFDeriv ℝ 2 (ψ k) 0 = iteratedFDeriv ℝ 2 φ 0 := fun k ↦ by
      rw [hψ_def, iteratedFDeriv_const_smul_apply ((hφk k).of_le (by simp)).contDiffAt,
        iteratedFDeriv_comp_const_smul _ hφ2]
      simp only [smul_zero, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (hc0 k)), one_smul]
    rw [iteratedFDeriv_sum hψ2, Finset.sum_apply]
    simp only [hD, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]

/-- **The lacunary construction.** If `q` is a smooth harmonic function whose Hessian does not
vanish at the origin, then there are smooth compactly supported functions with `|Δu| ≤ 1` and
`|u| ≤ 1` and with arbitrarily large Hessian at the origin. -/
private theorem exists_abs_laplacian_le_one_and_lt_norm_of_harmonic {q : V → ℝ}
    (hq : ContDiff ℝ ∞ q) (hΔq : ∀ x, Δ q x = 0) (h0 : iteratedFDeriv ℝ 2 q 0 ≠ 0) (C : ℝ) :
    ∃ u : V → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ (∀ x, |Δ u x| ≤ 1) ∧
      (∀ x, |u x| ≤ 1) ∧ C < ‖iteratedFDeriv ℝ 2 u 0‖ := by
  obtain ⟨φ, hφ, hφ0, hΔφ, hD0⟩ := exists_cutoff_of_harmonic hq hΔq
  have hφc : HasCompactSupport φ := HasCompactSupport.intro (isCompact_closedBall 0 2)
    fun x hx ↦ hφ0 x (not_le.1 (by simpa using hx)).le
  obtain ⟨M, hM⟩ := (hφ.of_le (by simp)).continuous_laplacian.bounded_above_of_compact_support
    hφc.laplacian
  obtain ⟨P, hP⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  -- Normalize by `K = max (max M (2 P)) 1`, after choosing `N > C K / ‖D²q(0)‖`.
  set a := ‖iteratedFDeriv ℝ 2 q 0‖ with ha_def
  have ha : 0 < a := norm_pos_iff.2 h0
  set K := max (max M (2 * P)) 1
  have hK : 0 < K := lt_max_of_lt_right one_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (C * K / a)
  obtain ⟨u, hu, huc, hΔu, hu_le, hDu⟩ := exists_lacunary_sum hφ hφ0 hΔφ
    ((norm_nonneg _).trans (hM 0)) (fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hM x))
    (fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hP x)) N
  refine ⟨K⁻¹ • u, hu.const_smul K⁻¹, huc.smul_left, fun x ↦ ?_, fun x ↦ ?_, ?_⟩
  · rw [laplacian_smul _ (hu.of_le (by simp)).contDiffAt, smul_eq_mul, abs_mul,
      abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK, mul_one]
    exact (hΔu x).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK, mul_one]
    exact (hu_le x).trans ((le_max_right _ _).trans (le_max_left _ _))
  · rw [iteratedFDeriv_const_smul_apply (hu.of_le (by simp)).contDiffAt, hDu, hD0,
      smul_smul, norm_smul, Real.norm_of_nonneg (by positivity), ← ha_def]
    rw [div_lt_iff₀ ha] at hN
    calc C = C * K / K := by field_simp
      _ < N * a / K := by gcongr
      _ = K⁻¹ * N * a := by ring

/-- **A bounded Laplacian does not bound the Hessian.** In dimension at least two, for every `C`
there is a smooth compactly supported function `u` with `|Δu| ≤ 1` and `|u| ≤ 1` everywhere whose
Hessian at the origin has norm greater than `C`. -/
theorem exists_abs_laplacian_le_one_and_lt_norm_iteratedFDeriv_two
    (hV : 2 ≤ Module.finrank ℝ V) (C : ℝ) :
    ∃ u : V → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ (∀ x, |Δ u x| ≤ 1) ∧
      (∀ x, |u x| ≤ 1) ∧ C < ‖iteratedFDeriv ℝ 2 u 0‖ := by
  -- Two orthonormal vectors `v, w` and the harmonic quadratic `⟪v, x⟫² - ⟪w, x⟫²`.
  set b := stdOrthonormalBasis ℝ V
  set v := b ⟨0, by omega⟩
  set w := b ⟨1, by omega⟩
  have hv : ‖v‖ = 1 := b.orthonormal.1 _
  have hw : ‖w‖ = 1 := b.orthonormal.1 _
  have hvw : ⟪w, v⟫_ℝ = 0 := b.orthonormal.2 (by simp [Fin.ext_iff])
  have hsq (z : V) : ContDiff ℝ ∞ fun y : V ↦ ⟪z, y⟫_ℝ ^ 2 :=
    ((contDiff_const.inner ℝ contDiff_id).pow 2)
  set q : V → ℝ := (fun y ↦ ⟪v, y⟫_ℝ ^ 2) - fun y ↦ ⟪w, y⟫_ℝ ^ 2 with hq_def
  have hq : ContDiff ℝ ∞ q := (hsq v).sub (hsq w)
  refine exists_abs_laplacian_le_one_and_lt_norm_of_harmonic hq (fun x ↦ ?_) (fun h ↦ ?_) C
  · rw [hq_def, ((hsq v).contDiffAt.of_le (by simp)).laplacian_sub
      ((hsq w).contDiffAt.of_le (by simp)), laplacian_inner_sq,
      laplacian_inner_sq, hv, hw, sub_self]
  · -- `D²q(0)(v, v) = 2 ‖v‖⁴ - 2 ⟪w, v⟫² = 2`.
    have h2 : iteratedFDeriv ℝ 2 q 0 ![v, v] = 2 := by
      have hg : ContDiff ℝ 2 fun t : ℝ ↦ t ^ 2 := contDiff_id.pow 2
      rw [hq_def, iteratedFDeriv_sub_apply ((hsq v).contDiffAt.of_le (by simp))
        ((hsq w).contDiffAt.of_le (by simp)), sub_apply,
        iteratedFDeriv_two_comp_inner v 0 hg.contDiffAt,
        iteratedFDeriv_two_comp_inner w 0 hg.contDiffAt, hvw, real_inner_self_eq_norm_sq, hv]
      simp
    rw [h, zero_apply] at h2
    norm_num at h2

variable [MeasurableSpace V] [BorelSpace V]

/-- **The `L^∞` estimate of the Hessian by the Laplacian fails.** In dimension at least two there
is no constant `C` with `‖D²u‖_{L^∞} ≤ C (‖Δu‖_{L^∞} + ‖u‖_{L^∞})` for all smooth compactly
supported functions `u`. -/
theorem not_exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_add_eLpNorm_top
    (hV : 2 ≤ Module.finrank ℝ V) :
    ¬ ∃ C : ℝ≥0, ∀ u : V → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (iteratedFDeriv ℝ 2 u) ∞ volume ≤
        C * (eLpNorm (Δ u) ∞ volume + eLpNorm u ∞ volume) := by
  rintro ⟨C, hC⟩
  obtain ⟨u, hu, huc, hΔ, hb, hlt⟩ :=
    exists_abs_laplacian_le_one_and_lt_norm_iteratedFDeriv_two hV (2 * C)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by simp)
  have hΔ' : eLpNorm (Δ u) ∞ volume ≤ 1 := by
    rw [eLpNorm_exponent_top hu2.continuous_laplacian.aestronglyMeasurable, ← ENNReal.ofReal_one]
    exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x ↦ (hΔ x))
  have hb' : eLpNorm u ∞ volume ≤ 1 := by
    rw [eLpNorm_exponent_top hu.continuous.aestronglyMeasurable, ← ENNReal.ofReal_one]
    exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x ↦ (hb x))
  have h0 : ‖iteratedFDeriv ℝ 2 u 0‖ₑ ≤ eLpNorm (iteratedFDeriv ℝ 2 u) ∞ volume :=
    (hu2.continuous_iteratedFDeriv le_rfl).continuousAt.eNorm_le_eLpNorm_top
  have h := h0.trans ((hC u hu huc).trans (mul_le_mul_right (add_le_add hΔ' hb') _))
  have h' : ‖iteratedFDeriv ℝ 2 u 0‖ ≤ C * 2 := by
    simpa [one_add_one_eq_two] using ENNReal.toReal_mono (by finiteness) h
  linarith

/-- **The Calderón–Zygmund estimate fails at `p = ∞`.** In dimension at least two there is no
constant `C` with `‖D²u‖_{L^∞} ≤ C ‖Δu‖_{L^∞}` for all real Schwartz functions `u`, in contrast to
`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real` for `1 < p < ∞`. -/
theorem not_exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_top
    (hV : 2 ≤ Module.finrank ℝ V) :
    ¬ ∃ C : ℝ≥0, ∀ u : 𝓢(V, ℝ), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) ∞ volume ≤
      C * eLpNorm ⇑(Δ u : 𝓢(V, ℝ)) ∞ volume := by
  rintro ⟨C, hC⟩
  refine not_exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_add_eLpNorm_top hV
    ⟨C, fun u hu huc ↦ ?_⟩
  have hcoe : ⇑(huc.toSchwartzMap hu) = u := by
    ext x
    simp
  have hΔ : ⇑(Δ (huc.toSchwartzMap hu) : 𝓢(V, ℝ)) = Δ u := by
    ext x
    rw [SchwartzMap.laplacian_apply, hcoe]
  have h := hC (huc.toSchwartzMap hu)
  rw [hΔ, hcoe] at h
  exact h.trans (mul_le_mul_right le_self_add _)

end TauCeti
