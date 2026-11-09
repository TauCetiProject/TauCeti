/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.ODE.TrajectoryOperator
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Normed.Operator.ClosedRange
import TauCeti.Analysis.Sobolev.GraphStep.Density
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The trajectory operator with a degenerate limit is not Fredholm

Let `A : ℝ → End(F)` be an essentially bounded family of operators on a real Banach space `F`.
If some nonzero vector `v` satisfies `A(s) v → 0` as `s → ∞` (or as `s → -∞`), for instance
because `A` has a limit `A⁺` with `A⁺ v = 0`, then the trajectory operator

`D_A u = u' + A u : W^{1,2}(ℝ, F) → L²(ℝ, F)`

is not Fredholm. Together with
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm`, this shows that for a
continuous family of operators on a finite-dimensional inner product space with symmetric limits
`A±`, `D_A` is Fredholm exactly when both limits are injective, that is, invertible
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff`, in
`TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov`).

The proof constructs an escaping approximate kernel. Fix a smooth bump `ψ` supported in
`(-1, 1)`, and put `uₙ(s) = (n + 1)^(-1/2) ψ((s - cₙ) / (n + 1)) v` up to a normalizing constant,
with centres `cₙ` so far out that `‖A(s) v‖ ≤ 1 / (n + 1)` on the support of `uₙ` and the supports
are pairwise disjoint. Then `‖uₙ‖_{L²} = 1`, `‖uₙ'‖_{L²}` is of order `1 / (n + 1)` and
`‖D_A uₙ‖_{L²} → 0`, while `‖uₙ - uₘ‖²_{L²} = 2` for `n ≠ m`. A Fredholm operator has closed range
and a finite-dimensional complemented kernel, so a bounded sequence on which it tends to zero has a
convergent subsequence (`ContinuousLinearMap.tendsto_subseq_of_cauchySeq_comp`). The sequence
`uₙ` has none.

## Main declarations

* `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_tendsto_atTop` and
  `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_tendsto_atBot`: if `A(s) v → 0` at
  `+∞` or at `-∞` for some `v ≠ 0`, then `D_A` is not Fredholm.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Theorem A (the operator `d/ds + A(s)` is Fredholm exactly when the limits
  are invertible).
* M. Schwarz, *Morse Homology*, Chapter 2 (linearized trajectory operators).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology Distributions

namespace TauCeti.WeakDerivStep

/-! ### The escaping profiles -/

/-- The smooth bump `ψ` on `ℝ`, equal to `1` on `[-1/2, 1/2]` and supported in `(-1, 1)`. -/
private def bump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

private theorem bump_ne_zero {t : ℝ} (ht : bump t ≠ 0) : |t| < 1 := by
  have h : t ∈ Function.support bump := ht
  rw [bump.support_eq] at h
  simpa [bump] using h

/-- The squares of a continuous compactly supported function are integrable. -/
private theorem integrable_sq {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable fun t ↦ g t ^ 2 := by
  simpa [sq, Pi.mul_def] using (hg.mul hg).integrable_of_hasCompactSupport hgc.mul_left

private theorem integral_bump_sq_pos : 0 < ∫ t, bump t ^ 2 := by
  have hint := integrable_sq bump.continuous bump.hasCompactSupport
  rw [integral_pos_iff_support_of_nonneg (fun t ↦ sq_nonneg _) hint]
  have hsupp : Function.support (fun t ↦ bump t ^ 2) = Metric.ball 0 1 := by
    ext t
    simpa [bump] using Set.ext_iff.1 bump.support_eq t
  rw [hsupp, Real.volume_ball]
  norm_num

/-- Translating by `c` and dilating by `r > 0` multiplies the integral by `r`. -/
private theorem integral_comp_sub_div (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ s, g ((s - c) / r) = r * ∫ t, g t := by
  rw [integral_sub_right_eq_self (μ := volume) (fun s ↦ g (s / r)) c, Measure.integral_comp_div,
    abs_of_pos hr, smul_eq_mul]

/-- The profile `s ↦ (r a)^(-1/2) ψ((s - c) / r)`, where `a = ∫ ψ²`, normalized to have unit `L²`
norm and supported in `(c - r, c + r)`. -/
private def profile (c r s : ℝ) : ℝ :=
  (√(r * ∫ t, bump t ^ 2))⁻¹ * bump ((s - c) / r)

private theorem contDiff_profile (c r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (profile c r) :=
  contDiff_const.mul (bump.contDiff.comp ((contDiff_id.sub contDiff_const).div_const r))

private theorem abs_sub_lt_of_profile_ne_zero {c r s : ℝ} (h : profile c r s ≠ 0) :
    |s - c| < |r| := by
  have hr : r ≠ 0 := by
    rintro rfl
    simp [profile] at h
  have h1 := bump_ne_zero (right_ne_zero_of_mul h)
  rwa [abs_div, div_lt_one (abs_pos.2 hr)] at h1

private theorem hasCompactSupport_profile (c r : ℝ) : HasCompactSupport (profile c r) :=
  HasCompactSupport.intro (isCompact_closedBall c |r|) fun s hs ↦ by
    by_contra h
    exact hs (Metric.mem_closedBall.2 (by
      rw [Real.dist_eq]
      exact (abs_sub_lt_of_profile_ne_zero h).le))

private theorem integrable_deriv_profile_sq (c r : ℝ) :
    Integrable fun s ↦ deriv (profile c r) s ^ 2 :=
  integrable_sq ((contDiff_profile c r).continuous_deriv (by simp))
    (hasCompactSupport_profile c r).deriv

private theorem integrable_profile_sq (c r : ℝ) : Integrable fun s ↦ profile c r s ^ 2 :=
  integrable_sq (contDiff_profile c r).continuous (hasCompactSupport_profile c r)

private theorem integral_profile_sq {c r : ℝ} (hr : 0 < r) : ∫ s, profile c r s ^ 2 = 1 := by
  have ha := integral_bump_sq_pos
  simp only [profile, mul_pow, inv_pow]
  rw [integral_const_mul, integral_comp_sub_div (fun t ↦ bump t ^ 2) c hr,
    Real.sq_sqrt (by positivity)]
  field_simp

private theorem deriv_profile (c r s : ℝ) :
    deriv (profile c r) s =
      (√(r * ∫ t, bump t ^ 2))⁻¹ * (deriv bump ((s - c) / r) * r⁻¹) := by
  have hψ : HasDerivAt bump (deriv bump ((s - c) / r)) ((s - c) / r) :=
    (bump.contDiff (n := 1).differentiable one_ne_zero _).hasDerivAt
  have hlin : HasDerivAt (fun s ↦ (s - c) / r) r⁻¹ s := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id s).sub_const c).div_const r
  exact ((hψ.comp s hlin).const_mul _).deriv

private theorem integral_deriv_profile_sq {c r : ℝ} (hr : 0 < r) :
    ∫ s, deriv (profile c r) s ^ 2 =
      (∫ t, deriv bump t ^ 2) / ((∫ t, bump t ^ 2) * r ^ 2) := by
  have ha := integral_bump_sq_pos
  simp only [deriv_profile, mul_pow, inv_pow]
  rw [integral_const_mul, integral_mul_const,
    integral_comp_sub_div (fun t ↦ deriv bump t ^ 2) c hr, Real.sq_sqrt (by positivity)]
  field_simp

/-! ### The escaping approximate kernel -/

/-- The profile as a test function on `ℝ`. -/
private def profileTest (c r : ℝ) : 𝓓((⊤ : Opens ℝ), ℝ) :=
  ⟨profile c r, contDiff_profile c r, hasCompactSupport_profile c r, by simp⟩

/-- The windows `|t - (aₙ + n + 1)| < n + 1`, that is `aₙ < t < aₙ + 2 (n + 1)`, are pairwise
disjoint when each `aₙ` lies beyond the window of every `aₘ` with `m < n`. -/
private theorem le_abs_sub_of_abs_sub_lt {a : ℕ → ℝ}
    (ha : ∀ m n, m < n → a m + 2 * ((m : ℝ) + 1) ≤ a n) {m n : ℕ} (hmn : m ≠ n) {t : ℝ}
    (ht : |t - (a m + (m + 1))| < m + 1) : (n : ℝ) + 1 ≤ |t - (a n + (n + 1))| := by
  rw [abs_lt] at ht
  rw [le_abs]
  rcases hmn.lt_or_gt with h | h
  · have := ha m n h
    right
    linarith
  · have := ha n m h
    left
    linarith

/-- Any sequence `S` is dominated in absolute value by a sequence `a` whose windows
`(aₙ, aₙ + 2 (n + 1))` are pairwise disjoint. -/
private theorem exists_abs_le_and_add_two_mul_le (S : ℕ → ℝ) :
    ∃ a : ℕ → ℝ, (∀ n, |S n| ≤ a n) ∧ ∀ m n, m < n → a m + 2 * ((m : ℝ) + 1) ≤ a n := by
  refine ⟨fun n ↦ ∑ k ∈ Finset.range n, (2 * ((k : ℝ) + 1) + |S k|) + |S n|,
    fun n ↦ le_add_of_nonneg_left (Finset.sum_nonneg fun k _ ↦ by positivity), fun m n hmn ↦ ?_⟩
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn)
    (fun k _ _ ↦ by positivity) (f := fun k : ℕ ↦ 2 * ((k : ℝ) + 1) + |S k|)
  rw [Finset.sum_range_succ] at h
  have := abs_nonneg (S n)
  dsimp only
  linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contDiff_profile_smul (w : F) (c r : ℝ) :
    ContDiff ℝ 1 fun s ↦ profile c r s • w :=
  ((contDiff_profile c r).of_le (by exact_mod_cast le_top)).smul contDiff_const

private theorem deriv_profile_smul (w : F) (c r s : ℝ) :
    deriv (fun s ↦ profile c r s • w) s = deriv (profile c r) s • w :=
  deriv_smul_const (((contDiff_profile c r).differentiable (by simp)) s) w

variable [CompleteSpace F] {A : ℝ → F →L[ℝ] F}

/-- The path `s ↦ profile c r s • w` in `W^{1,2}(ℝ, F)`. -/
private def profilePath (w : F) (c r : ℝ) : WeakDerivStep volume ⊤ 2
    (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :=
  smulRightW1pL w (W1p.ofTestFunctionₗ volume ⊤ 2 (profileTest c r))

private theorem prev_profilePath_ae_eq (w : F) (c r : ℝ) :
    ⇑(prev _ (profilePath w c r)) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ profile c r s • w :=
  prev_smulRightW1pL_ofTestFunctionₗ_ae_eq w (profileTest c r)

/-- Disjointly supported profiles are `√2` apart in `L²`. -/
private theorem norm_prev_profilePath_sub_sq {w : F} (hw : ‖w‖ = 1) {c c' r r' : ℝ} (hr : 0 < r)
    (hr' : 0 < r') (hdisj : ∀ s, profile c r s * profile c' r' s = 0) :
    ‖prev _ (profilePath w c r) - prev _ (profilePath w c' r')‖ ^ 2 = 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  have hae : (fun s ↦ ‖(prev _ (profilePath w c r) - prev _ (profilePath w c' r')) s‖ ^ 2)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ profile c r s ^ 2 + profile c' r' s ^ 2 := by
    filter_upwards [Lp.coeFn_sub (prev _ (profilePath w c r)) (prev _ (profilePath w c' r')),
      prev_profilePath_ae_eq w c r, prev_profilePath_ae_eq w c' r'] with s hs hs1 hs2
    rw [hs, Pi.sub_apply, hs1, hs2, ← sub_smul, norm_smul, hw, mul_one, Real.norm_eq_abs, sq_abs]
    linear_combination (-2 : ℝ) * hdisj s
  rw [integral_congr_ae hae, Opens.coe_top, Measure.restrict_univ,
    integral_add (integrable_profile_sq c r) (integrable_profile_sq c' r'),
    integral_profile_sq hr, integral_profile_sq hr']
  norm_num

/-- The squared `W^{1,2}` norm of a profile path is `1 + b / (a r²)`, where `a = ∫ ψ²` and
`b = ∫ ψ'²`; it does not depend on the centre. -/
private theorem norm_profilePath_sq {w : F} (hw : ‖w‖ = 1) {c r : ℝ} (hr : 0 < r) :
    ‖profilePath w c r‖ ^ 2 =
      1 + (∫ t, deriv bump t ^ 2) / ((∫ t, bump t ^ 2) * r ^ 2) := by
  have hu := prev_profilePath_ae_eq w c r
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, norm_prev_sq_eq_integral hu,
    norm_weakFDeriv_sq_eq_integral (contDiff_profile_smul w c r) hu]
  simp only [deriv_profile_smul, norm_smul, hw, mul_one, Real.norm_eq_abs, sq_abs]
  rw [integral_profile_sq hr, integral_deriv_profile_sq hr]

/-- `D_A` is small on a profile path where `‖A s w‖ ≤ ε` on the support of the profile. -/
private theorem norm_trajectoryOperator_profilePath_sq_le {w : F} (hw : ‖w‖ = 1) {c r ε : ℝ}
    (hr : 0 < r) (hA : ∀ s, |s - c| < r → ‖A s w‖ ≤ ε)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ‖trajectoryOperator AL (profilePath w c r)‖ ^ 2 ≤
      2 * ((∫ t, deriv bump t ^ 2) / ((∫ t, bump t ^ 2) * r ^ 2)) + 2 * ε ^ 2 := by
  rw [norm_trajectoryOperator_sq_eq_integral (contDiff_profile_smul w c r)
    (prev_profilePath_ae_eq w c r) AL hAL]
  calc _ ≤ ∫ s, (2 * deriv (profile c r) s ^ 2 + 2 * ε ^ 2 * profile c r s ^ 2) :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
          (((integrable_deriv_profile_sq c r).const_mul 2).add
            ((integrable_profile_sq c r).const_mul _)) (.of_forall fun s ↦ ?_)
    _ = _ := by
        rw [integral_add ((integrable_deriv_profile_sq c r).const_mul 2)
            ((integrable_profile_sq c r).const_mul _), integral_const_mul, integral_const_mul,
          integral_profile_sq hr, integral_deriv_profile_sq hr, mul_one]
  -- On the support of the profile, `‖A s w‖ ≤ ε`; off it, both sides of the bound vanish.
  have hAs : |profile c r s| * ‖A s w‖ ≤ |profile c r s| * ε := by
    by_cases h0 : profile c r s = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left (hA s ?_) (abs_nonneg _)
      simpa [abs_of_pos hr] using abs_sub_lt_of_profile_ne_zero h0
  have hsq : ‖A s (profile c r s • w)‖ ^ 2 ≤ ε ^ 2 * profile c r s ^ 2 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    calc (|profile c r s| * ‖A s w‖) ^ 2 ≤ (|profile c r s| * ε) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hAs 2
      _ = ε ^ 2 * profile c r s ^ 2 := by rw [mul_pow, sq_abs]; ring
  have hd : ‖deriv (fun s ↦ profile c r s • w) s‖ = |deriv (profile c r) s| := by
    rw [deriv_profile_smul, norm_smul, hw, mul_one, Real.norm_eq_abs]
  have htri := norm_add_le (deriv (fun s ↦ profile c r s • w) s) (A s (profile c r s • w))
  rw [hd] at htri
  nlinarith [norm_nonneg (deriv (fun s ↦ profile c r s • w) s + A s (profile c r s • w)),
    sq_nonneg (|deriv (profile c r) s| - ‖A s (profile c r s • w)‖), sq_abs (deriv (profile c r) s)]

/-- **The escaping approximate kernel.** Let `w` be a unit vector and let the windows
`|s - cₙ| < n + 1` be pairwise disjoint, with `‖A s w‖ ≤ εₙ` on the `n`-th window and `εₙ → 0`.
The profile paths `uₙ` on these windows are bounded in `W^{1,2}`, satisfy `D_A uₙ → 0` and stay
`√2` apart in `L²`, so `D_A` is not Fredholm. -/
private theorem not_isFredholm_trajectoryOperator_of_forall_abs_sub_lt {w : F} (hw : ‖w‖ = 1)
    {c ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hA : ∀ n s, |s - c n| < n + 1 → ‖A s w‖ ≤ ε n)
    (hdisj : ∀ m n, m ≠ n → ∀ s, |s - c m| < m + 1 → (n : ℝ) + 1 ≤ |s - c n|)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  intro hF
  have hr (n : ℕ) : (0 : ℝ) < n + 1 := by positivity
  set x := fun n : ℕ ↦ profilePath w (c n) (n + 1)
  set K := (∫ t, deriv bump t ^ 2) / ∫ t, bump t ^ 2
  have hK (n : ℕ) : (∫ t, deriv bump t ^ 2) / ((∫ t, bump t ^ 2) * ((n : ℝ) + 1) ^ 2) =
      K * (1 / ((n : ℝ) + 1)) ^ 2 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_div]
  have hK0 : 0 ≤ K :=
    div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) integral_bump_sq_pos.le
  have hbdd : Bornology.IsBounded (Set.range x) := by
    refine isBounded_iff_forall_norm_le.2 ⟨1 + K, Set.forall_mem_range.2 fun n ↦ ?_⟩
    have h := norm_profilePath_sq hw (c := c n) (hr n)
    have h1 : K * (1 / ((n : ℝ) + 1)) ^ 2 ≤ K := by
      refine mul_le_of_le_one_right hK0 (pow_le_one₀ (by positivity) ?_)
      rw [div_le_one (hr n)]
      linarith [n.cast_nonneg (α := ℝ)]
    rw [hK] at h
    nlinarith [norm_nonneg (x n)]
  have hTx : Tendsto (trajectoryOperator AL ∘ x) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ ↦ 2 * (K * (1 / ((n : ℝ) + 1)) ^ 2) + 2 * ε n ^ 2) atTop
        (𝓝 0) := by
      simpa using (((tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).const_mul K).const_mul 2).add
        ((hε.pow 2).const_mul 2)
    have hsq : Tendsto (fun n ↦ ‖trajectoryOperator AL (x n)‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ by positivity) (fun n ↦ (hK n) ▸
        norm_trajectoryOperator_profilePath_sq_le hw (hr n) (hA n) AL hAL) hbound
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  -- A Fredholm operator would give a convergent subsequence, but distinct terms are `√2` apart.
  obtain ⟨u, φ, hφ, hlim⟩ := (trajectoryOperator AL).tendsto_subseq_of_cauchySeq_comp
    hF.isClosed_range hF.finite_ker hF.closedComplemented_ker hbdd hTx.cauchySeq
  have hprev := ((prevL _).continuous.tendsto u).comp hlim
  have hdiff := (((hprev.comp (tendsto_add_atTop_nat 1)).sub hprev).norm.pow 2)
  have hconst (n : ℕ) : ‖prev _ (x (φ (n + 1))) - prev _ (x (φ n))‖ ^ 2 = 2 := by
    refine norm_prev_profilePath_sub_sq hw (hr _) (hr _) fun s ↦ ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    have h3 := hdisj _ _ (hφ (Nat.lt_succ_self n)).ne' s (by
      simpa [abs_of_pos (hr _)] using abs_sub_lt_of_profile_ne_zero h1)
    have h4 := abs_sub_lt_of_profile_ne_zero h2
    rw [abs_of_pos (hr _)] at h4
    linarith
  simp only [Function.comp_apply, prevL_apply, sub_self, norm_zero, hconst] at hdiff
  -- `hdiff` now says that the constant sequence `2` tends to `0`.
  norm_num [tendsto_const_nhds_iff] at hdiff

/-- **The trajectory operator with a degenerate limit at `+∞` is not Fredholm.** If `A(s) v → 0`
as `s → ∞` for some `v ≠ 0`, for instance because `A` tends to an operator `A⁺` with `A⁺ v = 0`,
then `u ↦ u' + A u` from `W^{1,2}(ℝ, F)` to `L²(ℝ, F)` is not Fredholm. The coefficient of the
operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_trajectoryOperator_of_tendsto_atTop {v : F} (hv : v ≠ 0)
    (hAv : Tendsto (fun s ↦ A s v) atTop (𝓝 0))
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  have hAw : Tendsto (fun s ↦ ‖A s (‖v‖⁻¹ • v)‖) atTop (𝓝 0) := by
    simpa [norm_smul] using (tendsto_zero_iff_norm_tendsto_zero.1 hAv).const_mul ‖v‖⁻¹
  have hS (n : ℕ) : ∃ S, ∀ s ≥ S, ‖A s (‖v‖⁻¹ • v)‖ ≤ 1 / ((n : ℝ) + 1) :=
    eventually_atTop.1 (hAw.eventually (eventually_le_nhds (by positivity)))
  choose S hS using hS
  obtain ⟨a, haS, ha⟩ := exists_abs_le_and_add_two_mul_le S
  refine not_isFredholm_trajectoryOperator_of_forall_abs_sub_lt (norm_smul_inv_norm hv)
    (c := fun n ↦ a n + (n + 1)) tendsto_one_div_add_atTop_nhds_zero_nat (fun n s hs ↦ hS n s ?_)
    (fun m n hmn s hs ↦ le_abs_sub_of_abs_sub_lt ha hmn hs) AL hAL
  rw [abs_lt] at hs
  linarith [le_abs_self (S n), haS n]

/-- **The trajectory operator with a degenerate limit at `-∞` is not Fredholm.** If `A(s) v → 0`
as `s → -∞` for some `v ≠ 0`, for instance because `A` tends to an operator `A⁻` with `A⁻ v = 0`,
then `u ↦ u' + A u` from `W^{1,2}(ℝ, F)` to `L²(ℝ, F)` is not Fredholm. The coefficient of the
operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_trajectoryOperator_of_tendsto_atBot {v : F} (hv : v ≠ 0)
    (hAv : Tendsto (fun s ↦ A s v) atBot (𝓝 0))
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  have hAw : Tendsto (fun s ↦ ‖A s (‖v‖⁻¹ • v)‖) atBot (𝓝 0) := by
    simpa [norm_smul] using (tendsto_zero_iff_norm_tendsto_zero.1 hAv).const_mul ‖v‖⁻¹
  have hS (n : ℕ) : ∃ S, ∀ s ≤ S, ‖A s (‖v‖⁻¹ • v)‖ ≤ 1 / ((n : ℝ) + 1) :=
    eventually_atBot.1 (hAw.eventually (eventually_le_nhds (by positivity)))
  choose S hS using hS
  obtain ⟨a, haS, ha⟩ := exists_abs_le_and_add_two_mul_le S
  -- The windows are the reflections of those used at `+∞`.
  have hrefl (n : ℕ) (s : ℝ) : |s - -(a n + (n + 1))| = |-s - (a n + (n + 1))| := by
    rw [← abs_neg]
    ring_nf
  refine not_isFredholm_trajectoryOperator_of_forall_abs_sub_lt (norm_smul_inv_norm hv)
    (c := fun n ↦ -(a n + (n + 1))) tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n s hs ↦ hS n s ?_) (fun m n hmn s hs ↦ ?_) AL hAL
  · rw [abs_lt] at hs
    linarith [neg_abs_le (S n), haS n]
  · rw [hrefl] at hs ⊢
    exact le_abs_sub_of_abs_sub_lt ha hmn hs

end TauCeti.WeakDerivStep
