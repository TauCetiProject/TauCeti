/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LyapunovForm
public import TauCeti.Analysis.ODE.EnergyEstimate.Basic
import TauCeti.Analysis.InnerProductSpace.Coercive
import TauCeti.Analysis.InnerProductSpace.Symmetric.Interpolation

/-!
# Global estimates for a first-order operator on the line

For symmetric coefficients, positivity of the potential `A(s)² - A'(s)` outside a
compact interval gives the global estimate

`∫ ‖u'‖² + γ ∫ ‖u‖² ≤ ∫ ‖u' + A u‖² + C ∫_{[-R,R]} ‖u‖²`.

The constants are independent of the compactly supported `C¹` path `u`, including
paths crossing the entire line. For finite-dimensional targets, the interior term
is the error supplied by compact restriction from `W^{1,2}` to `L²` on a bounded
interval in Peetre's Fredholm criterion.

We obtain the tail positivity from uniformly bounded-below limits of `A` and
vanishing limits of `A'`. The target need not be finite dimensional or complete.
The support-restricted coercivity estimate follows by making the interior error vanish.

Without symmetry or a derivative of `A`, the same kind of estimate holds when `A` is continuous
and its limits `A±` at `±∞` have Lyapunov forms (`ContinuousLinearMap.HasLyapunovForm`):

`∫ ‖u'‖² + ∫ ‖u‖² ≤ C ∫ ‖u' + A u‖² + C ∫_{[-R,R]} ‖u‖²`

(`exists_pos_nonneg_forall_integral_norm_deriv_sq_add_integral_norm_sq_le_of_hasLyapunovForm`).
Its proof integrates the quadratic form of a `C¹` family of symmetric operators interpolating
between Lyapunov forms of `A-` and `A+` (`TauCeti.half_mul_integral_norm_sq_le`).

These are estimates on classical test paths. Their extension to Sobolev paths and the Fredholm
conclusion are in `TauCeti.Analysis.ODE.EnergyEstimate.Sobolev` and
`TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*,
  2nd ed., Appendix A.1.
* M. Schwarz, *Morse Homology*, Chapter 2 (linearized trajectory operators).
-/

public section

namespace TauCeti

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : ℝ → E →L[ℝ] E}

/-- Positivity of `A² - A'` outside a compact interval gives a global energy
estimate with an interior `L²` error. No sign restriction on `γ` is needed. -/
theorem exists_nonneg_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {R γ : ℝ}
    (htail : ∀ s ∉ Icc (-R) R, ∀ v,
      γ * ‖v‖ ^ 2 ≤ ‖A s v‖ ^ 2 - ⟪v, deriv A s v⟫_ℝ) :
    ∃ C ≥ 0, ∀ (u : ℝ → E), ContDiff ℝ 1 u → HasCompactSupport u →
      (∫ s, ‖deriv u s‖ ^ 2) + γ * (∫ s, ‖u s‖ ^ 2) ≤
        (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) + C * ∫ s in Icc (-R) R, ‖u s‖ ^ 2 := by
  -- Bound the possibly negative potential in the interior by the norm of A'.
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
    hA.continuous_deriv_one.continuousOn
  let C := max (γ + M) 0
  refine ⟨C, le_max_right _ _, fun u hu hc ↦ ?_⟩
  have hcu : HasCompactSupport (fun s ↦ ‖u s‖ ^ 2) :=
    hc.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiu : Integrable (fun s ↦ ‖u s‖ ^ 2) :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hcu
  obtain ⟨hiA, hiCorr⟩ := integrable_norm_apply_sq_and_inner_deriv_apply hA hu.continuous hc
  have hpoint (s : ℝ) : γ * ‖u s‖ ^ 2 ≤
      ‖A s (u s)‖ ^ 2 - ⟪u s, deriv A s (u s)⟫_ℝ +
        C * (Icc (-R) R).indicator (fun s ↦ ‖u s‖ ^ 2) s := by
    by_cases hs : s ∈ Icc (-R) R
    · rw [indicator_of_mem hs]
      have hcorr : ⟪u s, deriv A s (u s)⟫_ℝ ≤ M * ‖u s‖ ^ 2 := by
        calc
          _ ≤ ‖u s‖ * ‖deriv A s (u s)‖ := real_inner_le_norm _ _
          _ ≤ ‖u s‖ * (M * ‖u s‖) := by
            gcongr
            exact ((deriv A s).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (hM s hs) (norm_nonneg _))
          _ = _ := by ring
      have hC : γ + M ≤ C := le_max_left _ _
      nlinarith [sq_nonneg ‖A s (u s)‖,
        mul_le_mul_of_nonneg_right hC (sq_nonneg ‖u s‖)]
    · simpa only [indicator_of_notMem hs, mul_zero, add_zero] using htail s hs (u s)
  -- Integrate the pointwise estimate and use the energy identity from Basic.
  have hiPot : Integrable (fun s ↦ ‖A s (u s)‖ ^ 2 - ⟪u s, deriv A s (u s)⟫_ℝ) :=
    hiA.sub hiCorr
  have hiErr : Integrable (fun s ↦ C * (Icc (-R) R).indicator (fun s ↦ ‖u s‖ ^ 2) s) :=
    (hiu.indicator measurableSet_Icc).const_mul C
  have hest := integral_mono (hiu.const_mul γ) (hiPot.add hiErr) hpoint
  simp only [Pi.add_apply] at hest
  rw [integral_const_mul, integral_add hiPot hiErr, integral_sub hiA hiCorr,
    integral_const_mul, integral_indicator measurableSet_Icc] at hest
  rw [integral_norm_deriv_add_sq_eq hA (fun s _ ↦ hsym s) hu hc]
  linarith

-- Convergence of the potential, rather than separate gap estimates for A and A',
-- gives the uniform tail lower bound used in the global estimate.
private theorem eventually_potential_lower_bound {l : Filter ℝ} [l.NeBot] {B : E →L[ℝ] E}
    {α : ℝ} (hα : 0 < α) (hB : ∀ v, α * ‖v‖ ≤ ‖B v‖)
    (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    (hlim : Tendsto A l (𝓝 B)) (hdlim : Tendsto (deriv A) l (𝓝 0)) :
    ∀ᶠ s in l, ∀ v, α ^ 2 / 2 * ‖v‖ ^ 2 ≤
      ‖A s v‖ ^ 2 - ⟪v, deriv A s v⟫_ℝ := by
  have hBsym : B.toLinearMap.IsSymmetric := by
    intro v w
    have hv : Tendsto (fun s ↦ A s v) l (𝓝 (B v)) :=
      ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto B).comp hlim
    have hw : Tendsto (fun s ↦ A s w) l (𝓝 (B w)) :=
      ((ContinuousLinearMap.apply ℝ E w).continuous.tendsto B).comp hlim
    exact tendsto_nhds_unique (hv.inner tendsto_const_nhds)
      ((tendsto_const_nhds.inner hw).congr'
        (Eventually.of_forall fun s ↦ ((hsym s).apply_clm v w).symm))
  have hpot : Tendsto (fun s ↦ A s * A s - deriv A s) l (𝓝 (B * B)) := by
    simpa using (hlim.mul hlim).sub hdlim
  filter_upwards [hpot (Metric.ball_mem_nhds (B * B)
    (by positivity : 0 < α ^ 2 / 2))] with s hs v
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm] at hs
  have hclose : ‖B * B - (A s * A s - deriv A s)‖ < α ^ 2 / 2 := by
    rw [norm_sub_rev]
    exact hs
  have hnorm : ‖(B * B - (A s * A s - deriv A s)) v‖ ≤ α ^ 2 / 2 * ‖v‖ :=
    ((B * B - (A s * A s - deriv A s)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hclose.le (norm_nonneg v))
  have hinner := (real_inner_le_norm v ((B * B - (A s * A s - deriv A s)) v)).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg v))
  have hgap : α ^ 2 * ‖v‖ ^ 2 ≤ ‖B v‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) (hB v) 2
  simp only [sub_apply, mul_apply_eq_comp,
    inner_sub_right, ← (hsym s).apply_clm v (A s v),
    ← hBsym.apply_clm v (B v), real_inner_self_eq_norm_sq] at hinner
  nlinarith

/-- **Global coercivity with an interior error.** Symmetric coefficients with a
common positive lower bound at both limits and derivative tending to zero satisfy
a uniform estimate for every compactly supported `C¹` path on the whole line. -/
theorem exists_pos_nonneg_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0)) :
    ∃ R > 0, ∃ C ≥ 0, ∀ (u : ℝ → E), ContDiff ℝ 1 u → HasCompactSupport u →
      (∫ s, ‖deriv u s‖ ^ 2) + (α ^ 2 / 2) * (∫ s, ‖u s‖ ^ 2) ≤
        (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) + C * ∫ s in Icc (-R) R, ‖u s‖ ^ 2 := by
  obtain ⟨rplus, hrplus⟩ := eventually_atTop.mp
    (eventually_potential_lower_bound hα hplus hsym htop hdtop)
  obtain ⟨rminus, hrminus⟩ := eventually_atBot.mp
    (eventually_potential_lower_bound hα hminus hsym hbot hdbot)
  let R := max 1 (max rplus (-rminus))
  have htail : ∀ s ∉ Icc (-R) R, ∀ v, α ^ 2 / 2 * ‖v‖ ^ 2 ≤
      ‖A s v‖ ^ 2 - ⟪v, deriv A s v⟫_ℝ := by
    intro s hs
    have hp : rplus ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    have hm : -rminus ≤ R := (le_max_right _ _).trans (le_max_right _ _)
    simp only [mem_Icc, not_and_or, not_le] at hs
    rcases hs with hs | hs
    · exact hrminus s (by linarith)
    · exact hrplus s (hp.trans hs.le)
  obtain ⟨C, hC, hest⟩ :=
    exists_nonneg_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le hA hsym htail
  exact ⟨R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), C, hC, hest⟩

/-- **Coercivity at infinity.** If the symmetric coefficients tend in operator norm to operators
with a common positive lower bound, and their derivative tends to zero at both ends, then
`d/ds + A(s)` controls the `L²` value and derivative of every compactly supported `C¹` path
supported outside one fixed compact interval. In finite dimension, invertible limits supply the
required lower bound. -/
theorem exists_pos_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0)) :
    ∃ R > 0, ∀ (u : ℝ → E), ContDiff ℝ 1 u → HasCompactSupport u →
      Function.support u ⊆ {s | R ≤ |s|} →
      (∫ s, ‖deriv u s‖ ^ 2) + (α ^ 2 / 2) * (∫ s, ‖u s‖ ^ 2) ≤
        ∫ s, ‖deriv u s + A s (u s)‖ ^ 2 := by
  obtain ⟨R, hR, C, _, hest⟩ :=
    exists_pos_nonneg_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le
      hA hsym hα hminus hplus hbot htop hdbot hdtop
  refine ⟨R, hR, fun u hu hc hs ↦ ?_⟩
  have hzero : (∫ s in Icc (-R) R, ‖u s‖ ^ 2) = 0 := by
    rw [integral_Icc_eq_integral_Ioo]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs'
    have hu0 : u s = 0 := by
      by_contra h
      exact (not_le_of_gt (abs_lt.mpr hs')) (hs h)
    simp [hu0]
  simpa only [hzero, mul_zero, add_zero] using hest u hu hc

/-! ### Hyperbolic limits -/

/-- **The trajectory estimate for hyperbolic limits on test paths.** Let `A` be a continuous
family of operators whose limits `A±` at `±∞` have Lyapunov forms. Then there are `R > 0` and
`C ≥ 0` with

`∫ ‖u'‖² + ∫ ‖u‖² ≤ C ∫ ‖u' + A u‖² + C ∫_{[-R, R]} ‖u‖²`

for every compactly supported `C¹` path `u`. -/
theorem exists_pos_nonneg_forall_integral_norm_deriv_sq_add_integral_norm_sq_le_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) :
    ∃ R > 0, ∃ C ≥ 0, ∀ u : ℝ → E, ContDiff ℝ 1 u → HasCompactSupport u →
      (∫ s, ‖deriv u s‖ ^ 2) + (∫ s, ‖u s‖ ^ 2) ≤
        C * (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) + C * ∫ s in Icc (-R) R, ‖u s‖ ^ 2 := by
  obtain ⟨Sm, hSm, cm, hcm, hm⟩ := hminus.exists_eventually_nhds
  obtain ⟨Sp, hSp, cp, hcp, hp⟩ := hplus.exists_eventually_nhds
  -- Outside `[-R, R]`, `A s` satisfies the Lyapunov inequality of the nearby limit and has
  -- bounded norm.
  obtain ⟨a, ha⟩ := eventually_atBot.mp ((hbot.eventually hm).and
    (hbot.norm.eventually (Iic_mem_nhds (lt_add_one ‖Aminus‖))))
  obtain ⟨b, hb⟩ := eventually_atTop.mp ((htop.eventually hp).and
    (htop.norm.eventually (Iic_mem_nhds (lt_add_one ‖Aplus‖))))
  set R := max (max (-a) b) 1
  have hRa : -R ≤ a := by linarith [le_max_left (-a) b, le_max_left (max (-a) b) 1]
  have hRb : b ≤ R := by linarith [le_max_right (-a) b, le_max_left (max (-a) b) 1]
  have hR : 0 < R := by linarith [le_max_right (max (-a) b) 1]
  -- The family of quadratic forms passes from `Sm` to `Sp` across `[-R, R]`.
  obtain ⟨S, hS, hsym, hSbot, hStop, hdS, hM⟩ :=
    exists_contDiff_isSymmetric_interpolation hSm hSp hR
  -- On `[-R, R]` the error term `⟪S A v, v⟫ - ½ ⟪S' v, v⟫` is bounded below by `-K ‖v‖²`.
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    (f := fun s ↦ ‖S s‖ * ‖A s‖ + ‖deriv S s‖ / 2)
    ((hS.continuous.norm.mul hA.norm).add (hS.continuous_deriv_one.norm.div_const 2)).continuousOn
  have hK' (s : ℝ) (hs : s ∈ Icc (-R) R) : ‖S s‖ * ‖A s‖ + ‖deriv S s‖ / 2 ≤ K :=
    (Real.le_norm_self _).trans (hK s hs)
  have hK₀ : 0 ≤ K := (by positivity : (0 : ℝ) ≤ ‖S 0‖ * ‖A 0‖ + ‖deriv S 0‖ / 2).trans
    (hK' 0 ⟨by linarith, by linarith⟩)
  -- A uniform bound on `A`.
  obtain ⟨KA, hKA⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hA.continuousOn
  set MA := max KA (max (‖Aminus‖ + 1) (‖Aplus‖ + 1))
  have hMA (s : ℝ) : ‖A s‖ ≤ MA := by
    rcases lt_or_ge s (-R) with hs | hs
    · exact (mem_Iic.mp (ha s (by linarith)).2).trans (le_max_of_le_right (le_max_left _ _))
    rcases le_or_gt s R with hs' | hs'
    · exact (hKA s ⟨hs, hs'⟩).trans (le_max_left _ _)
    · exact (mem_Iic.mp (hb s (by linarith)).2).trans (le_max_of_le_right (le_max_right _ _))
  set c := min cm cp
  have hc : 0 < c := lt_min hcm hcp
  refine ⟨R, hR, 2 + (2 * MA ^ 2 + 1) * (2 / c) * ((‖Sm‖ + ‖Sp - Sm‖) ^ 2 / (2 * c) + (K + c)),
    by positivity, fun u hu hcu ↦ ?_⟩
  have hY := half_mul_integral_norm_sq_le hS hsym hA hu hcu measurableSet_Icc hc hM
    (I := Icc (-R) R) (K := K) (fun s hs v ↦ by
      rw [hdS s hs, zero_apply, inner_zero_left, zero_div, sub_zero]
      rcases lt_or_ge s (-R) with h₁ | h₁
      · rw [hSbot s h₁.le]
        exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          ((ha s (by linarith)).1 v)
      · have h₂ : R < s := lt_of_not_ge fun h ↦ hs ⟨h₁, h⟩
        rw [hStop s h₂.le]
        exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
          ((hb s (by linarith)).1 v))
    (fun s hs v ↦ by
      have := mul_le_mul_of_nonneg_right (hK' s hs) (sq_nonneg ‖v‖)
      linarith [(S s).neg_mul_norm_sq_le_inner_sub (A s) (deriv S s) v])
  have hX := integral_norm_deriv_sq_le hA hu hcu hMA
  have hZ : 0 ≤ ∫ s, ‖deriv u s + A s (u s)‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  have hW : 0 ≤ ∫ s in Icc (-R) R, ‖u s‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun _ _ ↦ by positivity
  -- Solve `hY` for `∫ ‖u‖²` and substitute the result into `hX`.
  set a := (‖Sm‖ + ‖Sp - Sm‖) ^ 2 / (2 * c)
  set b := K + c
  have hY' : (∫ s, ‖u s‖ ^ 2) ≤ 2 / c * (a * (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) +
      b * ∫ s in Icc (-R) R, ‖u s‖ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  have hk : 0 ≤ (2 * MA ^ 2 + 1) * (2 / c) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hY' (by positivity : (0 : ℝ) ≤ 2 * MA ^ 2 + 1),
    mul_nonneg (mul_nonneg hk (by positivity : (0 : ℝ) ≤ b)) hZ,
    mul_nonneg (mul_nonneg hk (by positivity : (0 : ℝ) ≤ a)) hW]

end TauCeti
