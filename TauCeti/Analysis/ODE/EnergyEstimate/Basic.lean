/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Energy estimates for a first-order operator on the line

For a continuously differentiable family of operators `A(s)` on a real inner product
space, symmetric wherever the path is nonzero, integration by parts gives

`∫ ‖u' + A u‖² = ∫ ‖u'‖² + ∫ ‖A u‖² - ∫ ⟪u, A' u⟫`.

We prove this identity for compactly supported `C¹` paths, without a finite-dimensionality or
completeness assumption on the target. A spectral gap for `A` and a small upper bound on the
quadratic form of `A'` give a coercive estimate. A second integration by parts, against a `C¹`
family `S(s)` of symmetric operators, gives

`∫ ⟪S (u' + A u), u⟫ = ∫ ⟪S A u, u⟫ - ½ ∫ ⟪S' u, u⟫`

for any continuous family `A`, with no symmetry of `A` assumed
(`TauCeti.integral_inner_apply_deriv_add_eq`). When `⟪S A v, v⟫ - ½ ⟪S' v, v⟫` is coercive outside
a set `I` and bounded below on `I`, this controls `∫ ‖u‖²` by `∫ ‖u' + A u‖²` and `∫_I ‖u‖²`
(`TauCeti.half_mul_integral_norm_sq_le`); `∫ ‖u'‖²` is then controlled by
`TauCeti.integral_norm_deriv_sq_le`. A `C¹` family of symmetric operators passing from one
symmetric operator to another across a bounded interval is provided by
`TauCeti.exists_contDiff_isSymmetric_interpolation`. Global estimates with an interior
error and coercivity outside a compact interval are developed in `EnergyEstimate.Global`. These
estimates for bounded coefficients are inputs to the Fredholm property
of `d/ds + A(s)`; they do not assert surjectivity or the Fredholm property, nor treat unbounded
transverse operators on a strip.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A (first-order Fredholm operators).
* M. Schwarz, *Morse Homology*, Chapter 2 (linearized trajectory operators).
-/

public section

namespace TauCeti

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : ℝ → E →L[ℝ] E} {u : ℝ → E}

/-- The squared coefficient norm and coefficient-derivative quadratic form are integrable
along a compactly supported continuous path. -/
theorem integrable_norm_apply_sq_and_inner_deriv_apply (hA : ContDiff ℝ 1 A) (hu : Continuous u)
    (hc : HasCompactSupport u) :
    Integrable (fun s ↦ ‖A s (u s)‖ ^ 2) ∧
      Integrable (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) := by
  have hAu : HasCompactSupport (fun s ↦ A s (u s)) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcorr : HasCompactSupport (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcA : HasCompactSupport (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    hAu.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiA : Integrable (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    ((hA.continuous.clm_apply hu).norm.pow 2).integrable_of_hasCompactSupport hcA
  have hiCorr : Integrable (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.inner (hA.continuous_deriv_one.clm_apply hu)) hcorr
  exact ⟨hiA, hiCorr⟩

/-- The energy identity for `d/ds + A(s)`. The coefficient derivative contributes with a minus
sign. Symmetry is needed only on the support of the path, and is not assumed separately for the
coefficient derivative. -/
theorem integral_norm_deriv_add_sq_eq (hA : ContDiff ℝ 1 A)
    (hsym : ∀ s ∈ Function.support u, (A s).toLinearMap.IsSymmetric) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) =
      (∫ s, ‖deriv u s‖ ^ 2) + (∫ s, ‖A s (u s)‖ ^ 2) -
        ∫ s, ⟪u s, deriv A s (u s)⟫_ℝ := by
  -- Compact support makes every term in the integration-by-parts identity integrable.
  obtain ⟨hiA, hiCorr⟩ := integrable_norm_apply_sq_and_inner_deriv_apply hA hu.continuous hc
  have hpot : HasCompactSupport (fun s ↦ ⟪u s, A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcross : HasCompactSupport (fun s ↦ ⟪deriv u s, A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcD : HasCompactSupport (fun s ↦ ‖deriv u s‖ ^ 2) :=
    hc.deriv.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiD : Integrable (fun s ↦ ‖deriv u s‖ ^ 2) :=
    (hu.continuous_deriv_one.norm.pow 2).integrable_of_hasCompactSupport hcD
  have hiCross : Integrable (fun s ↦ ⟪deriv u s, A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous_deriv_one.inner (hA.continuous.clm_apply hu.continuous)) hcross
  -- Differentiate the potential `⟪u, A u⟫`, then integrate its derivative over the line.
  have hder (s : ℝ) : HasDerivAt (fun s ↦ ⟪u s, A s (u s)⟫_ℝ)
      (2 * ⟪deriv u s, A s (u s)⟫_ℝ + ⟪u s, deriv A s (u s)⟫_ℝ) s := by
    convert (hu.differentiable one_ne_zero s).hasDerivAt.inner ℝ
      ((hA.differentiable one_ne_zero s).hasDerivAt.clm_apply
        (hu.differentiable one_ne_zero s).hasDerivAt) using 1
    simp only [inner_add_right]
    by_cases hs : u s = 0
    · simp [hs]
    · rw [← (hsym s hs).apply_clm (u s) (deriv u s),
        real_inner_comm (A s (u s)) (deriv u s)]
      ring
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hder
    ((hiCross.const_mul 2).add hiCorr)
    ((hu.inner ℝ (hA.clm_apply hu)).continuous.integrable_of_hasCompactSupport hpot)
  rw [integral_add (hiCross.const_mul 2) hiCorr, integral_const_mul] at hzero
  have hexpand : (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) =
      (∫ s, ‖deriv u s‖ ^ 2) + 2 * (∫ s, ⟪deriv u s, A s (u s)⟫_ℝ) +
        ∫ s, ‖A s (u s)‖ ^ 2 := by
    simp only [norm_add_sq_real]
    have hiSum : Integrable (fun s ↦ ‖deriv u s‖ ^ 2 + 2 * ⟪deriv u s, A s (u s)⟫_ℝ) :=
      hiD.add (hiCross.const_mul 2)
    rw [integral_add hiSum hiA, integral_add hiD (hiCross.const_mul 2), integral_const_mul]
  linarith

/-- The integrand `⟪T w, u⟫` is integrable when `T` and `w` are continuous and `u` is a compactly
supported continuous path. -/
theorem integrable_inner_apply_of_hasCompactSupport {T : ℝ → E →L[ℝ] E} {w : ℝ → E}
    (hT : Continuous T) (hw : Continuous w) (hu : Continuous u) (hc : HasCompactSupport u) :
    Integrable fun s ↦ ⟪T s (w s), u s⟫_ℝ :=
  ((hT.clm_apply hw).inner hu).integrable_of_hasCompactSupport
    (hc.mono fun s hs hu0 ↦ hs (by simp [hu0]))

omit [InnerProductSpace ℝ E] in
/-- The squared norm of a compactly supported continuous path is integrable. -/
theorem integrable_norm_sq_of_hasCompactSupport {w : ℝ → E} (hw : Continuous w)
    (hc : HasCompactSupport w) : Integrable fun s ↦ ‖w s‖ ^ 2 := by
  have hcs : HasCompactSupport fun s ↦ ‖w s‖ ^ 2 :=
    hc.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  exact (hw.norm.pow 2).integrable_of_hasCompactSupport hcs

/-- **Integration by parts against a family of quadratic forms.** For a `C¹` family `S` of
symmetric operators, a continuous family `A` and a compactly supported `C¹` path `u`,

`∫ ⟪S (u' + A u), u⟫ = ∫ ⟪S A u, u⟫ - ½ ∫ ⟪S' u, u⟫`. -/
theorem integral_inner_apply_deriv_add_eq {S : ℝ → E →L[ℝ] E} (hS : ContDiff ℝ 1 S)
    (hsym : ∀ s, (S s : E →ₗ[ℝ] E).IsSymmetric) (hA : Continuous A) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    ∫ s, ⟪S s (deriv u s + A s (u s)), u s⟫_ℝ =
      (∫ s, ⟪S s (A s (u s)), u s⟫_ℝ) - (∫ s, ⟪deriv S s (u s), u s⟫_ℝ) / 2 := by
  have hiD := integrable_inner_apply_of_hasCompactSupport hS.continuous hu.continuous_deriv_one
    hu.continuous hc
  have hiA := integrable_inner_apply_of_hasCompactSupport hS.continuous
    (hA.clm_apply hu.continuous) hu.continuous hc
  have hiS := integrable_inner_apply_of_hasCompactSupport hS.continuous_deriv_one hu.continuous
    hu.continuous hc
  have hiq := integrable_inner_apply_of_hasCompactSupport hS.continuous hu.continuous
    hu.continuous hc
  have hder (s : ℝ) : HasDerivAt (fun s ↦ ⟪S s (u s), u s⟫_ℝ)
      (⟪deriv S s (u s), u s⟫_ℝ + 2 * ⟪S s (deriv u s), u s⟫_ℝ) s := by
    have hus := (hu.differentiable one_ne_zero s).hasDerivAt
    convert ((hS.differentiable one_ne_zero s).hasDerivAt.clm_apply hus).inner ℝ hus using 1
    rw [inner_add_left, (hsym s).apply_clm (u s) (deriv u s),
      real_inner_comm (S s (deriv u s)) (u s)]
    ring
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hder (hiS.add (hiD.const_mul 2)) hiq
  rw [integral_add hiS (hiD.const_mul 2), integral_const_mul] at hzero
  simp only [map_add, inner_add_left]
  rw [integral_add hiD hiA]
  linarith

/-- The estimate given by a family of quadratic forms: if `⟪S A v, v⟫ - ½ ⟪S' v, v⟫` is at least
`c ‖v‖²` outside a set `I` and at least `-K ‖v‖²` on `I`, and `‖S‖ ≤ M`, then
`c/2 ∫ ‖u‖² ≤ M²/(2c) ∫ ‖u' + A u‖² + (K + c) ∫_I ‖u‖²`. -/
theorem half_mul_integral_norm_sq_le {S : ℝ → E →L[ℝ] E} (hS : ContDiff ℝ 1 S)
    (hsym : ∀ s, (S s : E →ₗ[ℝ] E).IsSymmetric) (hA : Continuous A) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) {I : Set ℝ} (hI : MeasurableSet I) {c M K : ℝ} (hc0 : 0 < c)
    (hM : ∀ s, ‖S s‖ ≤ M)
    (hout : ∀ s ∉ I, ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S s (A s v), v⟫_ℝ - ⟪deriv S s v, v⟫_ℝ / 2)
    (hin : ∀ s ∈ I, ∀ v, -K * ‖v‖ ^ 2 ≤ ⟪S s (A s v), v⟫_ℝ - ⟪deriv S s v, v⟫_ℝ / 2) :
    c / 2 * ∫ s, ‖u s‖ ^ 2 ≤
      M ^ 2 / (2 * c) * (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) + (K + c) * ∫ s in I, ‖u s‖ ^ 2 := by
  have hiu := integrable_norm_sq_of_hasCompactSupport hu.continuous hc
  have hcD : HasCompactSupport fun s ↦ deriv u s + A s (u s) :=
    hc.deriv.add (hc.mono fun s hs hu0 ↦ hs (by simp [hu0]))
  have hiDu := integrable_norm_sq_of_hasCompactSupport (w := fun s ↦ deriv u s + A s (u s))
    (hu.continuous_deriv_one.add (hA.clm_apply hu.continuous)) hcD
  have hiI : Integrable fun s ↦ I.indicator (fun s ↦ ‖u s‖ ^ 2) s := hiu.indicator hI
  have hiA := integrable_inner_apply_of_hasCompactSupport hS.continuous
    (hA.clm_apply hu.continuous) hu.continuous hc
  have hiS := integrable_inner_apply_of_hasCompactSupport hS.continuous_deriv_one hu.continuous
    hu.continuous hc
  have hiSD := integrable_inner_apply_of_hasCompactSupport (w := fun s ↦ deriv u s + A s (u s))
    hS.continuous (hu.continuous_deriv_one.add (hA.clm_apply hu.continuous)) hu.continuous hc
  -- Pointwise lower bound for the right side of the integration-by-parts identity.
  have hlow (s : ℝ) : c * ‖u s‖ ^ 2 - (K + c) * I.indicator (fun s ↦ ‖u s‖ ^ 2) s ≤
      ⟪S s (A s (u s)), u s⟫_ℝ - ⟪deriv S s (u s), u s⟫_ℝ / 2 := by
    by_cases hs : s ∈ I
    · rw [indicator_of_mem hs]
      linarith [hin s hs (u s)]
    · rw [indicator_of_notMem hs, mul_zero, sub_zero]
      exact hout s hs (u s)
  -- Pointwise upper bound for the left side, by Cauchy–Schwarz and `2ab ≤ a² + b²`.
  have hup (s : ℝ) : ⟪S s (deriv u s + A s (u s)), u s⟫_ℝ ≤
      c / 2 * ‖u s‖ ^ 2 + M ^ 2 / (2 * c) * ‖deriv u s + A s (u s)‖ ^ 2 := by
    set w := deriv u s + A s (u s)
    have h₁ : ⟪S s w, u s⟫_ℝ ≤ M * ‖w‖ * ‖u s‖ :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right ((S s).le_of_opNorm_le (hM s) w) (norm_nonneg _))
    have h₂ : 2 * c * (c / 2 * ‖u s‖ ^ 2 + M ^ 2 / (2 * c) * ‖w‖ ^ 2) =
        c ^ 2 * ‖u s‖ ^ 2 + M ^ 2 * ‖w‖ ^ 2 := by
      field_simp
    refine h₁.trans (le_of_mul_le_mul_left ?_ (by positivity : 0 < 2 * c))
    rw [h₂]
    nlinarith [sq_nonneg (c * ‖u s‖ - M * ‖w‖)]
  have hL := integral_mono ((hiu.const_mul c).sub (hiI.const_mul (K + c)))
    (hiA.sub (hiS.div_const 2)) hlow
  have hU := integral_mono hiSD ((hiu.const_mul (c / 2)).add (hiDu.const_mul _)) hup
  simp only [Pi.sub_apply, Pi.add_apply] at hL hU
  rw [integral_sub (hiu.const_mul c) (hiI.const_mul (K + c)), integral_const_mul,
    integral_const_mul, integral_indicator hI, integral_sub hiA (hiS.div_const 2),
    integral_div] at hL
  rw [integral_add (hiu.const_mul (c / 2)) (hiDu.const_mul _), integral_const_mul,
    integral_const_mul, integral_inner_apply_deriv_add_eq hS hsym hA hu hc] at hU
  linarith

/-- A `C¹` family of symmetric operators equal to `Sm` on `(-∞, -R]` and to `Sp` on `[R, ∞)`, with
norm at most `‖Sm‖ + ‖Sp - Sm‖`. It interpolates through `Real.smoothTransition`. -/
theorem exists_contDiff_isSymmetric_interpolation {Sm Sp : E →L[ℝ] E}
    (hSm : (Sm : E →ₗ[ℝ] E).IsSymmetric) (hSp : (Sp : E →ₗ[ℝ] E).IsSymmetric) {R : ℝ}
    (hR : 0 < R) :
    ∃ S : ℝ → E →L[ℝ] E, ContDiff ℝ 1 S ∧ (∀ s, (S s : E →ₗ[ℝ] E).IsSymmetric) ∧
      (∀ s ≤ -R, S s = Sm) ∧ (∀ s, R ≤ s → S s = Sp) ∧
      (∀ s ∉ Icc (-R) R, deriv S s = 0) ∧ ∀ s, ‖S s‖ ≤ ‖Sm‖ + ‖Sp - Sm‖ := by
  set σ : ℝ → ℝ := fun s ↦ Real.smoothTransition ((s + R) / (2 * R))
  set S : ℝ → E →L[ℝ] E := fun s ↦ Sm + σ s • (Sp - Sm)
  have hSbot (s : ℝ) (hs : s ≤ -R) : S s = Sm := by
    have : σ s = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    simp [S, this]
  have hStop (s : ℝ) (hs : R ≤ s) : S s = Sp := by
    have : σ s = 1 := Real.smoothTransition.one_of_one_le
      (by rw [le_div_iff₀ (by positivity)]; linarith)
    simp [S, this]
  refine ⟨S, contDiff_const.add
    ((Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)).smul
      contDiff_const), fun s x y ↦ ?_, hSbot, hStop, fun s hs ↦ ?_, fun s ↦ ?_⟩
  · simp only [S, ContinuousLinearMap.coe_coe, add_apply, smul_apply, sub_apply, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      hSm.apply_clm, hSp.apply_clm, RCLike.conj_to_real]
  · -- Off `[-R, R]` the family is locally constant.
    rcases lt_or_ge s (-R) with h | h
    · have : S =ᶠ[𝓝 s] fun _ ↦ Sm := by
        filter_upwards [Iio_mem_nhds h] with t ht using hSbot t ht.le
      rw [this.deriv_eq, deriv_const]
    · have h' : R < s := lt_of_not_ge fun h' ↦ hs ⟨h, h'⟩
      have : S =ᶠ[𝓝 s] fun _ ↦ Sp := by
        filter_upwards [Ioi_mem_nhds h'] with t ht using hStop t ht.le
      rw [this.deriv_eq, deriv_const]
  · refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)

/-- The derivative of a compactly supported `C¹` path is controlled by `u' + A u` and `u`:
`∫ ‖u'‖² ≤ 2 ∫ ‖u' + A u‖² + 2 M² ∫ ‖u‖²` when `‖A s‖ ≤ M` everywhere. -/
theorem integral_norm_deriv_sq_le (hA : Continuous A) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) {M : ℝ} (hM : ∀ s, ‖A s‖ ≤ M) :
    ∫ s, ‖deriv u s‖ ^ 2 ≤
      2 * (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) + 2 * M ^ 2 * ∫ s, ‖u s‖ ^ 2 := by
  have hiu := integrable_norm_sq_of_hasCompactSupport hu.continuous hc
  have hiDu := integrable_norm_sq_of_hasCompactSupport (w := fun s ↦ deriv u s + A s (u s))
    (hu.continuous_deriv_one.add (hA.clm_apply hu.continuous))
    (hc.deriv.add (hc.mono fun s hs hu0 ↦ hs (by simp [hu0])))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hiDu.const_mul 2)
    (hiu.const_mul _)]
  refine integral_mono (integrable_norm_sq_of_hasCompactSupport hu.continuous_deriv_one hc.deriv)
    ((hiDu.const_mul 2).add (hiu.const_mul _)) fun s ↦ ?_
  have h₁ : ‖deriv u s‖ ≤ ‖deriv u s + A s (u s)‖ + M * ‖u s‖ := by
    calc ‖deriv u s‖ = ‖(deriv u s + A s (u s)) - A s (u s)‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖deriv u s + A s (u s)‖ + ‖A s (u s)‖ := norm_sub_le _ _
      _ ≤ ‖deriv u s + A s (u s)‖ + M * ‖u s‖ := by
          gcongr
          exact (A s).le_of_opNorm_le (hM s) (u s)
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  nlinarith [sq_nonneg (‖deriv u s + A s (u s)‖ - M * ‖u s‖)]

/-- A spectral gap and a bound on the coefficient derivative give a coercive estimate for a
compactly supported path. Symmetry and both bounds need hold only where the path is nonzero.
The estimate is useful when `β < α²`, but is valid without that extra hypothesis. -/
theorem integral_norm_deriv_sq_add_mul_integral_norm_sq_le (hA : ContDiff ℝ 1 A)
    (hsym : ∀ s ∈ Function.support u, (A s).toLinearMap.IsSymmetric) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) {α β : ℝ} (hα : 0 ≤ α)
    (hgap : ∀ s ∈ Function.support u, α * ‖u s‖ ≤ ‖A s (u s)‖)
    (hsmall : ∀ s ∈ Function.support u, ⟪u s, deriv A s (u s)⟫_ℝ ≤ β * ‖u s‖ ^ 2) :
    (∫ s, ‖deriv u s‖ ^ 2) + (α ^ 2 - β) * (∫ s, ‖u s‖ ^ 2) ≤
      ∫ s, ‖deriv u s + A s (u s)‖ ^ 2 := by
  obtain ⟨hiA, hiCorr⟩ := integrable_norm_apply_sq_and_inner_deriv_apply hA hu.continuous hc
  have hcu : HasCompactSupport (fun s ↦ ‖u s‖ ^ 2) :=
    hc.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiu : Integrable (fun s ↦ ‖u s‖ ^ 2) :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hcu
  have h₁ : α ^ 2 * (∫ s, ‖u s‖ ^ 2) ≤ ∫ s, ‖A s (u s)‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hiu.const_mul _) hiA
    intro s
    by_cases hs : u s = 0
    · simp only [hs, map_zero, norm_zero, zero_pow two_ne_zero, mul_zero, le_refl]
    · simpa only [mul_pow] using
        pow_le_pow_left₀ (mul_nonneg hα (norm_nonneg _)) (hgap s hs) 2
  have h₂ : (∫ s, ⟪u s, deriv A s (u s)⟫_ℝ) ≤ β * ∫ s, ‖u s‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono hiCorr (hiu.const_mul _)
    intro s
    by_cases hs : u s = 0
    · simp only [hs, inner_zero_left, norm_zero, zero_pow two_ne_zero, mul_zero, le_refl]
    · exact hsmall s hs
  rw [integral_norm_deriv_add_sq_eq hA hsym hu hc]
  nlinarith

end TauCeti
