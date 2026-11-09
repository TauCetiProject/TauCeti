/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Additional lemmas for interval integrals

This file records general-purpose lemmas about interval integrals `∫ x in a..b, f x ∂μ` that do
not belong to any particular application.

## Main results

* `TauCeti.intervalIntegral.monotoneOn_primitive_of_nonneg`: the primitive `t ↦ ∫ x in a..t, f x`
  of a function that is nonnegative and interval integrable on `[a, b]` is nondecreasing on
  `[a, b]`.
* `TauCeti.intervalIntegral.eq_of_integral_eq_sub`: if the increments of `F` are the interval
  integrals of a function vanishing outside `[-r, r]` with total integral zero, then `F` is
  constant outside `[-r, r]`.
* `TauCeti.intervalIntegral.integral_re_mul_im_sub_im_mul_re_eq`: a polarization identity
  expressing `∫ (x v - y u)` for `f = x + i y` and `g = u + i v` through the integrals of
  `‖g‖²`, `‖f‖²` and `‖g - i k f‖²`.
* `TauCeti.intervalIntegral.norm_sub_sub_integral_le`: the defect `a₂ - a₁ - ∫ g` from an integral
  equation changes by at most the changes of the endpoint values plus `δ |t₂ - t₁|` when the
  integrand changes by at most `δ`.
* `MeasureTheory.IntegrableOn.intervalIntegrable_of_mem_Icc`: a function integrable on `(a, b)`
  for a measure without mass at points is interval integrable between any two points of `[a, b]`.
* `ContinuousLinearEquiv.intervalIntegral_comp_comm`: a continuous linear equivalence commutes
  with interval integrals, with no integrability assumption.
* `MeasureTheory.LocallyIntegrableOn.intervalIntegrable_comp_max`: if `f` is locally integrable
  on `[c, ∞)`, then its constant extension `x ↦ f (max x c)` is interval integrable on every
  interval.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace intervalIntegral

/-- The primitive `t ↦ ∫ x in a..t, f x ∂μ` of a function that is almost everywhere nonnegative and
interval integrable on `[a, b]` is nondecreasing on `[a, b]`. -/
theorem monotoneOn_primitive_of_nonneg {f : ℝ → ℝ} {μ : Measure ℝ} {a b : ℝ}
    (hf : 0 ≤ᵐ[μ.restrict (Ioc a b)] f) (hfi : IntervalIntegrable f μ a b) :
    MonotoneOn (fun t ↦ ∫ x in a..t, f x ∂μ) (Icc a b) := fun _ hs _ ht hst ↦
  _root_.intervalIntegral.integral_mono_interval le_rfl hs.1 hst
    (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl) hf)
    (hfi.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le ht.1 ht.2)))

/-- If the increments of `F` are the interval integrals of a function `f` that vanishes outside
`[-r, r]` and has total integral zero, then `F` is constant outside `[-r, r]`. -/
theorem eq_of_integral_eq_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f F : ℝ → E} {r : ℝ} (hF : ∀ a b, ∫ t in a..b, f t = F b - F a)
    (hf : ∀ t, r < |t| → f t = 0) (h : ∫ t, f t = 0) {x y : ℝ} (hx : r < |x|) (hy : r < |y|) :
    F x = F y := by
  wlog hxy : x ≤ y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  have hxy' := hF x y
  rw [_root_.intervalIntegral.integral_of_le hxy] at hxy'
  refine (sub_eq_zero.mp (hxy'.symm.trans ?_)).symm
  rcases lt_abs.mp hx with hx | hx <;> rcases lt_abs.mp hy with hy | hy
  · -- Both points lie to the right of `[-r, r]`, so `f` vanishes between them.
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ hf t (lt_abs.mpr (.inl ?_))
    linarith [ht.1]
  · -- `r < x ≤ y < -r` forces `r < 0`, so `f` vanishes everywhere.
    exact setIntegral_eq_zero_of_forall_eq_zero fun t _ ↦ hf t (by linarith [abs_nonneg t])
  · -- The interval `(x, y]` contains `[-r, r]`, so the integral over it is the total integral.
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ hf t ?_, h]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
    exact lt_abs.mpr (ht.elim (fun ht ↦ .inr (by linarith)) fun ht ↦ .inl (by linarith))
  · -- Both points lie to the left of `[-r, r]`, so `f` vanishes between them.
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ hf t (lt_abs.mpr (.inr ?_))
    linarith [ht.2]

/-- A polarization identity for complex functions `f = x + i y` and `g = u + i v`, square
integrable on `uIoc a b`: for real `k ≠ 0`,
`∫ₐᵇ (x v - y u) = (∫ₐᵇ ‖g‖² + k² ∫ₐᵇ ‖f‖² - ∫ₐᵇ ‖g - i k f‖²) / (2k)`.
For a curve `f` with velocity `g`, the left side is twice the signed area of `f`. -/
theorem integral_re_mul_im_sub_im_mul_re_eq {a b : ℝ} {k : ℝ} (hk : k ≠ 0)
    {f g : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (uIoc a b)))
    (hg : MemLp g 2 (volume.restrict (uIoc a b))) :
    (∫ t in a..b, ((f t).re * (g t).im - (f t).im * (g t).re)) =
      ((∫ t in a..b, ‖g t‖ ^ 2) + k ^ 2 * (∫ t in a..b, ‖f t‖ ^ 2) -
        ∫ t in a..b, ‖g t - (k * Complex.I) * f t‖ ^ 2) / (2 * k) := by
  have hint {h : ℝ → ℂ} (hh : MemLp h 2 (volume.restrict (uIoc a b))) :
      IntervalIntegrable (fun t ↦ ‖h t‖ ^ 2) volume a b :=
    intervalIntegrable_iff.2 (hh.integrable_norm_pow two_ne_zero)
  have hG := hint hg
  have hF := hint hf
  have hH := hint (h := fun t ↦ g t - (k * Complex.I) * f t) (hg.sub (hf.const_mul _))
  -- Pointwise, `‖g - i k f‖² = ‖g‖² + k² ‖f‖² - 2 k (x v - y u)`.
  have hpt (t : ℝ) : (f t).re * (g t).im - (f t).im * (g t).re =
      (‖g t‖ ^ 2 + k ^ 2 * ‖f t‖ ^ 2 - ‖g t - (k * Complex.I) * f t‖ ^ 2) / (2 * k) := by
    field_simp
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  simp_rw [hpt]
  rw [_root_.intervalIntegral.integral_div,
    _root_.intervalIntegral.integral_sub (hG.add (hF.const_mul _)) hH,
    _root_.intervalIntegral.integral_add hG (hF.const_mul _),
    _root_.intervalIntegral.integral_const_mul]

/-- The defect `a₂ - a₁ - ∫ g` from an integral equation over `[t₁, t₂]` differs from the defect
`b₂ - b₁ - ∫ g'` by at most `‖a₁ - b₁‖ + ‖a₂ - b₂‖ + δ |t₂ - t₁|` when `‖g - g'‖ ≤ δ` on the
interval. -/
theorem norm_sub_sub_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a₁ a₂ b₁ b₂ : E} {g g' : ℝ → E} {t₁ t₂ δ : ℝ} (hg : IntervalIntegrable g volume t₁ t₂)
    (hg' : IntervalIntegrable g' volume t₁ t₂) (hgg : ∀ t ∈ uIoc t₁ t₂, ‖g t - g' t‖ ≤ δ) :
    ‖a₂ - a₁ - ∫ t in t₁..t₂, g t‖ ≤
      ‖b₂ - b₁ - ∫ t in t₁..t₂, g' t‖ + ‖a₁ - b₁‖ + ‖a₂ - b₂‖ + δ * |t₂ - t₁| := by
  have hI : ‖∫ t in t₁..t₂, (g t - g' t)‖ ≤ δ * |t₂ - t₁| :=
    _root_.intervalIntegral.norm_integral_le_of_norm_le_const hgg
  have hsplit : a₂ - a₁ - ∫ t in t₁..t₂, g t = (b₂ - b₁ - ∫ t in t₁..t₂, g' t) + (a₂ - b₂) -
      (a₁ - b₁) - ∫ t in t₁..t₂, (g t - g' t) := by
    rw [_root_.intervalIntegral.integral_sub hg hg']
    abel
  rw [hsplit]
  linarith [norm_sub_le ((b₂ - b₁ - ∫ t in t₁..t₂, g' t) + (a₂ - b₂) - (a₁ - b₁))
      (∫ t in t₁..t₂, (g t - g' t)),
    norm_sub_le ((b₂ - b₁ - ∫ t in t₁..t₂, g' t) + (a₂ - b₂)) (a₁ - b₁),
    norm_add_le (b₂ - b₁ - ∫ t in t₁..t₂, g' t) (a₂ - b₂)]

end intervalIntegral

/-- A function vanishing on `(-∞, a]` and on a ball around `a` has zero integral on `a..t` for
every `t < a + ε`, where `ε` is the radius of that ball. -/
lemma integral_eq_zero_of_lt_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} {a ε t : ℝ} {φ : ℝ → E} (hφ0 : ∀ x, x ≤ a → φ x = 0)
    (hφa : ∀ ⦃y⦄, dist y a < ε → φ y = 0) (ht : t < a + ε) : ∫ s in a..t, φ s ∂μ = 0 := by
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : E)) fun s hs ↦ ?_).trans
    intervalIntegral.integral_zero
  rcases le_or_gt s a with hsa | hsa
  · exact hφ0 s hsa
  · refine hφa ?_
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hsa)]
    linarith [(le_max_iff.1 hs.2).resolve_left hsa.not_ge]

/-- The primitive of a step velocity corrected by its average defect reaches the prescribed
endpoint. -/
theorem add_integral_add_inv_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} (hab : a ≠ b) {s : ℝ → E} (hsi : IntervalIntegrable s volume a b)
    (x y : E) :
    x + ∫ t in a..b, (s t + (b - a)⁻¹ • (y - x - ∫ t in a..b, s t)) = y := by
  rw [_root_.intervalIntegral.integral_add hsi (intervalIntegrable_const),
    _root_.intervalIntegral.integral_const, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab.symm),
    one_smul]
  abel

/-- The `L¹` norm over `(a, b]` of the constant `(b - a)⁻¹ • D` is `‖D‖`. -/
theorem setIntegral_norm_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a < b) (D : E) :
    (∫ _ in Ioc a b, ‖(b - a)⁻¹ • D‖) = ‖D‖ := by
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (sub_pos.mpr hab), smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_mul]

end TauCeti

/-- A function integrable on `(a, b)` for a measure without mass at points is interval integrable
between any two points `s, t ∈ [a, b]`. -/
theorem MeasureTheory.IntegrableOn.intervalIntegrable_of_mem_Icc {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {μ : Measure ℝ} [NullSingletonClass μ] {a b s t : ℝ}
    (hf : IntegrableOn f (Ioo a b) μ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    IntervalIntegrable f μ s t :=
  ((integrableOn_Icc_iff_integrableOn_Ioo (f := f)).2 hf |>.mono_set
    (uIcc_subset_Icc hs ht)).intervalIntegrable

/-- A continuous linear equivalence commutes with interval integrals of arbitrary functions;
compare `ContinuousLinearMap.intervalIntegral_comp_comm`, which needs integrability. -/
theorem ContinuousLinearEquiv.intervalIntegral_comp_comm {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] {μ : Measure ℝ} {a b : ℝ}
    (L : E ≃L[𝕜] F) (f : ℝ → E) :
    ∫ x in a..b, L (f x) ∂μ = L (∫ x in a..b, f x ∂μ) := by
  simp_rw [intervalIntegral, L.integral_comp_comm, map_sub]

/-- If `f` is locally integrable on `[c, ∞)` for a locally finite measure, then its constant
extension `x ↦ f (max x c)` to all of `ℝ` is interval integrable between any two points. -/
theorem MeasureTheory.LocallyIntegrableOn.intervalIntegrable_comp_max {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {c : ℝ}
    (hf : LocallyIntegrableOn f (Ici c) μ) (a b : ℝ) :
    IntervalIntegrable (fun x ↦ f (max x c)) μ a b := by
  suffices h : ∀ x, IntervalIntegrable (fun x ↦ f (max x c)) μ c x from (h a).symm.trans (h b)
  intro x
  rcases le_total c x with hx | hx
  · refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le hx]
    exact (hf.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc).congr_fun
      (fun y hy ↦ by rw [max_eq_left hy.1]) measurableSet_Icc
  · refine (intervalIntegrable_const (c := f c)).congr fun y hy ↦ ?_
    rw [uIoc_of_ge hx] at hy
    simp only [max_eq_right hy.2]
