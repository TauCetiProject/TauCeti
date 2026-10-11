/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Convex.Integral

/-!
# Norms of averages

The extended norm of the average of a function is at most the average of its extended norm, and
consequently the measure of a set times the norm of the average over it is at most the integral of
the norm over it. These are the estimates used to bound a function that has been replaced by its
averages on the pieces of a partition, as in the Calderón–Zygmund decomposition.

Both hold without any integrability or finiteness assumption: when the average is not defined it
is `0` by convention.

Measuring the mean oscillation of a function about its own average rather than about a constant
`c` costs at most a factor `2`: `⨍_s ‖f - f_s‖ ≤ 2 ⨍_s ‖f - c‖`. So a bound on the oscillation
about any convenient constant gives one about the average, the form used by the John–Nirenberg
inequality.

The average of a function over a set `s` is also controlled by its average over a larger set
`t ⊇ s`, at the cost of the ratio `μ t / μ s` of their measures; together with the factor-`2`
bound above this compares mean oscillations on nested sets, as in the theory of functions of
bounded mean oscillation. In square mean the comparison with a constant reads
`∫_s ‖f - f_s‖² ≤ 4 ∫_s ‖f - c‖²` on a set of finite measure; in an inner product space the
factor `4` drops to `1`, by the orthogonal splitting
`∫_s ‖f - c‖² = ∫_s ‖f - f_s‖² + μ s ‖f_s - c‖²`.

Averages are unchanged by a change of variables that rescales the measure by a constant factor,
such as an affine homothety of a finite-dimensional space with its Haar measure: if a measurable
equivalence `e` pushes `μ` forward to `a • ν` with `0 < a < ∞`, then the average of `f ∘ e` over
`e ⁻¹' s` with respect to `μ` is the average of `f` over `s` with respect to `ν`.

## Main results

* `TauCeti.enorm_setAverage_le_setLAverage`: the extended norm of an average over a set is at most
  the average of the extended norm over the set.
* `TauCeti.measure_mul_enorm_setAverage_le`: the measure of a set times the extended norm of the
  average over it is at most the integral of the extended norm over it.
* `TauCeti.setLAverage_enorm_sub_setAverage_le`: the mean oscillation of `f` about its
  average is at most twice its mean oscillation about any constant.
* `TauCeti.norm_setAverage_sub_le_of_subset`: the average over a subset `s ⊆ t`
  differs from a constant `c` by at most `μ t / μ s` times the average of `‖f - c‖` over `t`.
* `TauCeti.setLAverage_le_div_mul_setLAverage_of_subset`: the average of a nonnegative function
  over a subset `s ⊆ t` is at most `μ t / μ s` times its average over `t`.
* `TauCeti.enorm_setAverage_sub_le_of_subset`: the extended-norm form of
  `TauCeti.norm_setAverage_sub_le_of_subset`.
* `TauCeti.setIntegral_norm_sub_setAverage_sq_le`: the square mean oscillation of `f` about its
  average is at most four times its square mean oscillation about any constant.
* `TauCeti.setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add` and
  `TauCeti.setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq`: in an inner product
  space the square mean oscillation about a constant splits orthogonally, so the average is the
  best constant, with no loss.
* `TauCeti.sq_setAverage_norm_le_setAverage_norm_sq`: Jensen's inequality
  `(⨍_s ‖g‖)² ≤ ⨍_s ‖g‖²`, bounding the mean oscillation by the square mean oscillation.
* `TauCeti.setLIntegral_comp_preimage_of_map_eq_smul`,
  `TauCeti.setIntegral_comp_preimage_of_map_eq_smul`,
  `TauCeti.setLAverage_comp_preimage_of_map_eq_smul`,
  `TauCeti.setAverage_comp_preimage_of_map_eq_smul`: integrals and averages under a measurable
  equivalence that rescales the measure by a constant.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal InnerProductSpace

section ENorm

variable {α E : Type*} {_ : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The extended norm of an average is at most the average of the extended norm. -/
theorem enorm_average_le_laverage (μ : Measure α) (f : α → E) :
    ‖⨍ x, f x ∂μ‖ₑ ≤ ⨍⁻ x, ‖f x‖ₑ ∂μ := by
  rw [average_eq', laverage_eq']
  exact enorm_integral_le_lintegral_enorm _

/-- The extended norm of an average over a set is at most the average of the extended norm over
the set. -/
theorem enorm_setAverage_le_setLAverage (μ : Measure α) (f : α → E) (s : Set α) :
    ‖⨍ x in s, f x ∂μ‖ₑ ≤ ⨍⁻ x in s, ‖f x‖ₑ ∂μ :=
  enorm_average_le_laverage _ _

/-- The measure of a set times the extended norm of the average over it is at most the integral of
the extended norm over it. -/
theorem measure_mul_enorm_setAverage_le (μ : Measure α) (f : α → E) (s : Set α) :
    μ s * ‖⨍ x in s, f x ∂μ‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ := by
  by_cases hs : μ s = ∞
  · simp [setAverage_eq, measureReal_def, hs]
  · rw [← measure_mul_setLAverage _ hs]
    gcongr
    exact enorm_setAverage_le_setLAverage μ f s

end ENorm

section Oscillation

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {s : Set X}

/-- The mean oscillation of `f` on `s` about its own average is at most twice its mean oscillation
about any constant `c`: `⨍_s ‖f - f_s‖ ≤ 2 ⨍_s ‖f - c‖`. -/
theorem setLAverage_enorm_sub_setAverage_le (hf : IntegrableOn f s μ) (c : F) :
    ⨍⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ ≤ 2 * ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := by
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  rcases eq_or_ne (μ s) ∞ with htop | htop
  · simp [setLAverage_eq, htop]
  have heq : (⨍ y in s, f y ∂μ) - c = ⨍ y in s, (f y - c) ∂μ := by
    rw [setAverage_fun_sub hf (integrableOn_const htop), setAverage_const h0 htop]
  calc ⨍⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ∂μ
      ≤ ⨍⁻ x in s, (‖f x - c‖ₑ + ⨍⁻ y in s, ‖f y - c‖ₑ ∂μ) ∂μ := by
        refine setLAverage_mono_ae s (.of_forall fun x => ?_)
        calc ‖f x - ⨍ y in s, f y ∂μ‖ₑ = ‖(f x - c) - ((⨍ y in s, f y ∂μ) - c)‖ₑ := by
              congr 1; abel
          _ ≤ ‖f x - c‖ₑ + ‖(⨍ y in s, f y ∂μ) - c‖ₑ := enorm_sub_le
          _ ≤ ‖f x - c‖ₑ + ⨍⁻ y in s, ‖f y - c‖ₑ ∂μ := by
            rw [heq]
            gcongr
            exact enorm_setAverage_le_setLAverage μ _ s
    _ = 2 * ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := by
        rw [setLAverage_eq μ (fun x => ‖f x - c‖ₑ + ⨍⁻ y in s, ‖f y - c‖ₑ ∂μ) s,
          lintegral_add_right _ measurable_const, setLIntegral_const,
          ENNReal.add_div, ENNReal.mul_div_cancel_right h0 htop, ← setLAverage_eq, two_mul]

end Oscillation

section SquareIntegrable

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F] {g : X → F}
  {s : Set X}

/-- **Jensen's inequality for the square of a mean.** On a set `s` of finite nonzero measure, the
square of the mean of `‖g‖` is at most the mean of `‖g‖²`. -/
theorem sq_setAverage_norm_le_setAverage_norm_sq (hs0 : μ s ≠ 0) (hs : μ s ≠ ⊤)
    (hg : IntegrableOn g s μ) (hg2 : IntegrableOn (fun x ↦ ‖g x‖ ^ 2) s μ) :
    (⨍ x in s, ‖g x‖ ∂μ) ^ 2 ≤ ⨍ x in s, ‖g x‖ ^ 2 ∂μ :=
  (Even.convexOn_pow even_two).map_set_average_le (continuous_pow 2).continuousOn isClosed_univ
    hs0 hs (ae_of_all _ fun _ ↦ Set.mem_univ _) hg.norm hg2

end SquareIntegrable

section Subset

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {s t : Set X}

/-- The average of a nonnegative function over a subset `s` of `t` is at most `μ t / μ s` times
its average over `t`. -/
theorem setLAverage_le_div_mul_setLAverage_of_subset {g : X → ℝ≥0∞} (hst : s ⊆ t)
    (ht : μ t ≠ ⊤) : ⨍⁻ x in s, g x ∂μ ≤ μ t / μ s * ⨍⁻ x in t, g x ∂μ := by
  rcases eq_or_ne (μ t) 0 with ht0 | ht0
  · rw [setLAverage_eq, setLIntegral_measure_zero _ _ (measure_mono_null hst ht0),
      ENNReal.zero_div]
    exact zero_le
  have h : μ t / μ s * ((∫⁻ x in t, g x ∂μ) / μ t) = (∫⁻ x in t, g x ∂μ) / μ s := by
    rw [ENNReal.div_eq_inv_mul, mul_assoc, ENNReal.mul_div_cancel ht0 ht,
      ← ENNReal.div_eq_inv_mul]
  rw [setLAverage_eq, setLAverage_eq, h]
  exact ENNReal.div_le_div_right (lintegral_mono_set hst) _

/-- The average of `f` over a subset `s` of `t` differs from a constant `c` by at most `μ t / μ s`
times the average of `‖f - c‖ₑ` over `t`. This is the extended-norm form of
`TauCeti.norm_setAverage_sub_le_of_subset`; it needs `f` to be integrable only on `s`. -/
theorem enorm_setAverage_sub_le_of_subset (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ⊤)
    (hf : IntegrableOn f s μ) (c : F) :
    ‖(⨍ x in s, f x ∂μ) - c‖ₑ ≤ μ t / μ s * ⨍⁻ x in t, ‖f x - c‖ₑ ∂μ := by
  have hs' : μ s ≠ ⊤ := ne_top_of_le_ne_top ht (measure_mono hst)
  calc ‖(⨍ x in s, f x ∂μ) - c‖ₑ = ‖⨍ x in s, (f x - c) ∂μ‖ₑ := by
        rw [setAverage_fun_sub hf (integrableOn_const hs'), setAverage_const hs hs']
    _ ≤ ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := enorm_setAverage_le_setLAverage _ _ _
    _ ≤ μ t / μ s * ⨍⁻ x in t, ‖f x - c‖ₑ ∂μ :=
        setLAverage_le_div_mul_setLAverage_of_subset hst ht

/-- The average of `f` over a subset `s` of `t` differs from a constant `c` by at most
`μ t / μ s` times the average of `‖f - c‖` over `t`. -/
theorem norm_setAverage_sub_le_of_subset (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ⊤)
    (hf : IntegrableOn f t μ) (c : F) :
    ‖(⨍ x in s, f x ∂μ) - c‖ ≤ μ.real t / μ.real s * ⨍ x in t, ‖f x - c‖ ∂μ := by
  have hfc : IntegrableOn (fun x => f x - c) t μ := hf.sub (integrableOn_const ht)
  have hav : (⨍⁻ x in t, ‖f x - c‖ₑ ∂μ).toReal = ⨍ x in t, ‖f x - c‖ ∂μ := by
    simpa using toReal_setLAverage hfc.1.enorm (ae_of_all _ fun _ => enorm_ne_top)
  rw [← toReal_enorm, measureReal_def, measureReal_def, ← ENNReal.toReal_div, ← hav,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.div_ne_top ht hs) (setLAverage_lt_top hfc.2.ne).ne)
    (enorm_setAverage_sub_le_of_subset hst hs ht (hf.mono_set hst) c)

/-- The square mean oscillation of `f` on a set `s` of finite measure about its own average is at
most four times its square mean oscillation about any constant `c`:
`∫_s ‖f - f_s‖² ≤ 4 ∫_s ‖f - c‖²`. -/
theorem setIntegral_norm_sub_setAverage_sq_le (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ) {c : F}
    (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ 2) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ ≤ 4 * ∫ x in s, ‖f x - c‖ ^ 2 ∂μ := by
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  have hm : 0 < μ.real s := ENNReal.toReal_pos h0 hs
  set a := ‖(⨍ y in s, f y ∂μ) - c‖
  set J := ∫ x in s, ‖f x - c‖ ^ 2 ∂μ
  -- The average lies within the mean of `‖f - c‖` of `c`, and Jensen's inequality bounds the
  -- square of that mean by the mean of `‖f - c‖²`, so `μ s * a² ≤ J`.
  have ha : a ≤ ⨍ x in s, ‖f x - c‖ ∂μ := by
    simpa [div_self hm.ne'] using norm_setAverage_sub_le_of_subset subset_rfl h0 hs hf c
  have hJ : (⨍ x in s, ‖f x - c‖ ∂μ) ^ 2 ≤ ⨍ x in s, ‖f x - c‖ ^ 2 ∂μ :=
    sq_setAverage_norm_le_setAverage_norm_sq h0 hs (hf.sub (integrableOn_const hs)) hfc
  have haJ : μ.real s * a ^ 2 ≤ J := by
    calc μ.real s * a ^ 2 ≤ μ.real s * ⨍ x in s, ‖f x - c‖ ^ 2 ∂μ := by
          gcongr
          exact (pow_le_pow_left₀ (norm_nonneg _) ha 2).trans hJ
      _ = J := by rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  -- Pointwise, `‖f x - f_s‖² ≤ 2 ‖f x - c‖² + 2 a²`.
  calc ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ
      ≤ ∫ x in s, (2 * ‖f x - c‖ ^ 2 + 2 * a ^ 2) ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
          ((hfc.const_mul 2).add (integrableOn_const hs)) (ae_of_all _ fun x ↦ ?_)
        have htri : ‖f x - ⨍ y in s, f y ∂μ‖ ≤ ‖f x - c‖ + a := by
          calc ‖f x - ⨍ y in s, f y ∂μ‖ = ‖(f x - c) - ((⨍ y in s, f y ∂μ) - c)‖ := by
                congr 1; abel
            _ ≤ ‖f x - c‖ + a := norm_sub_le _ _
        have h0' : 0 ≤ ‖f x - ⨍ y in s, f y ∂μ‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖f x - c‖ - a)]
    _ = 2 * J + 2 * (μ.real s * a ^ 2) := by
        rw [integral_add (hfc.const_mul 2) (integrableOn_const hs), integral_const_mul,
          setIntegral_const, smul_eq_mul]
        ring
    _ ≤ 4 * J := by linarith

end Subset

section InnerProduct

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace F] {s : Set X} {f : X → F}

/-- In a real inner product space, the square mean oscillation of `f` on a set `s` of finite
measure about a constant `c` splits orthogonally:
`∫_s ‖f - c‖² = ∫_s ‖f - f_s‖² + μ s ‖f_s - c‖²`. -/
theorem setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add (hs : μ s ≠ ⊤)
    (hf : IntegrableOn f s μ) {c : F} (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ 2) s μ) :
    ∫ x in s, ‖f x - c‖ ^ 2 ∂μ =
      ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ + μ.real s * ‖(⨍ y in s, f y ∂μ) - c‖ ^ 2 := by
  set m := ⨍ y in s, f y ∂μ
  have hfm : Integrable (fun x ↦ f x - m) (μ.restrict s) := hf.sub (integrableOn_const hs)
  -- The cross term vanishes, since `∫_s (f - m) = 0`.
  have hcross : ∫ x in s, ⟪f x - m, m - c⟫_ℝ ∂μ = 0 := by
    simp_rw [real_inner_comm (m - c)]
    rw [integral_inner hfm, integral_sub hf (integrableOn_const hs), setIntegral_const,
      measure_smul_setAverage f hs, sub_self, inner_zero_right]
  have hint : Integrable (fun x ↦ ⟪f x - m, m - c⟫_ℝ) (μ.restrict s) := hfm.inner_const _
  -- Pointwise, `‖f - m‖² = ‖f - c‖² - 2 ⟪f - m, m - c⟫ - ‖m - c‖²`.
  have hpt : ∀ x, ‖f x - m‖ ^ 2 = ‖f x - c‖ ^ 2 - 2 * ⟪f x - m, m - c⟫_ℝ - ‖m - c‖ ^ 2 :=
    fun x ↦ by
      have := norm_add_sq_real (f x - m) (m - c)
      rw [sub_add_sub_cancel] at this
      linarith
  have h2 : Integrable (fun x ↦ ‖f x - c‖ ^ 2 - 2 * ⟪f x - m, m - c⟫_ℝ) (μ.restrict s) :=
    hfc.sub (hint.const_mul 2)
  simp_rw [hpt]
  rw [integral_sub h2 (integrableOn_const hs), integral_sub hfc (hint.const_mul 2),
    integral_const_mul, hcross, setIntegral_const, smul_eq_mul]
  ring

/-- In a real inner product space, the average of `f` over a set `s` of finite measure minimizes
the square mean oscillation: `∫_s ‖f - f_s‖² ≤ ∫_s ‖f - c‖²` for every constant `c`. -/
theorem setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq (hs : μ s ≠ ⊤)
    (hf : IntegrableOn f s μ) {c : F} (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ 2) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ ≤ ∫ x in s, ‖f x - c‖ ^ 2 ∂μ := by
  rw [setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add hs hf hfc]
  exact le_add_of_nonneg_right (by positivity)

end InnerProduct

section ChangeOfVariables

variable {X Y F : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {e : X ≃ᵐ Y} {a : ℝ≥0∞}

/-- If a measurable equivalence `e` pushes `μ` forward to `a • ν`, then the lower integral of
`g ∘ e` over `e ⁻¹' s` with respect to `μ` is `a` times the lower integral of `g` over `s` with
respect to `ν`. -/
theorem setLIntegral_comp_preimage_of_map_eq_smul (he : μ.map e = a • ν) (g : Y → ℝ≥0∞)
    (s : Set Y) : ∫⁻ x in e ⁻¹' s, g (e x) ∂μ = a * ∫⁻ y in s, g y ∂ν := by
  rw [← lintegral_map_equiv, ← e.measurableEmbedding.restrict_map, he, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul]

/-- Averages of nonnegative functions are invariant under a measurable equivalence `e` that pushes
`μ` forward to a positive finite multiple of `ν`. -/
theorem setLAverage_comp_preimage_of_map_eq_smul (he : μ.map e = a • ν) (ha : a ≠ 0)
    (ha' : a ≠ ∞) (g : Y → ℝ≥0∞) (s : Set Y) :
    ⨍⁻ x in e ⁻¹' s, g (e x) ∂μ = ⨍⁻ y in s, g y ∂ν := by
  rw [setLAverage_eq, setLAverage_eq, setLIntegral_comp_preimage_of_map_eq_smul he,
    ← e.map_apply, he, Measure.smul_apply, smul_eq_mul, ENNReal.mul_div_mul_left _ _ ha ha']

/-- If a measurable equivalence `e` pushes `μ` forward to `a • ν`, then the integral of `f ∘ e`
over `e ⁻¹' s` with respect to `μ` is `a.toReal` times the integral of `f` over `s` with respect
to `ν`. -/
theorem setIntegral_comp_preimage_of_map_eq_smul (he : μ.map e = a • ν) (f : Y → F) (s : Set Y) :
    ∫ x in e ⁻¹' s, f (e x) ∂μ = a.toReal • ∫ y in s, f y ∂ν := by
  rw [← setIntegral_map_equiv, he, Measure.restrict_smul, integral_smul_measure]

/-- Averages are invariant under a measurable equivalence `e` that pushes `μ` forward to a
positive finite multiple of `ν`. -/
theorem setAverage_comp_preimage_of_map_eq_smul (he : μ.map e = a • ν) (ha : a ≠ 0)
    (ha' : a ≠ ∞) (f : Y → F) (s : Set Y) :
    ⨍ x in e ⁻¹' s, f (e x) ∂μ = ⨍ y in s, f y ∂ν := by
  have hmeas : μ.real (e ⁻¹' s) = a.toReal * ν.real s := by
    rw [measureReal_def, ← e.map_apply, he, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      measureReal_def]
  rw [setAverage_eq, setAverage_eq, setIntegral_comp_preimage_of_map_eq_smul he, hmeas,
    smul_smul, mul_inv_rev, inv_mul_cancel_right₀ (ENNReal.toReal_ne_zero.2 ⟨ha, ha'⟩)]

end ChangeOfVariables

end TauCeti
