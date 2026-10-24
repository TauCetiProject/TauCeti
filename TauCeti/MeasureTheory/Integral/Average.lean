/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
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

Averages are unchanged when the measure is multiplied by a positive finite scalar. They are also
unchanged by a change of variables that rescales the measure by a constant factor,
such as an affine homothety of a finite-dimensional space with its Haar measure: if a measurable
equivalence `e` pushes `μ` forward to `a • ν` with `0 < a < ∞`, then the average of `f ∘ e` over
`e ⁻¹' s` with respect to `μ` is the average of `f` over `s` with respect to `ν`.

Along an increasing sequence of sets `V n` covering a set `s` of finite measure, the measures of
the pieces `s ∩ V n` converge to that of `s`, and so do the averages of an integrable function, as
used when an inequality proved on each set of an exhaustion is passed to the whole domain.

Hölder's inequality also bounds the average by the `Lᵖ` seminorm on the set, with the
normalizing factor `μ s ^ (-1/p)`, and bounds its `q`-th power by `(μ s)⁻¹ ∫⁻_s ‖f‖ₑ ^ q`.
These estimates hold for arbitrary sets, including zero or infinite measure, with only the
exponent restrictions `1 ≤ p < ∞` or `1 ≤ q`.

## Main results

* `TauCeti.enorm_setAverage_rpow_le`, `TauCeti.enorm_setAverage_le`: Hölder's bounds on an
  average over an arbitrary set, in `∫⁻` and `Lᵖ` form.
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
* `TauCeti.enorm_setAverage_sub_le_setLAverage`: on a set of finite positive measure, the average
  differs from a constant `c` by at most the average of `‖f - c‖ₑ`, with no integrability
  assumption.
* `TauCeti.setIntegral_norm_sub_setAverage_sq_le`: the square mean oscillation of `f` about its
  average is at most four times its square mean oscillation about any constant.
* `TauCeti.setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add` and
  `TauCeti.setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq`: in an inner product
  space the square mean oscillation about a constant splits orthogonally, so the average is the
  best constant, with no loss.
* `TauCeti.sq_setAverage_norm_le_setAverage_norm_sq`: Jensen's inequality
  `(⨍_s ‖g‖)² ≤ ⨍_s ‖g‖²`, bounding the mean oscillation by the square mean oscillation.
* `TauCeti.laverage_smul_measure`, `TauCeti.average_smul_measure`,
  `TauCeti.setLAverage_smul_measure`, `TauCeti.setAverage_smul_measure`: averages are unchanged
  when the measure is multiplied by a positive finite scalar.
* `TauCeti.setLIntegral_comp_preimage_of_map_eq_smul`,
  `TauCeti.setIntegral_comp_preimage_of_map_eq_smul`,
  `TauCeti.setLAverage_comp_preimage_of_map_eq_smul`,
  `TauCeti.setAverage_comp_preimage_of_map_eq_smul`: integrals and averages under a measurable
  equivalence that rescales the measure by a constant.
* `TauCeti.tendsto_measureReal_inter_of_monotone`, `TauCeti.tendsto_setAverage_inter_of_monotone`:
  along an increasing sequence of sets covering `s`, the measures of and averages over the pieces
  of `s` converge to those over `s`.
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

section Holder

variable {α F : Type*} [MeasurableSpace α] {mu : Measure α} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : α → F} {p : ℝ≥0∞} {s : Set α}

/-- **Hölder's bound on an average**, in `∫⁻` form: the `q`-th power of the average of `f` over a
set `s` is at most `(μ s)⁻¹` times the integral of `‖f‖ ^ q` over `s`.
The single factor `(μ s)⁻¹` is what survives after the `q`-th power of the normalization
`(μ s)⁻¹` cancels against the `(μ s) ^ (q - 1)` of Hölder's inequality.
No measurability or integrability hypothesis is needed, since a function not integrable on `s`
has average zero. -/
theorem enorm_setAverage_rpow_le {q : ℝ} (hq : 1 ≤ q) :
    ‖⨍ y in s, f y ∂mu‖ₑ ^ q ≤ (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
  have hq0 : (0 : ℝ) < q := one_pos.trans_le hq
  by_cases hs0 : mu s = 0
  · simp [setAverage_eq, measureReal_def, hs0, ENNReal.zero_rpow_of_pos hq0]
  by_cases hs : mu s = ∞
  · simp [setAverage_eq, measureReal_def, hs, ENNReal.zero_rpow_of_pos hq0]
  by_cases hf : IntegrableOn f s mu
  swap
  · simp [setAverage_eq, integral_undef hf, ENNReal.zero_rpow_of_pos hq0]
  have h0 : ‖⨍ y in s, f y ∂mu‖ₑ ≤ (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ∂mu := by
    simpa only [setLAverage_eq, ENNReal.div_eq_inv_mul] using
      enorm_setAverage_le_setLAverage mu f s
  have hholder : (∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q ≤ mu s ^ (q - 1) * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
    have := rpow_lintegral_le_measure_univ_rpow_mul (μ := mu.restrict s)
      (u := fun y => ‖f y‖ₑ) hf.aestronglyMeasurable.enorm hq
    rwa [Measure.restrict_apply_univ] at this
  have hexp : -q + (q - 1) = (-1 : ℝ) := by ring
  calc ‖⨍ y in s, f y ∂mu‖ₑ ^ q
      ≤ ((mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q := ENNReal.rpow_le_rpow h0 hq0.le
    _ = (mu s)⁻¹ ^ q * (∫⁻ y in s, ‖f y‖ₑ ∂mu) ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq0.le
    _ ≤ (mu s)⁻¹ ^ q * (mu s ^ (q - 1) * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu) := mul_le_mul' le_rfl hholder
    _ = (mu s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ ^ q ∂mu := by
        rw [← mul_assoc, ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hs0 hs,
          hexp, ENNReal.rpow_neg_one]

/-- **Hölder's bound on an average**: the average of `f` over a set `s` is at most
`μ s ^ (-1/p)` times the `Lᵖ` seminorm of `f` on `s`. At `p = 1` this is the
bound by the average of `‖f‖`, and the volume factor sharpens as `p` grows because a larger
exponent controls the mass of `s` more efficiently. No measurability or integrability hypothesis
is needed, since a function not integrable on `s` has average zero. -/
theorem enorm_setAverage_le (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ‖⨍ y in s, f y ∂mu‖ₑ ≤ mu s ^ (-(p.toReal)⁻¹) * eLpNorm f p (mu.restrict s) := by
  by_cases hf : IntegrableOn f s mu
  swap
  · simp [setAverage_eq, integral_undef hf]
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hq0 : (0 : ℝ) < p.toReal := one_pos.trans_le hq
  have hroot := ENNReal.rpow_le_rpow
    (enorm_setAverage_rpow_le (f := f) (mu := mu) (s := s) (q := p.toReal) hq) (inv_pos.mpr hq0).le
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hq0.ne', ENNReal.rpow_one] at hroot
  refine hroot.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.inv_rpow, ← ENNReal.rpow_neg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hf.aestronglyMeasurable, one_div]

end Holder

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
`TauCeti.norm_setAverage_sub_le_of_subset`. No integrability is assumed: if `f` is not integrable
on `s`, the right-hand side is infinite. -/
theorem enorm_setAverage_sub_le_of_subset (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ⊤)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (c : F) :
    ‖(⨍ x in s, f x ∂μ) - c‖ₑ ≤ μ t / μ s * ⨍⁻ x in t, ‖f x - c‖ₑ ∂μ := by
  have hs' : μ s ≠ ⊤ := ne_top_of_le_ne_top ht (measure_mono hst)
  by_cases hfi : IntegrableOn f s μ
  · calc ‖(⨍ x in s, f x ∂μ) - c‖ₑ = ‖⨍ x in s, (f x - c) ∂μ‖ₑ := by
          rw [setAverage_fun_sub hfi (integrableOn_const hs'), setAverage_const hs hs']
      _ ≤ ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := enorm_setAverage_le_setLAverage _ _ _
      _ ≤ μ t / μ s * ⨍⁻ x in t, ‖f x - c‖ₑ ∂μ :=
          setLAverage_le_div_mul_setLAverage_of_subset hst ht
  -- If `f` is not integrable on `s`, then `‖f - c‖ₑ` has infinite integral over `s ⊆ t`.
  have htop : ∫⁻ x in t, ‖f x - c‖ₑ ∂μ = ⊤ := by
    refine top_le_iff.1 ((top_le_iff.2 ?_).trans (lintegral_mono_set hst))
    by_contra h
    have hfc : IntegrableOn (fun x => f x - c) s μ :=
      ⟨hf.sub aestronglyMeasurable_const, lt_top_iff_ne_top.2 h⟩
    exact hfi ((hfc.add (integrableOn_const hs')).congr (.of_forall fun x => by simp))
  have hts : μ t / μ s ≠ 0 := by
    rw [Ne, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨fun h => hs (measure_mono_null hst h), hs'⟩
  rw [setLAverage_eq, htop, ENNReal.top_div_of_ne_top ht, ENNReal.mul_top hts]
  exact le_top

/-- On a set of finite positive measure, the average of an almost everywhere strongly measurable
`f` differs from a constant `c` by at most the average of `‖f - c‖ₑ`. No integrability is assumed:
if `f` is not integrable on `s`, the right-hand side is infinite. -/
theorem enorm_setAverage_sub_le_setLAverage (hf : AEStronglyMeasurable f (μ.restrict s))
    (hs : μ s ≠ 0) (hs' : μ s ≠ ⊤) (c : F) :
    ‖(⨍ x in s, f x ∂μ) - c‖ₑ ≤ ⨍⁻ x in s, ‖f x - c‖ₑ ∂μ := by
  simpa [ENNReal.div_self hs hs'] using enorm_setAverage_sub_le_of_subset subset_rfl hs hs' hf c

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
    (enorm_setAverage_sub_le_of_subset hst hs ht (hf.mono_set hst).1 c)

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

section SMulMeasure

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} {a : ℝ≥0∞}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The lower average is unchanged when the measure is multiplied by a positive finite
scalar. -/
@[simp]
theorem laverage_smul_measure (ha : a ≠ 0) (ha' : a ≠ ∞) (g : X → ℝ≥0∞) :
    ⨍⁻ x, g x ∂(a • μ) = ⨍⁻ x, g x ∂μ := by
  simp only [laverage_eq, lintegral_smul_measure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_div_mul_left _ _ ha ha'

/-- The lower average over a set is unchanged when the measure is multiplied by a positive finite
scalar. -/
theorem setLAverage_smul_measure (ha : a ≠ 0) (ha' : a ≠ ∞) (g : X → ℝ≥0∞) (s : Set X) :
    ⨍⁻ x in s, g x ∂(a • μ) = ⨍⁻ x in s, g x ∂μ := by
  simp only [Measure.restrict_smul, laverage_smul_measure ha ha']

/-- The average is unchanged when the measure is multiplied by a positive finite
scalar. -/
@[simp]
theorem average_smul_measure (ha : a ≠ 0) (ha' : a ≠ ∞) (f : X → F) :
    ⨍ x, f x ∂(a • μ) = ⨍ x, f x ∂μ := by
  rw [average_eq, average_eq, integral_smul_measure]
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [smul_smul, mul_inv_rev, inv_mul_cancel_right₀ (ENNReal.toReal_ne_zero.2 ⟨ha, ha'⟩)]

/-- The average over a set is unchanged when the measure is multiplied by a positive finite
scalar. -/
theorem setAverage_smul_measure (ha : a ≠ 0) (ha' : a ≠ ∞) (f : X → F) (s : Set X) :
    ⨍ x in s, f x ∂(a • μ) = ⨍ x in s, f x ∂μ := by
  simp only [Measure.restrict_smul, average_smul_measure ha ha']

end SMulMeasure

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

section Exhaustion

open Filter Topology

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : X → F} {s : Set X} {V : ℕ → Set X}

/-- Along an increasing sequence of sets `V n` whose union contains `s`, the measures of the
pieces `s ∩ V n` converge to the measure of `s`, if it is finite. -/
theorem tendsto_measureReal_inter_of_monotone (hV : Monotone V) (hsV : s ⊆ ⋃ n, V n)
    (hs : μ s ≠ ⊤) : Tendsto (fun n ↦ μ.real (s ∩ V n)) atTop (𝓝 (μ.real s)) := by
  have hunion : ⋃ n, s ∩ V n = s := by rw [← Set.inter_iUnion, Set.inter_eq_left.2 hsV]
  refine (ENNReal.tendsto_toReal hs).comp ?_
  simpa [hunion, Function.comp_def] using
    tendsto_measure_iUnion_atTop (μ := μ) fun m n hmn ↦ Set.inter_subset_inter_right s (hV hmn)

/-- Along an increasing sequence of sets `V n` whose union contains `s`, the averages of a
function integrable on `s` over the pieces `s ∩ V n` converge to its average over `s`, if `s` has
finite measure. -/
theorem tendsto_setAverage_inter_of_monotone (hV : Monotone V) (hsV : s ⊆ ⋃ n, V n)
    (hm : ∀ n, NullMeasurableSet (s ∩ V n) μ) (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ) :
    Tendsto (fun n ↦ ⨍ x in s ∩ V n, f x ∂μ) atTop (𝓝 (⨍ x in s, f x ∂μ)) := by
  rcases eq_or_ne (μ s) 0 with hs0 | hs0
  · simp [setAverage_eq, measureReal_def, hs0, measure_mono_null Set.inter_subset_left hs0]
  have hunion : ⋃ n, s ∩ V n = s := by rw [← Set.inter_iUnion, Set.inter_eq_left.2 hsV]
  simp only [setAverage_eq]
  refine ((tendsto_measureReal_inter_of_monotone hV hsV hs).inv₀
    (ENNReal.toReal_pos hs0 hs).ne').smul ?_
  simpa [hunion] using tendsto_setIntegral_of_monotone₀ hm
    (fun m n hmn ↦ Set.inter_subset_inter_right s (hV hmn)) (by rwa [hunion])

end Exhaustion

end TauCeti
