/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
public import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# An integral related to the arithmetic-geometric mean

For $a,b>0$ consider the improper integral
$$I(a,b) = \int_0^\infty \frac{dx}{\sqrt{(x^2+a^2)(x^2+b^2)}}.$$
Then making the substitution $x = t+\sqrt{t^2+ab}$ yields, after rearranging,
$$I(a,b) = \int_{-\infty}^\infty \frac{dx}{2\sqrt{(x^2+ab)(x^2+((a+b)/2)^2)}}
= I(\sqrt{ab},(a+b)/2).$$
Iterating this transformation drives both arguments towards the arithmetic-geometric mean
(AGM) of $a$ and $b$, by `Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean`, so we have
$$I(a,b)=I(\operatorname{agm}(a,b),\operatorname{agm}(a,b))=\frac{\pi/2}{\operatorname{agm}(a,b)}$$
where the second equality follows from an elementary integral.
This establishes a link between the AGM and complete elliptic integrals.

Adapted from Jeremy Tan's
[Mathlib PR #34397](https://github.com/leanprover-community/mathlib4/pull/34397),
commit `376352b6e080265bc0380074baaf9aafa0b70a80`.
The integral is finite for positive inputs; when either input is zero it diverges, and Lean's
totalized Bochner integral returns zero.
-/

public section

open MeasureTheory Real

namespace TauCeti

/-- The elliptic integral related to the arithmetic-geometric mean. It is finite for positive
inputs and has the totalized value zero if either input is zero. -/
noncomputable def agmIntegral (a b : ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, (√((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹

lemma agmIntegral_def (a b : ℝ) :
    agmIntegral a b = ∫ x in Set.Ioi 0, (√((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ := (rfl)

variable {a b : ℝ}

/-- The defining integrand is integrable on the positive half-line for positive inputs. -/
lemma integrableOn_agmIntegrand_Ioi_of_pos (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x ↦ (√((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹) (Set.Ioi 0) := by
  apply Integrable.mono' (g := fun x ↦ (x ^ 2 + min a b ^ 2)⁻¹)
  · exact (integrable_inv_sq_add_sq (by positivity : min a b ≠ 0)).restrict
  · exact (AEMeasurable.aestronglyMeasurable (by fun_prop)).restrict
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have hnonneg : 0 ≤ x ^ 2 + min a b ^ 2 := by positivity
    rw [norm_of_nonneg (by positivity), inv_le_inv₀ (by positivity) (by positivity),
      ← sqrt_mul_self hnonneg]
    gcongr <;> grind

/-- The AGM integral is symmetric in its arguments. -/
lemma agmIntegral_comm : agmIntegral a b = agmIntegral b a := by
  simp [agmIntegral, mul_comm]

/-- The integral diverges (and thus takes the junk value of 0 in Lean) when `a = 0`. -/
@[simp]
lemma agmIntegral_zero_left : agmIntegral 0 b = 0 := by
  have cong (x) (mx : x ∈ Set.Ioi 0) :
      (√((x ^ 2 + 0 ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ = (x * √(x ^ 2 + b ^ 2))⁻¹ := by
    rw [sq 0, mul_zero, add_zero, sqrt_mul (sq_nonneg _), sqrt_sq mx.le]
  rw [agmIntegral, setIntegral_congr_fun measurableSet_Ioi cong]
  apply integral_undef (?_ : ¬IntegrableOn _ _ _)
  by_contra h
  replace h := h.mono_set (Set.Ioc_subset_Ioi_self (a := 1))
  replace h : IntegrableOn (fun a ↦ a⁻¹ * (√(1 + b ^ 2))⁻¹) (Set.Ioc 0 1) := by
    apply h.mono' (measurable_inv.aestronglyMeasurable.restrict.mul_const _)
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun x ⟨hx₁, hx₂⟩ ↦ ?_
    rw [← mul_inv, norm_inv, norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    bound
  replace h : IntegrableOn _ _ _ := h.mul_const √(1 + b ^ 2)
  conv at h =>
    enter [1, x]
    rw [inv_mul_cancel_right₀ (by positivity)]
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  simp at h

/-- The integral diverges (and thus takes the junk value of 0 in Lean) when `b = 0`. -/
@[simp]
lemma agmIntegral_zero_right : agmIntegral a 0 = 0 := by
  rw [agmIntegral_comm, agmIntegral_zero_left]

/-- On the nonnegative diagonal the AGM integral is the elementary value `π / 2 / a`.
At zero both sides take their totalized value zero. -/
@[simp]
theorem agmIntegral_self (ha : 0 ≤ a) : agmIntegral a a = π / 2 / a := by
  rcases ha.eq_or_lt with rfl | ha; · simp
  unfold agmIntegral
  conv_lhs =>
    enter [2, x]
    rw [← sq, sqrt_sq (by positivity)]
  have hsub := integral_comp_mul_left_Ioi' (fun x : ℝ ↦ (x ^ 2 + a ^ 2)⁻¹) 0 ha
  rw [mul_zero] at hsub
  rw [← hsub, ← integral_smul]
  have hscale (x : ℝ) : a * ((a * x) ^ 2 + a ^ 2)⁻¹ = a⁻¹ * (1 + x ^ 2)⁻¹ := by
    field_simp
    ring
  simp_rw [smul_eq_mul, hscale]
  rw [integral_const_mul, integral_Ioi_inv_one_add_sq, arctan_zero]
  ring

/-- **Landen's transformation** for `agmIntegral`. -/
theorem agmIntegral_eq_agmIntegral_gm_am (ha : 0 ≤ a) (hb : 0 ≤ b) :
    agmIntegral a b = agmIntegral √(a * b) ((a + b) / 2) := by
  -- Handle degenerate cases
  rcases ha.eq_or_lt with rfl | ha; · simp
  rcases hb.eq_or_lt with rfl | hb; · simp
  -- Define prerequisites for the substitution
  let f (t : ℝ) := t + √(t ^ 2 + a * b)
  let f' (t : ℝ) := f t / √(t ^ 2 + a * b)
  let g (x : ℝ) := (√((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹
  have pf (t) : 0 < f t := by
    rcases le_or_gt 0 t with ht | ht; · positivity
    rw [← neg_lt_iff_pos_add']
    nth_rw 1 [← abs_of_nonpos ht.le, ← sqrt_sq_eq_abs, ← add_zero (t ^ 2)]
    gcongr
    positivity
  have df (t) : HasDerivAt f (f' t) t := by
    unfold f'
    rw [← div_add_one (by positivity), add_comm]
    apply (hasDerivAt_id' _).fun_add
    rw [← mul_div_mul_left _ _ two_ne_zero]
    refine ((HasDerivAt.add_const _) ?_).sqrt (by positivity)
    convert hasDerivAt_pow 2 t using 1
    ring
  have mf : StrictMono f := strictMono_of_hasDerivAt_pos df fun t ↦ by positivity [pf t]
  have rf : f '' Set.univ = Set.Ioi 0 := by
    ext x
    rw [Set.image_univ, Set.mem_range, Set.mem_Ioi]
    refine ⟨fun ⟨t, ht⟩ ↦ ht.symm ▸ (pf _), fun hx ↦ ?_⟩
    use (x ^ 2 - a * b) / (2 * x)
    unfold f
    have hradicand : ((x ^ 2 - a * b) / (2 * x)) ^ 2 + a * b =
        ((x ^ 2 + a * b) / (2 * x)) ^ 2 := by
      field_simp
      ring
    have hsqrt : √(((x ^ 2 - a * b) / (2 * x)) ^ 2 + a * b) =
        (x ^ 2 + a * b) / (2 * x) := by
      rw [hradicand, sqrt_sq (by positivity)]
    rw [hsqrt]
    field_simp
    ring
  -- Make the substitution, whose LHS is simply `agmIntegral a b`
  rw [agmIntegral_def a b]
  rw [← rf, integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun t _ ↦ hasDerivWithinAt_univ.mpr (df t)) (monotoneOn_univ.mpr mf.monotone) g]
  -- Simplify the post-substitution integral
  have rearr₁ (t) : (f t * (t - √(t ^ 2 + a * b))) ^ 2 = (a * b) ^ 2 := by
    rw [← sq_sub_sq, sq_sqrt (by positivity)]
    ring
  have rearr₂ (t) : f t ^ 2 + (t - √(t ^ 2 + a * b)) ^ 2 = 4 * t ^ 2 + 2 * a * b := by
    rw [add_sq, sub_sq, sq_sqrt (by positivity)]
    ring
  have rearr₃ (t) :
      (f t ^ 2 + a ^ 2) * (f t ^ 2 + b ^ 2) = (2 * f t) ^ 2 * (t ^ 2 + ((a + b) / 2) ^ 2) := by
    linear_combination (f t) ^ 2 * rearr₂ t - rearr₁ t
  have hsqrt (t : ℝ) : √((f t ^ 2 + a ^ 2) * (f t ^ 2 + b ^ 2)) =
      2 * f t * √(t ^ 2 + ((a + b) / 2) ^ 2) := by
    rw [rearr₃, sqrt_mul (sq_nonneg _), sqrt_sq (by positivity [pf t])]
  have htransform (t : ℝ) :
      f t / √(t ^ 2 + a * b) * (√((f t ^ 2 + a ^ 2) * (f t ^ 2 + b ^ 2)))⁻¹ =
        (2 : ℝ)⁻¹ * (√((t ^ 2 + a * b) * (t ^ 2 + ((a + b) / 2) ^ 2)))⁻¹ := by
    rw [hsqrt, sqrt_mul (by positivity : 0 ≤ t ^ 2 + a * b)]
    field_simp [(pf t).ne']
  unfold f' g
  simp_rw [smul_eq_mul, htransform]
  rw [integral_const_mul, inv_mul_eq_div, div_eq_iff two_ne_zero, Measure.restrict_univ]
  -- The current LHS integral is an even integrand over all ℝ,
  -- so it is twice the integral over (0, ∞), i.e. the RHS integral
  rw [mul_comm _ 2, agmIntegral, ← integral_comp_abs]
  congr! 4 with _ t
  rw [sq_abs, sq_sqrt (by positivity)]

/-- The AGM integral depends continuously on its two positive arguments. -/
lemma continuousOn_agmIntegral :
    ContinuousOn (fun p ↦ agmIntegral p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  rintro ⟨a, b⟩ ⟨ha : 0 < a, hb : 0 < b⟩
  apply continuousWithinAt_of_dominated (bound := fun x ↦ (x ^ 2 + (min a b / 2) ^ 2)⁻¹)
  · exact eventually_nhdsWithin_of_forall fun _ _ ↦
      (AEMeasurable.aestronglyMeasurable (by fun_prop)).restrict
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨min a b / 2, by positivity,
      fun (a', b') dp mp ↦
        ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_⟩
    simp_rw [Prod.dist_eq, max_lt_iff, dist_eq] at dp
    have hnonneg : 0 ≤ t ^ 2 + (min a b / 2) ^ 2 := by positivity
    rw [norm_of_nonneg (by positivity), inv_le_inv₀ (by positivity) (by positivity),
      ← sqrt_mul_self hnonneg]
    gcongr <;> grind
  · exact (integrable_inv_sq_add_sq (by positivity : min a b / 2 ≠ 0)).restrict
  · exact Filter.Eventually.of_forall fun _ ↦
      ContinuousWithinAt.inv₀ (by fun_prop) (by positivity)

open NNReal

variable {a b : ℝ≥0}

/-- Every iterate of the arithmetic-geometric mean preserves the integral. -/
lemma agmIntegral_eq_agmIntegral_agmSequences {n : ℕ} :
    agmIntegral a b = agmIntegral (agmSequences a b n).1 (agmSequences a b n).2 := by
  induction n with
  | zero =>
    rw [agmIntegral_eq_agmIntegral_gm_am (coe_nonneg a) (coe_nonneg b)]
    simp [agmSequences_zero]
  | succ n ih =>
    rw [ih, agmIntegral_eq_agmIntegral_gm_am (coe_nonneg _) (coe_nonneg _),
      agmSequences_succ', coe_sqrt, NNReal.coe_mul]
    rfl

open Filter Topology in
/-- The fundamental relation between `agmIntegral` and `NNReal.agm`. For positive inputs this
is the value of a convergent integral; if either input is zero both sides are totalized to zero. -/
theorem agmIntegral_eq_pi_div_two_div_agm : agmIntegral a b = π / 2 / agm a b := by
  by_cases h : a = 0 ∨ b = 0
  · obtain rfl | rfl := h <;> simp
  rw [not_or, ← Ne, ← pos_iff_ne_zero, ← Ne, ← pos_iff_ne_zero] at h
  let f (n : ℕ) : ℝ × ℝ := ((agmSequences a b n).1, (agmSequences a b n).2)
  let g (p : ℝ × ℝ) : ℝ := agmIntegral p.1 p.2
  suffices Tendsto (g ∘ f) atTop (𝓝 (agmIntegral (agm a b) (agm a b))) by
    rw [← agmIntegral_self (coe_nonneg _)]
    refine tendsto_nhds_unique ?_ this
    simpa only [Function.comp_def, g, f, ← agmIntegral_eq_agmIntegral_agmSequences] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ agmIntegral a b) atTop (𝓝 (agmIntegral a b)))
  have tt : Tendsto f atTop (𝓝 (agm a b, agm a b)) :=
    (Prod.tendsto_iff _ _).mpr
      ⟨tendsto_coe.mpr tendsto_agmSequences_fst_agm,
        tendsto_coe.mpr tendsto_agmSequences_snd_agm⟩
  refine (continuousOn_agmIntegral.continuousAt ?_).tendsto.comp tt
  exact prod_mem_nhds (Ioi_mem_nhds (agm_pos h.1 h.2)) (Ioi_mem_nhds (agm_pos h.1 h.2))

/-- The AGM integral is strictly positive when both inputs are positive. -/
lemma agmIntegral_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < agmIntegral a b := by
  have ha' : 0 < (⟨a, ha.le⟩ : ℝ≥0) := ha
  have hb' : 0 < (⟨b, hb.le⟩ : ℝ≥0) := hb
  calc
    0 < π / 2 / agm ⟨a, ha.le⟩ ⟨b, hb.le⟩ :=
      div_pos (div_pos Real.pi_pos two_pos) (NNReal.coe_pos.mpr (agm_pos ha' hb'))
    _ = agmIntegral a b :=
      (agmIntegral_eq_pi_div_two_div_agm (a := ⟨a, ha.le⟩) (b := ⟨b, hb.le⟩)).symm

end TauCeti
