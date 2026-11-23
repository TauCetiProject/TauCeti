/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import TauCeti.Statistics.MissingData.MissingAtRandom
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Augmented inverse probability weighting and double robustness

For a regression function `m : X → ℝ` and a propensity `π : X → ℝ`, the augmented
inverse-probability-weighted estimating function of the mean of a response that may be missing
is `φ_{m,π}(r, x, y) = m(x) + r (y - m(x)) / π(x)`, evaluated on observed data, where a missing
response is the placeholder `0`. Let the full-data law `Q` be missing at random with propensity
`π₀`, and let `m₀(X)` be a version of `E[Y | X]`. The mixed-bias identity
`E φ_{m,π} - E Y = E[(π₀ - π)(m₀ - m) / π]` holds for every `m` with `m(X)` integrable and every
`π` bounded below by a positive constant, with no square integrability. Double robustness is
read off it: the estimating function is unbiased when `π = π₀` or when `m = m₀`. By the
Cauchy–Schwarz inequality the bias is at most `δ⁻¹ ‖π - π₀‖₂ ‖m - m₀‖₂` when `π ≥ δ`.

## Main definitions

* `TauCeti.aipwScore m π`: the augmented inverse-probability-weighted estimating function.

## Main results

* `TauCeti.integral_aipwScore_sub`: the mixed-bias identity.
* `TauCeti.integral_aipwScore_eq`: double robustness.
* `TauCeti.abs_integral_aipwScore_sub_le`: the product bound on the bias.

## References

* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley, 2019.

The proofs are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Asymptotics/CrossFitting/FoldBounds.lean` (`enorm_integral_missingMeanScore_sub_le` and its
helpers `integral_mul_response_eq`, `enorm_integral_comp_mul_div_le` and
`integrable_ite_observed_of_norm_le`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*}

/-- The augmented inverse-probability-weighted estimating function
`m(x) + r (y - m(x)) / π(x)`, evaluated on observed data. -/
def aipwScore (m π : X → ℝ) (o : Bool × X × ℝ) : ℝ :=
  m o.2.1 + if o.1 then (o.2.2 - m o.2.1) / π o.2.1 else 0

/-- The defining formula of `aipwScore`. -/
theorem aipwScore_def (m π : X → ℝ) (o : Bool × X × ℝ) :
    aipwScore m π o = m o.2.1 + if o.1 then (o.2.2 - m o.2.1) / π o.2.1 else 0 := by
  rw [aipwScore]

/-- At an observed response, the augmented estimating function is `m(x) + (y - m(x)) / π(x)`. -/
@[simp]
theorem aipwScore_true (m π : X → ℝ) (x : X) (y : ℝ) :
    aipwScore m π (true, x, y) = m x + (y - m x) / π x := by
  simp [aipwScore_def]

/-- At a missing response, the augmented estimating function is `m(x)`. -/
@[simp]
theorem aipwScore_false (m π : X → ℝ) (x : X) (y : ℝ) : aipwScore m π (false, x, y) = m x := by
  simp [aipwScore_def]

/-- At a full observation, the augmented estimating function of the observed part is
`m(X) + 1{R = 1} (Y - m(X)) / π(X)`. -/
theorem aipwScore_observe (m π : X → ℝ) (w : Bool × X × ℝ) :
    aipwScore m π (observe w) =
      m w.2.1 + if w.1 then (w.2.2 - m w.2.1) / π w.2.1 else 0 := by
  obtain ⟨r, x, y⟩ := w
  cases r <;> simp

variable [MeasurableSpace X]

/-- The inverse-probability-weighted residual `1{R = 1} (Y - m(X)) / π(X)` is integrable when
`Y` and `m(X)` are and `π ≥ δ > 0`. -/
private theorem integrable_ite_div {Q : Measure (Bool × X × ℝ)} {m π : X → ℝ}
    (hY : Integrable (fun w : Bool × X × ℝ ↦ w.2.2) Q)
    (hm : Integrable (fun w : Bool × X × ℝ ↦ m w.2.1) Q) (hmm : Measurable m)
    (hπm : Measurable π) {δ : ℝ} (hδ : 0 < δ) (hπ : ∀ x, δ ≤ π x) :
    Integrable (fun w : Bool × X × ℝ ↦ if w.1 then (w.2.2 - m w.2.1) / π w.2.1 else 0) Q := by
  refine ((hY.sub hm).norm.const_mul δ⁻¹).mono' (Measurable.ite
    (measurable_fst (measurableSet_singleton true)) (by fun_prop)
      measurable_const).aestronglyMeasurable (ae_of_all _ fun w ↦ ?_)
  have hπ0 : 0 < π w.2.1 := hδ.trans_le (hπ _)
  have hb : ‖(w.2.2 - m w.2.1) / π w.2.1‖ ≤ δ⁻¹ * ‖w.2.2 - m w.2.1‖ := by
    rw [norm_div, Real.norm_eq_abs (π _), abs_of_pos hπ0, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ (hπ _)) (norm_nonneg _)
  split_ifs
  · exact hb
  · rw [norm_zero]; exact (norm_nonneg _).trans hb

/-- Multiplying an integrable function by `π₀(X) / π(X)`, with `π₀ ∈ [0, 1]` a propensity and
`π ≥ δ > 0`, keeps it integrable. -/
private theorem integrable_div_mul {Q : Measure (Bool × X × ℝ)} {π₀ π : X → ℝ}
    (hmar : IsMissingAtRandom Q π₀) (hπm : Measurable π) {δ : ℝ} (hδ : 0 < δ)
    (hπ : ∀ x, δ ≤ π x) {f : Bool × X × ℝ → ℝ} (hf : Integrable f Q) :
    Integrable (fun w ↦ π₀ w.2.1 / π w.2.1 * f w) Q := by
  refine hf.bdd_mul (c := δ⁻¹) ((hmar.measurable.div hπm).comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun w ↦ ?_)
  have hπ0 : 0 < π w.2.1 := hδ.trans_le (hπ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hmar.nonneg _) hπ0.le),
    div_le_iff₀ hπ0]
  calc π₀ w.2.1 ≤ 1 := hmar.le_one _
    _ = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
    _ ≤ δ⁻¹ * π w.2.1 := by gcongr; exact hπ _

/-- **The mixed-bias identity.** Let `Q` be missing at random with propensity `π₀`, let `Y` be
integrable, and let `m₀(X)` be an integrable version of `E[Y | X]`. For every measurable `m`
with `m(X)` integrable and every measurable `π ≥ δ > 0`,
`E φ_{m,π} - E Y = E[(π₀ - π)(m₀ - m) / π]`. -/
theorem integral_aipwScore_sub (Q : Measure (Bool × X × ℝ)) [IsFiniteMeasure Q]
    (π₀ m₀ m π : X → ℝ) (hmar : IsMissingAtRandom Q π₀)
    (hY : Integrable (fun w : Bool × X × ℝ ↦ w.2.2) Q) (hm₀ : Measurable m₀)
    (hreg : ∀ A : Set X, MeasurableSet A →
      ∫ w in {w | w.2.1 ∈ A}, w.2.2 ∂Q = ∫ w in {w | w.2.1 ∈ A}, m₀ w.2.1 ∂Q)
    (hm : Integrable (fun w : Bool × X × ℝ ↦ m w.2.1) Q) (hmm : Measurable m)
    (hπm : Measurable π) (δ : ℝ) (hδ : 0 < δ) (hπ : ∀ x, δ ≤ π x)
    (hm₀i : Integrable (fun w : Bool × X × ℝ ↦ m₀ w.2.1) Q) :
    ∫ w, aipwScore m π (observe w) ∂Q - ∫ w, w.2.2 ∂Q =
      ∫ w, (π₀ w.2.1 - π w.2.1) * (m₀ w.2.1 - m w.2.1) / π w.2.1 ∂Q := by
  have hπ0 : ∀ x, 0 < π x := fun x ↦ hδ.trans_le (hπ x)
  have hkb : ∀ {f : Bool × X × ℝ → ℝ}, Integrable f Q →
      Integrable (fun w ↦ π₀ w.2.1 / π w.2.1 * f w) Q := integrable_div_mul hmar hπm hδ hπ
  have hitei := integrable_ite_div hY hm hmm hπm hδ hπ
  -- Missingness at random: `E[1{R = 1} (Y - m(X)) / π(X)] = E[π₀(X) (Y - m(X)) / π(X)]`.
  have h1 : ∫ w, (if w.1 then (w.2.2 - m w.2.1) / π w.2.1 else 0) ∂Q =
      ∫ w, π₀ w.2.1 / π w.2.1 * w.2.2 ∂Q - ∫ w, π₀ w.2.1 / π w.2.1 * m w.2.1 ∂Q := by
    rw [← integral_sub (hkb hY) (hkb hm),
      hmar.integral_ite_eq (g := fun p : X × ℝ ↦ (p.2 - m p.1) / π p.1) (by fun_prop) hitei]
    refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
    field_simp [(hπ0 w.2.1).ne']
  -- The regression identities: `E[π₀(X) Y / π(X)] = E[π₀(X) m₀(X) / π(X)]` and `E Y = E m₀(X)`.
  have hX : Measurable fun w : Bool × X × ℝ ↦ w.2.1 := by fun_prop
  have h2 := MeasureTheory.integral_comp_mul_eq_of_forall_setIntegral_preimage_eq hX hY hm₀ hm₀i
    hreg (f := fun x ↦ π₀ x / π x) (hmar.measurable.div hπm) (hkb hY)
  have h3 : ∫ w, w.2.2 ∂Q = ∫ w, m₀ w.2.1 ∂Q := by
    simpa using MeasureTheory.integral_comp_mul_eq_of_forall_setIntegral_preimage_eq hX hY hm₀
      hm₀i hreg (f := fun _ ↦ 1) measurable_const (by simpa using hY)
  have hrhs : ∫ w, (π₀ w.2.1 - π w.2.1) * (m₀ w.2.1 - m w.2.1) / π w.2.1 ∂Q =
      ∫ w, π₀ w.2.1 / π w.2.1 * m₀ w.2.1 ∂Q - ∫ w, π₀ w.2.1 / π w.2.1 * m w.2.1 ∂Q -
        ∫ w, m₀ w.2.1 ∂Q + ∫ w, m w.2.1 ∂Q := by
    have hA : Integrable (fun w : Bool × X × ℝ ↦
        π₀ w.2.1 / π w.2.1 * m₀ w.2.1 - π₀ w.2.1 / π w.2.1 * m w.2.1) Q :=
      (hkb hm₀i).sub (hkb hm)
    have hB : Integrable (fun w : Bool × X × ℝ ↦
        π₀ w.2.1 / π w.2.1 * m₀ w.2.1 - π₀ w.2.1 / π w.2.1 * m w.2.1 - m₀ w.2.1) Q :=
      hA.sub hm₀i
    rw [← integral_sub (hkb hm₀i) (hkb hm), ← integral_sub hA hm₀i, ← integral_add hB hm]
    refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
    field_simp [(hπ0 w.2.1).ne']
    ring
  simp_rw [aipwScore_observe]
  rw [integral_add hm hitei, h1, h2, hrhs, h3]
  ring

/-- **Double robustness.** Let `Q` be missing at random with propensity `π₀`, let `Y` be
integrable, and let `m₀(X)` be an integrable version of `E[Y | X]`. The augmented estimating
function is unbiased for `E Y` when the propensity is correct and bounded below by a positive
constant, for every measurable `m` with `m(X)` integrable, and when the regression is correct, for
every measurable propensity bounded below by a positive constant; the second case needs no lower
bound on `π₀`. -/
theorem integral_aipwScore_eq (Q : Measure (Bool × X × ℝ)) [IsFiniteMeasure Q]
    (π₀ m₀ : X → ℝ) (hmar : IsMissingAtRandom Q π₀)
    (hY : Integrable (fun w : Bool × X × ℝ ↦ w.2.2) Q) (hm₀ : Measurable m₀)
    (hreg : ∀ A : Set X, MeasurableSet A →
      ∫ w in {w | w.2.1 ∈ A}, w.2.2 ∂Q = ∫ w in {w | w.2.1 ∈ A}, m₀ w.2.1 ∂Q)
    (hm₀i : Integrable (fun w : Bool × X × ℝ ↦ m₀ w.2.1) Q) :
    (∀ δ > 0, (∀ x, δ ≤ π₀ x) → ∀ m : X → ℝ, Measurable m →
      Integrable (fun w : Bool × X × ℝ ↦ m w.2.1) Q →
        ∫ w, aipwScore m π₀ (observe w) ∂Q = ∫ w, w.2.2 ∂Q) ∧
    ∀ π : X → ℝ, Measurable π → ∀ δ' > 0, (∀ x, δ' ≤ π x) →
      ∫ w, aipwScore m₀ π (observe w) ∂Q = ∫ w, w.2.2 ∂Q := by
  refine ⟨fun δ hδ hπ₀ m hmm hm ↦ ?_, fun π hπm δ' hδ' hπ ↦ ?_⟩
  · have := integral_aipwScore_sub Q π₀ m₀ m π₀ hmar hY hm₀ hreg hm hmm hmar.measurable δ hδ
      hπ₀ hm₀i
    simpa [sub_eq_zero] using this
  · have := integral_aipwScore_sub Q π₀ m₀ m₀ π hmar hY hm₀ hreg hm₀i hm₀ hπm δ' hδ' hπ hm₀i
    simpa [sub_eq_zero] using this

/-- **The product bound on the bias.** Under the hypotheses of the mixed-bias identity,
`|E φ_{m,π} - E Y| ≤ δ⁻¹ ‖π - π₀‖₂ ‖m - m₀‖₂`, with the `L²(Q)` norms of `π(X) - π₀(X)` and
`m(X) - m₀(X)` in `ℝ≥0∞`. -/
theorem abs_integral_aipwScore_sub_le (Q : Measure (Bool × X × ℝ)) [IsFiniteMeasure Q]
    (π₀ m₀ m π : X → ℝ) (hmar : IsMissingAtRandom Q π₀)
    (hY : Integrable (fun w : Bool × X × ℝ ↦ w.2.2) Q) (hm₀ : Measurable m₀)
    (hreg : ∀ A : Set X, MeasurableSet A →
      ∫ w in {w | w.2.1 ∈ A}, w.2.2 ∂Q = ∫ w in {w | w.2.1 ∈ A}, m₀ w.2.1 ∂Q)
    (hm : Integrable (fun w : Bool × X × ℝ ↦ m w.2.1) Q) (hmm : Measurable m)
    (hπm : Measurable π) (δ : ℝ) (hδ : 0 < δ) (hπ : ∀ x, δ ≤ π x)
    (hm₀i : Integrable (fun w : Bool × X × ℝ ↦ m₀ w.2.1) Q) :
    ENNReal.ofReal |∫ w, aipwScore m π (observe w) ∂Q - ∫ w, w.2.2 ∂Q| ≤
      ENNReal.ofReal δ⁻¹ * eLpNorm (fun w : Bool × X × ℝ ↦ π w.2.1 - π₀ w.2.1) 2 Q *
        eLpNorm (fun w : Bool × X × ℝ ↦ m w.2.1 - m₀ w.2.1) 2 Q := by
  have hπ0 : ∀ x, 0 < π x := fun x ↦ hδ.trans_le (hπ x)
  have hπ₀m := hmar.measurable
  rw [integral_aipwScore_sub Q π₀ m₀ m π hmar hY hm₀ hreg hm hmm hπm δ hδ hπ hm₀i,
    ← Real.eNorm_eq_ofReal_abs]
  calc ‖∫ w, (π₀ w.2.1 - π w.2.1) * (m₀ w.2.1 - m w.2.1) / π w.2.1 ∂Q‖ₑ
      ≤ ∫⁻ w, ‖(π₀ w.2.1 - π w.2.1) * (m₀ w.2.1 - m w.2.1) / π w.2.1‖ₑ ∂Q :=
        eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ w, ENNReal.ofReal δ⁻¹ * ‖(π w.2.1 - π₀ w.2.1) * (m w.2.1 - m₀ w.2.1)‖ₑ ∂Q := by
        refine lintegral_mono fun w ↦ ?_
        rw [div_eq_mul_inv, eNorm_mul, mul_comm, ← neg_sub (π w.2.1), ← neg_sub (m w.2.1),
          neg_mul_neg]
        gcongr
        rw [Real.eNorm_eq_ofReal_abs, abs_of_pos (inv_pos.2 (hπ0 _))]
        exact ENNReal.ofReal_le_ofReal (inv_anti₀ hδ (hπ _))
    _ = ENNReal.ofReal δ⁻¹ *
        eLpNorm (fun w : Bool × X × ℝ ↦ (π w.2.1 - π₀ w.2.1) * (m w.2.1 - m₀ w.2.1)) 1 Q := by
        rw [lintegral_const_mul _ (by fun_prop), eLpNorm_one_eq_lintegral_eNorm (by fun_prop)]
    _ ≤ ENNReal.ofReal δ⁻¹ * (eLpNorm (fun w : Bool × X × ℝ ↦ π w.2.1 - π₀ w.2.1) 2 Q *
        eLpNorm (fun w : Bool × X × ℝ ↦ m w.2.1 - m₀ w.2.1) 2 Q) := by
        gcongr
        simpa using eLpNorm_le_eLpNorm_mul_eLpNorm (p := 2) (q := 2) (r := 1) (μ := Q)
          (fun a b : ℝ ↦ a * b) 1 continuous_mul (by fun_prop) (by fun_prop)
          (ae_of_all _ fun w ↦ by simp)
    _ = _ := by rw [mul_assoc]

end TauCeti
