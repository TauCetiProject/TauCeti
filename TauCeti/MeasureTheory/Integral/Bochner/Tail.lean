/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tail Bochner integrals on ordered spaces

For a real-valued function `f` on a linearly ordered space `ι` whose order intervals are closed in
its topology, the tail integral `Ψ v = ∫ t in Ioi v, f t ∂μ` is Borel measurable without any
integrability or countability assumption on `f` or `μ`. When `f` is integrable, the weighted tails
`v ↦ f v * Ψ v ^ k` and `v ↦ f v * exp (Ψ v)` are integrable, and when `ι` is second countable and
`μ` vanishes on singletons they satisfy the power-rule and exponential-rule identities

* `∫ v, f v * (∫ t in Ioi v, f t ∂μ) ^ k ∂μ = (∫ v, f v ∂μ) ^ (k + 1) / (k + 1)`,
* `∫ v, f v * exp (∫ t in Ioi v, f t ∂μ) ∂μ = exp (∫ v, f v ∂μ) - 1`,

together with their restrictions to an arbitrary set `s`. These are the continuous counterparts of
`Summable.mul_pow_tsum_Ioi` and `Summable.tsum_Ioi_mul_pow_tsum_Ioi_le`, and control the Picard
iterates and derivative bounds of Volterra integral equations.

## Main statements

* `MeasureTheory.measurable_integral_Ioi`: `v ↦ ∫ t in Ioi v, f t ∂μ` is measurable.
* `MeasureTheory.Integrable.mul_pow_integral_Ioi` and
  `MeasureTheory.IntegrableOn.mul_pow_setIntegral_Ioi`: integrability of `f v * Ψ v ^ k`.
* `MeasureTheory.Integrable.integral_mul_pow_integral_Ioi` and
  `MeasureTheory.IntegrableOn.setIntegral_mul_pow_setIntegral_Ioi`: the tail power-rule identity.
* `MeasureTheory.Integrable.mul_exp_integral_Ioi` and
  `MeasureTheory.IntegrableOn.mul_exp_setIntegral_Ioi`: integrability of `f v * exp (Ψ v)`.
* `MeasureTheory.Integrable.integral_mul_exp_integral_Ioi` and
  `MeasureTheory.IntegrableOn.setIntegral_mul_exp_setIntegral_Ioi`: the tail exponential identity.
-/

public section

open Set Filter
open scoped Nat

namespace MeasureTheory

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderClosedTopology ι]
  [MeasurableSpace ι] [OpensMeasurableSpace ι] {μ : Measure ι} {f : ι → ℝ}

/-- If `g ≥ 0` is integrable on `Ioi v` for every `v` in an upward-closed set `S`, the truncated
tail integral `if v ∈ S then ∫ t in Ioi v, g t ∂μ else 0` is measurable. -/
private lemma measurable_ite_integral_Ioi_of_nonneg {S : Set ι}
    (hS : ∀ ⦃a b⦄, a ∈ S → a ≤ b → b ∈ S) {g : ι → ℝ} (hg0 : ∀ t, 0 ≤ g t)
    (hg : ∀ v ∈ S, IntegrableOn g (Ioi v) μ) [DecidablePred (· ∈ S)] :
    Measurable fun v ↦ if v ∈ S then ∫ t in Ioi v, g t ∂μ else 0 := by
  set h : ι → ℝ := fun v ↦ if v ∈ S then ∫ t in Ioi v, g t ∂μ else 0
  refine measurable_of_Ioi fun r ↦ Set.OrdConnected.measurableSet ⟨fun a ha b hb x hx ↦ ?_⟩
  have hh0 : 0 ≤ h x := by
    dsimp only [h]
    split_ifs with hxS
    · exact integral_nonneg hg0
    · exact le_rfl
  rcases lt_or_ge r 0 with hr | hr
  · exact hr.trans_le hh0
  · have haS : a ∈ S := by
      by_contra haS
      exact lt_irrefl 0 (hr.trans_lt (by simpa [h, haS] using ha))
    have hxS : x ∈ S := hS haS hx.1
    have hbS : b ∈ S := hS hxS hx.2
    have hbx : h b ≤ h x := by
      simp only [h, hbS, hxS, ↓reduceIte]
      exact setIntegral_mono_set (hg x hxS) (ae_of_all _ hg0) (ae_of_all _ (Ioi_subset_Ioi hx.2))
    exact lt_of_lt_of_le hb hbx

/-- The tail Bochner integral `v ↦ ∫ t in Ioi v, f t ∂μ` of a real-valued function on a linearly
ordered space with order-closed topology is Borel measurable, with no integrability assumption on
`f` and no finiteness assumption on `μ`. -/
theorem measurable_integral_Ioi (f : ι → ℝ) (μ : Measure ι) :
    Measurable fun v ↦ ∫ t in Ioi v, f t ∂μ := by
  classical
  set S : Set ι := {v | IntegrableOn f (Ioi v) μ}
  have hS : ∀ ⦃a b⦄, a ∈ S → a ≤ b → b ∈ S := fun a b ha hab ↦ ha.mono_set (Ioi_subset_Ioi hab)
  have hm₁ := measurable_ite_integral_Ioi_of_nonneg hS (fun t ↦ NNReal.coe_nonneg _)
    fun v (hv : IntegrableOn f (Ioi v) μ) ↦ hv.real_toNNReal
  have hm₂ := measurable_ite_integral_Ioi_of_nonneg hS (fun t ↦ NNReal.coe_nonneg _)
    fun v (hv : IntegrableOn f (Ioi v) μ) ↦ hv.neg.real_toNNReal
  have hEq : (fun v ↦ ∫ t in Ioi v, f t ∂μ) =
      (fun v ↦ if v ∈ S then ∫ t in Ioi v, (Real.toNNReal (f t) : ℝ) ∂μ else 0) -
        fun v ↦ if v ∈ S then ∫ t in Ioi v, (Real.toNNReal (-f t) : ℝ) ∂μ else 0 := by
    ext v
    by_cases hv : v ∈ S
    · simp only [Pi.sub_apply, hv, ↓reduceIte,
        integral_eq_integral_pos_part_sub_integral_neg_part hv]
    · simp [hv, integral_undef hv]
  rw [hEq]
  exact hm₁.sub hm₂

/-- Rewriting a tail integral with respect to `μ.restrict s` as a set integral over `s ∩ Ioi v`. -/
private lemma integral_Ioi_restrict (s : Set ι) (v : ι) :
    ∫ t in Ioi v, f t ∂μ.restrict s = ∫ t in s ∩ Ioi v, f t ∂μ := by
  rw [Measure.restrict_restrict measurableSet_Ioi, inter_comm]

omit [TopologicalSpace ι] [OrderClosedTopology ι] [OpensMeasurableSpace ι] in
/-- Pointwise norm bound `‖∫ t in Ioi v, f t ∂μ‖ ≤ ∫ t, ‖f t‖ ∂μ` for an integrable function. -/
private lemma norm_integral_Ioi_le (hf : Integrable f μ) (v : ι) :
    ‖∫ t in Ioi v, f t ∂μ‖ ≤ ∫ t, ‖f t‖ ∂μ :=
  (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral hf.norm (ae_of_all _ fun _ ↦ norm_nonneg _))

/-- If `f : ι → ℝ` is integrable, then `v ↦ f v * (∫ t in Ioi v, f t ∂μ) ^ k` is integrable for
every `k : ℕ`. -/
theorem Integrable.mul_pow_integral_Ioi (hf : Integrable f μ) (k : ℕ) :
    Integrable (fun v ↦ f v * (∫ t in Ioi v, f t ∂μ) ^ k) μ := by
  refine hf.mul_bdd ((measurable_integral_Ioi f μ).pow_const k).aestronglyMeasurable
    (c := (∫ t, ‖f t‖ ∂μ) ^ k) (ae_of_all _ fun v ↦ ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_integral_Ioi_le hf v) k

/-- Set-integral form of `Integrable.mul_pow_integral_Ioi` on an arbitrary set `s`. -/
theorem IntegrableOn.mul_pow_setIntegral_Ioi {s : Set ι} (hf : IntegrableOn f s μ) (k : ℕ) :
    IntegrableOn (fun v ↦ f v * (∫ t in s ∩ Ioi v, f t ∂μ) ^ k) s μ := by
  simpa only [IntegrableOn, integral_Ioi_restrict] using hf.mul_pow_integral_Ioi k

/-- Sigma-finite case of `Integrable.integral_mul_pow_integral_Ioi`. -/
private lemma integral_mul_pow_integral_Ioi_of_sigmaFinite [SecondCountableTopology ι]
    [SigmaFinite μ] [NullSingletonClass μ] (hf : Integrable f μ) (k : ℕ) :
    ∫ v, f v * (∫ t in Ioi v, f t ∂μ) ^ k ∂μ = (∫ v, f v ∂μ) ^ (k + 1) / (k + 1) := by
  induction k generalizing μ with
  | zero => simp
  | succ k ih =>
    set Ψ : ι → ℝ := fun v ↦ ∫ t in Ioi v, f t ∂μ
    set g : ι → ℝ := fun v ↦ f v * Ψ v ^ k
    have hg : Integrable g μ := hf.mul_pow_integral_Ioi k
    set G : ι × ι → ℝ := {p : ι × ι | p.1 < p.2}.indicator fun p ↦ f p.1 * g p.2
    have hG : Integrable G (μ.prod μ) := (hf.mul_prod hg).indicator measurableSet_lt'
    have hfub : ∫ u, ∫ v, G (u, v) ∂μ ∂μ = ∫ v, ∫ u, G (u, v) ∂μ ∂μ :=
      (integral_prod G hG).symm.trans (integral_prod_symm G hG)
    have hlhs : ∫ u, ∫ v, G (u, v) ∂μ ∂μ =
        (∫ u, f u * Ψ u ^ (k + 1) ∂μ) / (k + 1) := by
      have hinner (u : ι) : ∫ v, G (u, v) ∂μ = f u * Ψ u ^ (k + 1) / (k + 1) := by
        have hind : (fun v ↦ G (u, v)) = (Ioi u).indicator fun v ↦ f u * g v := rfl
        have hEq : EqOn g (fun v ↦ f v * (∫ t in Ioi v, f t ∂μ.restrict (Ioi u)) ^ k) (Ioi u) :=
          fun v hv ↦ by
            simp [g, Ψ, Ioi_inter_Ioi, max_eq_left (le_of_lt hv)]
        rw [hind, integral_indicator measurableSet_Ioi, integral_const_mul,
          setIntegral_congr_fun measurableSet_Ioi hEq, ih hf.integrableOn, mul_div_assoc]
      simp_rw [hinner, integral_div]
    have hrhs : ∫ v, ∫ u, G (u, v) ∂μ ∂μ =
        (∫ u, f u ∂μ) * ((∫ u, f u ∂μ) ^ (k + 1) / (k + 1)) - ∫ v, f v * Ψ v ^ (k + 1) ∂μ := by
      have hinner (v : ι) :
          ∫ u, G (u, v) ∂μ = (∫ u, f u ∂μ) * g v - f v * Ψ v ^ (k + 1) := by
        have hind : (fun u ↦ G (u, v)) = (Iio v).indicator fun u ↦ f u * g v := rfl
        have hsplit : ∫ u in Iio v, f u ∂μ = (∫ u, f u ∂μ) - Ψ v := by
          rw [← integral_Iic_eq_integral_Iio]
          have hadd := integral_add_compl (s := Iic v) measurableSet_Iic hf
          rw [compl_Iic] at hadd
          linarith
        rw [hind, integral_indicator measurableSet_Iio, integral_mul_const, hsplit]
        dsimp only [g]
        ring
      simp_rw [hinner]
      rw [integral_sub (hg.const_mul _) (hf.mul_pow_integral_Ioi (k + 1)),
        integral_const_mul, ih hf]
    rw [hlhs, hrhs] at hfub
    dsimp only [Ψ] at hfub
    field_simp at hfub ⊢
    rw [← pow_succ'] at hfub
    push_cast at hfub ⊢
    linarith

/-- **Tail power rule for Bochner integrals.** On a second-countable linearly ordered space with
order-closed topology and a measure vanishing on singletons, every integrable function `f : ι → ℝ`
satisfies `∫ v, f v * (∫ t in Ioi v, f t ∂μ) ^ k ∂μ = (∫ v, f v ∂μ) ^ (k + 1) / (k + 1)`. No
`SFinite` or `SigmaFinite` assumption on `μ` is required. -/
theorem Integrable.integral_mul_pow_integral_Ioi [SecondCountableTopology ι] [NullSingletonClass μ]
    (hf : Integrable f μ) (k : ℕ) :
    ∫ v, f v * (∫ t in Ioi v, f t ∂μ) ^ k ∂μ = (∫ v, f v ∂μ) ^ (k + 1) / (k + 1) := by
  set s := hf.aefinStronglyMeasurable.sigmaFiniteSet
  have hs : MeasurableSet s := hf.aefinStronglyMeasurable.measurableSet
  have hs0 : f =ᵐ[μ.restrict sᶜ] 0 := hf.aefinStronglyMeasurable.ae_eq_zero_compl
  have hzero : ∀ {F : ι → ℝ}, Integrable F μ → (∀ x, f x = 0 → F x = 0) →
      ∫ x, F x ∂μ = ∫ x in s, F x ∂μ := fun hF hFf ↦ by
    rw [← integral_add_compl hs hF,
      integral_eq_zero_of_ae (hs0.mono fun x hx ↦ hFf x hx), add_zero]
  have htail (v : ι) : ∫ t in Ioi v, f t ∂μ = ∫ t in Ioi v, f t ∂μ.restrict s := by
    rw [← integral_add_compl hs hf.integrableOn, Measure.restrict_comm hs.compl,
      integral_eq_zero_of_ae (ae_restrict_of_ae hs0), add_zero, Measure.restrict_comm hs]
  rw [hzero (hf.mul_pow_integral_Ioi k) (fun x hx ↦ by simp [hx]), hzero hf (fun _ hx ↦ hx)]
  simp_rw [htail]
  exact integral_mul_pow_integral_Ioi_of_sigmaFinite hf.integrableOn k

/-- Set-integral form of `Integrable.integral_mul_pow_integral_Ioi` on an arbitrary set `s`. -/
theorem IntegrableOn.setIntegral_mul_pow_setIntegral_Ioi [SecondCountableTopology ι]
    [NullSingletonClass μ] {s : Set ι} (hf : IntegrableOn f s μ) (k : ℕ) :
    ∫ v in s, f v * (∫ t in s ∩ Ioi v, f t ∂μ) ^ k ∂μ =
      (∫ v in s, f v ∂μ) ^ (k + 1) / (k + 1) := by
  simpa only [integral_Ioi_restrict] using hf.integral_mul_pow_integral_Ioi k

/-- If `f : ι → ℝ` is integrable, then `v ↦ f v * exp (∫ t in Ioi v, f t ∂μ)` is integrable. -/
theorem Integrable.mul_exp_integral_Ioi (hf : Integrable f μ) :
    Integrable (fun v ↦ f v * Real.exp (∫ t in Ioi v, f t ∂μ)) μ := by
  refine hf.mul_bdd (Real.continuous_exp.measurable.comp
    (measurable_integral_Ioi f μ)).aestronglyMeasurable
    (c := Real.exp (∫ t, ‖f t‖ ∂μ)) (ae_of_all _ fun v ↦ ?_)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (norm_integral_Ioi_le hf v))

/-- Set-integral form of `Integrable.mul_exp_integral_Ioi` on an arbitrary set `s`. -/
theorem IntegrableOn.mul_exp_setIntegral_Ioi {s : Set ι} (hf : IntegrableOn f s μ) :
    IntegrableOn (fun v ↦ f v * Real.exp (∫ t in s ∩ Ioi v, f t ∂μ)) s μ := by
  simpa only [IntegrableOn, integral_Ioi_restrict] using hf.mul_exp_integral_Ioi

/-- **Tail exponential identity for Bochner integrals.** On a second-countable linearly ordered
space with order-closed topology and a measure vanishing on singletons, every integrable function
`f : ι → ℝ` satisfies
`∫ v, f v * exp (∫ t in Ioi v, f t ∂μ) ∂μ = exp (∫ v, f v ∂μ) - 1`. -/
theorem Integrable.integral_mul_exp_integral_Ioi [SecondCountableTopology ι] [NullSingletonClass μ]
    (hf : Integrable f μ) :
    ∫ v, f v * Real.exp (∫ t in Ioi v, f t ∂μ) ∂μ = Real.exp (∫ v, f v ∂μ) - 1 := by
  set Ψ : ι → ℝ := fun v ↦ ∫ t in Ioi v, f t ∂μ
  set F : ℕ → ι → ℝ := fun k v ↦ f v * (Ψ v ^ k / k !)
  have hF_int (k : ℕ) : Integrable (F k) μ := by
    simpa only [F, mul_div_assoc] using (hf.mul_pow_integral_Ioi k).div_const (k ! : ℝ)
  have hF_sum : Summable fun k ↦ ∫ v, ‖F k v‖ ∂μ := by
    set M := ∫ t, ‖f t‖ ∂μ
    refine ((Real.summable_pow_div_factorial M).mul_left M).of_nonneg_of_le
      (fun k ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun k ↦ ?_
    have hpt (v : ι) : ‖F k v‖ ≤ ‖f v‖ * (M ^ k / k !) := by
      dsimp only [F]
      rw [norm_mul, norm_div, norm_pow, Real.norm_natCast]
      gcongr
      exact norm_integral_Ioi_le hf v
    exact (integral_mono (hF_int k).norm (hf.norm.mul_const _) hpt).trans_eq
      (integral_mul_const _ _)
  have hpt_sum (v : ι) : ∑' k, F k v = f v * Real.exp (∫ t in Ioi v, f t ∂μ) := by
    rw [Real.exp_eq_exp_ℝ]
    exact ((NormedSpace.expSeries_div_hasSum_exp (Ψ v)).mul_left (f v)).tsum_eq
  simp_rw [← hpt_sum, ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
  have hterm (k : ℕ) : ∫ v, F k v ∂μ = (∫ v, f v ∂μ) ^ (k + 1) / (k + 1)! := by
    simp only [F, Ψ, ← mul_div_assoc, integral_div, hf.integral_mul_pow_integral_Ioi k, div_div,
      Nat.factorial_succ]
    push_cast
    ring
  simp_rw [hterm]
  have hexp := NormedSpace.expSeries_div_hasSum_exp (∫ v, f v ∂μ)
  rw [Real.exp_eq_exp_ℝ, ← hexp.tsum_eq, hexp.summable.tsum_eq_zero_add]
  norm_num

/-- Set-integral form of `Integrable.integral_mul_exp_integral_Ioi` on an arbitrary set `s`. -/
theorem IntegrableOn.setIntegral_mul_exp_setIntegral_Ioi [SecondCountableTopology ι]
    [NullSingletonClass μ] {s : Set ι} (hf : IntegrableOn f s μ) :
    ∫ v in s, f v * Real.exp (∫ t in s ∩ Ioi v, f t ∂μ) ∂μ =
      Real.exp (∫ v in s, f v ∂μ) - 1 := by
  simpa only [integral_Ioi_restrict] using hf.integral_mul_exp_integral_Ioi

end MeasureTheory
