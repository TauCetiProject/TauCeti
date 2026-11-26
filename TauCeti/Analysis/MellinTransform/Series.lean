/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform

import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Mellin transforms of series of dilates

Absolute summability in the weighted `L¹` norm permits a Mellin transform to be taken term by
term. For a sum of dilates of a single kernel, the integrability test then reduces to a series
in the dilation parameters, as in Mellin representations of Dirichlet series.
-/

public section

open Complex MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {ι E : Type*} [Countable ι] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Mellin transform of a series converges absolutely and equals the sum of the transforms
if the individual Mellin integrands are integrable and their `L¹` norms are summable. -/
theorem hasMellin_tsum {f : ι → ℝ → E} {s : ℂ} (hf : ∀ i, MellinConvergent (f i) s)
    (hs : Summable fun i ↦ ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) • f i t‖) :
    HasMellin (fun t ↦ ∑' i, f i t) s (∑' i, mellin (f i) s) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F (i : ι) (t : ℝ) := (t : ℂ) ^ (s - 1) • f i t
  have hF (i : ι) : Integrable (F i) μ := hf i
  let G (i : ι) : ℝ →₁[μ] E := (hF i).toL1 (F i)
  have hG : ∑' i, ‖G i‖ₑ ≠ ∞ := by
    have (i : ι) : ‖G i‖ₑ = ‖∫ t, ‖F i t‖ ∂μ‖ₑ :=
      (hF i).eNorm_toL1.trans (eNorm_integral_norm_eq_lintegral_eNorm (hF i)).symm
    simp_rw [this]
    exact tsum_eNorm_ne_top_iff_summable_norm.mpr
      (by simpa only [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)] using hs)
  have hsum : (fun t ↦ ∑' i, G i t) =ᵐ[μ] fun t ↦ ∑' i, F i t := by
    filter_upwards [ae_all_iff.mpr fun i ↦ (hF i).coeFn_toL1] with t ht
    exact tsum_congr ht
  have heq (t : ℝ) : (t : ℂ) ^ (s - 1) • (∑' i, f i t) = ∑' i, F i t :=
    (tsum_const_smul'' _).symm
  exact ⟨(L1.integrable_coeFn (∑' i, G i)).congr
    (((Lp.coeFn_tsum hG).trans hsum).trans (ae_of_all μ fun t ↦ (heq t).symm)), by
    simp_rw [mellin, heq]
    exact (integral_tsum_of_summable_integral_norm hF hs).symm⟩

end TauCeti

namespace HasMellin

open TauCeti

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Dilations of a common Mellin kernel can be integrated term by term if the norms of the
scaled coefficients are summable. Each positive dilation `a i` contributes `(a i)^(-s)`. -/
theorem tsum_smul_comp_mul_right {f : ℝ → E} {s : ℂ} {m : E} (h : HasMellin f s m)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {c : ι → ℂ}
    (hc : Summable fun i ↦ ‖c i‖ * a i ^ (-s.re)) :
    HasMellin (fun t ↦ ∑' i, c i • f (t * a i)) s ((∑' i, c i * (a i : ℂ) ^ (-s)) • m) := by
  have hcs : Summable fun i ↦ c i * (a i : ℂ) ^ (-s) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_cpow_eq_rpow_re_of_pos (ha _), neg_re] using hc
  let I := Function.support c
  have hcount : I.Countable := by
    apply hcs.countable_support.mono
    intro i hi
    apply mul_ne_zero hi
    rw [Ne, cpow_eq_zero_iff]
    simp [(ha i).ne']
  let : Countable I := hcount.to_subtype
  have hterm (i : I) : HasMellin (fun t ↦ c i • f (t * a i)) s
      ((c i * (a i : ℂ) ^ (-s)) • m) := by
    have hd := h.comp_mul_right (ha i)
    simpa only [hd.2, smul_smul] using hasMellin_const_smul hd.1 (c i)
  have hnorm (i : I) : (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) • (c i • f (t * a i))‖) =
      (‖c i‖ * a i ^ (-s.re)) * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) • f t‖ := by
    calc
      _ = ∫ t : ℝ in Ioi 0, ‖c i‖ * a i ^ (1 - s.re) *
          ‖((t * a i : ℝ) : ℂ) ^ (s - 1) • f (t * a i)‖ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
        simp only [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re,
          norm_cpow_eq_rpow_re_of_pos (mul_pos ht (ha i)), Real.mul_rpow ht.le (ha i).le]
        have hcancel : a i ^ (s.re - 1) * a i ^ (1 - s.re) = 1 := by
          simp [← Real.rpow_add (ha i)]
        calc
          _ = t ^ (s.re - 1) * (‖c i‖ * ‖f (t * a i)‖) *
              (a i ^ (s.re - 1) * a i ^ (1 - s.re)) := by rw [hcancel, mul_one]
          _ = _ := by ring
      _ = _ := by
        rw [integral_const_mul, integral_comp_mul_right_Ioi
          (fun t : ℝ ↦ ‖(t : ℂ) ^ (s - 1) • f t‖) 0 (ha i), zero_mul, smul_eq_mul,
          ← mul_assoc, mul_assoc ‖c i‖, ← Real.rpow_neg_one, ← Real.rpow_add (ha i)]
        congr 3
        ring
  have H := hasMellin_tsum (fun i ↦ (hterm i).1)
    (by simpa only [hnorm, Function.comp_apply] using (hc.subtype (· ∈ I)).mul_right _)
  have hkernel (t : ℝ) : (∑' i : I, c i • f (t * a i)) = ∑' i, c i • f (t * a i) :=
    tsum_subtype_eq_of_support_subset (f := fun i ↦ c i • f (t * a i)) (s := I) fun i hi ↦
      Function.mem_support.mpr fun hz ↦ hi (by simp [hz])
  have hcoeff : (∑' i : I, c i * (a i : ℂ) ^ (-s)) = ∑' i, c i * (a i : ℂ) ^ (-s) :=
    tsum_subtype_eq_of_support_subset (f := fun i ↦ c i * (a i : ℂ) ^ (-s)) (s := I) fun i hi ↦
      Function.mem_support.mpr fun hz ↦ hi (by simp [hz])
  have hsum : HasSum (fun i : I ↦ c i * (a i : ℂ) ^ (-s))
      (∑' i : I, c i * (a i : ℂ) ^ (-s)) := (hcs.subtype (· ∈ I)).hasSum
  simpa only [hkernel, (hterm _).2, (hsum.smul_const m).tsum_eq, hcoeff] using H

end HasMellin
