/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm.ContDiff
import TauCeti.Analysis.Calculus.ContDiff.Integrable
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.MeasureTheory.Function.LpSeminorm.Support

/-!
# The Leibniz bound for `Cᵏ` products

Let `V ⊆ U` be open planar sets, let `a` and `f` be `Cᵏ` on `U`, and let `B` be a continuous
bilinear map. If the derivatives of `a` of order at most `k` are bounded by `c` on `V`, and those of
the product `B (a y) (f y)` vanish on `U \ V`, then
`‖B a f‖_{W^{k,p}(U)} ≤ C ‖f‖_{W^{k,p}(V)}`, with `C` depending on `k`, `‖B‖` and `c`
(`TauCeti.eLpNormWkp_bilin_le`). With `V = U` it bounds multiplication by a coefficient with
bounded derivatives; with a cutoff `a` that vanishes near `U \ V` it localizes the norm of `a f` on
`U` to that of `f` on `V`.

## Main results

* `TauCeti.eLpNormWkp_bilin_le`: the Leibniz bound.
* `TauCeti.eLpNormWkp_clm_apply_le`: the bound for a field of continuous linear maps applied to a
  function.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {p : ℝ≥0∞} {G₁ G₂ G₃ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
  [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [CompleteSpace G₂] [NormedAddCommGroup G₃]
  [NormedSpace ℝ G₃] [CompleteSpace G₃]

/-- **The Leibniz bound for the `W^{k,p}` norm.** Let `V ⊆ U` be open, let `a` and `f` be `Cᵏ` on
`U`, and let `B` be a continuous bilinear map. If the derivatives of `a` of order at most `k` are
bounded by `c` on `V`, and those of `y ↦ B (a y) (f y)` vanish on `U \ V`, then the `W^{k,p}(U)`
norm of `y ↦ B (a y) (f y)` is at most `(k + 1) 2ᵏ ‖B‖ c` times the `W^{k,p}(V)`
norm of `f`. -/
theorem eLpNormWkp_bilin_le (hp : 1 ≤ p) (B : G₁ →L[ℝ] G₂ →L[ℝ] G₃) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) {k : ℕ} {a : ℂ → G₁} {f : ℂ → G₂}
    (ha : ContDiffOn ℝ k a U) (hf : ContDiffOn ℝ k f U) {c : ℝ≥0}
    (hc : ∀ x ∈ V, ∀ l ≤ k, ‖iteratedFDeriv ℝ l a x‖ ≤ c)
    (h0 : ∀ x ∈ U \ V, ∀ l ≤ k, iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y)) x = 0) :
    eLpNormWkp p U k (fun y ↦ B (a y) (f y)) ≤
      ((k + 1) * (‖B‖₊ * c * 2 ^ k) : ℝ≥0) * eLpNormWkp p V k f := by
  have hBaf : ContDiffOn ℝ k (fun y ↦ B (a y) (f y)) U :=
    (B.contDiff.comp_contDiffOn ha).clm_apply hf
  set M : ℝ≥0 := ‖B‖₊ * c * 2 ^ k
  set S : ℂ → ℝ := ∑ j ∈ Finset.range (k + 1), fun x ↦ ‖iteratedFDeriv ℝ j f x‖
  have hS (x : ℂ) : S x = ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j f x‖ :=
    Finset.sum_apply x _ _
  have hW : eLpNorm S p (volume.restrict V) ≤ eLpNormWkp p V k f := by
    rw [eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv hV k (hf.mono hVU)]
    refine (eLpNorm_sum_le hp).trans_eq (Finset.sum_congr rfl fun j hj ↦ eLpNorm_norm _
      ((hf.mono hVU).aestronglyMeasurable_iteratedFDeriv hV (Finset.mem_range_succ_iff.1 hj)))
  -- The pointwise Leibniz rule, with every derivative of `f` of order at most `k` bounded by `S`.
  have hpt (x : ℂ) (hx : x ∈ V) (l : ℕ) (hl : l ≤ k) :
      ‖iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y)) x‖ ≤ M * S x := by
    have hxU : U ∈ nhds x := hU.mem_nhds (hVU hx)
    refine (B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le
      ((ha.contDiffAt hxU).of_le (by exact_mod_cast hl))
      ((hf.contDiffAt hxU).of_le (by exact_mod_cast hl)) (M₁ := c) (M₂ := S x)
      (fun i hi ↦ hc x hx i (hi.trans hl)) fun i hi ↦ hS x ▸ Finset.single_le_sum
        (f := fun j ↦ ‖iteratedFDeriv ℝ j f x‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_range_succ_iff.2 (hi.trans hl))).trans ?_
    have hS0 : 0 ≤ S x := hS x ▸ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have h2 : (2 : ℝ) ^ l ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hl
    calc ‖B‖ * 2 ^ l * c * S x = ‖B‖ * c * 2 ^ l * S x := by ring
      _ ≤ ‖B‖ * c * 2 ^ k * S x := by gcongr
      _ = M * S x := by simp [M]
  have hl (l : ℕ) (hl : l ≤ k) :
      eLpNorm (iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y))) p (volume.restrict U) ≤
        M * eLpNormWkp p V k f := by
    -- The derivative vanishes on `U \ V`, so only `V` contributes.
    rw [← eLpNorm_restrict_eq_of_ae_compl_eq_zero (μ := volume.restrict U) hV.nullMeasurableSet
      ((ae_restrict_mem hU.measurableSet).mono fun x hx hxV ↦ h0 x ⟨hx, hxV⟩ l hl),
      Measure.restrict_restrict_of_subset hVU]
    calc eLpNorm (iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y))) p (volume.restrict V)
        ≤ eLpNorm ((M : ℝ) • S) p (volume.restrict V) := by
          refine eLpNorm_mono_ae_real ((hBaf.mono hVU).aestronglyMeasurable_iteratedFDeriv hV hl) ?_
          filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
          simpa only [Pi.smul_apply, smul_eq_mul] using hpt x hx l hl
      _ = M * eLpNorm S p (volume.restrict V) := by
          rw [eLpNorm_const_smul, Real.eNorm_of_nonneg M.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      _ ≤ M * eLpNormWkp p V k f := by gcongr
  rw [eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv hU k hBaf]
  calc ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y))) p
        (volume.restrict U)
      ≤ ∑ _l ∈ Finset.range (k + 1), (M : ℝ≥0∞) * eLpNormWkp p V k f :=
        Finset.sum_le_sum fun l hl' ↦ hl l (Finset.mem_range_succ_iff.1 hl')
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **The Leibniz bound for a field of continuous linear maps applied to a function.** The bound
`TauCeti.eLpNormWkp_bilin_le` for the evaluation `(L, v) ↦ L v`, with constant `(k + 1) 2ᵏ c`. -/
theorem eLpNormWkp_clm_apply_le (hp : 1 ≤ p) {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) {k : ℕ} {a : ℂ → G₂ →L[ℝ] G₃} {f : ℂ → G₂} (ha : ContDiffOn ℝ k a U)
    (hf : ContDiffOn ℝ k f U) {c : ℝ≥0} (hc : ∀ x ∈ V, ∀ l ≤ k, ‖iteratedFDeriv ℝ l a x‖ ≤ c)
    (h0 : ∀ x ∈ U \ V, ∀ l ≤ k, iteratedFDeriv ℝ l (fun y ↦ a y (f y)) x = 0) :
    eLpNormWkp p U k (fun y ↦ a y (f y)) ≤ ((k + 1) * (c * 2 ^ k) : ℝ≥0) * eLpNormWkp p V k f := by
  have h1 : ‖ContinuousLinearMap.id ℝ (G₂ →L[ℝ] G₃)‖₊ * c ≤ c :=
    mul_le_of_le_one_left c.property ContinuousLinearMap.norm_id_le
  exact (eLpNormWkp_bilin_le hp (ContinuousLinearMap.id ℝ (G₂ →L[ℝ] G₃)) hU hV hVU ha hf hc
    h0).trans (by gcongr)

end TauCeti
