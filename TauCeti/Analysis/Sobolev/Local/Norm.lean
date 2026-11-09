/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The `W^{k,p}` size of a function on a planar set

`TauCeti.eLpNormWkp p U k f` is the extended `W^{k,p}(U)` norm of `f : ℂ → F`, for a real normed
space `F`: the `Lᵖ(U)` norm of `f` plus, recursively, the `W^{k-1,p}(U)` size of its weak
derivative on `interior U`, minimized over all weak derivatives. It is `∞` when no weak
derivative exists, or when one of the norms is infinite. Its derivatives are taken on the
interior and its norms on `U` itself, matching `TauCeti.MemWkpLoc`. On an open set weak
derivatives are unique almost everywhere, so the minimum is attained by every weak derivative.

This is the quantity in which interior estimates of elliptic equations are stated. The file
supplies its unfolding, monotonicity in the set, invariance under almost-everywhere change, the
triangle inequality and the operator-norm bound under a continuous linear map of the codomain.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p : ℝ≥0∞} {U V : Set ℂ} {k : ℕ} {f g : ℂ → F}

/-- The extended `W^{k,p}(U)` norm: the `Lᵖ(U)` norm of `f` plus the smallest `W^{k-1,p}(U)` norm
of a weak derivative of `f` on `interior U`. It is `∞` when no weak derivative exists. -/
def eLpNormWkp (p : ℝ≥0∞) (U : Set ℂ) :
    (k : ℕ) → {F : Type*} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℂ → F) → ℝ≥0∞
  | 0, _, _, _, f => eLpNorm f p (volume.restrict U)
  | k + 1, F, _, _, f => eLpNorm f p (volume.restrict U) +
      ⨅ (D : ℂ → ℂ →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
        eLpNormWkp p U k D

/-- At order zero the `W^{k,p}` norm is the `Lᵖ` norm. -/
@[simp]
theorem eLpNormWkp_zero : eLpNormWkp p U 0 f = eLpNorm f p (volume.restrict U) := by
  rw [eLpNormWkp]

/-- The successor-order unfolding of the `W^{k,p}` norm. -/
theorem eLpNormWkp_succ : eLpNormWkp p U (k + 1) f = eLpNorm f p (volume.restrict U) +
    ⨅ (D : ℂ → ℂ →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
      eLpNormWkp p U k D := by
  rw [eLpNormWkp]

/-- The `Lᵖ` norm is bounded by every `W^{k,p}` norm. -/
theorem eLpNorm_le_eLpNormWkp : eLpNorm f p (volume.restrict U) ≤ eLpNormWkp p U k f := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_self_add

/-- Any weak derivative bounds the successor-order norm. -/
theorem eLpNormWkp_succ_le {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f ≤ eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D := by
  rw [eLpNormWkp_succ]
  gcongr
  exact iInf₂_le D hD

/-- The `W^{k,p}` norm increases with the set. -/
theorem eLpNormWkp_mono_set (hVU : V ⊆ U) : eLpNormWkp p V k f ≤ eLpNormWkp p U k f := by
  induction k generalizing F with
  | zero => exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ]
    gcongr ?_ + ?_
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
    · exact le_iInf₂ fun D hD => iInf₂_le_of_le D (hD.mono (interior_mono hVU)) ih

/-- Almost-everywhere equality on `U` preserves the `W^{k,p}(U)` norm. -/
theorem eLpNormWkp_congr_ae (hfg : f =ᵐ[volume.restrict U] g) :
    eLpNormWkp p U k f = eLpNormWkp p U k g := by
  cases k with
  | zero => exact eLpNorm_congr_ae hfg
  | succ k =>
    have hint : f =ᵐ[volume.restrict (Opens.interior U)] g :=
      ae_mono (Measure.restrict_mono_set volume interior_subset) hfg
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNorm_congr_ae hfg]
    congr 1
    refine le_antisymm (le_iInf₂ fun D hD => iInf₂_le_of_le D ?_ le_rfl)
      (le_iInf₂ fun D hD => iInf₂_le_of_le D ?_ le_rfl)
    · exact hD.congr_ae (Filter.EventuallyEq.symm hint)
    · exact hD.congr_ae hint

/-- The zero function has zero `W^{k,p}` norm. -/
@[simp]
theorem eLpNormWkp_zero_fun [CompleteSpace F] : eLpNormWkp p U k (0 : ℂ → F) = 0 := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    refine le_antisymm ((eLpNormWkp_succ_le hasWeakFDerivOn_zero).trans ?_) zero_le
    simp [ih]

/-- The triangle inequality for the `W^{k,p}` norm. -/
theorem eLpNormWkp_add_le (hp : 1 ≤ p) :
    eLpNormWkp p U k (f + g) ≤ eLpNormWkp p U k f + eLpNormWkp p U k g := by
  induction k generalizing F with
  | zero => exact eLpNorm_add_le hp
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNormWkp_succ, add_add_add_comm]
    gcongr ?_ + ?_
    · exact eLpNorm_add_le hp
    · exact ENNReal.le_iInf_add_iInf fun D D' => ENNReal.le_iInf_add_iInf fun hD hD' =>
        iInf₂_le_of_le (D + D') (hD.add hD') ih

/-- A continuous linear map of the codomain scales the `Lᵖ` norm by at most its operator norm,
with no measurability assumption. -/
private theorem eLpNorm_clm_comp_le {μ : Measure ℂ} (A : F →L[ℝ] G) :
    eLpNorm (fun z => A (f z)) p μ ≤ ‖A‖ₑ * eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (A.continuous.comp_aestronglyMeasurable hf)
      (Filter.Eventually.of_forall fun z => by
        simpa only [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using
          A.le_opNNNorm (f z)) p
  · by_cases hA : A = 0
    · simp [hA]
    · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top (by
        rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 hA))]
      exact le_top

/-- A continuous linear map of the codomain scales the `W^{k,p}` norm by at most its operator
norm. -/
theorem eLpNormWkp_clm_comp_le [CompleteSpace G] (A : F →L[ℝ] G) :
    eLpNormWkp p U k (fun z => A (f z)) ≤ ‖A‖ₑ * eLpNormWkp p U k f := by
  induction k generalizing F G with
  | zero => exact eLpNorm_clm_comp_le A
  | succ k ih =>
    by_cases hA : A = 0
    · subst hA
      have h0 : (fun z => (0 : F →L[ℝ] G) (f z)) = (0 : ℂ → G) := rfl
      rw [h0, eLpNormWkp_zero_fun]
      exact zero_le
    have hA₀ : ‖A‖ₑ ≠ 0 := by
      rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 hA)
    have hA_top : ‖A‖ₑ ≠ ⊤ := enorm_ne_top
    rw [eLpNormWkp_succ, eLpNormWkp_succ, mul_add]
    gcongr ?_ + ?_
    · exact eLpNorm_clm_comp_le A
    · rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
      refine le_iInf fun D => ?_
      rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
      refine le_iInf fun hD => iInf₂_le_of_le _ (hD.clm_comp A) ?_
      refine (ih (ContinuousLinearMap.compL ℝ ℂ F G A)).trans ?_
      gcongr
      have hle : ‖ContinuousLinearMap.compL ℝ ℂ F G A‖ ≤ ‖A‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun B => A.opNorm_comp_le B
      exact enorm_le_iff_norm_le.2 hle

end TauCeti
