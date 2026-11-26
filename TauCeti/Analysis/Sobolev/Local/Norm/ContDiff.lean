/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Calculus.ContDiff.Integrable
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

/-!
# The `W^{k,p}` size of a `Cᵏ` function

For a function `f` that is `Cᵏ` on an open planar set `S`, the classical derivative is a weak
derivative, so the extended `W^{k,p}(S)` norm `TauCeti.eLpNormWkp p S k f` is the sum of the
`Lᵖ(S)` norms of the classical iterated derivatives of `f` of orders `0` through `k`
(`TauCeti.eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv`).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {p : ℝ≥0∞}

/-- The `Lᵖ` norm of a function `Cᵐ` on an open set `S` is that of its zeroth derivative. -/
private theorem eLpNorm_eq_eLpNorm_iteratedFDeriv_zero {S : Set ℂ} (hS : IsOpen S) {m : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}
    (hf : ContDiffOn ℝ m f S) :
    eLpNorm f p (volume.restrict S) = eLpNorm (iteratedFDeriv ℝ 0 f) p (volume.restrict S) :=
  eLpNorm_congr_norm_ae (hf.continuousOn.aestronglyMeasurable hS.measurableSet)
    (hf.aestronglyMeasurable_iteratedFDeriv hS (Nat.zero_le m))
    (ae_of_all _ fun _ ↦ (norm_iteratedFDeriv_zero).symm)

/-- **The `W^{k,p}` norm of a `Cᵏ` function.** On an open set `S`, the `W^{k,p}(S)` norm of a
function that is `Cᵏ` on `S` is the sum of the `Lᵖ(S)` norms of its classical iterated derivatives
of orders `0` through `k`. -/
theorem eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv {S : Set ℂ} (hS : IsOpen S) (k : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F}
    (hf : ContDiffOn ℝ k f S) :
    eLpNormWkp p S k f =
      ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l f) p (volume.restrict S) := by
  induction k generalizing F f with
  | zero => rw [eLpNormWkp_zero, Finset.sum_range_one, eLpNorm_eq_eLpNorm_iteratedFDeriv_zero hS hf]
  | succ k ih =>
    have hD : HasWeakFDerivOn volume (⟨S, hS⟩ : TopologicalSpace.Opens ℂ) f (fderiv ℝ f) :=
      (hf.of_le (by exact_mod_cast Nat.le_add_left 1 k)).hasWeakFDerivOn_fderiv
    have hf' : ContDiffOn ℝ k (fderiv ℝ f) S :=
      hf.fderiv_of_isOpen hS (by exact_mod_cast le_rfl)
    have h := eLpNormWkp_succ_eq_of_hasWeakFDerivOn (p := p) (k := k) hD
    rw [TopologicalSpace.Opens.coe_mk] at h
    rw [h, ih hf', Finset.sum_range_succ' _ (k + 1), add_comm,
      eLpNorm_eq_eLpNorm_iteratedFDeriv_zero hS hf]
    congr 1
    refine Finset.sum_congr rfl fun l hl ↦ eLpNorm_congr_norm_ae
      (hf'.aestronglyMeasurable_iteratedFDeriv hS (Finset.mem_range_succ_iff.1 hl))
      (hf.aestronglyMeasurable_iteratedFDeriv hS
        (Nat.succ_le_succ (Finset.mem_range_succ_iff.1 hl)))
      (ae_of_all _ fun _ ↦ norm_iteratedFDeriv_fderiv)

end TauCeti
