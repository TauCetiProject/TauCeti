/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Calculus.CoordinateDeriv
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# `Lᵖ` norms of derivatives of partial derivatives

On `ℝⁿ`, with respect to any measure `μ`, the derivatives of order `i` of the first partial
derivatives `∂ⱼ f` and the derivative of order `i + 1` of `f` control each other in `Lᵖ(μ)`:

* `‖Dⁱ (∂ⱼ f)‖_p ≤ ‖D^(i+1) f‖_p` (`TauCeti.lpNorm_iteratedFDeriv_coordinateDeriv_le`), and in
  particular `Dⁱ (∂ⱼ f) ∈ Lᵖ` when `D^(i+1) f ∈ Lᵖ`
  (`TauCeti.memLp_iteratedFDeriv_coordinateDeriv`), so that the partial derivatives of a smooth
  function with all derivatives in `Lᵖ` are again such functions
  (`TauCeti.memLp_iteratedFDeriv_coordinateDeriv_of_forall`);
* `‖D^(i+1) f‖_p ≤ ∑ⱼ ‖Dⁱ (∂ⱼ f)‖_p` for `1 ≤ p`
  (`TauCeti.lpNorm_iteratedFDeriv_succ_le_sum_coordinateDeriv`).

They are the `Lᵖ` forms of the pointwise bounds `TauCeti.norm_iteratedFDeriv_coordinateDeriv_le`
and `TauCeti.norm_iteratedFDeriv_succ_le_sum_coordinateDeriv`.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} {μ : Measure (CoordinateSpace n)}

/-- A derivative of order `i` of a partial derivative of a `C^(i+1)` function `f` is in `Lᵖ(μ)` if
the derivative of order `i + 1` of `f` is. -/
theorem memLp_iteratedFDeriv_coordinateDeriv {i : ℕ} {f : CoordinateSpace n → F}
    (hf : ContDiff ℝ (i + 1) f) (hfm : MemLp (iteratedFDeriv ℝ (i + 1) f) p μ) (j : Fin n) :
    MemLp (iteratedFDeriv ℝ i (coordinateDeriv [j] f)) p μ :=
  hfm.of_le ((hf.coordinateDeriv_of_le [j] (by simp)).continuous_iteratedFDeriv
      le_rfl).aestronglyMeasurable
    (.of_forall (norm_iteratedFDeriv_coordinateDeriv_le hf j))

/-- The partial derivatives of a smooth function with all derivatives in `Lᵖ(μ)` again have all
derivatives in `Lᵖ(μ)`. -/
theorem memLp_iteratedFDeriv_coordinateDeriv_of_forall {f : CoordinateSpace n → F}
    (hf : ContDiff ℝ ∞ f) (hfm : ∀ i, MemLp (iteratedFDeriv ℝ i f) p μ) (j : Fin n) (i : ℕ) :
    MemLp (iteratedFDeriv ℝ i (coordinateDeriv [j] f)) p μ :=
  memLp_iteratedFDeriv_coordinateDeriv (hf.of_le (by exact_mod_cast le_top)) (hfm _) j

/-- The `Lᵖ(μ)` norm of a derivative of order `i` of a partial derivative of a `C^(i+1)` function
`f` is at most that of the derivative of order `i + 1` of `f`, `‖Dⁱ (∂ⱼ f)‖_p ≤ ‖D^(i+1) f‖_p`, when
the latter is in `Lᵖ(μ)`. -/
theorem lpNorm_iteratedFDeriv_coordinateDeriv_le {i : ℕ} {f : CoordinateSpace n → F}
    (hf : ContDiff ℝ (i + 1) f) (hfm : MemLp (iteratedFDeriv ℝ (i + 1) f) p μ) (j : Fin n) :
    lpNorm (iteratedFDeriv ℝ i (coordinateDeriv [j] f)) p μ ≤
      lpNorm (iteratedFDeriv ℝ (i + 1) f) p μ :=
  (lpNorm_le_mul_lpNorm_of_ae_le_mul
    (memLp_iteratedFDeriv_coordinateDeriv hf hfm j).aestronglyMeasurable hfm
    (.of_forall fun x ↦ (norm_iteratedFDeriv_coordinateDeriv_le hf j x).trans_eq
      (one_mul _).symm)).trans_eq (one_mul _)

/-- For `1 ≤ p`, the `Lᵖ(μ)` norm of the derivative of order `i + 1` of a `C^(i+1)` function is at
most the sum of the `Lᵖ(μ)` norms of the derivatives of order `i` of its partial derivatives,
`‖D^(i+1) f‖_p ≤ ∑ⱼ ‖D^i (∂ⱼ f)‖_p`. -/
theorem lpNorm_iteratedFDeriv_succ_le_sum_coordinateDeriv {i : ℕ} {f : CoordinateSpace n → F}
    (hf : ContDiff ℝ (i + 1) f) (hp : 1 ≤ p) :
    lpNorm (iteratedFDeriv ℝ (i + 1) f) p μ ≤
      ∑ j, lpNorm (iteratedFDeriv ℝ i (coordinateDeriv [j] f)) p μ := by
  by_cases hm : MemLp (iteratedFDeriv ℝ (i + 1) f) p μ
  · have hmj (j : Fin n) := memLp_iteratedFDeriv_coordinateDeriv hf hm j
    have hsum : (fun x ↦ ∑ j, ‖iteratedFDeriv ℝ i (coordinateDeriv [j] f) x‖) =
        ∑ j, fun x ↦ ‖iteratedFDeriv ℝ i (coordinateDeriv [j] f) x‖ := by
      ext x
      simp
    calc lpNorm (iteratedFDeriv ℝ (i + 1) f) p μ
        ≤ lpNorm (fun x ↦ ∑ j, ‖iteratedFDeriv ℝ i (coordinateDeriv [j] f) x‖) p μ :=
          lpNorm_mono_real (memLp_finsetSum _ fun j _ ↦ (hmj j).norm)
            (norm_iteratedFDeriv_succ_le_sum_coordinateDeriv hf)
      _ ≤ ∑ j, lpNorm (fun x ↦ ‖iteratedFDeriv ℝ i (coordinateDeriv [j] f) x‖) p μ :=
          hsum ▸ lpNorm_sum_le (fun j _ ↦ (hmj j).norm) hp
      _ = ∑ j, lpNorm (iteratedFDeriv ℝ i (coordinateDeriv [j] f)) p μ := by
          simp only [lpNorm_norm (hmj _).aestronglyMeasurable]
  · rw [lpNorm_of_not_memLp hm]
    exact Finset.sum_nonneg fun _ _ ↦ lpNorm_nonneg

end TauCeti
