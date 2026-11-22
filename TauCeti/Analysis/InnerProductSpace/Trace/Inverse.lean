/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Topology.Algebra.Module.Trace
import TauCeti.Analysis.InnerProductSpace.BilinearForm.End
import TauCeti.Analysis.InnerProductSpace.Trace.Free

/-!
# Inverse-metric traces of bilinear forms

On a finite-dimensional real inner product space, raising one index with the inner product
identifies the ordinary endomorphism trace with the metric trace. For a symmetric bilinear
form, the trace of the squared raised-index endomorphism is its squared coefficient sum in
any orthonormal basis, so this sum is independent of the basis.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006), §2.3.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

noncomputable section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Finite-dimensional real inner product spaces are complete. -/
local instance traceInverseCompleteSpace : CompleteSpace F :=
  FiniteDimensional.completeSpace ℝ F

/-- If `g` is the inner product, raising one index of a bilinear form and taking
the endomorphism trace gives its metric trace. -/
theorem _root_.ContinuousLinearMap.traceCLM_inverse_comp_eq_metricTrace
    (g : F →L[ℝ] F →L[ℝ] ℝ) (hg : ∀ v w, g v w = inner ℝ v w)
    (B : F →L[ℝ] F →L[ℝ] ℝ) :
    traceCLM ℝ F (g.inverse ∘L B) = LinearMap.BilinMap.metricTrace B.toBilinForm := by
  rw [traceCLM_apply, g.toLinearMap_inverse_comp_eq_bilinFormToEnd hg B,
    LinearMap.BilinForm.trace_bilinFormToEnd]

/-- The trace of the square of a symmetric bilinear form with one index raised
is its squared coefficient sum in every orthonormal basis. -/
theorem _root_.ContinuousLinearMap.traceCLM_inverse_comp_self_eq_sum_sq
    (g : F →L[ℝ] F →L[ℝ] ℝ) (hg : ∀ v w, g v w = inner ℝ v w)
    (B : F →L[ℝ] F →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F) :
    traceCLM ℝ F ((g.inverse ∘L B) ∘L (g.inverse ∘L B)) =
      ∑ i, ∑ j, B (b i) (b j) ^ 2 := by
  -- The raised map `A` is symmetric, so `A ∘ A = A† ∘ A` and its trace is the Frobenius sum.
  let A : F →ₗ[ℝ] F := bilinFormToEnd B.toBilinForm
  have hA : A.IsSymmetric := isSymmetric_bilinFormToEnd_iff.mpr
    ⟨fun v w ↦ by simpa only [ContinuousLinearMap.toBilinForm_apply] using hB v w⟩
  have hsq : A ∘ₗ A = A.adjoint ∘ₗ A := by rw [hA.adjoint_eq]
  rw [traceCLM_apply, ContinuousLinearMap.toLinearMap_comp,
    g.toLinearMap_inverse_comp_eq_bilinFormToEnd hg B, hsq,
    LinearMap.trace_adjoint_comp_self_eq_sum_norm_apply_sq A b, RCLike.ofReal_real_eq_id, id]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← b.sum_sq_inner_left]
  simp only [A, LinearMap.BilinForm.inner_bilinFormToEnd_left,
    ContinuousLinearMap.toBilinForm_apply]

end TauCeti
