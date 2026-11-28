/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Topology.Algebra.Module.Trace
import TauCeti.Analysis.InnerProductSpace.BilinearForm.End
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.Trace.Free

/-!
# Inverse-metric traces of bilinear forms

On a finite-dimensional real inner product space, raising one index with the inner product
identifies the ordinary endomorphism trace with the metric trace. The trace of the composite
of two raised-index bilinear forms is their mixed coefficient
contraction in any orthonormal basis. The symmetric square is the special case giving the
squared coefficient sum, so this sum is independent of the basis.

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

/-- Raising one index of two bilinear forms and taking the trace of their composite gives
their mixed coefficient contraction. No symmetry is required of either form. -/
theorem _root_.ContinuousLinearMap.traceCLM_inverse_comp_inverse_comp_eq_sum_mul
    (g : F →L[ℝ] F →L[ℝ] ℝ) (hg : ∀ v w, g v w = inner ℝ v w)
    (B D : F →L[ℝ] F →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F) :
    traceCLM ℝ F ((g.inverse ∘L B) ∘L (g.inverse ∘L D)) =
      ∑ i, ∑ j, D (b i) (b j) * B (b j) (b i) := by
  have hinv : g.IsInvertible :=
    InnerProductSpace.isInvertible_of_apply_apply_eq_mul_inner (c := 1) one_ne_zero
      (by simpa only [one_mul] using hg)
  have hpair (K : F →L[ℝ] F →L[ℝ] ℝ) (v w : F) :
      inner ℝ v (g.inverse (K w)) = K w v := by
    rw [real_inner_comm, ← hg]
    exact congrArg (fun φ ↦ φ v) (hinv.self_apply_inverse (K w))
  rw [traceCLM_apply, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, hpair]
  calc
    B (g.inverse (D (b i))) (b i) =
        B (∑ j, inner ℝ (b j) (g.inverse (D (b i))) • b j) (b i) := by
      rw [b.sum_repr']
    _ = ∑ j, D (b i) (b j) * B (b j) (b i) := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hpair]

/-- The trace of the square of a symmetric bilinear form with one index raised
is its squared coefficient sum in every orthonormal basis. -/
theorem _root_.ContinuousLinearMap.traceCLM_inverse_comp_self_eq_sum_sq
    (g : F →L[ℝ] F →L[ℝ] ℝ) (hg : ∀ v w, g v w = inner ℝ v w)
    (B : F →L[ℝ] F →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F) :
    traceCLM ℝ F ((g.inverse ∘L B) ∘L (g.inverse ∘L B)) =
      ∑ i, ∑ j, B (b i) (b j) ^ 2 := by
  rw [ContinuousLinearMap.traceCLM_inverse_comp_inverse_comp_eq_sum_mul g hg B B b]
  simp_rw [hB (b _) (b _), pow_two]

end TauCeti
