/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Topology.Algebra.Module.Trace
import TauCeti.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Trace

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
theorem traceCLM_inverse_comp_eq_bilinFormTrace
    (g : F →L[ℝ] F →L[ℝ] ℝ) (hg : ∀ v w, g v w = inner ℝ v w)
    (B : F →L[ℝ] F →L[ℝ] ℝ) :
    traceCLM ℝ F (g.inverse ∘L B) = bilinFormTrace B.toBilinForm := by
  have hinv : g.IsInvertible :=
    InnerProductSpace.isInvertible_of_apply_apply_eq_mul_inner (c := 1) one_ne_zero
      (by simpa only [one_mul] using hg)
  let b := stdOrthonormalBasis ℝ F
  rw [traceCLM_apply, LinearMap.trace_eq_sum_inner _ b, bilinFormTrace_eq_sum _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- The composed endomorphism evaluates by raising the first index with `g`.
  change inner ℝ (b i) (g.inverse (B (b i))) = B (b i) (b i)
  rw [real_inner_comm, ← hg]
  exact congrArg (fun φ ↦ φ (b i)) (hinv.self_apply_inverse (B (b i)))

/-- The trace of the square of a symmetric bilinear form with one index raised
is its squared coefficient sum in every orthonormal basis. -/
theorem traceCLM_inverse_comp_self_eq_sum_sq
    (g : F →L[ℝ] F →L[ℝ] ℝ) (hg : ∀ v w, g v w = inner ℝ v w)
    (B : F →L[ℝ] F →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F) :
    traceCLM ℝ F ((g.inverse ∘L B) ∘L (g.inverse ∘L B)) =
      ∑ i, ∑ j, B (b i) (b j) ^ 2 := by
  have hinv : g.IsInvertible :=
    InnerProductSpace.isInvertible_of_apply_apply_eq_mul_inner (c := 1) one_ne_zero
      (by simpa only [one_mul] using hg)
  let A : F →L[ℝ] F := g.inverse ∘L B
  have hpair (v w : F) : inner ℝ v (A w) = B w v := by
    rw [real_inner_comm, ← hg]
    exact congrArg (fun φ ↦ φ v) (hinv.self_apply_inverse (B w))
  rw [traceCLM_apply, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Expand the square of the raised-index endomorphism.
  change inner ℝ (b i) (A (A (b i))) = _
  rw [hpair]
  calc
    B (A (b i)) (b i) =
        B (∑ j, inner ℝ (b j) (A (b i)) • b j) (b i) := by rw [b.sum_repr']
    _ = ∑ j, inner ℝ (b j) (A (b i)) * B (b j) (b i) := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    _ = ∑ j, B (b i) (b j) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hpair, hB (b j) (b i), pow_two]

end TauCeti
