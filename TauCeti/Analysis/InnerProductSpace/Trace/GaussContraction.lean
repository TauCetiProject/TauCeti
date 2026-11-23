/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The curvature contraction in the hypersurface Gauss equation

The commutator of a symmetric endomorphism with the curvature expression in the hypersurface
Gauss equation contracts to the difference of its trace times its square and the trace of its
square times itself. This supplies the algebraic curvature term in Simons' identity for minimal
hypersurfaces and applies in every finite dimension, including dimension zero.
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fintype ι]

/-- The commutator contraction for a curvature expression satisfying the hypersurface Gauss
equation. -/
theorem sum_gauss_curvature_commutator (b : OrthonormalBasis ι ℝ V)
    (S : V →ₗ[ℝ] V) (hS : S.IsSymmetric) (R : V → V → V → V)
    (hR : ∀ u v w, R u v w =
      inner ℝ (S v) w • S u - inner ℝ (S u) w • S v) (v : V) :
    (∑ i, (R (b i) v (S (b i)) - S (R (b i) v (b i)))) =
      LinearMap.trace ℝ V S • S (S v) -
        LinearMap.trace ℝ V (S.comp S) • S v := by
  classical
  have hs (u w : V) : inner ℝ (S u) w = inner ℝ u (S w) := hS u w
  have hsum (w : V) : ∑ i, inner ℝ w (b i) • S (b i) = S w := by
    simp_rw [← map_smul]
    rw [← map_sum]
    congr 1
    simpa only [real_inner_comm] using b.sum_repr' w
  have hsum₃ : ∑ i, inner ℝ (S v) (S (b i)) • S (b i) = S (S (S v)) := by
    simp_rw [← hs (S v)]
    exact hsum (S (S v))
  have hsum₃' : ∑ i, inner ℝ (S v) (b i) • S (S (b i)) = S (S (S v)) := by
    calc
      _ = S (∑ i, inner ℝ (S v) (b i) • S (b i)) := by simp only [map_sum, map_smul]
      _ = _ := by rw [hsum]
  have hsqtrace : ∑ i, inner ℝ (S (b i)) (S (b i)) =
      LinearMap.trace ℝ V (S.comp S) := by
    rw [LinearMap.trace_eq_sum_inner _ b]
    apply Finset.sum_congr rfl
    intro i _
    exact hS (b i) (S (b i))
  have htrace : ∑ i, inner ℝ (S (b i)) (b i) =
      LinearMap.trace ℝ V S := by
    rw [LinearMap.trace_eq_sum_inner _ b]
    exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _
  simp only [hR, map_sub, map_smul, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hsum₃, hsum₃', hsqtrace, htrace]
  abel

end OrthonormalBasis
