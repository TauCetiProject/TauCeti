/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.RingTheory.MvPolynomial.Harmonic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Polynomial evaluation and the Euclidean Laplacian

The formal polynomial Laplacian agrees under evaluation with the differential Laplacian on
`EuclideanSpace ℝ σ`. This connects the algebraic harmonic homogeneous submodules to actual
harmonic functions, before restricting them to a sphere.

We use `MvPolynomial.hasFDerivAt_eval` for the derivative on the finite coordinate space and
transport it through `EuclideanSpace.equiv`. The second coordinate derivatives are evaluated
formal second partials; their trace in the standard orthonormal basis is the Laplacian.
The differential Laplacian here is the ordinary sum of second partials, not its negative.
No homogeneity or positive-dimension assumption is needed for this comparison.

## References

* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer (2001),
  Chapters 1 and 5 (harmonic polynomials and spherical harmonics).
-/

public section

namespace MvPolynomial

variable {σ : Type*} [Fintype σ]

/-- Evaluation intertwines the formal polynomial Laplacian and the ordinary Euclidean
differential Laplacian. -/
-- Rewrite before simp evaluates the polynomial inside the differentiated function.
@[simp↓]
theorem laplacian_eval_euclidean (p : MvPolynomial σ ℝ) :
    Laplacian.laplacian (fun x : EuclideanSpace ℝ σ ↦ eval x p) =
      fun x : EuclideanSpace ℝ σ ↦ eval x (laplacian p) := by
  classical
  have hcont : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ σ ↦ eval x p) :=
    (AnalyticOnNhd.eval_continuousLinearMap
      (EuclideanSpace.equiv σ ℝ).toContinuousLinearMap p).contDiff
  funext x
  rw [TauCeti.laplacian_eq_sum_fderiv_fderiv_apply (EuclideanSpace.basisFun σ ℝ)
    ((hcont.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num))]
  simp [laplacian_apply]

/-- A real polynomial evaluates to a harmonic function on the whole Euclidean space exactly
when its formal Laplacian vanishes. This includes constants and the zero-dimensional space. -/
theorem harmonicOnNhd_eval_euclidean_iff (p : MvPolynomial σ ℝ) :
    InnerProductSpace.HarmonicOnNhd
      (fun x : EuclideanSpace ℝ σ ↦ eval x p) Set.univ ↔ laplacian p = 0 := by
  constructor
  · intro h
    apply MvPolynomial.funext
    intro x
    have hx := (h ((EuclideanSpace.equiv σ ℝ).symm x) (Set.mem_univ _)).2.self_of_nhds
    simpa [laplacian_eval_euclidean] using hx
  · intro h x _
    refine ⟨?_, ?_⟩
    · exact ((AnalyticOnNhd.eval_continuousLinearMap
        (EuclideanSpace.equiv σ ℝ).toContinuousLinearMap p).contDiff).contDiffAt
    · filter_upwards [] with y
      simp [laplacian_eval_euclidean, h]

end MvPolynomial
