/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.Jacobi.Basic
public import TauCeti.Analysis.Calculus.FDeriv.Det.Rpow
public import TauCeti.Analysis.Calculus.FDeriv.Det.NormDet
public import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Determinant roots of Jacobi operator curves

For a Jacobi operator curve with vanishing initial mutual Wronskian and symmetric curvature,
the trace bound `-m * κ ≤ trace K` gives `f'' ≤ κ * f`, where `f = normDet ^ (1 / m)`.
The inequality holds at interior nonsingular points and feeds comparison with the
constant-curvature model sine.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Filter Set ContinuousLinearMap
open scoped Topology Matrix.Norms.Operator

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Read the native operator Riccati equation in fixed orthonormal coordinates. -/
private theorem hasDerivAt_operatorMatrix_logDeriv (b : OrthonormalBasis ι ℝ F)
    {J V : ℝ → F →L[ℝ] F} {K : F →L[ℝ] F} {t : ℝ}
    (hJ : HasDerivAt J (V t) t) (hV : HasDerivAt V (-(K.comp (J t))) t)
    (hi : (J t).IsInvertible) :
    HasDerivAt (fun r ↦ toMatrixCLM b.toBasis (V r) * (toMatrixCLM b.toBasis (J r))⁻¹)
      (-((toMatrixCLM b.toBasis (V t) * (toMatrixCLM b.toBasis (J t))⁻¹) *
        (toMatrixCLM b.toBasis (V t) * (toMatrixCLM b.toBasis (J t))⁻¹)) -
          toMatrixCLM b.toBasis K) t := by
  have heq :
      (fun r ↦ toMatrixCLM b.toBasis (V r) * (toMatrixCLM b.toBasis (J r))⁻¹) =ᶠ[𝓝 t]
        (fun r ↦ toMatrixCLM b.toBasis ((V r).comp (J r).inverse)) :=
    .of_forall fun r ↦ (toMatrixCLM_comp_inverse b.toBasis (V r) (J r)).symm
  have hR := (toMatrixCLM b.toBasis).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_jacobi_logDeriv hJ hV hi)
  convert! hR.congr_of_eventuallyEq heq using 1
  -- The matrix algebra's scalar actions are fixed by the coordinate map on the right.
  change -((toMatrixCLM b.toBasis (V t) * (toMatrixCLM b.toBasis (J t))⁻¹) *
      (toMatrixCLM b.toBasis (V t) * (toMatrixCLM b.toBasis (J t))⁻¹)) -
      toMatrixCLM b.toBasis K =
    toMatrixCLM b.toBasis (-(((V t).comp (J t).inverse).comp
      ((V t).comp (J t).inverse)) - K)
  rw [(toMatrixCLM b.toBasis).map_sub, (toMatrixCLM b.toBasis).map_neg,
    toMatrixCLM_comp, toMatrixCLM_comp_inverse]

/-- The actual determinant root of a nonsingular Jacobi operator satisfies the scalar Ricci
inequality. The equations hold within a convex parameter set, while curvature symmetry is
needed only in its interior. Comparison is asserted at an interior nonsingular point. -/
theorem deriv2_normDet_rpow_le_of_jacobi
    {J V K : ℝ → F →L[ℝ] F} {s : Set ℝ} {a t κ : ℝ}
    (hm : 0 < Module.finrank ℝ F)
    (hJ : ∀ r ∈ s, HasDerivWithinAt J (V r) s r)
    (hVc : ContinuousOn V s)
    (hV : ∀ r ∈ interior s, HasDerivWithinAt V (-((K r).comp (J r))) s r)
    (hK : ∀ r ∈ interior s, LinearMap.IsSymmetric (K r).toLinearMap)
    (hs : Convex ℝ s) (ha : a ∈ s)
    (hW : ∀ u v, inner ℝ (J a u) (V a v) - inner ℝ (V a u) (J a v) = 0)
    (ht : t ∈ interior s) (hi : (J t).IsInvertible)
    (hRic : -(Module.finrank ℝ F : ℝ) * κ ≤ LinearMap.trace ℝ F (K t).toLinearMap) :
    deriv (deriv (fun r ↦ (J r).toLinearMap.normDet ^ (1 / (Module.finrank ℝ F : ℝ)))) t ≤
      κ * (J t).toLinearMap.normDet ^ (1 / (Module.finrank ℝ F : ℝ)) := by
  let b := stdOrthonormalBasis ℝ F
  let j := fun r ↦ (toMatrixCLM b.toBasis) (J r)
  let v := fun r ↦ (toMatrixCLM b.toBasis) (V r)
  let k := (toMatrixCLM b.toBasis) (K t)
  have ht' := interior_subset ht
  have hJa (r : ℝ) (hr : r ∈ interior s) : HasDerivAt J (V r) r :=
    (hJ r (interior_subset hr)).hasDerivAt (mem_interior_iff_mem_nhds.mp hr)
  have hJM (r : ℝ) (hr : r ∈ interior s) : HasDerivAt j (v r) r :=
    (toMatrixCLM b.toBasis).hasFDerivAt.comp_hasDerivAt r (hJa r hr)
  have hne : (j t).det ≠ 0 := by
    dsimp only [j]
    rw [ContinuousLinearMap.toMatrixCLM_apply, LinearMap.det_toMatrix]
    exact hi.det_ne_zero
  have hSym := isSymmetric_jacobi_logDeriv
    hJ hVc hV hK hs ha hW ht' hi
  have hSM : (v t * (j t)⁻¹).IsSymm := by
    have hm := (LinearMap.isHermitian_toMatrix_iff b).mpr hSym
    rw [← toMatrixCLM_apply b.toBasis, toMatrixCLM_comp_inverse] at hm
    simpa only [v, j, Matrix.isHermitian_iff_isSymm] using hm
  have hR' : HasDerivAt (fun r ↦ v r * (j r)⁻¹)
      (-((v t * (j t)⁻¹) * (v t * (j t)⁻¹)) - k) t :=
    hasDerivAt_operatorMatrix_logDeriv b (hJa t ht)
      ((hV t ht).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)) hi
  have hbound := Matrix.deriv2_abs_det_rpow_le_of_riccati
    (J := j) (V := v) (K := k) (κ := κ) (by simpa using hm)
    (by filter_upwards [isOpen_interior.mem_nhds ht] with r hr using hJM r hr)
    hne hSM hR' (by simpa only [k, ContinuousLinearMap.toMatrixCLM_apply, Fintype.card_fin,
      ← LinearMap.trace_eq_matrix_trace ℝ b.toBasis] using hRic)
  have hnorm (r : ℝ) : (J r).toLinearMap.normDet = |(j r).det| := by
    simp only [j, ContinuousLinearMap.toMatrixCLM_apply, LinearMap.det_toMatrix,
      LinearMap.normDet_eq_abs_det]
  simpa only [hnorm, Fintype.card_fin] using hbound

end TauCeti
