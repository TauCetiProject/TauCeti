/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Covector
public import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The universal linearization of the differential at a critical point

On a manifold `M` modelled on a finite-dimensional real space `E`, the **universal differential**
is the section `S(f, x) = df_x` of the cotangent bundle over `C^n(M, ℝ) × M`. Its zeros are the
pairs `(f, x)` with `x` a critical point of `f`, so the critical points of all functions at once,
and a function `f` is Morse exactly when the fibre of the projection `(f, x) ↦ f` over it consists
of nondegenerate zeros. This is the setting in which the genericity of Morse functions follows
from the Sard–Smale theorem, applied to that projection.

The section `S` is linear in the function. In the chart at `x`, its derivative in the point at a
zero `(f, x)` is the second derivative of the coordinate expression of `f`, the critical Hessian,
while its derivative in the function is `h ↦ dh_x`. Its linearization at a zero is therefore the
continuous linear map

`(v, h) ↦ Hess_x f (v) + dh_x : T_x M × C^n(M, ℝ) →L T*_x M`,

the coproduct of `TauCeti.criticalHessian I f x` and the derivative at `x`,
`ContMDiffMap.mvfderivCLM`. This file proves the linear facts about this map that the
transversality argument runs on.

* It is **surjective**, already on the function directions `h`, for every `f` and `x` and every
  `n ≥ 1` (`TauCeti.surjective_criticalHessian_coprod_mvfderivCLM`): every covector is the
  derivative at `x` of a function supported near `x`, chosen linearly and continuously in the
  covector by `SmoothBumpFunction.bumpCovectorCLM`. This is the linear ingredient of the
  transversality of the universal differential to the zero section.
* The projection of its kernel to the parameter space `C^n(M, ℝ)`, the native parameter
  projection `ContinuousLinearMap.parameterProj`, is **surjective exactly when `x` is a
  nondegenerate critical point of `f`**, for `n ≥ 2` and `M` without boundary
  (`TauCeti.surjective_parameterProj_criticalHessian_mvfderivCLM_iff`). Thus the regular
  parameters of the projection are exactly the functions whose critical points are nondegenerate.
* That projection has **index zero** (`TauCeti.index_parameterProj_criticalHessian_mvfderivCLM`):
  the Hessian maps the tangent space to its dual, of the same finite dimension, and the projection
  has the index of the Hessian. Its kernel is the kernel of the Hessian
  (`ContinuousLinearMap.kerEquivKerParameterProj`).

The section `S` itself, its regularity as a map on a Banach space of `C^k` functions and the
identification of its derivative with this map are not part of this file; the statements here
concern the linear map alone.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.3 (the parameter projection of a universal
  linearization and its regular values).
* M. Hirsch, *Differential Topology*, GTM 33, Springer, 1976, Chapter 6, §1 (genericity of Morse
  functions).
-/

public section

open Function ContinuousLinearMap
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] {n : ℕ∞} [IsManifold I n M]

/-- **The universal linearization is onto.** For `1 ≤ n`, the linear map
`(v, h) ↦ Hess_x f (v) + dh_x` is onto, already on the function directions. Once it is identified
with the derivative of a sufficiently regular universal differential, this is transversality of
that section to the zero section. -/
theorem surjective_criticalHessian_coprod_mvfderivCLM (hn : 1 ≤ (n : ℕ∞ω)) (f : M → ℝ) (x : M) :
    Surjective ((criticalHessian I f x).coprod (ContMDiffMap.mvfderivCLM (F := ℝ) hn x)) :=
  fun ξ ↦
    let ⟨h, hh⟩ := ContMDiffMap.surjective_mvfderivCLM (F := ℝ) hn x ξ
    ⟨(0, h), by simp [hh]⟩

/-- The parameter projection of the universal linearization at `(f, x)` has the index of the
critical Hessian, which is zero. -/
theorem index_parameterProj_criticalHessian_mvfderivCLM (hn : 1 ≤ (n : ℕ∞ω)) (f : M → ℝ)
    (x : M) :
    index (parameterProj (criticalHessian I f x) (ContMDiffMap.mvfderivCLM (F := ℝ) hn x)) = 0 := by
  rw [index_parameterProj _ _ (surjective_criticalHessian_coprod_mvfderivCLM hn f x)]
  -- The critical Hessian maps `TangentSpace I x`, which is `E`, to its dual.
  rw [index_eq_of_finiteDimensional (T := (criticalHessian I f x : E →L[ℝ] E →L[ℝ] ℝ))]
  exact sub_eq_zero.2
    (congrArg Nat.cast (ContinuousLinearMap.dual_finrank_eq (𝕜 := ℝ) (E := E)).symm)

variable [I.Boundaryless]

/-- **Regular parameters are Morse at the point.** For `2 ≤ n`, at a critical point `x` of a
`C^n` function `f` on a manifold without boundary, the parameter projection of the universal
linearization `(v, h) ↦ Hess_x f (v) + dh_x` is onto exactly when `x` is a nondegenerate critical
point of `f`. -/
theorem surjective_parameterProj_criticalHessian_mvfderivCLM_iff (hn : 2 ≤ n)
    {f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯} {x : M} (hx : x ∈ criticalPoints I f) :
    Surjective (parameterProj (criticalHessian I f x)
        (ContMDiffMap.mvfderivCLM (F := ℝ) (n := n) (by exact_mod_cast one_le_two.trans hn) x)) ↔
      IsManifoldNondegenerateCriticalPoint I f x := by
  rw [parameterProj_surjective_iff _ _ (surjective_criticalHessian_coprod_mvfderivCLM _ f x),
    isManifoldNondegenerateCriticalPoint_iff_criticalHessian]
  have hf : ContMDiffAt I 𝓘(ℝ) 2 f x :=
    (f.contMDiff.of_le (WithTop.coe_le_coe.2 hn)).contMDiffAt
  -- The critical Hessian maps `TangentSpace I x`, which is `E`, to its dual, of the same
  -- dimension, so it is invertible exactly when it is onto.
  exact ⟨fun hs ↦ ⟨hf, mem_criticalPoints.1 hx, isInvertible_of_surjective (E := E) hs⟩,
    fun ⟨_, _, hinv⟩ ↦ hinv.surjective⟩

end TauCeti
