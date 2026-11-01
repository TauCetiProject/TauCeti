/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Variational
public import Mathlib.Analysis.Calculus.VectorField
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Lie brackets and commuting flows on Banach spaces

For a globally Lipschitz `C¹` vector field `v`, differentiating the pullback of a differentiable
field `w` along its flow gives the pullback of `[v, w]`. Consequently, `[v, w] = 0` if and only if
every time map of the flow of `v` preserves `w`. If `w` is also globally Lipschitz, this is
equivalent to commutation of the two flows.

These statements use the existing `flowOfLipschitz`, not a separate choice of solutions.
The variational equation gives the derivative of the spatial Jacobian; differentiation of its
inverse then gives the bracket, with the convention `[v, w] = Dw(v) - Dv(w)`.
No finite-dimensionality or second derivative of either field is needed.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012,
  Theorems 9.38 and 9.44 (the same flow argument, here on a Banach space).
-/

public section

noncomputable section

open VectorField
open scoped Topology NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v w : E → E} {K L : ℝ≥0}

variable (hv : LipschitzWith K v) (hvs : ContDiff ℝ 1 v)
include hvs

/-- The derivative of a pulled-back vector field is the pullback of its Lie bracket with the
flow's generating field. The other field only needs to be differentiable at the orbit point. -/
theorem hasDerivAt_pullback_flowOfLipschitz (x : E) (t : ℝ)
    (hw : DifferentiableAt ℝ w (flowOfLipschitz v hv t x)) :
    HasDerivAt (fun s ↦ pullback ℝ (flowOfLipschitz v hv s) w x)
      (pullback ℝ (flowOfLipschitz v hv t) (lieBracket ℝ v w) x) t := by
  have hd := differentiable_flowOfLipschitz_apply hv hvs
  have hi := (flowOfLipschitz v hv).isInvertible_fderiv (hd (-t) _) (hd t x)
  have h := (hasDerivAt_fderiv_flowOfLipschitz hv hvs x t).clm_inverse_apply_of_completeSpace hi
      (hw.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_flowOfLipschitz hv x t))
  simpa only [pullback, lieBracket, ContinuousLinearMap.comp_apply, Function.comp_apply,
    hi.self_apply_inverse, map_sub] using h

/-- Vanishing bracket implies that every time map of the flow preserves the other field. -/
theorem pullback_flowOfLipschitz_eq_of_lieBracket_eq_zero (hw : Differentiable ℝ w)
    (hvw : lieBracket ℝ v w = 0) (t : ℝ) :
    pullback ℝ (flowOfLipschitz v hv t) w = w := by
  funext x
  have hd (s : ℝ) : HasDerivAt (fun s ↦ pullback ℝ (flowOfLipschitz v hv s) w x) 0 s := by
    simpa only [hvw, pullback, Pi.zero_apply, map_zero] using
      hasDerivAt_pullback_flowOfLipschitz hv hvs x s (hw _)
  have h := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0
  simpa only [Flow.map_zero, pullback, fderiv_id, ContinuousLinearMap.inverse_id,
    ContinuousLinearMap.id_apply, id_eq] using h

/-- A differentiable field has zero bracket with `v` exactly when the flow of `v` preserves it. -/
theorem lieBracket_eq_zero_iff_pullback_flowOfLipschitz_eq (hw : Differentiable ℝ w) :
    lieBracket ℝ v w = 0 ↔ ∀ t, pullback ℝ (flowOfLipschitz v hv t) w = w := by
  refine ⟨fun h t ↦ pullback_flowOfLipschitz_eq_of_lieBracket_eq_zero hv hvs hw h t, ?_⟩
  intro h
  funext x
  have hd := hasDerivAt_pullback_flowOfLipschitz hv hvs x 0 (by
    simpa only [Flow.map_zero_apply] using hw x)
  have hc : HasDerivAt (fun s ↦ pullback ℝ (flowOfLipschitz v hv s) w x) 0 0 :=
    (hasDerivAt_const 0 (w x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s ↦ congrFun (h s) x)
  simpa only [Flow.map_zero, pullback, fderiv_id, ContinuousLinearMap.inverse_id,
    ContinuousLinearMap.id_apply, id_eq, Pi.zero_apply] using hd.unique hc

/-- If the bracket vanishes, the differential of each time map carries `w` to `w`. -/
theorem fderiv_flowOfLipschitz_apply_of_lieBracket_eq_zero (hw : Differentiable ℝ w)
    (hvw : lieBracket ℝ v w = 0) (t : ℝ) (x : E) :
    fderiv ℝ (flowOfLipschitz v hv t) x (w x) = w (flowOfLipschitz v hv t x) := by
  have hd := differentiable_flowOfLipschitz_apply hv hvs
  have hi := (flowOfLipschitz v hv).isInvertible_fderiv (hd (-t) _) (hd t x)
  have h := congrFun (pullback_flowOfLipschitz_eq_of_lieBracket_eq_zero hv hvs hw hvw t) x
  rw [← h, pullback, hi.self_apply_inverse]

/-- Globally Lipschitz fields with zero bracket have commuting flows. Only the first field must
be `C¹`; differentiability of the second suffices. -/
theorem flowOfLipschitz_comm_of_lieBracket_eq_zero (hw : LipschitzWith L w)
    (hwd : Differentiable ℝ w) (hvw : lieBracket ℝ v w = 0) (s t : ℝ) (x : E) :
    flowOfLipschitz v hv s (flowOfLipschitz w hw t x) =
      flowOfLipschitz w hw t (flowOfLipschitz v hv s x) := by
  have hγ (u : ℝ) : HasDerivAt
      (fun u ↦ flowOfLipschitz v hv s (flowOfLipschitz w hw u x))
      (w (flowOfLipschitz v hv s (flowOfLipschitz w hw u x))) u := by
    have h := (differentiable_flowOfLipschitz_apply hv hvs s _).hasFDerivAt.comp_hasDerivAt u
      (hasDerivAt_flowOfLipschitz hw x u)
    rwa [fderiv_flowOfLipschitz_apply_of_lieBracket_eq_zero hv hvs hwd hvw] at h
  simpa only [Flow.map_zero_apply] using eq_flowOfLipschitz hw hγ t

/-- Commuting flows force the bracket to vanish. Here too, the second field need only be
Lipschitz and differentiable, rather than continuously differentiable. -/
theorem lieBracket_eq_zero_of_flowOfLipschitz_comm (hw : LipschitzWith L w)
    (hwd : Differentiable ℝ w)
    (hcomm : ∀ s t x, flowOfLipschitz v hv s (flowOfLipschitz w hw t x) =
      flowOfLipschitz w hw t (flowOfLipschitz v hv s x)) :
    lieBracket ℝ v w = 0 := by
  apply (lieBracket_eq_zero_iff_pullback_flowOfLipschitz_eq hv hvs hwd).mpr
  intro s
  funext x
  have h₁ := (differentiable_flowOfLipschitz_apply hv hvs s x).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hasDerivAt_flowOfLipschitz hw x 0)
      (Flow.map_zero_apply _ x).symm
  have h₂ := hasDerivAt_flowOfLipschitz hw (flowOfLipschitz v hv s x) 0
  have heq : (fun t ↦ flowOfLipschitz v hv s (flowOfLipschitz w hw t x)) =
      (fun t ↦ flowOfLipschitz w hw t (flowOfLipschitz v hv s x)) :=
    funext fun t ↦ hcomm s t x
  simp only [Function.comp_def, heq] at h₁
  have hrel : fderiv ℝ (flowOfLipschitz v hv s) x (w x) =
      w (flowOfLipschitz v hv s x) := by
    simpa only [Flow.map_zero_apply] using h₁.unique h₂
  have hd := differentiable_flowOfLipschitz_apply hv hvs
  have hi := (flowOfLipschitz v hv).isInvertible_fderiv (hd (-s) _) (hd s x)
  rw [pullback, ← hrel, hi.inverse_apply_self]

/-- For globally Lipschitz fields, zero bracket is equivalent to commutation of the flows. -/
theorem lieBracket_eq_zero_iff_flowOfLipschitz_comm (hw : LipschitzWith L w)
    (hwd : Differentiable ℝ w) :
    lieBracket ℝ v w = 0 ↔ ∀ s t x,
      flowOfLipschitz v hv s (flowOfLipschitz w hw t x) =
        flowOfLipschitz w hw t (flowOfLipschitz v hv s x) :=
  ⟨fun h ↦ flowOfLipschitz_comm_of_lieBracket_eq_zero hv hvs hw hwd h,
    lieBracket_eq_zero_of_flowOfLipschitz_comm hv hvs hw hwd⟩

end TauCeti
