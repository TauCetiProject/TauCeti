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

Both consequences are local along orbits. If `[v, w]` vanishes along the orbit segment
`{Φ_σ x | σ ∈ [[0, t]]}` of the flow `Φ` of `v`, then the pullback of `w` by `Φ_t` agrees with
`w` at `x` (`TauCeti.pullback_flowOfLipschitz_apply_eq_of_forall_lieBracket_eq_zero`), that is,
`dΦ_t` sends `w x` to `w (Φ_t x)`
(`TauCeti.fderiv_flowOfLipschitz_apply_of_forall_lieBracket_eq_zero`). If `[v, w]` vanishes at the
points `Φ_σ (Ψ_τ x)` with `σ ∈ [[0, s]]` and `τ ∈ [[0, t]]`, where `Ψ` is the flow of `w`, then
`Φ_s (Ψ_t x) = Ψ_t (Φ_s x)` (`TauCeti.flowOfLipschitz_comm_of_forall_lieBracket_eq_zero`). So if
`[v, w]` vanishes near a point `a`, the flows commute for short times near `a`
(`TauCeti.eventually_flowOfLipschitz_comm_of_lieBracket_eventuallyEq_zero`). This is what the
straightening of commuting vector fields needs after cutting them off to globally Lipschitz fields.

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

/-- **Local preservation of a field with vanishing bracket.** If `[v, w]` vanishes along the
orbit segment `{Φ_σ x | σ ∈ [[0, t]]}` of the flow `Φ` of `v`, and `w` is differentiable there,
then the pullback of `w` by the time-`t` map agrees with `w` at `x`. -/
theorem pullback_flowOfLipschitz_apply_eq_of_forall_lieBracket_eq_zero {t : ℝ} {x : E}
    (hw : ∀ σ ∈ Set.uIcc 0 t, DifferentiableAt ℝ w (flowOfLipschitz v hv σ x))
    (hvw : ∀ σ ∈ Set.uIcc 0 t, lieBracket ℝ v w (flowOfLipschitz v hv σ x) = 0) :
    pullback ℝ (flowOfLipschitz v hv t) w x = w x := by
  -- The pullback of `w` along the flow has zero derivative on `[[0, t]]`, so it is constant there.
  have hF : ∀ σ ∈ Set.uIcc 0 t, HasDerivWithinAt
      (fun s ↦ pullback ℝ (flowOfLipschitz v hv s) w x) 0 (Set.uIcc 0 t) σ := fun σ hσ ↦ by
    have h := hasDerivAt_pullback_flowOfLipschitz hv hvs x σ (hw σ hσ)
    rw [pullback, hvw σ hσ, map_zero] at h
    exact h.hasDerivWithinAt
  have hconst := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hF
    (fun _ _ ↦ by simp) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hconst
  simpa only [Flow.map_zero, pullback, fderiv_id, ContinuousLinearMap.inverse_id,
    ContinuousLinearMap.id_apply, id_eq] using hconst

/-- Vanishing bracket implies that every time map of the flow preserves the other field. -/
theorem pullback_flowOfLipschitz_eq_of_lieBracket_eq_zero (hw : Differentiable ℝ w)
    (hvw : lieBracket ℝ v w = 0) (t : ℝ) :
    pullback ℝ (flowOfLipschitz v hv t) w = w :=
  funext fun _ ↦ pullback_flowOfLipschitz_apply_eq_of_forall_lieBracket_eq_zero hv hvs
    (fun _ _ ↦ hw _) fun _ _ ↦ congrFun hvw _

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

/-- **Local preservation of a field with vanishing bracket.** If `[v, w]` vanishes along the
orbit segment `{Φ_σ x | σ ∈ [[0, t]]}` of the flow `Φ` of `v`, and `w` is differentiable there,
then the differential of the time-`t` map sends `w x` to `w (Φ_t x)`. -/
theorem fderiv_flowOfLipschitz_apply_of_forall_lieBracket_eq_zero {t : ℝ} {x : E}
    (hw : ∀ σ ∈ Set.uIcc 0 t, DifferentiableAt ℝ w (flowOfLipschitz v hv σ x))
    (hvw : ∀ σ ∈ Set.uIcc 0 t, lieBracket ℝ v w (flowOfLipschitz v hv σ x) = 0) :
    fderiv ℝ (flowOfLipschitz v hv t) x (w x) = w (flowOfLipschitz v hv t x) := by
  have hd := differentiable_flowOfLipschitz_apply hv hvs
  have hi := (flowOfLipschitz v hv).isInvertible_fderiv (hd (-t) _) (hd t x)
  rw [← pullback_flowOfLipschitz_apply_eq_of_forall_lieBracket_eq_zero hv hvs hw hvw, pullback,
    hi.self_apply_inverse]

/-- If the bracket vanishes, the differential of each time map carries `w` to `w`. -/
theorem fderiv_flowOfLipschitz_apply_of_lieBracket_eq_zero (hw : Differentiable ℝ w)
    (hvw : lieBracket ℝ v w = 0) (t : ℝ) (x : E) :
    fderiv ℝ (flowOfLipschitz v hv t) x (w x) = w (flowOfLipschitz v hv t x) :=
  fderiv_flowOfLipschitz_apply_of_forall_lieBracket_eq_zero hv hvs (fun _ _ ↦ hw _)
    fun _ _ ↦ congrFun hvw _

/-- **Local commutation of flows with vanishing bracket.** Let `Φ` and `Ψ` be the flows of `v`
and of a globally Lipschitz field `w`. If `[v, w]` vanishes at every point
`Φ_σ (Ψ_τ x)` with `σ ∈ [[0, s]]` and `τ ∈ [[0, t]]`, and `w` is differentiable at these points,
then `Φ_s (Ψ_t x) = Ψ_t (Φ_s x)`. -/
theorem flowOfLipschitz_comm_of_forall_lieBracket_eq_zero (hw : LipschitzWith L w) {s t : ℝ}
    {x : E}
    (hwd : ∀ σ ∈ Set.uIcc 0 s, ∀ τ ∈ Set.uIcc 0 t,
      DifferentiableAt ℝ w (flowOfLipschitz v hv σ (flowOfLipschitz w hw τ x)))
    (hvw : ∀ σ ∈ Set.uIcc 0 s, ∀ τ ∈ Set.uIcc 0 t,
      lieBracket ℝ v w (flowOfLipschitz v hv σ (flowOfLipschitz w hw τ x)) = 0) :
    flowOfLipschitz v hv s (flowOfLipschitz w hw t x) =
      flowOfLipschitz w hw t (flowOfLipschitz v hv s x) := by
  -- `τ ↦ Φ_s (Ψ_τ x)` is an integral curve of `w` on `[[0, t]]`.
  have hγ : IsIntegralCurveOn (fun τ ↦ flowOfLipschitz v hv s (flowOfLipschitz w hw τ x))
      (fun _ y ↦ w y) (Set.uIcc 0 t) := fun τ hτ ↦ by
    have h := (differentiable_flowOfLipschitz_apply hv hvs s _).hasFDerivAt.comp_hasDerivAt τ
      (hasDerivAt_flowOfLipschitz hw x τ)
    rw [Function.comp_def, fderiv_flowOfLipschitz_apply_of_forall_lieBracket_eq_zero hv hvs
      (fun σ hσ ↦ hwd σ hσ τ hτ) fun σ hσ ↦ hvw σ hσ τ hτ] at h
    exact h.hasDerivWithinAt
  simpa only [Flow.map_zero_apply] using eq_flowOfLipschitz_of_isIntegralCurveOn hw hγ le_rfl

/-- **Short-time commutation of flows with bracket vanishing near a point.** Let `Φ` and `Ψ` be
the flows of `v` and of a globally Lipschitz field `w`. If `w` is differentiable and `[v, w]`
vanishes on a neighbourhood of `a`, then `Φ_s (Ψ_t y) = Ψ_t (Φ_s y)` for all `(s, t, y)` near
`(0, 0, a)`. -/
theorem eventually_flowOfLipschitz_comm_of_lieBracket_eventuallyEq_zero (hw : LipschitzWith L w)
    {a : E} (hwd : ∀ᶠ y in 𝓝 a, DifferentiableAt ℝ w y) (hvw : lieBracket ℝ v w =ᶠ[𝓝 a] 0) :
    ∀ᶠ q : ℝ × ℝ × E in 𝓝 (0, 0, a),
      flowOfLipschitz v hv q.1 (flowOfLipschitz w hw q.2.1 q.2.2) =
        flowOfLipschitz w hw q.2.1 (flowOfLipschitz v hv q.1 q.2.2) := by
  have hc : Continuous fun q : ℝ × ℝ × E ↦
      flowOfLipschitz v hv q.1 (flowOfLipschitz w hw q.2.1 q.2.2) :=
    (flowOfLipschitz v hv).continuous continuous_fst
      ((flowOfLipschitz w hw).continuous (continuous_fst.comp continuous_snd)
        (continuous_snd.comp continuous_snd))
  -- A ball around `(0, 0, a)` whose points `(σ, τ, y)` send `Φ_σ (Ψ_τ y)` where `w` is
  -- differentiable and `[v, w] = 0`.
  have hmem : ∀ᶠ q : ℝ × ℝ × E in 𝓝 (0, 0, a),
      DifferentiableAt ℝ w (flowOfLipschitz v hv q.1 (flowOfLipschitz w hw q.2.1 q.2.2)) ∧
        lieBracket ℝ v w (flowOfLipschitz v hv q.1 (flowOfLipschitz w hw q.2.1 q.2.2)) = 0 :=
    have hvw' : ∀ᶠ y in 𝓝 (flowOfLipschitz v hv 0 (flowOfLipschitz w hw 0 a)),
        DifferentiableAt ℝ w y ∧ lieBracket ℝ v w y = 0 := by
      simp only [Flow.map_zero_apply]
      exact hwd.and hvw
    (hc.tendsto (0, 0, a)).eventually hvw'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hmem
  filter_upwards [Metric.ball_mem_nhds _ hε] with q hq
  -- The ball contains `(σ, τ, q.2.2)` for `σ ∈ [[0, q.1]]` and `τ ∈ [[0, q.2.1]]`.
  have hmem' : ∀ σ ∈ Set.uIcc 0 q.1, ∀ τ ∈ Set.uIcc 0 q.2.1,
      DifferentiableAt ℝ w (flowOfLipschitz v hv σ (flowOfLipschitz w hw τ q.2.2)) ∧
        lieBracket ℝ v w (flowOfLipschitz v hv σ (flowOfLipschitz w hw τ q.2.2)) = 0 :=
    fun σ hσ τ hτ ↦ hball (y := (σ, τ, q.2.2)) (lt_of_le_of_lt ?_ hq)
  · exact flowOfLipschitz_comm_of_forall_lieBracket_eq_zero hv hvs hw
      (fun σ hσ τ hτ ↦ (hmem' σ hσ τ hτ).1) fun σ hσ τ hτ ↦ (hmem' σ hσ τ hτ).2
  have hσ' : dist σ 0 ≤ dist q.1 0 := by
    simpa [Real.dist_eq] using Set.abs_sub_left_of_mem_uIcc hσ
  have hτ' : dist τ 0 ≤ dist q.2.1 0 := by
    simpa [Real.dist_eq] using Set.abs_sub_left_of_mem_uIcc hτ
  simp only [Prod.dist_eq]
  exact max_le_max hσ' (max_le_max hτ' le_rfl)

/-- Globally Lipschitz fields with zero bracket have commuting flows. Only the first field must
be `C¹`; differentiability of the second suffices. -/
theorem flowOfLipschitz_comm_of_lieBracket_eq_zero (hw : LipschitzWith L w)
    (hwd : Differentiable ℝ w) (hvw : lieBracket ℝ v w = 0) (s t : ℝ) (x : E) :
    flowOfLipschitz v hv s (flowOfLipschitz w hw t x) =
      flowOfLipschitz w hw t (flowOfLipschitz v hv s x) :=
  flowOfLipschitz_comm_of_forall_lieBracket_eq_zero hv hvs hw (fun _ _ _ _ ↦ hwd _)
    fun _ _ _ _ ↦ congrFun hvw _

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
