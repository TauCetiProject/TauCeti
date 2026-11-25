/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.Analysis.ODE.InitialCondition
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The flow of a globally Lipschitz vector field

A vector field whose solutions may blow up in finite time generates no flow: the group law
`φ (t₁ + t₂) = φ t₁ ∘ φ t₂` needs solutions defined for all time. A globally Lipschitz vector
field on a Banach space has them, by `ODE.globalSolution`, and this file assembles them into a
`Flow ℝ E`.

The group law is uniqueness of solutions applied to the time-translated orbit, the identity law is
the initial condition, and the joint continuity required by `Flow` is
`ODE.continuous_globalSolution`.

## Main declarations

* `TauCeti.flowOfLipschitz`: the flow of a globally Lipschitz vector field on a Banach space.
* `TauCeti.contDiff_flowOfLipschitz` and `TauCeti.contDiff_flowOfLipschitz_apply`: a globally
  `C^(n+1)` field has a `C^(n+1)` flow, jointly and at each fixed time.
* `TauCeti.hasDerivAt_flowOfLipschitz` and `TauCeti.isIntegralCurve_flowOfLipschitz`: its
  orbits solve the differential equation.
* `TauCeti.eq_flowOfLipschitz`: every global solution is an orbit of the flow.
* `TauCeti.eq_flowOfLipschitz_of_isIntegralCurveOn`: the corresponding uniqueness statement for a
  solution on any time set containing the interval between zero and the chosen time.
* `TauCeti.flowOfLipschitz_congr`: it does not depend on the chosen Lipschitz bound.
* `TauCeti.flowOfLipschitz_apply_eq_of_eqOn`: flows of two Lipschitz fields agree at time `t` on
  `y` when the fields agree along the orbit segment from `0` to `t`.
* `TauCeti.forall_flowOfLipschitz_eq_self_iff`: the rest points of the flow are the zeros of the
  vector field.
* `TauCeti.flowOfLipschitz_eq_self_of_vectorField_flow_eq_zero`: an orbit that meets a rest point
  is constant.
* `TauCeti.norm_flowOfLipschitz_sub_le`: a bound `M` on the vector field bounds the displacement
  of the time-`t` map by `M |t|`.
* `TauCeti.flowOfLipschitz_apply_eq_add_smul`: where the vector field is the constant `c` along the
  segment from `x` to `x + t • c`, the time-`t` map translates `x` by `t • c`.
* `TauCeti.lipschitzWith_flowOfLipschitz`, `TauCeti.norm_fderiv_flowOfLipschitz_le`: the time-`t`
  map is `exp (K |t|)`-Lipschitz, and its `fderiv` has norm at most `exp (K |t|)`.
* `TauCeti.lipschitzWith_flowOfLipschitz_sub_id`, `TauCeti.norm_fderiv_flowOfLipschitz_sub_id_le`:
  the displacement `x ↦ φₜ x - x` is `(exp (K |t|) - 1)`-Lipschitz, so the time-`t` map is within
  `exp (K |t|) - 1` of the identity in derivative. This is Grönwall's inequality for the difference
  of two orbits and their initial points.
* `TauCeti.flowOfLipschitz_eq_add_integral`: orbits satisfy the integral equation.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : E → E} {K : ℝ≥0}

/-- **The flow of a globally Lipschitz vector field** on a Banach space: the time-`t` map sends an
initial point to the value at time `t` of the unique global solution of `γ' = v ∘ γ` through it. -/
noncomputable def flowOfLipschitz (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) : Flow ℝ E where
  toFun t x := ODE.globalSolution v hv x t
  cont' := ODE.continuous_globalSolution v hv
  map_add' t₁ t₂ x := by
    simpa [add_comm] using ODE.globalSolution_add v hv x t₂ t₁
  map_zero' x := ODE.globalSolution_zero v hv x

@[simp]
theorem flowOfLipschitz_apply (hv : LipschitzWith K v) (t : ℝ) (x : E) :
    flowOfLipschitz v hv t x = ODE.globalSolution v hv x t := (rfl)

/-- **Independence of the Lipschitz bound.** Two Lipschitz witnesses for the same vector field,
with possibly different constants, produce the same flow. -/
theorem flowOfLipschitz_congr {K' : ℝ≥0} (hv : LipschitzWith K v) (hv' : LipschitzWith K' v) :
    flowOfLipschitz v hv = flowOfLipschitz v hv' :=
  Flow.ext fun t x ↦ congrFun (ODE.globalSolution_congr v hv hv' x) t

/-- **A globally Lipschitz `C^(n+1)` vector field has a `C^(n+1)` global flow**, jointly in time
and the initial condition. -/
theorem contDiff_flowOfLipschitz (n : ℕ) (v : E → E) (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) :
    ContDiff ℝ (n + 1) (Function.uncurry (flowOfLipschitz v hv)) := by
  convert (ODE.contDiff_globalSolution (n := n) v hv (by exact_mod_cast hvs)).comp
    (contDiff_snd.prodMk contDiff_fst) using 1
  funext p
  rw [Function.comp_apply, Function.uncurry_apply_pair, flowOfLipschitz_apply]

/-- At each fixed time, the flow of a globally Lipschitz `C^(n+1)` vector field is `C^(n+1)` in
the initial condition. -/
theorem contDiff_flowOfLipschitz_apply (n : ℕ) (v : E → E) (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) (t : ℝ) :
    ContDiff ℝ (n + 1) (flowOfLipschitz v hv t) := by
  convert ODE.contDiff_globalSolution_apply (n := n) v hv (by exact_mod_cast hvs) t using 1
  funext x
  rw [flowOfLipschitz_apply]

/-- Every orbit of the flow solves the differential equation. -/
theorem hasDerivAt_flowOfLipschitz (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ flowOfLipschitz v hv t x) (v (flowOfLipschitz v hv t x)) t :=
  ODE.hasDerivAt_globalSolution v hv x t

/-- Every orbit of the flow is an integral curve of the vector field. -/
theorem isIntegralCurve_flowOfLipschitz (hv : LipschitzWith K v) (x : E) :
    IsIntegralCurve (fun t ↦ flowOfLipschitz v hv t x) fun _ y ↦ v y :=
  ODE.isIntegralCurve_globalSolution v hv x

/-- **Every global solution is an orbit** of the flow, namely the one through its initial value. -/
theorem eq_flowOfLipschitz (hv : LipschitzWith K v) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (t : ℝ) : γ t = flowOfLipschitz v hv t (γ 0) :=
  congrFun (ODE.eq_globalSolution v hv hγ) t

/-- **Uniqueness on a time set.** An integral curve on a set containing the interval between zero
and `t` agrees at `t` with the globally Lipschitz flow through its value at zero. -/
theorem eq_flowOfLipschitz_of_isIntegralCurveOn (hv : LipschitzWith K v) {γ : ℝ → E}
    {s : Set ℝ} (hγ : IsIntegralCurveOn γ (fun _ y ↦ v y) s) {t : ℝ}
    (hst : uIcc 0 t ⊆ s) :
    γ t = flowOfLipschitz v hv t (γ 0) := by
  have hγ' := hγ.mono hst
  let η : ℝ → E := fun s ↦ flowOfLipschitz v hv s (γ 0)
  have hη : IsIntegralCurve η (fun _ y ↦ v y) := isIntegralCurve_flowOfLipschitz hv (γ 0)
  have hinit : γ 0 = η 0 := by simp only [η, _root_.Flow.map_zero_apply]
  rcases le_total 0 t with ht | ht
  · rw [uIcc_of_le ht] at hγ'
    have heq := ODE_solution_unique (a := 0) (b := t) (v := fun _ y ↦ v y)
      (fun _ ↦ hv) hγ'.continuousOn
      (fun s hs ↦ (hγ' s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs))
      hη.continuous.continuousOn (fun s _ ↦ (hη s).hasDerivWithinAt) hinit
    exact heq ⟨ht, le_rfl⟩
  · rw [uIcc_of_ge ht] at hγ'
    have heq := ODE_solution_unique_of_mem_Icc_left (a := t) (b := 0)
      (v := fun _ y ↦ v y) (s := fun _ ↦ univ) (K := K)
      (fun _ _ ↦ hv.lipschitzOnWith) hγ'.continuousOn
      (fun s hs ↦ (hγ' s ⟨hs.1.le, hs.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem hs))
      (fun _ _ ↦ mem_univ _) hη.continuous.continuousOn
      (fun s _ ↦ (hη s).hasDerivWithinAt) (fun _ _ ↦ mem_univ _) hinit
    exact heq ⟨le_rfl, ht⟩

/-- **The rest points of the flow are the zeros of the vector field.** -/
theorem forall_flowOfLipschitz_eq_self_iff (hv : LipschitzWith K v) (x : E) :
    (∀ t, flowOfLipschitz v hv t x = x) ↔ v x = 0 := by
  refine ⟨fun h ↦ ?_, fun h t ↦ ?_⟩
  · have h1 : HasDerivAt (fun t ↦ flowOfLipschitz v hv t x)
        (v (flowOfLipschitz v hv 0 x)) 0 :=
      hasDerivAt_flowOfLipschitz hv x 0
    have h2 : HasDerivAt (fun t : ℝ ↦ flowOfLipschitz v hv t x) 0 0 :=
      (hasDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq (.of_forall h)
    have h3 := h1.unique h2
    rwa [h 0] at h3
  · have hconst : ∀ s : ℝ, HasDerivAt (fun _ : ℝ ↦ x) (v ((fun _ : ℝ ↦ x) s)) s := fun s ↦ by
      simpa [h] using hasDerivAt_const s x
    simpa using (eq_flowOfLipschitz hv hconst t).symm

/-- **An orbit through a rest point is constant.** If the flow carries `x` at some time `s` to a
zero of the vector field, then the flow fixes `x` at every time. -/
theorem flowOfLipschitz_eq_self_of_vectorField_flow_eq_zero (hv : LipschitzWith K v) {x : E}
    {s : ℝ} (hs : v (flowOfLipschitz v hv s x) = 0) (t : ℝ) : flowOfLipschitz v hv t x = x := by
  have hrest := (forall_flowOfLipschitz_eq_self_iff hv _).2 hs
  -- Flowing the rest point back for time `s` returns to `x`, so `x` is that rest point.
  have hx : flowOfLipschitz v hv s x = x := by
    have h := hrest (-s)
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at h
    exact h.symm
  calc flowOfLipschitz v hv t x = flowOfLipschitz v hv t (flowOfLipschitz v hv s x) := by rw [hx]
    _ = flowOfLipschitz v hv s x := hrest t
    _ = x := hx


/-- **Flows agree where the fields agree.** If the Lipschitz fields `v` and `w` coincide along the
orbit segment `{ψ_τ y | τ ∈ [[0, t]]}` of the flow `ψ` of `w`, then the flow of `v` sends `y` at
time `t` to the same point. -/
theorem flowOfLipschitz_apply_eq_of_eqOn {w : E → E} {K' : ℝ≥0} (hv : LipschitzWith K v)
    (hw : LipschitzWith K' w) {y : E} {t : ℝ}
    (h : ∀ τ ∈ uIcc 0 t, v (flowOfLipschitz w hw τ y) = w (flowOfLipschitz w hw τ y)) :
    flowOfLipschitz v hv t y = flowOfLipschitz w hw t y := by
  have hγ : IsIntegralCurveOn (fun τ ↦ flowOfLipschitz w hw τ y) (fun _ z ↦ v z) (uIcc 0 t) :=
    fun τ hτ ↦ by
      beta_reduce
      rw [h τ hτ]
      exact (hasDerivAt_flowOfLipschitz hw y τ).hasDerivWithinAt
  have := eq_flowOfLipschitz_of_isIntegralCurveOn hv hγ le_rfl
  rw [Flow.map_zero_apply] at this
  exact this.symm

/-- **Displacement bound.** If the vector field is bounded by `M`, the time-`t` map moves no point
by more than `M |t|`. -/
theorem norm_flowOfLipschitz_sub_le (hv : LipschitzWith K v) {M : ℝ} (hM : ∀ z, ‖v z‖ ≤ M)
    (t : ℝ) (x : E) : ‖flowOfLipschitz v hv t x - x‖ ≤ M * |t| := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s ↦ flowOfLipschitz v hv s x)
    (fun s _ ↦ (hasDerivAt_flowOfLipschitz hv x s).hasDerivWithinAt) (fun s _ ↦ hM _)
    (mem_univ 0) (mem_univ t)
  simpa using h

/-- **Flow along a constant field.** If the vector field equals `c` along the segment
`{x + τ • c | τ ∈ [[0, t]]}`, then the time-`t` map sends `x` to `x + t • c`. -/
theorem flowOfLipschitz_apply_eq_add_smul (hv : LipschitzWith K v) {x c : E} {t : ℝ}
    (hc : ∀ τ ∈ uIcc 0 t, v (x + τ • c) = c) : flowOfLipschitz v hv t x = x + t • c := by
  have hγ : IsIntegralCurveOn (fun τ : ℝ ↦ x + τ • c) (fun _ y ↦ v y) (uIcc 0 t) :=
    fun τ hτ ↦ by
      simp only [hc τ hτ]
      exact (((hasDerivAt_id τ).smul_const c).const_add x).hasDerivWithinAt.congr_deriv (by simp)
  have h := eq_flowOfLipschitz_of_isIntegralCurveOn hv hγ le_rfl
  simp only [zero_smul, add_zero] at h
  exact h.symm

/-- **The time-`t` map of the flow of a `K`-Lipschitz vector field is `exp (K |t|)`-Lipschitz.** -/
theorem lipschitzWith_flowOfLipschitz (hv : LipschitzWith K v) (t : ℝ) :
    LipschitzWith (Real.exp (K * |t|)).toNNReal (flowOfLipschitz v hv t) :=
  LipschitzWith.of_dist_le_mul fun a b ↦ by
    rw [flowOfLipschitz_apply, flowOfLipschitz_apply,
      Real.coe_toNNReal _ (Real.exp_pos _).le, mul_comm]
    exact ODE.dist_globalSolution_le v hv a b t

/-- **A bound on the derivative of the flow.** For a `K`-Lipschitz vector field, `fderiv` of the
time-`t` map of the flow has norm at most `exp (K |t|)`. The field need not be differentiable, so
this is a bound on Lean's `fderiv`, which is `0` where the time-`t` map is not differentiable; where
it is differentiable (e.g. for a `C¹` field), it bounds the genuine derivative. -/
theorem norm_fderiv_flowOfLipschitz_le (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    ‖fderiv ℝ (flowOfLipschitz v hv t) x‖ ≤ Real.exp (K * |t|) := by
  simpa [Real.coe_toNNReal _ (Real.exp_pos _).le] using
    norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_flowOfLipschitz hv t) (x₀ := x)

/-- A function vanishing at `0` whose derivative at `s` is bounded by `K exp (K |s|) c` is
bounded at `t` by `(exp (K |t|) - 1) c`, the integral of that bound from `0` to `t`. -/
private theorem norm_le_exp_sub_one_mul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {L c : ℝ} (hf : ∀ s, HasDerivAt f (f' s) s) (hf0 : f 0 = 0)
    (hf' : ∀ s, ‖f' s‖ ≤ L * Real.exp (L * |s|) * c) (t : ℝ) :
    ‖f t‖ ≤ (Real.exp (L * |t|) - 1) * c := by
  -- Forward in time this is the comparison with the boundary `s ↦ (exp (L s) - 1) c`.
  have hfwd {g g' : ℝ → F} (hg : ∀ s, HasDerivAt g (g' s) s) (hg0 : g 0 = 0)
      (hg' : ∀ s, 0 ≤ s → ‖g' s‖ ≤ L * Real.exp (L * s) * c) {t : ℝ} (ht : 0 ≤ t) :
      ‖g t‖ ≤ (Real.exp (L * t) - 1) * c := by
    have hB (s : ℝ) : HasDerivAt (fun s ↦ (Real.exp (L * s) - 1) * c)
        (L * Real.exp (L * s) * c) s := by
      convert ((((hasDerivAt_id' (x := s)).const_mul L).exp).sub_const 1).mul_const c using 1
      ring
    exact image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun s _ ↦ (hg s).continuousAt.continuousWithinAt) (fun s _ ↦ (hg s).hasDerivWithinAt)
      (by simp [hg0]) hB (fun s hs ↦ hg' s hs.1) ⟨ht, le_rfl⟩
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact hfwd hf hf0 (fun s hs ↦ by simpa [abs_of_nonneg hs] using hf' s) ht
  · -- Backward in time, apply the forward bound to `s ↦ f (-s)`.
    have h := hfwd (g := fun s ↦ f (-s)) (g' := fun s ↦ -f' (-s))
      (fun s ↦ by simpa [Function.comp_def] using (hf (-s)).scomp s (hasDerivAt_neg s))
      (by simpa using hf0)
      (fun s hs ↦ by simpa [norm_neg, abs_of_nonneg hs] using hf' (-s)) (neg_nonneg.2 ht)
    rwa [neg_neg, ← abs_of_nonpos ht] at h

/-- **The time-`t` map of the flow is close to the identity.** For a `K`-Lipschitz vector field,
the displacement `x ↦ φₜ x - x` of the time-`t` map is `(exp (K |t|) - 1)`-Lipschitz. In
particular it tends to a constant map in the Lipschitz sense as `K |t| → 0`. -/
theorem lipschitzWith_flowOfLipschitz_sub_id (hv : LipschitzWith K v) (t : ℝ) :
    LipschitzWith (Real.exp (K * |t|) - 1).toNNReal (fun x ↦ flowOfLipschitz v hv t x - x) := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  rw [Real.coe_toNNReal _ (sub_nonneg.2 (Real.one_le_exp (by positivity))), dist_eq_norm,
    dist_eq_norm, mul_comm]
  -- The difference of the two displacements has derivative `v (φₛ a) - v (φₛ b)`, bounded through
  -- the Lipschitz bound `exp (K |s|)` on the flow.
  have hbound (s : ℝ) : ‖v (flowOfLipschitz v hv s a) - v (flowOfLipschitz v hv s b)‖ ≤
      K * Real.exp (K * |s|) * ‖a - b‖ := by
    rw [← dist_eq_norm, mul_assoc]
    refine (hv.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
    rw [flowOfLipschitz_apply, flowOfLipschitz_apply, mul_comm, ← dist_eq_norm]
    exact ODE.dist_globalSolution_le v hv a b s
  have h := norm_le_exp_sub_one_mul (f := fun s ↦
      (flowOfLipschitz v hv s a - a) - (flowOfLipschitz v hv s b - b))
    (fun s ↦ by
      exact ((hasDerivAt_flowOfLipschitz hv a s).sub_const a).fun_sub
        ((hasDerivAt_flowOfLipschitz hv b s).sub_const b)) (by simp) hbound t
  simpa [mul_comm] using h

/-- **The derivative of the time-`t` map is close to the identity.** For a `K`-Lipschitz vector
field, wherever the time-`t` map of the flow is differentiable (everywhere for a `C¹` field), its
derivative differs from the identity by at most `exp (K |t|) - 1` in operator norm. -/
theorem norm_fderiv_flowOfLipschitz_sub_id_le (hv : LipschitzWith K v) {x : E} {t : ℝ}
    (hx : DifferentiableAt ℝ (flowOfLipschitz v hv t) x) :
    ‖fderiv ℝ (flowOfLipschitz v hv t) x - ContinuousLinearMap.id ℝ E‖ ≤
      Real.exp (K * |t|) - 1 := by
  have h := norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_flowOfLipschitz_sub_id hv t) (x₀ := x)
  have hd : HasFDerivAt (fun y ↦ flowOfLipschitz v hv t y - y)
      (fderiv ℝ (flowOfLipschitz v hv t) x - ContinuousLinearMap.id ℝ E) x :=
    hx.hasFDerivAt.sub (hasFDerivAt_id x)
  rwa [hd.fderiv, Real.coe_toNNReal _ (sub_nonneg.2 (Real.one_le_exp (by positivity)))] at h

/-- **The integral equation of the flow**: `φₜ y = y + ∫₀ᵗ v (φ_τ y) dτ`. -/
theorem flowOfLipschitz_eq_add_integral (hv : LipschitzWith K v) (y : E) (t : ℝ) :
    flowOfLipschitz v hv t y = y + ∫ τ in (0 : ℝ)..t, v (flowOfLipschitz v hv τ y) := by
  simpa only [flowOfLipschitz_apply] using ODE.globalSolution_eq_integral v hv y t

end TauCeti
