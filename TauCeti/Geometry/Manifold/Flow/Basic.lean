/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Flow
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The maximal flow of a vector field

This file presents Tau Ceti's maximal integral curves as a partial flow whose arguments are ordered
as time followed by initial point.  The domain and value are adapters for
`maximalIntegralCurveFlowDomain` and `maximalIntegralCurve`, not independent constructions.  The
domain-aware group law records both the value equation and the condition that the composite time
remains in the interval of existence.

For complete normed model spaces, the existing smooth-dependence theorem for maximal integral
curves gives joint openness of the domain and joint smoothness of the flow, so flowing a `C^n`
family of points for a `C^n` family of times is again `C^n`.  At time zero, the derivative of the
flow is the field in the time direction and the identity in the space directions, so flowing for a
time `τ` vanishing at `x` has derivative `w ↦ w + dτ_x(w) • v x` at `x`.  Along a trajectory, a
function changes at the rate of its derivative in the direction of the vector field.  The escape
theorem says that a maximal trajectory approaching a finite right endpoint eventually leaves every
compact set.

## Main declarations

* `TauCeti.flowDomain`: the domain of the maximal flow, in `(time, point)` order.
* `TauCeti.flowOf`: the maximal flow, total with junk values outside `flowDomain`.
* `TauCeti.isOpen_flowDomain`: openness of the domain for complete model spaces.
* `TauCeti.contMDiffOn_flowOf`: joint regularity of the flow for complete model spaces.
* `TauCeti.contMDiffAt_flowOf_comp`: flowing `C^n` families of points for `C^n` families of times.
* `TauCeti.isOpen_setOf_mem_flowDomain`: the parameters of a continuous family of times and
  points at which the flow is defined form an open set.
* `TauCeti.mfderiv_flowOf_comp_apply`: the differential of `(t, s) ↦ φₜ(f s)`.
* `TauCeti.mfderiv_flowOf_comp_prodMk_apply`: the differential of `y ↦ φ_{τ y}(f y)`.
* `TauCeti.hasDerivAt_comp_flowOf`: the time derivative of a function along a trajectory.
* `TauCeti.mfderiv_flowOf_zero_apply`: the derivative of the flow at time zero.
* `TauCeti.hasMFDerivAt_flowOf_comp_of_eq_zero`: the derivative of flowing for a time that
  vanishes at the base point.
* `TauCeti.mfderiv_flowOf_trajectory_apply`, `TauCeti.mfderiv_flowOf_trajectory_zero_apply`: the
  derivative of a trajectory is the field.
* `TauCeti.mfderiv_flowOf_apply_self`: the differential of the time-`t` map carries the field to
  itself.
* `TauCeti.flowOf_add`: the domain-aware group law.
* `TauCeti.flowOf_neg_flowOf`: flowing backwards undoes flowing forwards.
* `TauCeti.eventually_flowOf_notMem`: escape from compact sets at a finite right endpoint.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9.
-/

public section

noncomputable section

open Function Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The domain of the maximal flow in `(time, point)` order.  This is
`maximalIntegralCurveFlowDomain` transported by `Prod.swap`. -/
def flowDomain (v : (x : M) → TangentSpace I x) : Set (ℝ × M) :=
  Prod.swap ⁻¹' maximalIntegralCurveFlowDomain v

/-- The maximal flow of a vector field, total with the same junk values as
`maximalIntegralCurve`. -/
def flowOf (v : (x : M) → TangentSpace I x) (t : ℝ) (x : M) : M :=
  maximalIntegralCurve v x t

/-- The maximal-flow adapter evaluates to the existing maximal integral curve. -/
@[simp]
theorem flowOf_apply (v : (x : M) → TangentSpace I x) (t : ℝ) (x : M) :
    flowOf v t x = maximalIntegralCurve v x t :=
  (rfl)

/-- Membership in the maximal-flow domain is membership in the maximal interval through the
initial point. -/
@[simp]
theorem mem_flowDomain {v : (x : M) → TangentSpace I x} {t : ℝ} {x : M} :
    (t, x) ∈ flowDomain v ↔ t ∈ maximalIntegralCurveInterval v x := by
  simp only [flowDomain, mem_preimage, Prod.swap_prod_mk,
    mem_maximalIntegralCurveFlowDomain]

/-- Time zero belongs to the maximal-flow domain of `x` as soon as some time does. -/
theorem mem_flowDomain_zero_of_mem {v : (x : M) → TangentSpace I x} {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : ((0 : ℝ), x) ∈ flowDomain v :=
  mem_flowDomain.mpr (zero_mem_maximalIntegralCurveInterval_of_mem (mem_flowDomain.mp ht))

/-- The maximal flow fixes every point at time zero. -/
theorem flowOf_zero (v : (x : M) → TangentSpace I x) (x : M) : flowOf v 0 x = x := by
  rw [flowOf_apply, maximalIntegralCurve_zero]

variable [T2Space M] [BoundarylessManifold I M] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The trajectory `t ↦ flowOf v t x` is an integral curve on its maximal interval of
existence. -/
theorem isMIntegralCurveOn_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) :
    IsMIntegralCurveOn (fun t ↦ flowOf v t x) v {t | (t, x) ∈ flowDomain v} := by
  have hcurve : (fun t ↦ flowOf v t x) = maximalIntegralCurve v x := by
    funext t
    exact flowOf_apply v t x
  have hdomain : {t | (t, x) ∈ flowDomain v} = maximalIntegralCurveInterval v x := by
    ext t
    exact mem_flowDomain
  rw [hcurve, hdomain]
  exact isMIntegralCurveOn_maximalIntegralCurve hv

omit [T2Space M] in
/-- Time zero belongs to the maximal-flow domain. -/
theorem mem_flowDomain_zero [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) :
    ((0 : ℝ), x) ∈ flowDomain v := by
  rw [mem_flowDomain]
  exact zero_mem_maximalIntegralCurveInterval hv.contMDiffAt

omit [CompleteSpace E] in
/-- A global integral curve of a `C¹` field is the maximal flow through its initial value.
No completeness hypothesis is needed on the field or the model space. -/
theorem flowOf_eq_of_isMIntegralCurve [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    flowOf v t (γ 0) = γ t := by
  rw [flowOf_apply]
  exact hγ.maximalIntegralCurve_eq hv t

omit [CompleteSpace E] in
/-- The velocity of a maximal-flow trajectory is the vector field at the current point,
whenever the trajectory is in its domain. -/
theorem curveVelocity_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) :
    Manifold.curveVelocity I (fun s ↦ flowOf v s x) t = v (flowOf v t x) := by
  have hdom : {s | (s, x) ∈ flowDomain v} ∈ 𝓝 t := by
    simpa only [mem_flowDomain, ofPred_mem_eq] using
      isOpen_maximalIntegralCurveInterval.mem_nhds (mem_flowDomain.mp ht)
  have hc := (isMIntegralCurveOn_flowOf hv x).isMIntegralCurveAt hdom
  simpa only [Manifold.curveVelocityWithin_univ] using
    Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
      hc.hasMFDerivAt.hasMFDerivWithinAt uniqueDiffWithinAt_univ

omit [CompleteSpace E] in
/-- A maximal-flow trajectory is differentiable at every time in its domain. -/
theorem mdifferentiableAt_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) :
    MDifferentiableAt 𝓘(ℝ) I (fun s ↦ flowOf v s x) t := by
  have hdom : {s | (s, x) ∈ flowDomain v} ∈ 𝓝 t := by
    simpa only [mem_flowDomain, ofPred_mem_eq] using
      isOpen_maximalIntegralCurveInterval.mem_nhds (mem_flowDomain.mp ht)
  exact ((isMIntegralCurveOn_flowOf hv x).isMIntegralCurveAt hdom).hasMFDerivAt.mdifferentiableAt

omit [CompleteSpace E] in
/-- **The derivative of a trajectory.** At every time in its domain, the derivative of
`s ↦ flowOf v s x` sends `a` to `a • v (flowOf v t x)`. -/
theorem mfderiv_flowOf_trajectory_apply [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (a : ℝ) :
    mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s x) t a = a • v (flowOf v t x) := by
  -- Reading `TangentSpace 𝓘(ℝ) t` as `ℝ`, the derivative sends `a = a • 1` to `a` times the
  -- velocity.
  rw [← curveVelocity_flowOf hv ht, Manifold.curveVelocity_apply]
  exact (congrArg (mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s x) t) (mul_one a).symm).trans
    ((mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s x) t).map_smul a (1 : ℝ))

/-- **The derivative of a trajectory at time zero.** The derivative of `s ↦ flowOf v s x` at
`s = 0` sends `a` to `a • v x`. -/
theorem mfderiv_flowOf_trajectory_zero_apply [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) (a : ℝ) :
    mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s x) 0 a = a • v x := by
  rw [mfderiv_flowOf_trajectory_apply hv (mem_flowDomain_zero hv x)]
  -- The tangent spaces at `flowOf v 0 x` and at `x` are both the model space `E`, so `v` may be
  -- treated as a non-dependent function here.
  exact congrArg (a • v ·) (flowOf_zero v x)

/-- On a complete normed model space, the domain of the maximal flow is jointly open in time
and initial point. -/
theorem isOpen_flowDomain [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    IsOpen (flowDomain v) := by
  simpa only [flowDomain] using
    (isOpen_maximalIntegralCurveFlowDomain hv).preimage continuous_swap

/-- On a complete normed model space, a `C^n` vector field has a jointly `C^n` maximal flow on
its domain. -/
theorem contMDiffOn_flowOf {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I n (fun p : ℝ × M ↦ flowOf v p.1 p.2)
      (flowDomain v) := by
  have h := (contMDiffOn_maximalIntegralCurve hn hv).comp
    (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn fun _ hp ↦ hp
  have hfun : ((fun p : M × ℝ ↦ maximalIntegralCurve v p.1 p.2) ∘
      fun p : ℝ × M ↦ (p.2, p.1)) =
    fun p : ℝ × M ↦ flowOf v p.1 p.2 := by
    funext p
    exact (flowOf_apply v p.1 p.2).symm
  have hdomain : (fun p : ℝ × M ↦ (p.2, p.1)) ⁻¹'
      maximalIntegralCurveFlowDomain v = flowDomain v := by
    rfl
  rw [hfun, hdomain] at h
  exact h

/-- On a complete normed model space, flowing a `C^n` family of initial points for a `C^n` family
of times is `C^n`, wherever the flow is defined. -/
theorem contMDiffAt_flowOf_comp {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    {τ : N → ℝ} {f : N → M} {z : N} (hτ : ContMDiffAt J 𝓘(ℝ) n τ z)
    (hf : ContMDiffAt J I n f z) (hz : (τ z, f z) ∈ flowDomain v) :
    ContMDiffAt J I n (fun y ↦ flowOf v (τ y) (f y)) z :=
  ((contMDiffOn_flowOf hn hv).contMDiffAt
    ((isOpen_flowDomain (hv.of_le (by exact_mod_cast hn))).mem_nhds hz)).comp z (hτ.prodMk hf)

/-- **The differential of a flow out of a map.** On a complete normed model space, at a point
`(t, s)` where `φₜ(f s)` is defined, the differential of `(t, s) ↦ φₜ(f s)` sends a tangent vector
`(r, w)` to `r v + dφₜ(df w)`. -/
theorem mfderiv_flowOf_comp_apply [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] {f : N → M}
    {p : ℝ × N} (hf : ContMDiffAt J I 1 f p.2) (hp : (p.1, f p.2) ∈ flowDomain v)
    (w : TangentSpace (𝓘(ℝ).prod J) p) :
    mfderiv (𝓘(ℝ).prod J) I (fun q : ℝ × N ↦ flowOf v q.1 (f q.2)) p w =
      w.1 • v (flowOf v p.1 (f p.2)) +
        mfderiv I I (flowOf v p.1) (f p.2) (mfderiv J I f p.2 w.2) := by
  -- The time-`t` map is differentiable at `f s`.
  have hflow : MDifferentiableAt I I (flowOf v p.1) (f p.2) :=
    (contMDiffAt_flowOf_comp le_rfl hv contMDiffAt_const contMDiffAt_id hp).mdifferentiableAt
      one_ne_zero
  have hcomp : mfderiv J I (flowOf v p.1 ∘ f) p.2 =
      (mfderiv I I (flowOf v p.1) (f p.2)).comp (mfderiv J I f p.2) :=
    mfderiv_comp p.2 hflow (hf.mdifferentiableAt one_ne_zero)
  have hΦ : MDifferentiableAt (𝓘(ℝ).prod J) I (fun q : ℝ × N ↦ flowOf v q.1 (f q.2)) p :=
    (contMDiffAt_flowOf_comp le_rfl hv contMDiffAt_fst (hf.comp p contMDiffAt_snd)
      hp).mdifferentiableAt one_ne_zero
  refine (mfderiv_prod_eq_add_apply hΦ).trans ?_
  -- The trajectory through `f s` has velocity `v` at time `t`.
  rw [mfderiv_flowOf_trajectory_apply hv hp]
  exact congrArg₂ (· + ·) rfl (DFunLike.congr_fun hcomp w.2)

/-- On a complete normed model space, the set of parameters `y` at which the flow of a continuous
family of initial points `f y` for a continuous family of times `τ y` is defined is open. -/
theorem isOpen_setOf_mem_flowDomain [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {N : Type*} [TopologicalSpace N]
    {τ : N → ℝ} {f : N → M} (hτ : Continuous τ) (hf : Continuous f) :
    IsOpen {y | (τ y, f y) ∈ flowDomain v} :=
  (isOpen_flowDomain hv).preimage (hτ.prodMk hf)

/-- **The differential of flowing a family of points for a family of times.** On a complete normed
model space, at a point `z` where `φ_{τ z}(f z)` is defined, the differential of
`y ↦ φ_{τ y}(f y)` sends a tangent vector `w` to `dτ(w) v + dφ_{τ z}(df w)`. This is
`TauCeti.mfderiv_flowOf_comp_apply` composed with the differential of `y ↦ (τ y, f y)`. -/
theorem mfderiv_flowOf_comp_prodMk_apply [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] {τ : N → ℝ}
    {f : N → M} {z : N} (hτ : MDifferentiableAt J 𝓘(ℝ) τ z) (hf : MDifferentiableAt J I f z)
    (hz : (τ z, f z) ∈ flowDomain v) (w : TangentSpace J z) :
    mfderiv J I (fun y ↦ flowOf v (τ y) (f y)) z w =
      mvfderiv J τ z w • v (flowOf v (τ z) (f z)) +
        mfderiv I I (flowOf v (τ z)) (f z) (mfderiv J I f z w) := by
  have hΦ : MDifferentiableAt (𝓘(ℝ).prod I) I (fun q : ℝ × M ↦ flowOf v q.1 q.2) (τ z, f z) :=
    (contMDiffAt_flowOf_comp le_rfl hv contMDiffAt_fst contMDiffAt_snd hz).mdifferentiableAt
      one_ne_zero
  rw [show (fun y ↦ flowOf v (τ y) (f y)) =
      (fun q : ℝ × M ↦ flowOf v q.1 q.2) ∘ fun y ↦ (τ y, f y) from rfl,
    mfderiv_comp z hΦ (hτ.prodMk hf), ContinuousLinearMap.comp_apply, mfderiv_prodMk hτ hf]
  -- Apply the differential of `(t, x) ↦ φₜ(x)` to the vector `(dτ w, df w)`.
  have h := mfderiv_flowOf_comp_apply (f := id) (p := (τ z, f z)) hv contMDiffAt_id hz
    ((mfderiv J 𝓘(ℝ) τ z).prod (mfderiv J I f z) w)
  rw [mfderiv_id, ContinuousLinearMap.id_apply] at h
  exact h

omit [CompleteSpace E] in
/-- **Derivative along a flow line.** The derivative in time of a function `g` along the
trajectory of `v` through `x` is the derivative of `g` in the direction of `v`. -/
theorem hasDerivAt_comp_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : M → F} {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain v) (hg : MDifferentiableAt I 𝓘(ℝ, F) g (flowOf v t x)) :
    HasDerivAt (fun s ↦ g (flowOf v s x)) (mvfderiv I g (flowOf v t x) (v (flowOf v t x))) t := by
  have hopen : {s | (s, x) ∈ flowDomain v} ∈ 𝓝 t := by
    simpa only [mem_flowDomain, ofPred_mem_eq] using
      isOpen_maximalIntegralCurveInterval.mem_nhds (mem_flowDomain.mp hx)
  exact Manifold.hasDerivAt_comp_curve hg
    (((isMIntegralCurveOn_flowOf hv x).isMIntegralCurveAt hopen).hasMFDerivAt)

/-- **The derivative of the flow at time zero.** At `(0, x)`, the derivative of
`(t, y) ↦ flowOf v t y` sends the time direction to the field at `x` and is the identity in the
space direction. -/
theorem mfderiv_flowOf_zero_apply [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) (a : ℝ)
    (w : TangentSpace I x) :
    -- The two sides live in tangent spaces at different points, both equal to `E` by definition,
    -- so the equation is stated in `E`.
    @Eq E (mfderiv (𝓘(ℝ).prod I) I (fun y : ℝ × M ↦ flowOf v y.1 y.2) (0, x) ((a, w) : ℝ × E))
      (a • v x + w) := by
  have h0 : ((0 : ℝ), x) ∈ flowDomain v := mem_flowDomain_zero hv x
  have hG : MDifferentiableAt (𝓘(ℝ).prod I) I (fun y : ℝ × M ↦ flowOf v y.1 y.2) (0, x) :=
    ((contMDiffOn_flowOf le_rfl hv).contMDiffAt
      ((isOpen_flowDomain hv).mem_nhds h0)).mdifferentiableAt one_ne_zero
  have hspace : (fun z : M ↦ flowOf v 0 z) = id := funext (flowOf_zero v)
  have h1 : @Eq E (mfderiv 𝓘(ℝ) I (fun t : ℝ ↦ flowOf v t x) 0 a) (a • v x) :=
    mfderiv_flowOf_trajectory_zero_apply hv x a
  have h2 : @Eq E (mfderiv I I (fun z : M ↦ flowOf v 0 z) x w) w := by
    rw [hspace, mfderiv_id]
    rfl
  -- The splitting of the derivative into its time and space parts is an equation in the tangent
  -- space at `flowOf v 0 x`, which is `E` by definition, so it composes with `h1` and `h2`.
  exact (mfderiv_prod_eq_add_apply hG).trans (congrArg₂ (· + ·) h1 h2)

/-- **Flowing for a time that vanishes at a point.** If `τ x = 0`, the map
`z ↦ flowOf v (τ z) z` has derivative `w ↦ w + dτ_x(w) • v x` at `x`. -/
theorem hasMFDerivAt_flowOf_comp_of_eq_zero [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {x : M} {τ : M → ℝ}
    {dτ : TangentSpace I x →L[ℝ] ℝ} (hτ : HasMFDerivAt I 𝓘(ℝ) τ x dτ) (hτx : τ x = 0) :
    HasMFDerivAt I I (fun z ↦ flowOf v (τ z) z) x
      (ContinuousLinearMap.id ℝ (TangentSpace I x) + dτ.smulRight (v x)) := by
  have h0 : (τ x, x) ∈ flowDomain v := hτx ▸ mem_flowDomain_zero hv x
  have hG : MDifferentiableAt (𝓘(ℝ).prod I) I (fun y : ℝ × M ↦ flowOf v y.1 y.2) (τ x, x) :=
    ((contMDiffOn_flowOf le_rfl hv).contMDiffAt
      ((isOpen_flowDomain hv).mem_nhds h0)).mdifferentiableAt one_ne_zero
  refine (hG.hasMFDerivAt.comp (f := fun z ↦ (τ z, id z)) x
    (hτ.prodMk (hasMFDerivAt_id x))).congr_mfderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  -- Evaluate the composite with the pairing `z ↦ (τ z, z)` at `w`, as an equation in `E`.
  change @Eq E (mfderiv (𝓘(ℝ).prod I) I (fun y : ℝ × M ↦ flowOf v y.1 y.2) (τ x, x)
    ((dτ w, w) : ℝ × E)) (w + dτ w • v x)
  rw [hτx, mfderiv_flowOf_zero_apply hv, add_comm]

omit [CompleteSpace E] in
/-- The domain-aware group law for the maximal flow.  If time `s` is defined at `x` and time `t`
is defined after flowing for `s`, then time `s + t` is defined at `x` and gives the same value. -/
theorem flowOf_add [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s t : ℝ} {x : M}
    (hs : (s, x) ∈ flowDomain v) (ht : (t, flowOf v s x) ∈ flowDomain v) :
    (s + t, x) ∈ flowDomain v ∧ flowOf v t (flowOf v s x) = flowOf v (s + t) x := by
  have hs' : s ∈ maximalIntegralCurveInterval v x := mem_flowDomain.mp hs
  have ht' : t ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v x s) := by
    simpa only [flowOf_apply] using mem_flowDomain.mp ht
  have hst : s + t ∈ maximalIntegralCurveInterval v x :=
    (mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv hs').mp ht'
  refine ⟨mem_flowDomain.mpr hst, ?_⟩
  simpa only [flowOf_apply] using (maximalIntegralCurve_add hv hs' hst).symm

omit [CompleteSpace E] in
/-- The flow can be run backwards along a trajectory: if time `t` is defined at `x`, then time
`-t` is defined at `flowOf v t x`. -/
theorem neg_mem_flowDomain_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : (-t, flowOf v t x) ∈ flowDomain v := by
  rw [mem_flowDomain, flowOf_apply,
    mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv (mem_flowDomain.mp ht),
    add_neg_cancel, ← mem_flowDomain]
  exact mem_flowDomain_zero_of_mem ht

omit [CompleteSpace E] in
/-- Flowing for time `-t` undoes flowing for time `t`. -/
theorem flowOf_neg_flowOf [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) : flowOf v (-t) (flowOf v t x) = x := by
  rw [(flowOf_add hv ht (neg_mem_flowDomain_flowOf hv ht)).2, add_neg_cancel, flowOf_zero]

omit [CompleteSpace E] in
/-- If `x` returns to itself at time `t`, it does so at every natural multiple of `t`. -/
theorem flowOf_natCast_mul_of_flowOf_eq [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (hx : flowOf v t x = x) (k : ℕ) :
    ((k : ℝ) * t, x) ∈ flowDomain v ∧ flowOf v ((k : ℝ) * t) x = x := by
  induction k with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul] using ⟨mem_flowDomain_zero_of_mem ht, flowOf_zero v x⟩
  | succ k ih =>
    obtain ⟨hk, hkx⟩ := ih
    obtain ⟨hmem, heq⟩ := flowOf_add hv hk (t := t) (by rwa [hkx])
    rw [hkx, hx] at heq
    simpa only [Nat.cast_succ, add_one_mul] using ⟨hmem, heq.symm⟩

omit [CompleteSpace E] in
/-- If `x` returns to itself at time `s`, then so does every point `flowOf v t x` of its
trajectory. -/
theorem flowOf_flowOf_of_flowOf_eq [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (hs : (s, x) ∈ flowDomain v) (hx : flowOf v s x = x) :
    (s, flowOf v t x) ∈ flowDomain v ∧ flowOf v s (flowOf v t x) = flowOf v t x := by
  obtain ⟨hst, heq⟩ := flowOf_add hv hs (hx.symm ▸ ht)
  have hs' : (s, flowOf v t x) ∈ flowDomain v := by
    rw [mem_flowDomain, flowOf_apply,
      mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv (mem_flowDomain.mp ht), add_comm,
      ← mem_flowDomain]
    exact hst
  refine ⟨hs', ?_⟩
  rw [(flowOf_add hv ht hs').2, add_comm, ← heq, hx]

/-- **The flow preserves its generating field.** If time `t` is defined at `x`, the derivative of
the time-`t` map of the flow carries `v x` to `v (flowOf v t x)`. -/
theorem mfderiv_flowOf_apply_self [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) :
    mfderiv I I (flowOf v t) x (v x) = v (flowOf v t x) := by
  have hopen := isOpen_flowDomain hv
  -- The velocity at time `0` of the trajectory through `y` is `v y`.
  have hvel : ∀ y, mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s y) 0 (1 : ℝ) = v y := fun y ↦
    (mfderiv_flowOf_trajectory_zero_apply hv y 1).trans (one_smul ℝ (v y))
  have hcurve : ContinuousAt (fun s ↦ flowOf v s x) 0 :=
    (mdifferentiableAt_flowOf hv (mem_flowDomain_zero hv x)).continuousAt
  -- Near `s = 0`, flowing for time `s` and then `t` is flowing for time `t` and then `s`.
  have hcomm : (flowOf v t ∘ fun s ↦ flowOf v s x) =ᶠ[𝓝 0]
      fun s ↦ flowOf v s (flowOf v t x) := by
    have h₁ : ∀ᶠ s in 𝓝 (0 : ℝ), (s, x) ∈ flowDomain v :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (hopen.mem_nhds (mem_flowDomain_zero hv x))
    have h₂ : ∀ᶠ s in 𝓝 (0 : ℝ), (t, flowOf v s x) ∈ flowDomain v :=
      (continuousAt_const.prodMk hcurve).preimage_mem_nhds
        (hopen.mem_nhds (by simpa only [flowOf_zero v x] using ht))
    have h₃ : ∀ᶠ s in 𝓝 (0 : ℝ), (s, flowOf v t x) ∈ flowDomain v :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (hopen.mem_nhds (mem_flowDomain_zero hv _))
    filter_upwards [h₁, h₂, h₃] with s hs hts hst
    rw [comp_apply, (flowOf_add hv hs hts).2, (flowOf_add hv ht hst).2, add_comm]
  have hΦ : MDifferentiableAt I I (flowOf v t) x :=
    (contMDiffAt_flowOf_comp le_rfl hv contMDiffAt_const contMDiffAt_id ht).mdifferentiableAt
      one_ne_zero
  have key := mfderiv_comp_apply_of_eq (0 : ℝ) hΦ
    (mdifferentiableAt_flowOf hv (mem_flowDomain_zero hv x)) (flowOf_zero v x) (1 : ℝ)
  have hvel' : mfderiv 𝓘(ℝ) I (flowOf v t ∘ fun s ↦ flowOf v s x) 0 (1 : ℝ) =
      v (flowOf v t x) := by
    rw [hcomm.mfderiv_eq]
    -- `tangentSpaceCast` is the identity of the model space.
    exact hvel _
  rw [hvel] at key
  exact key.symm.trans hvel'

/-- At a finite right endpoint of a maximal interval, the trajectory eventually leaves every
compact set. -/
theorem eventually_flowOf_notMem [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {x : M} {b : ℝ}
    (hb : IsLUB {t | (t, x) ∈ flowDomain v} b) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[<] b, flowOf v t x ∉ K := by
  have hdomain : {t | (t, x) ∈ flowDomain v} = maximalIntegralCurveInterval v x := by
    ext t
    exact mem_flowDomain
  have hb' : IsLUB (maximalIntegralCurveInterval v x) b := by
    rw [← hdomain]
    exact hb
  simpa only [flowOf_apply] using
    eventually_notMem_nhdsLT_maximalIntegralCurve hv hb' hK

end TauCeti
