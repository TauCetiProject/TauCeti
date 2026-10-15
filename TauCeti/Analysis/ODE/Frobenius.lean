/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.ODE.ExistUnique
public import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.ODE.SmoothParameter

/-!
# The local Frobenius theorem

Let `E` and `F` be real normed spaces and `f : E × F → (E →L[ℝ] F)`. The *total differential
equation* `D u x = f (x, u x)` asks for a function `u : E → F` whose graph is tangent, at each of
its points `p`, to the graph `{(v, f p v) | v : E}` of `f p`. Differentiating the equation once
more shows that solutions can exist through all points near `p₀` only if `f` satisfies the
**Frobenius integrability condition** `TauCeti.IsFrobeniusIntegrableAt` near `p₀`: the bilinear
map `(v, w) ↦ fderiv ℝ f p (v, f p v) w` is symmetric. The local Frobenius theorem says that the
condition is also sufficient, and that the local solutions are unique.

The integrability condition is the involutivity of the distribution `p ↦ {(v, f p v)}`, written
in coordinates: the vector fields `p ↦ (v, f p v)` span it, and the Lie bracket of the fields
attached to `v` and `w` is `(0, fderiv ℝ f p (v, f p v) w - fderiv ℝ f p (w, f p w) v)`, which is
tangent to the distribution exactly when it vanishes. In a chart adapted to an involutive
distribution on a manifold, the distribution takes this graph form, and the graphs of the local
solutions are its integral manifolds. This is the analytic content of the Frobenius theorem for
involutive distributions, which integrates a Lie subalgebra of the Lie algebra of a Lie group to a
connected Lie subgroup.

## Main definitions and results

* `TauCeti.IsFrobeniusIntegrableAt f p`: the Frobenius integrability condition at `p`.
* `TauCeti.isFrobeniusIntegrableAt_of_eventually_hasFDerivAt`: the condition holds along the
  graph of every solution.
* `TauCeti.exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt`: **the local Frobenius
  theorem**, existence of a local solution through a point near which the condition holds.
* `TauCeti.exists_contDiffAt_solution_family_of_isFrobeniusIntegrableAt`: nearby solutions can be
  chosen to depend smoothly on their initial value.
* `TauCeti.exists_frobenius_flat_coordinate`: the solution family gives an invertible local
  coordinate map whose horizontal slices are tangent to the graph field.
* `TauCeti.eventuallyEq_of_eventually_hasFDerivAt`: local solutions with the same initial value
  agree.
* `TauCeti.eventually_exists_hasFDerivAt_iff_eventually_isFrobeniusIntegrableAt`: solutions exist
  through all points near `p₀` exactly when the condition holds near `p₀`.

## Implementation notes

Existence is proved in finite dimension, where a smooth germ has a globally Lipschitz smooth
representative, so that the parameterized Picard theorem
`ODE.exists_contDiffAt_picard_solution_of_contDiff` applies. The solution through `(x₀, y₀)` is
built along rays: for a small parameter `z`, the ordinary differential equation
`b' = f (x₀ + t • z, b) z` with `b 0 = y₀` is solved on `[0, 1]`, smoothly in `z`, and
`u (x₀ + z) = b 1`. Translating the state by a variable initial value makes the Picard solution
smooth jointly in `z` and that initial value. Rescaling time shows that
`b t = u (x₀ + t • z)`, so `u` solves the equation in the radial direction:
`D u x (x - x₀) = f (x, u x) (x - x₀)`. To upgrade the radial equation,
fix `w` and a ray; then `h t = t • (D u (x₀ + t • z) w - f (x₀ + t • z, u (x₀ + t • z)) w)` solves
a linear ordinary differential equation with `h 0 = 0`, so `h` vanishes. The derivative of `h` is
computed without differentiating `u` twice: `t • D u (x₀ + t • z) w` is the derivative in `s` of
`u` along the ray in the direction `z + s • w`, which is an integral of `f` along that ray by the
radial equation, and it is differentiated under the integral sign. The integrability condition
then turns this derivative into the linear equation. So `f` only needs to be `C¹`.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press (1969), Section 10.9.
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Chapter VI, §1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace TauCeti

section General

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The Frobenius integrability condition** for the total differential equation
`D u x = f (x, u x)` at the point `p`: the bilinear map obtained by differentiating `f` at `p`
along the graph directions `(v, f p v)`, namely `(v, w) ↦ fderiv 𝕜 f p (v, f p v) w`, is
symmetric. The condition is meant for `f` differentiable at `p`: otherwise `fderiv 𝕜 f p` is zero
and the condition holds trivially. -/
def IsFrobeniusIntegrableAt (f : E × F → E →L[𝕜] F) (p : E × F) : Prop :=
  ∀ v w : E, fderiv 𝕜 f p (v, f p v) w = fderiv 𝕜 f p (w, f p w) v

/-- The defining property of the Frobenius integrability condition. -/
theorem isFrobeniusIntegrableAt_iff {f : E × F → E →L[𝕜] F} {p : E × F} :
    IsFrobeniusIntegrableAt f p ↔
      ∀ v w : E, fderiv 𝕜 f p (v, f p v) w = fderiv 𝕜 f p (w, f p w) v :=
  Iff.rfl

/-- The Frobenius integrability condition at `p` only depends on the germ of `f` at `p`. -/
theorem _root_.Filter.EventuallyEq.isFrobeniusIntegrableAt_iff {f g : E × F → E →L[𝕜] F}
    {p : E × F} (h : f =ᶠ[𝓝 p] g) :
    IsFrobeniusIntegrableAt f p ↔ IsFrobeniusIntegrableAt g p := by
  simp only [IsFrobeniusIntegrableAt, h.fderiv_eq, h.eq_of_nhds]

/-- **The Frobenius integrability condition is necessary.** If `u` solves the total differential
equation `D u y = f (y, u y)` near `x` and `f` is differentiable at `(x, u x)`, then `f` satisfies
the Frobenius integrability condition at `(x, u x)`: the condition is the symmetry of the second
derivative of `u` at `x`. -/
theorem isFrobeniusIntegrableAt_of_eventually_hasFDerivAt [IsRCLikeNormedField 𝕜]
    {f : E × F → E →L[𝕜] F} {u : E → F} {x : E}
    (hu : ∀ᶠ y in 𝓝 x, HasFDerivAt u (f (y, u y)) y) (hf : DifferentiableAt 𝕜 f (x, u x)) :
    IsFrobeniusIntegrableAt f (x, u x) := by
  intro v w
  have hgraph : HasFDerivAt (fun y ↦ (y, u y))
      ((ContinuousLinearMap.id 𝕜 E).prod (f (x, u x))) x :=
    (hasFDerivAt_id x).prodMk hu.self_of_nhds
  simpa using second_derivative_symmetric_of_eventually hu (hf.hasFDerivAt.comp x hgraph) v w

end General

section Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The variational equation along a ray, integrated.** Let `α` be `C¹` on an open set `U` and
solve the total differential equation `D α y = g (y, α y)` in the radial direction `y - x₀` at
every point of `U`, and let the segment `x₀ + [0, 1] • z` lie in `U`. Then along that segment the
derivative of `α` in the direction `w`, scaled by the time `t`, is the integral below. It is the
derivative in `s` at `s = 0` of `α` along the ray in the direction `z + s • w`, computed by
differentiating under the integral sign the equation that `α` solves along that ray. -/
private theorem smul_fderiv_apply_eq_intervalIntegral [CompleteSpace F] {g : E × F → E →L[ℝ] F}
    (hg : ContDiff ℝ 1 g) {α : E → F} {U : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ 1 α U)
    {x₀ z : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • z ∈ U)
    (hrad : ∀ y ∈ U, fderiv ℝ α y (y - x₀) = g (y, α y) (y - x₀)) (w : E) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    t • fderiv ℝ α (x₀ + t • z) w = ∫ τ in (0 : ℝ)..t,
      (fderiv ℝ g (x₀ + τ • z, α (x₀ + τ • z)) (τ • w, τ • fderiv ℝ α (x₀ + τ • z) w) z +
        g (x₀ + τ • z, α (x₀ + τ • z)) w) := by
  -- The rays from `x₀` in the directions `z + s • w`, and the field along them.
  obtain ⟨P, hP⟩ : ∃ P : ℝ × ℝ → E, P = fun q ↦ x₀ + q.2 • (z + q.1 • w) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ × ℝ → F, G = fun q ↦ g (P q, α (P q)) (z + q.1 • w) := ⟨_, rfl⟩
  have hPc : ContDiff ℝ 1 P := by rw [hP]; fun_prop
  have hV : IsOpen (P ⁻¹' U) := hU.preimage hPc.continuous
  have hαV : ContDiffOn ℝ 1 (fun q ↦ α (P q)) (P ⁻¹' U) :=
    hα.comp hPc.contDiffOn fun _ hq ↦ hq
  have hGV : ContDiffOn ℝ 1 G (P ⁻¹' U) := by
    rw [hG]
    exact (hg.comp_contDiffOn (hPc.contDiffOn.prodMk hαV)).clm_apply (by fun_prop)
  have hV0 (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : ((0 : ℝ), τ) ∈ P ⁻¹' U := by
    simpa [hP] using hseg τ hτ
  have hslice (s : ℝ) : Continuous fun τ : ℝ ↦ (s, τ) := by fun_prop
  -- Nearby rays stay in `U` up to time `1`, and along each of them `α` integrates `G`.
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ τ ∈ Icc (0 : ℝ) 1, (s, τ) ∈ P ⁻¹' U :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun τ hτ ↦ hV.mem_nhds (hV0 τ hτ)
  have hint : ∀ᶠ s in 𝓝 (0 : ℝ), α (x₀ + t • (z + s • w)) = α x₀ + ∫ τ in (0 : ℝ)..t, G (s, τ) := by
    filter_upwards [hnear] with s hs
    have hst (τ : ℝ) (hτ : τ ∈ Icc 0 t) : (s, τ) ∈ P ⁻¹' U := hs τ ⟨hτ.1, hτ.2.trans ht.2⟩
    have hderiv (τ : ℝ) (hτ : τ ∈ Ioo 0 t) : HasDerivAt (fun τ ↦ α (P (s, τ))) (G (s, τ)) τ := by
      have hmem : P (s, τ) ∈ U := hst τ (Ioo_subset_Icc_self hτ)
      have hray : HasDerivAt (fun τ : ℝ ↦ P (s, τ)) (z + s • w) τ := by
        simpa [hP] using ((hasDerivAt_id τ).smul_const (z + s • w)).const_add x₀
      have hd := ((hα.contDiffAt (hU.mem_nhds hmem)).differentiableAt one_ne_zero).hasFDerivAt
      refine (hd.comp_hasDerivAt τ hray).congr_deriv ?_
      -- The radial equation at `P (s, τ)`, divided by `τ ≠ 0`.
      have h := hrad _ hmem
      simp only [hP, add_sub_cancel_left, map_smul] at h
      simpa [hG, hP] using smul_right_injective F hτ.1.ne' h
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hαV.continuousOn.comp (hslice s).continuousOn hst) hderiv
      ((hGV.continuousOn.comp (hslice s).continuousOn
        (by rw [uIcc_of_le ht.1]; exact hst)).intervalIntegrable)
    simp only [hP, Function.comp_apply, zero_smul, add_zero] at hFTC
    rw [hFTC, add_sub_cancel]
  -- Differentiate in `s` at `s = 0`, under the integral sign.
  obtain ⟨-, hR⟩ := hasDerivAt_intervalIntegral_of_contDiffOn hV hGV (x₀ := 0) (a := 0) (b := t)
    (by
      rintro ⟨s, τ⟩ ⟨rfl, hτ⟩
      rw [uIcc_of_le ht.1] at hτ
      exact hV0 τ ⟨hτ.1, hτ.2.trans ht.2⟩)
  have hL : HasDerivAt (fun s : ℝ ↦ α (x₀ + t • (z + s • w))) (fderiv ℝ α (x₀ + t • z) (t • w))
      0 := by
    have hd : HasFDerivAt α (fderiv ℝ α (x₀ + t • z)) (x₀ + t • (z + (0 : ℝ) • w)) := by
      rw [zero_smul, add_zero]
      exact ((hα.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt one_ne_zero).hasFDerivAt
    have hray : HasDerivAt (fun s : ℝ ↦ x₀ + t • (z + s • w)) (t • w) 0 := by
      simpa using ((((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z).const_smul t).const_add x₀
    exact hd.comp_hasDerivAt (0 : ℝ) hray
  rw [← map_smul, hL.unique ((hR.const_add (α x₀)).congr_of_eventuallyEq hint)]
  -- Identify the partial derivative of `G` in `s`.
  refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
  rw [uIcc_of_le ht.1] at hτ
  have hmem := hV0 τ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hmem' : x₀ + τ • z ∈ U := hseg τ ⟨hτ.1, hτ.2.trans ht.2⟩
  have h1 : HasDerivAt (fun s : ℝ ↦ G (s, τ)) (fderiv ℝ G (0, τ) (1, 0)) 0 :=
    ((hGV.differentiableOn one_ne_zero _ hmem).differentiableAt
      (hV.mem_nhds hmem)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) τ))
  have hray : HasDerivAt (fun s : ℝ ↦ P (s, τ)) (τ • w) 0 := by
    simpa [hP] using ((((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z).const_smul τ).const_add
      x₀
  have hP0 : P (0, τ) = x₀ + τ • z := by simp [hP]
  have hdα := ((hα.contDiffAt (hU.mem_nhds hmem')).differentiableAt one_ne_zero).hasFDerivAt
  rw [← hP0] at hdα
  have h2 : HasDerivAt (fun s : ℝ ↦ G (s, τ))
      (fderiv ℝ g (x₀ + τ • z, α (x₀ + τ • z)) (τ • w, τ • fderiv ℝ α (x₀ + τ • z) w) z +
        g (x₀ + τ • z, α (x₀ + τ • z)) w) 0 := by
    have hgP := (hg.differentiable one_ne_zero (P (0, τ), α (P (0, τ)))).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (hray.prodMk (hdα.comp_hasDerivAt (0 : ℝ) hray))
    have hdir : HasDerivAt (fun s : ℝ ↦ z + s • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
    rw [hG]
    refine (hgP.clm_apply hdir).congr_deriv ?_
    simp [hP0, map_smul]
  exact h1.unique h2

/-- **The defect of a radial solution along a ray.** Let `α` be `C¹` on an open set `U` and solve
the total differential equation `D α y = g (y, α y)` in the radial direction `y - x₀` on `U`, and
let the segment `x₀ + [0, 1] • z` lie in `U`. Along the ray `s ↦ x₀ + s • z`, the defect
`s • (D α - g (·, α ·))`, applied to a fixed vector `w`, solves a linear ordinary differential
equation from the right at every time `t ∈ [0, 1)` at which the Frobenius integrability condition
holds at the corresponding point of the graph. -/
private theorem hasDerivWithinAt_smul_radialDefect [CompleteSpace F] {g : E × F → E →L[ℝ] F}
    (hg : ContDiff ℝ 1 g) {α : E → F} {U : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ 1 α U)
    {x₀ z : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • z ∈ U)
    (hrad : ∀ y ∈ U, fderiv ℝ α y (y - x₀) = g (y, α y) (y - x₀)) (w : E) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hint : IsFrobeniusIntegrableAt g (x₀ + t • z, α (x₀ + t • z))) :
    HasDerivWithinAt
      (fun s : ℝ ↦ s • (fderiv ℝ α (x₀ + s • z) w - g (x₀ + s • z, α (x₀ + s • z)) w))
      (fderiv ℝ g (x₀ + t • z, α (x₀ + t • z))
        (0, t • (fderiv ℝ α (x₀ + t • z) w - g (x₀ + t • z, α (x₀ + t • z)) w)) z) (Ici t) t := by
  have hmem : x₀ + t • z ∈ U := hseg t (Ico_subset_Icc_self ht)
  have hT : IsOpen {τ : ℝ | x₀ + τ • z ∈ U} := hU.preimage (by fun_prop)
  -- The integrand of `smul_fderiv_apply_eq_intervalIntegral` is continuous near `[0, 1]`.
  have hφ : ContinuousOn (fun τ : ℝ ↦ fderiv ℝ g (x₀ + τ • z, α (x₀ + τ • z))
      (τ • w, τ • fderiv ℝ α (x₀ + τ • z) w) z + g (x₀ + τ • z, α (x₀ + τ • z)) w)
      {τ : ℝ | x₀ + τ • z ∈ U} := by
    have hDα : ContinuousOn (fun τ : ℝ ↦ fderiv ℝ α (x₀ + τ • z)) {τ : ℝ | x₀ + τ • z ∈ U} :=
      (hα.continuousOn_fderiv_of_isOpen hU le_rfl).comp (by fun_prop) fun _ hτ ↦ hτ
    have hα' : ContinuousOn (fun τ : ℝ ↦ α (x₀ + τ • z)) {τ : ℝ | x₀ + τ • z ∈ U} :=
      hα.continuousOn.comp (by fun_prop) fun _ hτ ↦ hτ
    have hgraph : ContinuousOn (fun τ : ℝ ↦ (x₀ + τ • z, α (x₀ + τ • z)))
        {τ : ℝ | x₀ + τ • z ∈ U} :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn.prodMk hα'
    exact (((hg.continuous_fderiv one_ne_zero).comp_continuousOn hgraph).clm_apply
      ((continuous_id.smul continuous_const).continuousOn.prodMk
        (continuousOn_id.smul (hDα.clm_apply continuousOn_const)))).clm_apply
      continuousOn_const |>.add ((hg.continuous.comp_continuousOn hgraph).clm_apply
        continuousOn_const)
  have h1 : HasDerivWithinAt (fun s : ℝ ↦ s • fderiv ℝ α (x₀ + s • z) w)
      (fderiv ℝ g (x₀ + t • z, α (x₀ + t • z)) (t • w, t • fderiv ℝ α (x₀ + t • z) w) z +
        g (x₀ + t • z, α (x₀ + t • z)) w) (Ici t) t := by
    have hI := intervalIntegral.integral_hasDerivAt_right (a := 0)
      ((hφ.mono fun τ hτ ↦ by
        rw [uIcc_of_le ht.1] at hτ
        exact hseg τ ⟨hτ.1, hτ.2.trans ht.2.le⟩).intervalIntegrable)
      (hφ.stronglyMeasurableAtFilter hT t hmem) (hφ.continuousAt (hT.mem_nhds hmem))
    refine hI.hasDerivWithinAt.congr_of_eventuallyEq ?_
      (smul_fderiv_apply_eq_intervalIntegral hg hU hα hseg hrad w (Ico_subset_Icc_self ht))
    filter_upwards [Icc_mem_nhdsGE ht.2] with s hs
    exact smul_fderiv_apply_eq_intervalIntegral hg hU hα hseg hrad w ⟨ht.1.trans hs.1, hs.2⟩
  have hray : HasDerivAt (fun s : ℝ ↦ x₀ + s • z) z t := by
    simpa only [id, one_smul] using ((hasDerivAt_id t).smul_const z).const_add x₀
  have hdα := ((hα.contDiffAt (hU.mem_nhds hmem)).differentiableAt one_ne_zero).hasFDerivAt
  have h2 : HasDerivAt (fun s ↦ g (x₀ + s • z, α (x₀ + s • z)) w)
      (fderiv ℝ g (x₀ + t • z, α (x₀ + t • z)) (z, fderiv ℝ α (x₀ + t • z) z) w) t :=
    (((hg.differentiable one_ne_zero (x₀ + t • z, α (x₀ + t • z))).hasFDerivAt.comp_hasDerivAt
      (f := fun s : ℝ ↦ (x₀ + s • z, α (x₀ + s • z))) t
      (hray.prodMk (hdα.comp_hasDerivAt (f := fun s : ℝ ↦ x₀ + s • z) t hray))).clm_apply
      (hasDerivAt_const t w)).congr_deriv (by simp)
  simp only [smul_sub]
  refine (h1.sub ((hasDerivAt_id t).smul h2).hasDerivWithinAt).congr_deriv ?_
  -- Combine the radial equation and the integrability condition at `x₀ + t • z`.
  have r2 := hrad _ hmem
  have i1 := hint z w
  rw [add_sub_cancel_left] at r2
  simp only [id_eq, one_smul]
  generalize fderiv ℝ g (x₀ + t • z, α (x₀ + t • z)) = A at *
  generalize g (x₀ + t • z, α (x₀ + t • z)) = G at *
  generalize fderiv ℝ α (x₀ + t • z) = Dy at *
  have a1 : A (t • w, t • Dy w) z = A (t • w, t • G w) z + A (0, t • Dy w - t • G w) z := by
    rw [← add_apply, ← map_add, Prod.mk_add_mk, add_zero, add_sub_cancel]
  have a2 : t • A (z, Dy z) w = t • A (z, G z) w := by
    rw [← smul_apply, ← map_smul, ← smul_apply, ← map_smul, Prod.smul_mk, Prod.smul_mk,
      ← map_smul, ← map_smul, r2]
  have a3 : A (t • w, t • G w) z = t • A (w, G w) z := by
    rw [← Prod.smul_mk, map_smul, smul_apply]
  linear_combination (norm := module) a1 - a2 - t • i1 + a3

/-- **From the radial equation to the total differential equation.** Let `α` be `C¹` on an open
set `U` and solve the total differential equation `D α y = g (y, α y)` in the radial direction
`y - x₀` at every point of `U`, where `g` is `C¹` and globally Lipschitz. If the Frobenius
integrability condition holds along the graph of `α` over `U`, then `α` solves the full equation
at every point `x` whose segment from `x₀` lies in `U`. -/
private theorem fderiv_eq_of_radial [CompleteSpace F] {g : E × F → E →L[ℝ] F} {K : ℝ≥0}
    (hg : ContDiff ℝ 1 g) (hgK : LipschitzWith K g) {α : E → F} {U : Set E} (hU : IsOpen U)
    (hα : ContDiffOn ℝ 1 α U) {x₀ x : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • (x - x₀) ∈ U)
    (hrad : ∀ y ∈ U, fderiv ℝ α y (y - x₀) = g (y, α y) (y - x₀))
    (hint : ∀ y ∈ U, IsFrobeniusIntegrableAt g (y, α y)) :
    fderiv ℝ α x = g (x, α x) := by
  ext w
  -- The defect along the segment solves a linear ODE with zero initial value, so it vanishes.
  obtain ⟨L, hL⟩ : ∃ L : ℝ → F →L[ℝ] F, L = fun t ↦ ((fderiv ℝ g (x₀ + t • (x - x₀),
      α (x₀ + t • (x - x₀)))).comp (ContinuousLinearMap.inr ℝ E F)).flip (x - x₀) := ⟨_, rfl⟩
  have hLip (t : ℝ) : LipschitzWith (K * ‖x - x₀‖₊) (L t) := by
    refine (L t).lipschitzWith.weaken ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    obtain ⟨A, hA⟩ : ∃ A, A = fderiv ℝ g (x₀ + t • (x - x₀), α (x₀ + t • (x - x₀))) := ⟨_, rfl⟩
    calc ‖L t‖ ≤ ‖A.comp (ContinuousLinearMap.inr ℝ E F)‖ * ‖x - x₀‖ := by
          simpa [hL, hA, ContinuousLinearMap.opNorm_flip] using
            (A.comp (ContinuousLinearMap.inr ℝ E F)).flip.le_opNorm (x - x₀)
      _ ≤ ‖A‖ * ‖x - x₀‖ := by
          gcongr
          exact (A.opNorm_comp_le _).trans
            (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ..))
      _ ≤ K * ‖x - x₀‖ := by
          gcongr
          exact hA ▸ norm_fderiv_le_of_lipschitz ℝ hgK
  have hcont : ContinuousOn (fun s : ℝ ↦ s • (fderiv ℝ α (x₀ + s • (x - x₀)) w -
      g (x₀ + s • (x - x₀), α (x₀ + s • (x - x₀))) w)) (Icc 0 1) := by
    have hDα : ContinuousOn (fun s : ℝ ↦ fderiv ℝ α (x₀ + s • (x - x₀))) (Icc 0 1) :=
      (hα.continuousOn_fderiv_of_isOpen hU le_rfl).comp (by fun_prop) hseg
    have hα' : ContinuousOn (fun s : ℝ ↦ α (x₀ + s • (x - x₀))) (Icc 0 1) :=
      hα.continuousOn.comp (by fun_prop) hseg
    have hgraph : ContinuousOn (fun s : ℝ ↦ (x₀ + s • (x - x₀), α (x₀ + s • (x - x₀))))
        (Icc 0 1) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn.prodMk hα'
    exact continuousOn_id.smul ((hDα.clm_apply continuousOn_const).sub
      ((hg.continuous.comp_continuousOn hgraph).clm_apply continuousOn_const))
  have hh (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : HasDerivWithinAt (fun s : ℝ ↦ s • (fderiv ℝ α
      (x₀ + s • (x - x₀)) w - g (x₀ + s • (x - x₀), α (x₀ + s • (x - x₀))) w)) (L t (t •
      (fderiv ℝ α (x₀ + t • (x - x₀)) w - g (x₀ + t • (x - x₀), α (x₀ + t • (x - x₀))) w)))
      (Ici t) t :=
    (hasDerivWithinAt_smul_radialDefect hg hU hα hseg hrad w ht
      (hint _ (hseg t (Ico_subset_Icc_self ht)))).congr_deriv (by
        simp only [hL, ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp,
          Function.comp_apply, ContinuousLinearMap.inr_apply])
  have heq := ODE_solution_unique (v := fun t k ↦ L t k) (g := fun _ ↦ (0 : F)) hLip hcont hh
    continuousOn_const
    (fun t _ ↦ by simpa using (hasDerivAt_const t (0 : F)).hasDerivWithinAt (s := Ici t))
    (by simp) (right_mem_Icc.2 zero_le_one)
  simpa [sub_eq_zero] using heq

/-- **Uniqueness in the local Frobenius theorem.** Two solutions of the total differential
equation `D u x = f (x, u x)` near `x₀` taking the same value at `x₀` agree near `x₀`, as soon as
`f` is Lipschitz near `(x₀, u₁ x₀)`. Neither integrability nor finite dimensionality is needed:
along each ray from `x₀` both solutions solve the same ordinary differential equation. -/
theorem eventuallyEq_of_eventually_hasFDerivAt {f : E × F → E →L[ℝ] F} {u₁ u₂ : E → F} {x₀ : E}
    {K : ℝ≥0} {s : Set (E × F)} (hs : s ∈ 𝓝 (x₀, u₁ x₀)) (hf : LipschitzOnWith K f s)
    (hu₁ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt u₁ (f (x, u₁ x)) x)
    (hu₂ : ∀ᶠ x in 𝓝 x₀, HasFDerivAt u₂ (f (x, u₂ x)) x) (h₀ : u₁ x₀ = u₂ x₀) :
    u₁ =ᶠ[𝓝 x₀] u₂ := by
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.1 hs
  have hball₁ := hu₁.self_of_nhds.continuousAt.eventually (Metric.ball_mem_nhds _ hδ)
  have hball₂ := hu₂.self_of_nhds.continuousAt.eventually (Metric.ball_mem_nhds _ hδ)
  rw [← h₀] at hball₂
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (((hu₁.and hu₂).and (hball₁.and hball₂)).and (Metric.ball_mem_nhds x₀ hδ))
  filter_upwards [Metric.ball_mem_nhds x₀ hρ] with x hx
  -- Both solutions solve the same ODE along the segment from `x₀` to `x`.
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x₀ + t • (x - x₀) ∈ Metric.ball x₀ ρ :=
    (convex_ball x₀ ρ).add_smul_sub_mem (Metric.mem_ball_self hρ) hx ht
  have hcurve (u : E → F) (hu : ∀ y ∈ Metric.ball x₀ ρ, HasFDerivAt u (f (y, u y)) y) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun s ↦ u (x₀ + s • (x - x₀)))
        (f (x₀ + t • (x - x₀), u (x₀ + t • (x - x₀))) (x - x₀)) t :=
    ((hu _ (hseg t ht)).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (x - x₀)).const_add x₀)).congr_deriv (by simp)
  have hLip (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : LipschitzOnWith (K * ‖x - x₀‖₊)
      (fun k ↦ f (x₀ + t • (x - x₀), k) (x - x₀)) (Metric.ball (u₁ x₀) δ) := by
    refine LipschitzOnWith.of_dist_le_mul fun k hk k' hk' ↦ ?_
    have hmem (k : F) (hk : k ∈ Metric.ball (u₁ x₀) δ) : (x₀ + t • (x - x₀), k) ∈ s :=
      hδs (by rw [← ball_prod_same]; exact ⟨(hball _ (hseg t (Ico_subset_Icc_self ht))).2, hk⟩)
    rw [dist_eq_norm, ← sub_apply]
    calc ‖(f (x₀ + t • (x - x₀), k) - f (x₀ + t • (x - x₀), k')) (x - x₀)‖
        ≤ ‖f (x₀ + t • (x - x₀), k) - f (x₀ + t • (x - x₀), k')‖ * ‖x - x₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * dist (x₀ + t • (x - x₀), k) (x₀ + t • (x - x₀), k')) * ‖x - x₀‖ := by
          gcongr
          rw [← dist_eq_norm]
          exact hf.dist_le_mul _ (hmem k hk) _ (hmem k' hk')
      _ = K * ‖x - x₀‖₊ * dist k k' := by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
          push_cast
          ring
  have heq := ODE_solution_unique_of_mem_Icc_right hLip
    (f := fun s ↦ u₁ (x₀ + s • (x - x₀))) (g := fun s ↦ u₂ (x₀ + s • (x - x₀)))
    (HasDerivAt.continuousOn fun t ht ↦ hcurve u₁ (fun y hy ↦ (hball y hy).1.1.1) t ht)
    (fun t ht ↦ (hcurve u₁ (fun y hy ↦ (hball y hy).1.1.1) t
      (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht ↦ (hball _ (hseg t (Ico_subset_Icc_self ht))).1.2.1)
    (HasDerivAt.continuousOn fun t ht ↦ hcurve u₂ (fun y hy ↦ (hball y hy).1.1.2) t ht)
    (fun t ht ↦ (hcurve u₂ (fun y hy ↦ (hball y hy).1.1.2) t
      (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht ↦ (hball _ (hseg t (Ico_subset_Icc_self ht))).1.2.2)
    (by simpa using h₀) (right_mem_Icc.2 zero_le_one)
  simpa using heq

/-- **Rescaling time along a ray rescales the parameter.** Let `c z`, for `z` in a ball, be
continuous curves starting at `p₀` which solve the system `(ξ, b)' = (z, g (ξ, b) z)` on `[0, 1)`,
where `g` is globally Lipschitz. Then for `t ∈ [0, 1]` the curve attached to `t • z` reaches at
time `1` the point which the curve attached to `z` reaches at time `t`. -/
private theorem rayFamily_smul_apply_one {g : E × F → E →L[ℝ] F} {K : ℝ≥0}
    (hgK : LipschitzWith K g) {r : ℝ} {p₀ : E × F} {c : E → ℝ → E × F}
    (hcont : ∀ z, Continuous (c z)) (hc0 : ∀ z ∈ Metric.ball (0 : E) r, c z 0 = p₀)
    (hcR : ∀ z ∈ Metric.ball (0 : E) r, ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (c z) (z, g (c z t) z) (Ici t) t)
    {z : E} (hz : z ∈ Metric.ball 0 r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    c (t • z) 1 = c z t := by
  have htz : t • z ∈ Metric.ball (0 : E) r := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
  -- Both curves solve the system with parameter `t • z`, whose field is globally Lipschitz.
  have hLip (_ : ℝ) : LipschitzWith (K * ‖t • z‖₊) (fun q : E × F ↦ (t • z, g q (t • z))) := by
    refine LipschitzWith.of_dist_le_mul fun q q' ↦ ?_
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm, ← sub_apply]
    push_cast
    calc ‖(g q - g q') (t • z)‖ ≤ ‖g q - g q'‖ * ‖t • z‖ := (g q - g q').le_opNorm _
      _ ≤ (K * dist q q') * ‖t • z‖ := by
          gcongr
          rw [← dist_eq_norm]
          exact hgK.dist_le_mul q q'
      _ = K * ‖t • z‖ * dist q q' := by ring
  have heq := ODE_solution_unique (v := fun _ q ↦ (t • z, g q (t • z))) hLip
    (f := c (t • z)) (g := fun s ↦ c z (t * s)) (hcont _).continuousOn
    (fun s hs ↦ hcR _ htz s hs) (by fun_prop)
    (fun s hs ↦ ?_) (by simp [hc0 z hz, hc0 _ htz]) (right_mem_Icc.2 zero_le_one)
  · simpa using heq
  · have hts : t * s ∈ Ico (0 : ℝ) 1 :=
      ⟨mul_nonneg ht.1 hs.1, (mul_le_of_le_one_left hs.1 ht.2).trans_lt hs.2⟩
    have := (hcR z hz (t * s) hts).scomp s
      (((hasDerivAt_id s).const_mul t).hasDerivWithinAt (s := Ici s))
      (fun s' (hs' : s ≤ s') ↦ mul_le_mul_of_nonneg_left hs' ht.1)
    exact this.congr_deriv (by simp [Prod.smul_mk, map_smul])

end Real

section FiniteDimensional

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Solutions along rays which depend smoothly on the initial value. -/
private theorem exists_rayFamily_of_initial [CompleteSpace E] [CompleteSpace F] {n : ℕ∞}
    {g : E × F → E →L[ℝ] F} (hg : ContDiff ℝ (n + 1) g) (x₀ : E) (y₀ : F) :
    ∃ (c : E × F → ℝ → E × F) (r : ℝ), 0 < r ∧
      ContDiffAt ℝ (n + 1) (fun q ↦ c q 1) (0, y₀) ∧ c (0, y₀) 1 = (x₀, y₀) ∧
      (∀ q, Continuous (c q)) ∧ ∀ q ∈ Metric.ball ((0 : E), y₀) r,
        c q 0 = (x₀, q.2) ∧
          (∀ t ∈ Ico (0 : ℝ) 1,
            HasDerivWithinAt (c q) (q.1, g (c q t) q.1) (Ici t) t) ∧
          ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (c q) (q.1, g (c q t) q.1) t := by
  let G : (E × F) × (E × F) → E × F := fun q ↦
    (q.1.1, g (q.2.1, q.1.2 + q.2.2) q.1.1)
  have hG : ContDiff ℝ (n + 1) G := by
    dsimp only [G]
    fun_prop
  obtain ⟨γ, hγ, hγ0, hprop⟩ := ODE.exists_contDiffAt_picard_solution_of_contDiff
    G ((0 : E), y₀) (x₀, 0) hG (.of_forall fun q ↦ by simp [G])
  obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff_ball.1 hprop
  let c : E × F → ℝ → E × F := fun q t ↦
    let z := γ q (projIcc 0 1 zero_le_one t)
    (z.1, q.2 + z.2)
  refine ⟨c, r, hr, ?_, ?_, fun q ↦ ?_, fun q hq ↦ ?_⟩
  · have heval : ContDiffAt ℝ (n + 1)
        (fun q : E × F ↦ γ q (⟨1, right_mem_Icc.2 zero_le_one⟩ : Icc (0 : ℝ) 1))
        ((0 : E), y₀) := by
      convert (ContinuousMap.evalCLM (R := ℝ)
        (⟨1, right_mem_Icc.2 zero_le_one⟩ : Icc (0 : ℝ) 1)).contDiff.comp_contDiffAt
          ((0 : E), y₀) hγ using 1
      funext q
      rfl
    simpa only [c, projIcc_right] using heval.fst.prodMk (contDiffAt_snd.add heval.snd)
  · simp [c, hγ0]
  · exact ((γ q).continuous.comp continuous_projIcc).fst.prodMk
      (continuous_const.add ((γ q).continuous.comp continuous_projIcc).snd)
  obtain ⟨hpicard, hinterior, hright⟩ := hP q hq
  have hc0 : c q 0 = (x₀, q.2) := by
    have := hpicard ⟨0, left_mem_Icc.2 zero_le_one⟩
    simp only [intervalIntegral.integral_same, add_zero] at this
    dsimp only [c]
    rw [projIcc_left]
    rw [this]
    simp
  refine ⟨hc0, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have h := hright t ht
    have hfst : HasDerivWithinAt (fun s ↦ ((γ q) (projIcc 0 1 zero_le_one s)).1)
        (G (q, (γ q) (projIcc 0 1 zero_le_one t))).1 (Ici t) t := h.fst
    have hsnd : HasDerivWithinAt (fun s ↦ ((γ q) (projIcc 0 1 zero_le_one s)).2)
        (G (q, (γ q) (projIcc 0 1 zero_le_one t))).2 (Ici t) t := h.snd
    exact (hfst.prodMk ((hasDerivWithinAt_const t (Ici t) q.2).add hsnd)).congr_deriv (by
      simp [G, c])
  · have h := hinterior t ht
    have hfst : HasDerivAt (fun s ↦ ((γ q) (projIcc 0 1 zero_le_one s)).1)
        (G (q, (γ q) (projIcc 0 1 zero_le_one t))).1 t := h.fst
    have hsnd : HasDerivAt (fun s ↦ ((γ q) (projIcc 0 1 zero_le_one s)).2)
        (G (q, (γ q) (projIcc 0 1 zero_le_one t))).2 t := h.snd
    exact (hfst.prodMk ((hasDerivAt_const (x := t) q.2).add hsnd)).congr_deriv (by
      simp [G, c])

/-- A ray family is evaluated by rescaling its endpoint parameter. -/
private theorem rayFamily_eval {g : E × F → E →L[ℝ] F} {K : ℝ≥0} {r : ℝ}
    {x₀ : E} {y₀ : F} {c : E × F → ℝ → E × F} (hgK : LipschitzWith K g)
    (hcont : ∀ q, Continuous (c q))
    (hc0 : ∀ q ∈ Metric.ball ((0 : E), y₀) r, c q 0 = (x₀, q.2))
    (hcR : ∀ q ∈ Metric.ball ((0 : E), y₀) r, ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (c q) (q.1, g (c q t) q.1) (Ici t) t)
    {q : E × F} (hq : q ∈ Metric.ball ((0 : E), y₀) r) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    c q s = (x₀ + s • q.1, (c (s • q.1, q.2) 1).2) := by
  have hpair_mem {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
      (z, q.2) ∈ Metric.ball ((0 : E), y₀) r := by
    rw [Metric.mem_ball, Prod.dist_eq] at hq ⊢
    exact (max_lt_iff).2 ⟨hz, (max_lt_iff).1 hq |>.2⟩
  have hzq : q.1 ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, Prod.dist_eq] at hq
    exact (max_lt_iff).1 hq |>.1
  apply Prod.ext
  · refine eq_of_has_deriv_right_eq (f := fun τ ↦ (c q τ).1)
      (g := fun τ ↦ x₀ + τ • q.1) (f' := fun _ ↦ q.1) (fun τ hτ ↦ ?_)
      (fun τ _ ↦ ?_) (hcont q).fst.continuousOn (by fun_prop)
      (by simp [(hc0 q hq)]) s hs
    · exact (hcR q hq τ hτ).fst
    · simpa using (((hasDerivAt_id τ).smul_const q.1).const_add x₀).hasDerivWithinAt
  · have hscale := rayFamily_smul_apply_one (p₀ := (x₀, q.2)) (z := q.1)
      (c := fun z τ ↦ c (z, q.2) τ) hgK (fun z ↦ hcont (z, q.2))
      (fun z hz ↦ hc0 (z, q.2) (hpair_mem hz))
      (fun z hz ↦ hcR (z, q.2) (hpair_mem hz)) hzq hs
    exact congrArg Prod.snd hscale |>.symm

/-- Radial solutions which depend smoothly on their initial value. -/
private theorem exists_radial_solution_family [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {n : ℕ∞} {g : E × F → E →L[ℝ] F} {K : ℝ≥0} (hg : ContDiff ℝ (n + 1) g)
    (hgK : LipschitzWith K g) (x₀ : E) (y₀ : F) :
    ∃ α : E × F → F, α (x₀, y₀) = y₀ ∧ ContDiffAt ℝ (n + 1) α (x₀, y₀) ∧
      (∀ᶠ y in 𝓝 y₀, α (x₀, y) = y) ∧ ∃ r > 0,
        ∀ q ∈ Metric.ball ((0 : E), y₀) r, ∀ t ∈ Ioo (0 : ℝ) 1,
          DifferentiableAt ℝ (fun x ↦ α (x, q.2)) (x₀ + t • q.1) →
            fderiv ℝ (fun x ↦ α (x, q.2)) (x₀ + t • q.1) q.1 =
              g (x₀ + t • q.1, α (x₀ + t • q.1, q.2)) q.1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨c, r, hr, hc1, hc01, hcont, hc⟩ := exists_rayFamily_of_initial hg x₀ y₀
  let α : E × F → F := fun q ↦ (c (q.1 - x₀, q.2) 1).2
  refine ⟨α, by simp [α, hc01], ?_, ?_, r, hr, fun q hq t ht hd ↦ ?_⟩
  · have hc1' : ContDiffAt ℝ (n + 1) (fun q ↦ c q 1) (x₀ - x₀, y₀) := by
      rw [sub_self]
      exact hc1
    exact contDiff_snd.comp_contDiffAt (x₀, y₀)
      (hc1'.comp (f := fun q : E × F ↦ (q.1 - x₀, q.2)) (x₀, y₀)
        ((contDiffAt_fst.sub contDiffAt_const).prodMk contDiffAt_snd))
  · filter_upwards [Metric.ball_mem_nhds y₀ hr] with y hy
    have hpair {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
        (z, y) ∈ Metric.ball ((0 : E), y₀) r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact (max_lt_iff).2 ⟨hz, hy⟩
    have hz : (0 : E) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
    have hscale := rayFamily_smul_apply_one (p₀ := (x₀, y)) (z := (0 : E))
      (c := fun z τ ↦ c (z, y) τ) hgK (fun z ↦ hcont (z, y))
      (fun z hz ↦ (hc (z, y) (hpair hz)).1)
      (fun z hz ↦ (hc (z, y) (hpair hz)).2.1) hz (left_mem_Icc.2 zero_le_one)
    have hscale' : c (0, y) 1 = c (0, y) 0 := by simpa using hscale
    simp only [α, sub_self]
    rw [hscale', (hc (0, y) (hpair hz)).1]
  have heval (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :=
    rayFamily_eval hgK hcont (fun q hq ↦ (hc q hq).1)
      (fun q hq ↦ (hc q hq).2.1) hq hs
  have hfst (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (c q s).1 = x₀ + s • q.1 := congrArg Prod.fst (heval s hs)
  have hray (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      α (x₀ + s • q.1, q.2) = (c q s).2 := by
    simp only [α, add_sub_cancel_left]
    exact congrArg Prod.snd (heval s hs) |>.symm
  have h1 : HasDerivAt (fun s ↦ α (x₀ + s • q.1, q.2))
      (g (c q t) q.1) t := by
    exact ((hasFDerivAt_snd.comp_hasDerivAt t ((hc q hq).2.2 t ht)).congr_of_eventuallyEq
      (eventually_of_mem (Icc_mem_nhds ht.1 ht.2) hray)).congr_deriv (by simp)
  have h2 := hd.hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const q.1).const_add x₀)
  simp only [id_eq, one_smul] at h2
  rw [h2.unique h1]
  congr 2
  exact Prod.ext (hfst t (Ioo_subset_Icc_self ht)) (hray t (Ioo_subset_Icc_self ht)).symm

/-- Upgrade radial equations for a smooth family to the full equation on every nearby slice. -/
private theorem eventually_hasFDerivAt_of_radial_solution_family
    [FiniteDimensional ℝ F] {n : ℕ∞}
    {f g : E × F → E →L[ℝ] F} {K : ℝ≥0} {x₀ : E} {y₀ : F} {α : E × F → F}
    (hg : ContDiff ℝ (n + 1) g) (hgK : LipschitzWith K g)
    (hα0 : α (x₀, y₀) = y₀) (hαsmooth : ContDiffAt ℝ (n + 1) α (x₀, y₀))
    {r : ℝ} (hr : 0 < r)
    (hαrad : ∀ q ∈ Metric.ball ((0 : E), y₀) r, ∀ t ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (fun x ↦ α (x, q.2)) (x₀ + t • q.1) →
        fderiv ℝ (fun x ↦ α (x, q.2)) (x₀ + t • q.1) q.1 =
          g (x₀ + t • q.1, α (x₀ + t • q.1, q.2)) q.1)
    (hgint : ∀ᶠ p in 𝓝 (x₀, y₀), IsFrobeniusIntegrableAt g p ∧ g p = f p) :
    ∀ᶠ p in 𝓝 (x₀, y₀),
      HasFDerivAt (fun x ↦ α (x, p.2)) (f (p.1, α p)) p.1 := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  -- Choose one product ball where the family is `C¹`, integrability holds, and `g = f`.
  obtain ⟨V, hV, hαV⟩ := (hαsmooth.of_le le_add_self).contDiffOn le_rfl (by simp)
  have hgraph : Tendsto (fun p : E × F ↦ (p.1, α p)) (𝓝 (x₀, y₀)) (𝓝 (x₀, y₀)) := by
    simpa [hα0] using (continuousAt_fst.prodMk hαsmooth.continuousAt).tendsto
  have hV' : ∀ᶠ p in 𝓝 (x₀, y₀), p ∈ V := hV
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (hV'.and (hgraph.eventually hgint))
  let ρ := min ρ₁ (r / 4)
  have hρ : 0 < ρ := lt_min hρ₁ (div_pos hr (by norm_num))
  have hU (p : E × F) (hp : p ∈ Metric.ball (x₀, y₀) ρ) :=
    hball p (Metric.ball_subset_ball (min_le_left ρ₁ (r / 4)) hp)
  have hpair (y : F) (hy : dist y y₀ < ρ) (x : E) (hx : x ∈ Metric.ball x₀ ρ) :
      (x, y) ∈ Metric.ball (x₀, y₀) ρ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    exact (max_lt_iff).2 ⟨hx, hy⟩
  have hslice (y : F) (hy : dist y y₀ < ρ) :
      ContDiffOn ℝ 1 (fun x ↦ α (x, y)) (Metric.ball x₀ ρ) :=
    hαV.comp (by fun_prop) fun x hx ↦ (hU (x, y) (hpair y hy x hx)).1
  have hsliceDiff (y : F) (hy : dist y y₀ < ρ) (x : E)
      (hx : x ∈ Metric.ball x₀ ρ) : DifferentiableAt ℝ (fun z ↦ α (z, y)) x :=
    (((hslice y hy).differentiableOn one_ne_zero) x hx).differentiableAt
      (Metric.isOpen_ball.mem_nhds hx)
  filter_upwards [Metric.ball_mem_nhds (x₀, y₀) (half_pos hρ)] with p hp
  rw [Metric.mem_ball, Prod.dist_eq] at hp
  have hpx : dist p.1 x₀ < ρ := (max_lt_iff).1 hp |>.1 |>.trans (half_lt_self hρ)
  have hpy : dist p.2 y₀ < ρ := (max_lt_iff).1 hp |>.2 |>.trans (half_lt_self hρ)
  have hpball : (p.1, p.2) ∈ Metric.ball (x₀, y₀) ρ := hpair p.2 hpy p.1 hpx
  -- Evaluate the parameterized radial equation at half time, with a doubled direction.
  have hrad (x : E) (hx : x ∈ Metric.ball x₀ ρ) :
      fderiv ℝ (fun z ↦ α (z, p.2)) x (x - x₀) =
        g (x, α (x, p.2)) (x - x₀) := by
    have hz : ((2 : ℝ) • (x - x₀), p.2) ∈ Metric.ball ((0 : E), y₀) r := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [dist_zero_right, norm_smul, Real.norm_two]
        rw [Metric.mem_ball, dist_eq_norm] at hx
        nlinarith [min_le_right ρ₁ (r / 4)]
      · nlinarith [hpy, min_le_right ρ₁ (r / 4)]
    have hx' : x₀ + (1 / 2 : ℝ) • ((2 : ℝ) • (x - x₀)) = x := by
      rw [smul_smul]
      norm_num
    have h := hαrad _ hz (1 / 2) ⟨by norm_num, by norm_num⟩ (by
      rw [hx']
      exact hsliceDiff p.2 hpy x hx)
    rw [hx', map_smul, map_smul] at h
    exact smul_right_injective F two_ne_zero h
  -- Frobenius integrability upgrades equality in the radial direction to equality of maps.
  have hfd := fderiv_eq_of_radial (hg.of_le le_add_self) hgK Metric.isOpen_ball
    (hslice p.2 hpy)
    (fun t ht ↦ (convex_ball x₀ ρ).add_smul_sub_mem (Metric.mem_ball_self hρ) hpx ht) hrad
    (fun x hx ↦ (hU (x, p.2) (hpair p.2 hpy x hx)).2.1)
  rw [← (hU (p.1, p.2) hpball).2.2, ← hfd]
  exact (hsliceDiff p.2 hpy p.1 hpx).hasFDerivAt

/-- **A smooth local family of Frobenius solutions.** Under the hypotheses of the local
Frobenius theorem, the solutions through `(x₀, y)` for `y` near `y₀` can be chosen to depend
smoothly on both `x` and `y`. The value at `x₀` is the parameter `y`, and every nearby fixed-
parameter slice solves the total differential equation. -/
theorem exists_contDiffAt_solution_family_of_isFrobeniusIntegrableAt
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ∞}
    {f : E × F → E →L[ℝ] F} {s : Set (E × F)} {x₀ : E} {y₀ : F}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ 𝓝 (x₀, y₀))
    (hint : ∀ᶠ p in 𝓝 (x₀, y₀), IsFrobeniusIntegrableAt f p) :
    ∃ u : E × F → F, u (x₀, y₀) = y₀ ∧ ContDiffAt ℝ (n + 1) u (x₀, y₀) ∧
      (∀ᶠ y in 𝓝 y₀, u (x₀, y) = y) ∧
      ∀ᶠ p in 𝓝 (x₀, y₀),
        HasFDerivAt (fun x ↦ u (x, p.2)) (f (p.1, u p)) p.1 := by
  obtain ⟨g, K, hg, hgK, hgf⟩ :=
    hf.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional hs
  have hgint : ∀ᶠ p in 𝓝 (x₀, y₀), IsFrobeniusIntegrableAt g p ∧ g p = f p := by
    filter_upwards [hint, hgf.eventuallyEq_nhds] with p hp hpe
    exact ⟨hpe.isFrobeniusIntegrableAt_iff.2 hp, hpe.eq_of_nhds⟩
  obtain ⟨α, hα0, hαsmooth, hαinit, r, hr, hαrad⟩ :=
    exists_radial_solution_family hg hgK x₀ y₀
  exact ⟨α, hα0, hαsmooth, hαinit,
    eventually_hasFDerivAt_of_radial_solution_family hg hgK hα0 hαsmooth hr hαrad hgint⟩

/-- **The local Frobenius theorem.** Let `E` and `F` be finite-dimensional real normed spaces and
let `f : E × F → (E →L[ℝ] F)` be `C^(n+1)` near `(x₀, y₀)`, for instance `C¹`. If `f` satisfies the
Frobenius integrability condition near `(x₀, y₀)`, then the total differential equation
`D u x = f (x, u x)` has a local solution `u` with `u x₀ = y₀`, which is `C^(n+1)` at `x₀`. -/
theorem exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {n : ℕ∞} {f : E × F → E →L[ℝ] F} {s : Set (E × F)}
    {x₀ : E} {y₀ : F} (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ 𝓝 (x₀, y₀))
    (hint : ∀ᶠ p in 𝓝 (x₀, y₀), IsFrobeniusIntegrableAt f p) :
    ∃ u : E → F, u x₀ = y₀ ∧ ContDiffAt ℝ (n + 1) u x₀ ∧
      ∀ᶠ x in 𝓝 x₀, HasFDerivAt u (f (x, u x)) x := by
  obtain ⟨u, hu₀, husmooth, -, husol⟩ :=
    exists_contDiffAt_solution_family_of_isFrobeniusIntegrableAt hf hs hint
  refine ⟨fun x ↦ u (x, y₀), hu₀, ?_, ?_⟩
  · exact husmooth.comp x₀ (contDiffAt_id.prodMk contDiffAt_const)
  · simpa using (continuousAt_id.prodMk continuousAt_const).eventually husol

/-- The graph of a smooth solution family has the canonical graph-shear derivative. -/
private theorem hasFDerivAt_graph_of_solution_family {n : ℕ∞}
    {f : E × F → E →L[ℝ] F} {u : E × F → F} {x₀ : E} {y₀ : F}
    (hu₀ : u (x₀, y₀) = y₀) (husmooth : ContDiffAt ℝ (n + 1) u (x₀, y₀))
    (huinit : ∀ᶠ y in 𝓝 y₀, u (x₀, y) = y)
    (husol : ∀ᶠ p in 𝓝 (x₀, y₀),
      HasFDerivAt (fun x ↦ u (x, p.2)) (f (p.1, u p)) p.1) :
    HasFDerivAt (fun p : E × F ↦ (p.1, u p))
      ((ContinuousLinearEquiv.refl ℝ E).skewProd
        (ContinuousLinearEquiv.refl ℝ F) (f (x₀, y₀)) : (E × F) →L[ℝ] (E × F))
      (x₀, y₀) := by
  -- The solution equation determines the derivative in horizontal directions.
  have hx : HasFDerivAt (fun x ↦ u (x, y₀)) (f (x₀, y₀)) x₀ := by
    simpa only [hu₀] using husol.self_of_nhds
  -- The initial-value identity determines the derivative in vertical directions.
  have huinit' : (fun y ↦ u (x₀, y)) =ᶠ[𝓝 y₀] id := huinit
  have hy : HasFDerivAt (fun y ↦ u (x₀, y)) (ContinuousLinearMap.id ℝ F) y₀ :=
    (hasFDerivAt_id y₀).congr_of_eventuallyEq huinit'
  exact (husmooth.differentiableAt (by simp)).hasFDerivAt_fst_prodMk_of_slices hx hy

/-- **Flat coordinates for an integrable graph field.** The smooth family of Frobenius solutions
defines a local coordinate change `(x, y) ↦ (x, u (x, y))`. Its derivative at the base point is
the invertible graph shear, and its horizontal slices have derivative equal to the prescribed
graph field. -/
theorem exists_frobenius_flat_coordinate [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {n : ℕ∞} {f : E × F → E →L[ℝ] F} {s : Set (E × F)} {x₀ : E} {y₀ : F}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ 𝓝 (x₀, y₀))
    (hint : ∀ᶠ p in 𝓝 (x₀, y₀), IsFrobeniusIntegrableAt f p) :
    ∃ (u : E × F → F) (e : OpenPartialHomeomorph (E × F) (E × F)),
      u (x₀, y₀) = y₀ ∧ ContDiffAt ℝ (n + 1) u (x₀, y₀) ∧
      (∀ᶠ y in 𝓝 y₀, u (x₀, y) = y) ∧
      (e : E × F → E × F) = (fun p ↦ (p.1, u p)) ∧ (x₀, y₀) ∈ e.source ∧
      ContDiffAt ℝ (n + 1) e.symm (x₀, y₀) ∧
      ∀ᶠ p in 𝓝 (x₀, y₀), HasFDerivAt (fun x ↦ e (x, p.2))
        ((ContinuousLinearMap.id ℝ E).prod (f (e p))) p.1 := by
  obtain ⟨u, hu₀, husmooth, huinit, husol⟩ :=
    exists_contDiffAt_solution_family_of_isFrobeniusIntegrableAt hf hs hint
  let Φ : E × F → E × F := fun p ↦ (p.1, u p)
  let A : (E × F) ≃L[ℝ] (E × F) :=
    (ContinuousLinearEquiv.refl ℝ E).skewProd (ContinuousLinearEquiv.refl ℝ F) (f (x₀, y₀))
  have hΦsmooth : ContDiffAt ℝ (n + 1) Φ (x₀, y₀) := contDiffAt_fst.prodMk husmooth
  have hΦ : HasFDerivAt Φ (A : (E × F) →L[ℝ] (E × F)) (x₀, y₀) := by
    simpa only [Φ, A] using
      hasFDerivAt_graph_of_solution_family hu₀ husmooth huinit husol
  have hΦ₀ : Φ (x₀, y₀) = (x₀, y₀) := by simp [Φ, hu₀]
  let e : OpenPartialHomeomorph (E × F) (E × F) :=
    hΦsmooth.toOpenPartialHomeomorph Φ hΦ (by simp)
  have hefun : (e : E × F → E × F) = Φ := by
    exact hΦsmooth.toOpenPartialHomeomorph_coe hΦ (by simp)
  have hesource : (x₀, y₀) ∈ e.source :=
    hΦsmooth.mem_toOpenPartialHomeomorph_source hΦ (by simp)
  have hesymm : ContDiffAt ℝ (n + 1) e.symm (x₀, y₀) := by
    rw [← hΦ₀]
    exact hΦsmooth.to_localInverse hΦ (by simp)
  have hefun' : (e : E × F → E × F) = (fun p ↦ (p.1, u p)) := by
    simpa only [Φ] using hefun
  refine ⟨u, e, hu₀, husmooth, huinit, hefun', hesource, hesymm, ?_⟩
  filter_upwards [husol] with p hp
  simpa only [hefun, Φ, id_eq] using (hasFDerivAt_id p.1).prodMk hp

/-- **The Frobenius theorem for total differential equations.** Let `E` and `F` be
finite-dimensional real normed spaces and let `f : E × F → (E →L[ℝ] F)` be `C^(n+1)` near `p₀`,
for instance `C¹`. The total differential equation `D u x = f (x, u x)` has a local solution
through every point near `p₀` if and only if `f` satisfies the Frobenius integrability condition
near `p₀`. -/
theorem eventually_exists_hasFDerivAt_iff_eventually_isFrobeniusIntegrableAt
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ∞}
    {f : E × F → E →L[ℝ] F} {s : Set (E × F)} {p₀ : E × F}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ 𝓝 p₀) :
    (∀ᶠ p in 𝓝 p₀, ∃ u : E → F, u p.1 = p.2 ∧ ∀ᶠ x in 𝓝 p.1, HasFDerivAt u (f (x, u x)) x) ↔
      ∀ᶠ p in 𝓝 p₀, IsFrobeniusIntegrableAt f p := by
  constructor
  · intro h
    filter_upwards [h, eventually_mem_nhds_iff.2 hs] with p ⟨u, hu₀, hu⟩ hsp
    have hfp : DifferentiableAt ℝ f (p.1, u p.1) := by
      rw [hu₀]
      exact (hf.contDiffAt hsp).differentiableAt (by simp)
    simpa [hu₀] using isFrobeniusIntegrableAt_of_eventually_hasFDerivAt hu hfp
  · intro h
    filter_upwards [h.eventually_nhds, eventually_mem_nhds_iff.2 hs] with p hp hsp
    obtain ⟨u, hu₀, -, hu⟩ := exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt hf
      (x₀ := p.1) (y₀ := p.2) hsp hp
    exact ⟨u, hu₀, hu⟩

end FiniteDimensional

end TauCeti
