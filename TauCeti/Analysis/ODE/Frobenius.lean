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
`u (x₀ + z) = b 1`. Rescaling time shows that `b t = u (x₀ + t • z)`, so `u` solves the equation
in the radial direction: `D u x (x - x₀) = f (x, u x) (x - x₀)`. To upgrade the radial equation,
fix `w` and a ray; then `h t = t • (D u (x₀ + t • z) w - f (x₀ + t • z, u (x₀ + t • z)) w)` solves
a linear ordinary differential equation with `h 0 = 0`, by the symmetry of the second derivative
of `u`, the derivative of the radial equation, and the integrability condition. So `h` vanishes.
The argument differentiates `u` twice, which is why `f` is assumed to be `C²`, while the classical
statement only needs `f` to be `C¹`.

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

/-- **The derivative of the radial equation.** If `α` is `C²` on an open set `U` and solves the
total differential equation `D α y = g (y, α y)` in the radial direction `y - x₀` at every point
of `U`, then differentiating that identity at `y ∈ U` in the direction `w` gives the relation
below. -/
private theorem fderiv_fderiv_apply_sub_add {g : E × F → E →L[ℝ] F} (hg : Differentiable ℝ g)
    {α : E → F} {U : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U) {x₀ y : E} (hy : y ∈ U)
    (hrad : ∀ y ∈ U, fderiv ℝ α y (y - x₀) = g (y, α y) (y - x₀)) (w : E) :
    fderiv ℝ (fderiv ℝ α) y w (y - x₀) + fderiv ℝ α y w =
      fderiv ℝ g (y, α y) (w, fderiv ℝ α y w) (y - x₀) + g (y, α y) w := by
  have hD := ((hα.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  have hD2 := (((hα.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).contDiffAt
    (hU.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
  have hgraph : HasFDerivAt (fun y ↦ g (y, α y))
      (fderiv ℝ g (y, α y) ∘L (ContinuousLinearMap.id ℝ E).prod (fderiv ℝ α y)) y :=
    (hg _).hasFDerivAt.comp y ((hasFDerivAt_id y).prodMk hD)
  have hΦ := (hD2.clm_apply ((hasFDerivAt_id y).sub_const x₀)).sub
    (hgraph.clm_apply ((hasFDerivAt_id y).sub_const x₀))
  have hzero : HasFDerivAt (fun y ↦ fderiv ℝ α y (y - x₀) - g (y, α y) (y - x₀))
      (0 : E →L[ℝ] F) y :=
    (hasFDerivAt_const (0 : F) y).congr_of_eventuallyEq
      (eventually_of_mem (hU.mem_nhds hy) fun y' hy' ↦ by simp [hrad y' hy'])
  have := congrArg (fun L : E →L[ℝ] F ↦ L w) (hΦ.unique hzero)
  simp only [sub_apply, add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply, zero_apply, id_eq] at this
  rw [sub_eq_zero] at this
  linear_combination (norm := module) this

/-- **The defect of a radial solution along a ray.** Let `α` be `C²` on an open set `U` and solve
the total differential equation `D α y = g (y, α y)` in the radial direction `y - x₀` on `U`.
Along the ray `s ↦ x₀ + s • z`, the defect `s • (D α - g (·, α ·))`, applied to a fixed vector
`w`, solves a linear ordinary differential equation at every time `t` at which the ray lies in
`U` and the Frobenius integrability condition holds at the corresponding point of the graph. -/
private theorem hasDerivAt_smul_radialDefect {g : E × F → E →L[ℝ] F} (hg : Differentiable ℝ g)
    {α : E → F} {U : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U) {x₀ : E}
    (hrad : ∀ y ∈ U, fderiv ℝ α y (y - x₀) = g (y, α y) (y - x₀)) (z w : E) {t : ℝ}
    (ht : x₀ + t • z ∈ U) (hint : IsFrobeniusIntegrableAt g (x₀ + t • z, α (x₀ + t • z))) :
    HasDerivAt (fun s : ℝ ↦ s • (fderiv ℝ α (x₀ + s • z) w - g (x₀ + s • z, α (x₀ + s • z)) w))
      (fderiv ℝ g (x₀ + t • z, α (x₀ + t • z))
        (0, t • (fderiv ℝ α (x₀ + t • z) w - g (x₀ + t • z, α (x₀ + t • z)) w)) z) t := by
  have hray : HasDerivAt (fun s : ℝ ↦ x₀ + s • z) z t := by
    simpa only [id, one_smul] using ((hasDerivAt_id t).smul_const z).const_add x₀
  have hD (y : E) (hy : y ∈ U) : HasFDerivAt α (fderiv ℝ α y) y :=
    ((hα.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  have hD2 := (((hα.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).contDiffAt
    (hU.mem_nhds ht)).differentiableAt one_ne_zero).hasFDerivAt
  have r1 := fderiv_fderiv_apply_sub_add hg hU hα ht hrad w
  have s1 := second_derivative_symmetric_of_eventually
    (eventually_of_mem (hU.mem_nhds ht) hD) hD2 z w
  have h1 : HasDerivAt (fun s ↦ fderiv ℝ α (x₀ + s • z) w)
      (fderiv ℝ (fderiv ℝ α) (x₀ + t • z) z w) t :=
    ((hD2.comp_hasDerivAt (f := fun s : ℝ ↦ x₀ + s • z) t hray).clm_apply
      (hasDerivAt_const t w)).congr_deriv (by simp)
  have h2 : HasDerivAt (fun s ↦ g (x₀ + s • z, α (x₀ + s • z)) w)
      (fderiv ℝ g (x₀ + t • z, α (x₀ + t • z)) (z, fderiv ℝ α (x₀ + t • z) z) w) t :=
    (((hg (x₀ + t • z, α (x₀ + t • z))).hasFDerivAt.comp_hasDerivAt
      (f := fun s : ℝ ↦ (x₀ + s • z, α (x₀ + s • z))) t
      (HasDerivAt.prodMk hray ((hD _ ht).comp_hasDerivAt (f := fun s : ℝ ↦ x₀ + s • z) t
        hray))).clm_apply
      (hasDerivAt_const t w)).congr_deriv (by simp)
  refine ((hasDerivAt_id t).smul (h1.sub h2)).congr_deriv ?_
  -- Combine the derivative of the radial equation, the radial equation itself, the symmetry of
  -- the second derivative of `α`, and the integrability condition, all at `x₀ + t • z`.
  have r2 := hrad _ ht
  have i1 := hint z w
  rw [add_sub_cancel_left] at r1 r2
  simp only [id_eq, one_smul, Pi.sub_apply]
  generalize fderiv ℝ g (x₀ + t • z, α (x₀ + t • z)) = A at *
  generalize g (x₀ + t • z, α (x₀ + t • z)) = G at *
  generalize fderiv ℝ (fderiv ℝ α) (x₀ + t • z) = D2 at *
  generalize fderiv ℝ α (x₀ + t • z) = Dy at *
  have a1 : A (w, Dy w) z = A (w, G w) z + A (0, Dy w - G w) z := by
    rw [← add_apply, ← map_add, Prod.mk_add_mk, add_zero, add_sub_cancel]
  have a2 : t • A (z, Dy z) w = t • A (z, G z) w := by
    rw [← smul_apply, ← map_smul, ← smul_apply, ← map_smul, Prod.smul_mk, Prod.smul_mk,
      ← map_smul, ← map_smul, r2]
  have a3 : A (0, t • (Dy w - G w)) z = t • A (0, Dy w - G w) z := by
    rw [← smul_apply, ← map_smul, Prod.smul_mk, smul_zero]
  simp only [map_smul] at r1
  linear_combination (norm := module) t • a1 + t • s1 - a2 - t • i1 + r1 - a3

/-- **From the radial equation to the total differential equation.** Let `α` be `C²` on an open
set `U` and solve the total differential equation `D α y = g (y, α y)` in the radial direction
`y - x₀` at every point of `U`, where `g` is differentiable and globally Lipschitz. If the
Frobenius integrability condition holds along the graph of `α` over `U`, then `α` solves the full
equation at every point `x` whose segment from `x₀` lies in `U`. -/
private theorem fderiv_eq_of_radial {g : E × F → E →L[ℝ] F} {K : ℝ≥0} (hg : Differentiable ℝ g)
    (hgK : LipschitzWith K g) {α : E → F} {U : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U)
    {x₀ x : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • (x - x₀) ∈ U)
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
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun s : ℝ ↦ s • (fderiv ℝ α
      (x₀ + s • (x - x₀)) w - g (x₀ + s • (x - x₀), α (x₀ + s • (x - x₀))) w)) (L t (t •
      (fderiv ℝ α (x₀ + t • (x - x₀)) w - g (x₀ + t • (x - x₀), α (x₀ + t • (x - x₀))) w))) t :=
    (hasDerivAt_smul_radialDefect hg hU hα hrad (x - x₀) w (hseg t ht)
      (hint _ (hseg t ht))).congr_deriv (by
        simp only [hL, ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp,
          Function.comp_apply, ContinuousLinearMap.inr_apply])
  have heq := ODE_solution_unique (v := fun t k ↦ L t k) (g := fun _ ↦ (0 : F)) hLip
    (fun t ht ↦ (hh t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hh t (Ico_subset_Icc_self ht)).hasDerivWithinAt) continuousOn_const
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
  have hLip (q₀ : ℝ) : LipschitzWith (K * ‖t • z‖₊) (fun q : E × F ↦ (t • z, g q (t • z))) := by
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

/-- **Solutions along rays.** For a globally `C^(n+1)` field `g` on complete spaces, the
autonomous system `(ξ, b)' = (z, g (ξ, b) z)` with initial value `(x₀, y₀)`, whose field vanishes
at the parameter `z = 0`, has for every parameter `z` in a ball a solution `c z` on `[0, 1]`, and
the value at time `1` depends in a `C^(n+1)` way on `z` near `0`. -/
private theorem exists_rayFamily [CompleteSpace E] [CompleteSpace F] {n : ℕ∞}
    {g : E × F → E →L[ℝ] F} (hg : ContDiff ℝ (n + 1) g) (x₀ : E) (y₀ : F) :
    ∃ (c : E → ℝ → E × F) (r : ℝ), 0 < r ∧ ContDiffAt ℝ (n + 1) (fun z ↦ c z 1) 0 ∧
      c 0 1 = (x₀, y₀) ∧ (∀ z, Continuous (c z)) ∧ ∀ z ∈ Metric.ball (0 : E) r,
        c z 0 = (x₀, y₀) ∧
          (∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (c z) (z, g (c z t) z) (Ici t) t) ∧
          ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (c z) (z, g (c z t) z) t := by
  have hΦ : ContDiff ℝ (n + 1) fun q : E × (E × F) ↦ (q.1, g q.2 q.1) :=
    contDiff_fst.prodMk ((hg.comp contDiff_snd).clm_apply contDiff_fst)
  obtain ⟨γ, hγ, hγ0, hprop⟩ := ODE.exists_contDiffAt_picard_solution_of_contDiff
    (fun q : E × (E × F) ↦ (q.1, g q.2 q.1)) 0 (x₀, y₀) hΦ (.of_forall fun q ↦ by simp)
  obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff_ball.1 hprop
  refine ⟨fun z s ↦ γ z (projIcc 0 1 zero_le_one s), r, hr, ?_, by simp [hγ0],
    fun z ↦ (γ z).continuous.comp continuous_projIcc, fun z hz ↦
      ⟨by simpa using (hP z hz).1 ⟨0, left_mem_Icc.2 zero_le_one⟩, (hP z hz).2.2, (hP z hz).2.1⟩⟩
  refine (((ContinuousMap.evalCLM (R := ℝ) (⟨1, right_mem_Icc.2 zero_le_one⟩ :
    Icc (0 : ℝ) 1)).contDiff).comp_contDiffAt 0 hγ).congr_of_eventuallyEq (.of_forall fun z ↦ ?_)
  simp only [projIcc_right]
  rfl

/-- **A solution of the radial equation.** For a globally `C^(n+1)` and globally Lipschitz `g` on
finite-dimensional spaces, there is a function `α` with `α x₀ = y₀`, `C^(n+1)` at `x₀`, which
solves the total differential equation `D α y = g (y, α y)` in the direction of each short ray
from `x₀`: `α (x₀ + z)` is the value at time `1` of the solution of `b' = g (x₀ + t • z, b) z`
with `b 0 = y₀`. -/
private theorem exists_radial_solution [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ∞}
    {g : E × F → E →L[ℝ] F} {K : ℝ≥0} (hg : ContDiff ℝ (n + 1) g) (hgK : LipschitzWith K g)
    (x₀ : E) (y₀ : F) :
    ∃ α : E → F, α x₀ = y₀ ∧ ContDiffAt ℝ (n + 1) α x₀ ∧ ∃ r > 0, ∀ z ∈ Metric.ball (0 : E) r,
      ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ α (x₀ + t • z) →
        fderiv ℝ α (x₀ + t • z) z = g (x₀ + t • z, α (x₀ + t • z)) z := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨c, r, hr, hc1, hc01, hcont, hc⟩ := exists_rayFamily hg x₀ y₀
  -- The first component of each solution moves along its ray.
  have hfst (z : E) (hz : z ∈ Metric.ball 0 r) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (c z t).1 = x₀ + t • z := by
    refine eq_of_has_deriv_right_eq (f := fun s ↦ (c z s).1) (g := fun s ↦ x₀ + s • z)
      (f' := fun _ ↦ z) (fun s hs ↦ ?_) (fun s _ ↦ ?_)
      (hcont z).fst.continuousOn (by fun_prop) (by simp [(hc z hz).1]) t ht
    · exact hasFDerivAt_fst.comp_hasDerivWithinAt s ((hc z hz).2.1 s hs)
    · simpa using (((hasDerivAt_id s).smul_const z).const_add x₀).hasDerivWithinAt
  -- The solution `α`, read off at time `1` along the ray through `x`, and its values on rays.
  refine ⟨fun x ↦ (c (x - x₀) 1).2, by simp [hc01], ?_, r, hr, fun z hz t ht hd ↦ ?_⟩
  · have hc1' : ContDiffAt ℝ (n + 1) (fun z ↦ c z 1) (x₀ - x₀) := by rw [sub_self]; exact hc1
    exact contDiff_snd.comp_contDiffAt x₀
      (hc1'.comp (f := fun x ↦ x - x₀) x₀ (contDiffAt_id.sub contDiffAt_const))
  have hray (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : (c (x₀ + s • z - x₀) 1).2 = (c z s).2 := by
    rw [add_sub_cancel_left, rayFamily_smul_apply_one hgK hcont (fun z hz ↦ (hc z hz).1)
      (fun z hz ↦ (hc z hz).2.1) hz hs]
  -- Along the ray, `α` has the velocity prescribed by the system.
  have h1 : HasDerivAt (fun s ↦ (c (x₀ + s • z - x₀) 1).2) (g (c z t) z) t :=
    ((hasFDerivAt_snd.comp_hasDerivAt t ((hc z hz).2.2 t ht)).congr_of_eventuallyEq
      (eventually_of_mem (Icc_mem_nhds ht.1 ht.2) hray)).congr_deriv (by simp)
  have h2 := hd.hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const z).const_add x₀)
  simp only [id_eq, one_smul] at h2
  rw [h2.unique h1]
  congr 2
  exact Prod.ext (hfst z hz t (Ioo_subset_Icc_self ht)) (hray t (Ioo_subset_Icc_self ht)).symm

/-- **The local Frobenius theorem.** Let `E` and `F` be finite-dimensional real normed spaces and
let `f : E × F → (E →L[ℝ] F)` be `C^(n+1)`, with `1 ≤ n`, near `(x₀, y₀)`. If `f` satisfies the
Frobenius integrability condition near `(x₀, y₀)`, then the total differential equation
`D u x = f (x, u x)` has a local solution `u` with `u x₀ = y₀`, which is `C^(n+1)` at `x₀`. -/
theorem exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {n : ℕ∞} (hn : 1 ≤ n) {f : E × F → E →L[ℝ] F} {s : Set (E × F)}
    {x₀ : E} {y₀ : F} (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ 𝓝 (x₀, y₀))
    (hint : ∀ᶠ p in 𝓝 (x₀, y₀), IsFrobeniusIntegrableAt f p) :
    ∃ u : E → F, u x₀ = y₀ ∧ ContDiffAt ℝ (n + 1) u x₀ ∧
      ∀ᶠ x in 𝓝 x₀, HasFDerivAt u (f (x, u x)) x := by
  -- Replace `f` by a globally smooth and globally Lipschitz field agreeing with it near `(x₀, y₀)`.
  obtain ⟨g, K, hg, hgK, hgf⟩ :=
    hf.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional hs
  have hgint : ∀ᶠ p in 𝓝 (x₀, y₀), IsFrobeniusIntegrableAt g p ∧ g p = f p := by
    filter_upwards [hint, hgf.eventuallyEq_nhds] with p hp hpe
    exact ⟨hpe.isFrobeniusIntegrableAt_iff.2 hp, hpe.eq_of_nhds⟩
  obtain ⟨α, hα0, hαsmooth, r, hr, hαrad⟩ := exists_radial_solution hg hgK x₀ y₀
  -- Shrink to a ball on which `α` is `C²`, its graph stays where `g` is integrable and agrees
  -- with `f`, and the rays of twice the radius stay in the parameter ball.
  have h2 : (2 : WithTop ℕ∞) ≤ n + 1 := by
    calc (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
      _ ≤ n + 1 := by gcongr; exact_mod_cast hn
  obtain ⟨V, hV, hαV⟩ := (hαsmooth.of_le h2).contDiffOn le_rfl (by simp)
  have hgraph : Tendsto (fun x ↦ (x, α x)) (𝓝 x₀) (𝓝 (x₀, y₀)) := by
    simpa [hα0] using (continuousAt_id.prodMk hαsmooth.continuousAt).tendsto
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((show ∀ᶠ x in 𝓝 x₀, x ∈ V from hV).and (hgraph.eventually hgint))
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = min ρ₁ (r / 2) := ⟨_, rfl⟩
  have hρ : 0 < ρ := hρdef ▸ lt_min hρ₁ (half_pos hr)
  have hU (x : E) (hx : x ∈ Metric.ball x₀ ρ) :=
    hball x (Metric.ball_subset_ball (hρdef ▸ min_le_left _ _) hx)
  have hαU : ContDiffOn ℝ 2 α (Metric.ball x₀ ρ) := hαV.mono fun x hx ↦ (hU x hx).1
  have hαd (x : E) (hx : x ∈ Metric.ball x₀ ρ) : DifferentiableAt ℝ α x :=
    ((hαU.differentiableOn (by norm_num)) x hx).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  -- On that ball, `α` solves the radial equation: write `y = x₀ + (1 / 2) • (2 • (y - x₀))`.
  have hrad (y : E) (hy : y ∈ Metric.ball x₀ ρ) :
      fderiv ℝ α y (y - x₀) = g (y, α y) (y - x₀) := by
    have hz : (2 : ℝ) • (y - x₀) ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_two]
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith [hρdef ▸ min_le_right ρ₁ (r / 2)]
    have hy' : x₀ + (1 / 2 : ℝ) • ((2 : ℝ) • (y - x₀)) = y := by
      rw [smul_smul]
      norm_num
    have := hαrad _ hz (1 / 2) ⟨by norm_num, by norm_num⟩ (by rw [hy']; exact hαd y hy)
    rw [hy', map_smul, map_smul] at this
    exact smul_right_injective F two_ne_zero this
  refine ⟨α, hα0, hαsmooth, eventually_of_mem (Metric.ball_mem_nhds x₀ hρ) fun x hx ↦ ?_⟩
  have hfd := fderiv_eq_of_radial (hg.differentiable (by simp)) hgK Metric.isOpen_ball hαU
    (fun t ht ↦ (convex_ball x₀ ρ).add_smul_sub_mem (Metric.mem_ball_self hρ) hx ht) hrad
    (fun y hy ↦ (hU y hy).2.1)
  rw [← (hU x hx).2.2, ← hfd]
  exact (hαd x hx).hasFDerivAt

/-- **The Frobenius theorem for total differential equations.** Let `E` and `F` be
finite-dimensional real normed spaces and let `f : E × F → (E →L[ℝ] F)` be `C^(n+1)`, with
`1 ≤ n`, near `p₀`. The total differential equation `D u x = f (x, u x)` has a local solution
through every point near `p₀` if and only if `f` satisfies the Frobenius integrability condition
near `p₀`. -/
theorem eventually_exists_hasFDerivAt_iff_eventually_isFrobeniusIntegrableAt
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ∞} (hn : 1 ≤ n)
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
    obtain ⟨u, hu₀, -, hu⟩ := exists_eventually_hasFDerivAt_of_isFrobeniusIntegrableAt hn hf
      (x₀ := p.1) (y₀ := p.2) hsp hp
    exact ⟨u, hu₀, hu⟩

end FiniteDimensional

end TauCeti
