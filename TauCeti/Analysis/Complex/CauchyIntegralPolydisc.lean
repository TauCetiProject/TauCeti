/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.MeasureTheory.Integral.Torus.ContinuousMap
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units
import TauCeti.Analysis.Calculus.FDeriv.Pi
import TauCeti.Topology.Compactness.Normed

/-!
# The Cauchy integral formula on polydiscs and analyticity in several variables

This file proves the iterated Cauchy integral formula on a polydisc for continuous functions which
are complex differentiable in each variable separately, and deduces Osgood's lemma: such a function
of finitely many complex variables is analytic. In particular a function on a finite-dimensional
complex normed space which is complex differentiable on an open set is analytic there. Mathlib
proves the one-variable cases (`DifferentiableOn.circleIntegral_sub_inv_smul`,
`DifferentiableOn.analyticOnNhd`); the several-variable statements are the basic tools for
proving joint analyticity of functions defined by parameter-dependent integrals. The file ends with
the first such statement: an integral over a compact family, in particular a contour integral,
whose integrand is jointly analytic in a parameter and the integration variable is analytic in the
parameter.

A polydisc in `ℂⁿ` is the product `Set.univ.pi fun i => ball (c i) (R i)` of open discs, and its
distinguished boundary is the torus `T(c, R)` of Mathlib's `torusIntegral`.

## Main results

* `ContinuousOn.torusIntegral_prod_sub_inv_smul`: **the Cauchy integral formula on a
  polydisc.** If `f : ℂⁿ → E` is continuous on the closed polydisc with center `c` and polyradius
  `R` and complex differentiable in each variable separately, then for `w` in the open polydisc,
  `∯ z in T(c, R), (∏ i, (z i - w i))⁻¹ • f z = (2πi)ⁿ • f w`.
  `DifferentiableOn.torusIntegral_prod_sub_inv_smul` is the case of a jointly differentiable `f`.
* `ContinuousOn.analyticAt_of_differentiableAt_update`,
  `ContinuousOn.analyticOnNhd_of_differentiableAt_update`: **Osgood's lemma.** A function on
  `ι → ℂ`, for a finite type `ι`, which is continuous on an open set and complex differentiable in
  each variable separately there is analytic on it.
* `TauCeti.analyticOnNhd_iff_continuousOn_and_differentiableAt_update`: on an open subset of
  `ι → ℂ`, analyticity is equivalent to continuity together with separate complex
  differentiability.
* `DifferentiableOn.analyticAt_of_finiteDimensional`,
  `DifferentiableOn.analyticOnNhd_of_finiteDimensional`: a function on a finite-dimensional complex
  normed space which is complex differentiable on a neighbourhood of a point is analytic there.
* `DifferentiableOn.contDiffOn_of_finiteDimensional`: such a function is `C^n` on an open set on
  which it is complex differentiable, for every `n`.
* `TauCeti.analyticOnNhd_iff_differentiableOn_of_finiteDimensional`: on an open subset of a
  finite-dimensional complex normed space, analyticity and complex differentiability agree.
* `TauCeti.hasFDerivAt_integral_smul_of_analyticAt`: an integral `q ↦ ∫ a, g a • f (q, φ a) ∂μ`,
  with `g` integrable and `φ` continuous with values in a compact set `K`, whose integrand is
  jointly analytic along `{p} × K` may be differentiated under the integral sign at `p`.
* `TauCeti.analyticAt_integral_smul`: for a parameter in a finite-dimensional complex normed
  space, such an integral is analytic in the parameter. Only analyticity near `{p} × K` is needed,
  so the integrand may be singular elsewhere.
* `TauCeti.hasFDerivAt_circleIntegral`: a contour integral `p ↦ ∮ ζ in C(c, R), f (p, ζ)` whose
  integrand is jointly analytic along `{p} × sphere c |R|` may be differentiated under the
  integral sign at `p`.
* `TauCeti.analyticAt_circleIntegral`, `TauCeti.analyticOnNhd_circleIntegral`: **analytic
  dependence on parameters.** For a parameter in a finite-dimensional complex normed space, such a
  contour integral is analytic in the parameter.

## The argument

The Cauchy formula follows by induction on `n` from the one-variable formula, splitting off the
first coordinate of the torus integral with `torusIntegral_succ`. The induction only uses
continuity, for Fubini's theorem, and the one-variable formula for the slices of `f`, so separate
differentiability suffices.

For analyticity at `z`, choose a closed polydisc `closedBall z R` inside the domain and let `X` be
the torus `∏ sphere (z i) R`. On the Banach algebra `C(X, ℂ)`, the Cauchy kernel
`w ↦ (ζ ↦ ∏ i, (ζ i - w i))` is a polynomial in `w`, and it is a unit at `w = z`, so its inverse
is analytic in `w` near `z` (`analyticAt_inverse`). Integrating against `f` over the torus is a
continuous linear functional on `C(X, ℂ)`, so by the Cauchy formula `f` is a continuous linear
image of an analytic function near `z`. This is the several-variable form of the argument in
`TauCeti.Analysis.Polynomial.RootSum`. Since the Cauchy formula only needs continuity and separate
differentiability, this proves Osgood's lemma; a function on a finite-dimensional space is
transported to `Fin n → ℂ` along a basis.

For an integral depending on a parameter, the partial derivative of the integrand in the
parameter is continuous, hence bounded uniformly near the compact set `K`, so Mathlib's theorem on
differentiation under the integral sign applies. Analyticity in a parameter from a
finite-dimensional space then follows from complex differentiability on a neighbourhood. Contour
integrals are the case of Lebesgue measure on `Ioc 0 (2π)`, the weight `deriv (circleMap c R)` and
`φ = circleMap c R`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter Function MeasureTheory Metric Real Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

namespace TauCeti

section CauchyFormula

/-- For nonnegative radii, a point of the torus `T(c, R)` lies on the product of the circles
`sphere (c i) (R i)`. -/
theorem torusMap_mem_pi_sphere {c : Fin n → ℂ} {R : Fin n → ℝ} (hR : ∀ i, 0 ≤ R i)
    (θ : Fin n → ℝ) : torusMap c R θ ∈ univ.pi fun i => sphere (c i) (R i) :=
  fun i _ => circleMap_mem_sphere (c i) (hR i) (θ i)

/-- Each coordinate of the torus parametrization has distance equal to its nonnegative
radius from the corresponding center. -/
theorem norm_torusMap_apply_sub_center {c : Fin n → ℂ} {R : Fin n → ℝ}
    (θ : Fin n → ℝ) (i : Fin n) (hR : 0 ≤ R i) :
    ‖torusMap c R θ i - c i‖ = R i := by
  simp [torusMap, abs_of_nonneg hR]

/-- The parametrization `torusMap c R` of the torus `T(c, R)` is continuous. -/
@[fun_prop]
theorem continuous_torusMap (c : Fin n → ℂ) (R : Fin n → ℝ) :
    Continuous (torusMap c R) :=
  continuous_pi fun i => (continuous_circleMap (c i) (R i)).comp (continuous_apply i)

/-- The Cauchy integrand on a polydisc is integrable over the distinguished boundary. -/
private theorem torusIntegrable_prod_sub_inv_smul {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ}
    {R : Fin n → ℝ} (hf : ContinuousOn f (univ.pi fun i => closedBall (c i) (R i)))
    (hw : w ∈ univ.pi fun i => ball (c i) (R i)) :
    TorusIntegrable (fun z => (∏ i, (z i - w i))⁻¹ • f z) c R := by
  have hR : ∀ i, 0 ≤ R i := fun i => (pos_of_mem_ball (hw i trivial)).le
  have hmem := torusMap_mem_pi_sphere (c := c) hR
  refine Continuous.integrableOn_Icc (Continuous.smul ?_ ?_)
  · refine (continuous_finsetProd _ fun i _ => ?_).inv₀ fun θ => ?_
    · exact ((continuous_apply i).comp (continuous_torusMap c R)).sub continuous_const
    · refine Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 fun h => ?_
      have h1 : dist (torusMap c R θ i) (c i) = R i := hmem θ i trivial
      have h2 : dist (w i) (c i) < R i := hw i trivial
      rw [h] at h1
      exact h2.ne h1
  · exact hf.comp_continuous (continuous_torusMap c R) fun θ i _ =>
      sphere_subset_closedBall (hmem θ i trivial)

/-- **The Cauchy integral formula on a polydisc, for separately holomorphic functions.** Let `f` be
continuous on the closed polydisc with center `c` and polyradius `R`, and complex differentiable
in each variable separately: at every point `z` of the closed polydisc whose `i`-th coordinate lies
in the open disc `ball (c i) (R i)`, the slice `x ↦ f (update z i x)` is complex differentiable at
`z i`. Then for every `w` in the open polydisc, the integral of `(∏ i, (z i - w i))⁻¹ • f z` over
the distinguished boundary `T(c, R)` is `(2πi)ⁿ • f w`. -/
theorem _root_.ContinuousOn.torusIntegral_prod_sub_inv_smul [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hc : ContinuousOn f (univ.pi fun i => closedBall (c i) (R i)))
    (hd : ∀ z ∈ univ.pi (fun i => closedBall (c i) (R i)), ∀ i, z i ∈ ball (c i) (R i) →
      DifferentiableAt ℂ (fun x => f (update z i x)) (z i))
    (hw : w ∈ univ.pi fun i => ball (c i) (R i)) :
    (∯ z in T(c, R), (∏ i, (z i - w i))⁻¹ • f z) = (2 * π * I) ^ n • f w := by
  induction n with
  | zero => simp [torusIntegral_dim0, Subsingleton.elim c w]
  | succ n ih =>
    have hR0 : 0 < R 0 := pos_of_mem_ball (hw 0 trivial)
    have hwt : Fin.tail w ∈ univ.pi fun i => ball (Fin.tail c i) (Fin.tail R i) :=
      fun i _ => hw i.succ trivial
    have hcons : ∀ x ∈ closedBall (c 0) (R 0),
        ∀ y ∈ univ.pi fun i => closedBall (Fin.tail c i) (Fin.tail R i),
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ univ.pi fun i => closedBall (c i) (R i) :=
      fun x hx y hy => by
        simp only [mem_univ_pi, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
        exact ⟨hx, fun i => hy i trivial⟩
    -- Integrate first over the last `n` coordinates, using the formula in dimension `n` for the
    -- slices of `f` with fixed first coordinate.
    have hinner : ∀ x ∈ sphere (c 0) (R 0),
        (∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - w i))⁻¹ • f (Fin.cons x y)) =
          (2 * π * I) ^ n • ((x - w 0)⁻¹ • f (Fin.cons x (Fin.tail w))) := by
      intro x hx
      have hcx : ContinuousOn (fun y => f (Fin.cons x y))
          (univ.pi fun i => closedBall (Fin.tail c i) (Fin.tail R i)) :=
        hc.comp (by fun_prop) fun y hy => hcons x (sphere_subset_closedBall hx) y hy
      have hdx : ∀ y ∈ univ.pi (fun i => closedBall (Fin.tail c i) (Fin.tail R i)), ∀ i,
          y i ∈ ball (Fin.tail c i) (Fin.tail R i) →
          DifferentiableAt ℂ (fun x' => f (Fin.cons x (update y i x'))) (y i) :=
          fun y hy i hyi => by
        simpa only [Fin.cons_update, Fin.cons_succ] using
          hd _ (hcons x (sphere_subset_closedBall hx) y hy) i.succ hyi
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_inv, mul_smul]
      rw [torusIntegral_smul, smul_comm ((2 * π * I) ^ n)]
      congr 1
      exact ih hcx hdx hwt
    rw [torusIntegral_succ (torusIntegrable_prod_sub_inv_smul hc hw),
      circleIntegral.integral_congr hR0.le hinner, circleIntegral.integral_smul]
    -- The remaining integral is the one-variable Cauchy formula for the first slice through `w`.
    have hmem : ∀ x ∈ closedBall (c 0) (R 0),
        (Fin.cons x (Fin.tail w) : Fin (n + 1) → ℂ) ∈ univ.pi fun i => closedBall (c i) (R i) :=
      fun x hx => hcons x hx _ fun i _ => ball_subset_closedBall (hwt i trivial)
    have hcw : ContinuousOn (fun x => f (Fin.cons x (Fin.tail w))) (closedBall (c 0) (R 0)) :=
      hc.comp (by fun_prop) hmem
    have hdw : ∀ x ∈ ball (c 0) (R 0) \ ∅,
        DifferentiableAt ℂ (fun x => f (Fin.cons x (Fin.tail w))) x := fun x hx => by
      simpa only [Fin.update_cons_zero, Fin.cons_zero] using
        hd _ (hmem x (ball_subset_closedBall hx.1)) 0 hx.1
    rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      (hw 0 trivial) hcw hdw, Fin.cons_self_tail, smul_smul, pow_succ]

/-- **The Cauchy integral formula on a polydisc.** If `f` is complex differentiable on the closed
polydisc with center `c` and polyradius `R`, then for every `w` in the open polydisc, the integral
of `(∏ i, (z i - w i))⁻¹ • f z` over the distinguished boundary `T(c, R)` is `(2πi)ⁿ • f w`. -/
theorem _root_.DifferentiableOn.torusIntegral_prod_sub_inv_smul [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hd : DifferentiableOn ℂ f (univ.pi fun i => closedBall (c i) (R i)))
    (hw : w ∈ univ.pi fun i => ball (c i) (R i)) :
    (∯ z in T(c, R), (∏ i, (z i - w i))⁻¹ • f z) = (2 * π * I) ^ n • f w := by
  refine hd.continuousOn.torusIntegral_prod_sub_inv_smul (fun z hz i hzi => ?_) hw
  exact ((hd z hz).comp_update i (t := closedBall (c i) (R i)) fun x hx =>
    (Set.update_mem_pi_iff_of_mem hz).2 fun _ => hx).differentiableAt
    (closedBall_mem_nhds_of_mem hzi)

end CauchyFormula

section Analytic

variable {z : Fin n → ℂ} {R : ℝ}

/-- A function of `n` complex variables which is continuous on a closed polydisc and separately
complex differentiable in each variable is analytic at the center of the polydisc. -/
private theorem analyticAt_of_continuousOn_closedBall_pi [CompleteSpace E] {f : (Fin n → ℂ) → E}
    (hR : 0 < R) (hc : ContinuousOn f (closedBall z R))
    (hd : ∀ y ∈ closedBall z R, ∀ i, y i ∈ ball (z i) R →
      DifferentiableAt ℂ (fun x => f (update y i x)) (y i)) :
    AnalyticAt ℂ f z := by
  rw [closedBall_pi z hR.le] at hc hd
  -- On the torus `X = ∏ sphere (z i) R`, the Cauchy kernel is a unit of `C(X, ℂ)` at `w = z`.
  let F : C((i : Fin n) → sphere (z i) |R|, E) :=
    ⟨fun x => f fun i => x i, hc.comp_continuous (by fun_prop) fun x i _ =>
      sphere_subset_closedBall (by simpa only [abs_of_pos hR] using (x i).2)⟩
  let K : (Fin n → ℂ) → C((i : Fin n) → sphere (z i) |R|, ℂ) := fun w =>
    ∏ i, (⟨fun x => (x i : ℂ), by fun_prop⟩ - algebraMap ℂ _ (w i))
  have hKapply : ∀ w x, K w x = ∏ i, ((x i : ℂ) - w i) := fun w x => by
    simp [K, ContinuousMap.prod_apply]
  have hK : AnalyticAt ℂ K z := by
    refine Finset.analyticAt_fun_prod _ fun i _ => analyticAt_const.sub ?_
    exact ((algebraMapCLM ℂ C((i : Fin n) → sphere (z i) |R|, ℂ)).comp
      (ContinuousLinearMap.proj i)).analyticAt z
  have hunit : IsUnit (K z) := (ContinuousMap.isUnit_iff_forall_ne_zero _).2 fun x => by
    rw [hKapply]
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      sub_ne_zero.2 (ne_of_mem_sphere (x i).2 (abs_pos.mpr hR.ne').ne')
  have hinv : AnalyticAt ℂ (fun w => Ring.inverse (K w)) z := by
    have h := analyticAt_inverse (𝕜 := ℂ) hunit.unit
    rw [hunit.unit_spec] at h
    exact h.comp hK
  -- Multiply the scalar kernel by the fixed boundary values before integrating.
  let M : C((i : Fin n) → sphere (z i) |R|, ℂ) →L[ℂ]
      C((i : Fin n) → sphere (z i) |R|, E) :=
    { toFun := fun g => g • F
      map_add' := fun g h => by ext x; simp [add_smul]
      map_smul' := fun a g => by ext x; simp [mul_smul]
      cont := ContinuousMap.continuous_of_continuous_uncurry _
        (continuous_eval.smul (F.continuous.comp continuous_snd)) }
  let J := (torusIntegralCLM (E := E) z (fun _ => R)).comp M
  refine (((J.analyticAt _).comp hinv).const_smul
    (c := ((2 * π * I) ^ n)⁻¹)).congr ?_
  -- Near `z`, the kernel is still a unit, and the Cauchy formula recovers `f`.
  filter_upwards [hK.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit),
    ball_mem_nhds z hR] with w hw hwb
  rw [ball_pi z hR] at hwb
  have hinvw : ∀ x, Ring.inverse (K w) x = (∏ i, ((x i : ℂ) - w i))⁻¹ := fun x => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hKapply, ← ContinuousMap.mul_apply, Ring.inverse_mul_cancel _ hw,
      ContinuousMap.one_apply]
  have hJ : J (Ring.inverse (K w)) =
      ∯ ζ in T(z, fun _ => R), (∏ i, (ζ i - w i))⁻¹ • f ζ := by
    apply torusIntegralCLM_eq_torusIntegral
    intro x
    simp only [M, LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousMap.smul_apply', hinvw, F, ContinuousMap.coe_mk]
  rw [Pi.smul_apply, Function.comp_apply, hJ,
    hc.torusIntegral_prod_sub_inv_smul hd hwb, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ two_pi_I_ne_zero), one_smul]

end Analytic

section Osgood

variable [CompleteSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℂ) → E}
  {s : Set (ι → ℂ)} {z : ι → ℂ}

/-- **Osgood's lemma.** A function of finitely many complex variables which is continuous on a
neighbourhood of a point and complex differentiable in each variable separately on that
neighbourhood is analytic at the point. -/
theorem _root_.ContinuousOn.analyticAt_of_differentiableAt_update (hc : ContinuousOn f s)
    (hs : s ∈ 𝓝 z) (hd : ∀ y ∈ s, ∀ i, DifferentiableAt ℂ (fun x => f (update y i x)) (y i)) :
    AnalyticAt ℂ f z := by
  -- Transport to `Fin n → ℂ` along an enumeration `e` of `ι`.
  let e := Fintype.equivFin ι
  let M := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin (Fintype.card ι) => ℂ) e
  have hM : ∀ y, M.symm y = y ∘ e := fun y => funext (Equiv.piCongrLeft_symm_apply _ e y)
  obtain ⟨R, hR, hRs⟩ := nhds_basis_closedBall.mem_iff.1
    (M.symm.continuous.continuousAt.preimage_mem_nhds (by rwa [M.symm_apply_apply]))
  have h : AnalyticAt ℂ (f ∘ M.symm) (M z) := by
    refine analyticAt_of_continuousOn_closedBall_pi hR
      (hc.comp M.symm.continuous.continuousOn fun y hy => hRs hy) fun y hy j _ => ?_
    simpa only [Function.comp_apply, hM, update_comp_equiv, Equiv.apply_symm_apply] using
      hd (M.symm y) (hRs hy) (e.symm j)
  have hf : (f ∘ M.symm) ∘ M = f := funext fun x => congrArg f (M.symm_apply_apply x)
  exact hf ▸ h.comp (M.analyticAt z)

/-- **Osgood's lemma.** A function of finitely many complex variables which is continuous on an
open set and complex differentiable in each variable separately on it is analytic on it. -/
theorem _root_.ContinuousOn.analyticOnNhd_of_differentiableAt_update (hc : ContinuousOn f s)
    (hs : IsOpen s) (hd : ∀ y ∈ s, ∀ i, DifferentiableAt ℂ (fun x => f (update y i x)) (y i)) :
    AnalyticOnNhd ℂ f s :=
  fun _z hz => hc.analyticAt_of_differentiableAt_update (hs.mem_nhds hz) hd

/-- On an open subset of `ι → ℂ`, a function is analytic if and only if it is continuous and complex
differentiable in each variable separately. -/
theorem analyticOnNhd_iff_continuousOn_and_differentiableAt_update (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ ContinuousOn f s ∧
      ∀ y ∈ s, ∀ i, DifferentiableAt ℂ (fun x => f (update y i x)) (y i) :=
  ⟨fun h => ⟨h.continuousOn, fun y hy i => (h y hy).differentiableAt.comp_update i⟩,
    fun h => h.1.analyticOnNhd_of_differentiableAt_update hs h.2⟩

end Osgood

section FiniteDimensional

variable [CompleteSpace E] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] {f : V → E} {s : Set V} {z : V}

/-- A function on a finite-dimensional complex normed space which is complex differentiable on a
neighbourhood of a point is analytic at that point. This is the several-variable form of
`DifferentiableOn.analyticAt`. -/
theorem _root_.DifferentiableOn.analyticAt_of_finiteDimensional (hd : DifferentiableOn ℂ f s)
    (hs : s ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  let e := (Module.finBasis ℂ V).equivFunL
  have hde : DifferentiableOn ℂ (f ∘ e.symm) (interior (e.symm ⁻¹' s)) :=
    (hd.comp e.symm.differentiableOn (mapsTo_preimage _ _)).mono interior_subset
  have h : AnalyticAt ℂ (f ∘ e.symm) (e z) :=
    hde.continuousOn.analyticAt_of_differentiableAt_update
      (interior_mem_nhds.2 (e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hs)))
      fun y hy i => (hde.differentiableAt (isOpen_interior.mem_nhds hy)).comp_update i
  have hfe : (f ∘ e.symm) ∘ e = f := by
    ext x
    simp
  exact hfe ▸ h.comp (e.analyticAt z)

/-- A function on a finite-dimensional complex normed space which is complex differentiable on an
open set is analytic on it. This is the several-variable form of `DifferentiableOn.analyticOnNhd`.
-/
theorem _root_.DifferentiableOn.analyticOnNhd_of_finiteDimensional (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : AnalyticOnNhd ℂ f s :=
  fun _z hz => hd.analyticAt_of_finiteDimensional (hs.mem_nhds hz)

/-- A function on a finite-dimensional complex normed space which is complex differentiable on an
open set is `C^n` on it for every `n`, including `n = ω`. This is the several-variable form of
`DifferentiableOn.contDiffOn`. -/
theorem _root_.DifferentiableOn.contDiffOn_of_finiteDimensional {n : WithTop ℕ∞}
    (hd : DifferentiableOn ℂ f s) (hs : IsOpen s) : ContDiffOn ℂ n f s :=
  (hd.analyticOnNhd_of_finiteDimensional hs).contDiffOn_of_completeSpace

/-- On an open subset of a finite-dimensional complex normed space, a function is analytic if and
only if it is complex differentiable. This is the several-variable form of
`Complex.analyticOnNhd_iff_differentiableOn`. -/
theorem analyticOnNhd_iff_differentiableOn_of_finiteDimensional (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, fun hd => hd.analyticOnNhd_of_finiteDimensional hs⟩

end FiniteDimensional

section Parametric

variable [CompleteSpace E] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

section Integral

variable {Y α : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [MeasurableSpace α]
  [TopologicalSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α}
  {f : V × Y → E} {φ : α → Y} {g : α → ℂ} {K : Set Y}

/-- **Differentiation under the integral sign for a jointly analytic integrand.** If `f` is
jointly analytic at every point of `{p} × K`, with `K` compact, and `φ` is a continuous map with
values in `K`, then for every integrable weight `g` the integral `q ↦ ∫ a, g a • f (q, φ a) ∂μ`
has derivative at `p` the integral of the partial derivatives of `f` in the parameter. -/
theorem hasFDerivAt_integral_smul_of_analyticAt {p : V} (hK : IsCompact K) (hφ : Continuous φ)
    (hφK : ∀ a, φ a ∈ K) (hf : ∀ y ∈ K, AnalyticAt ℂ f (p, y)) (hg : Integrable g μ) :
    HasFDerivAt (fun q ↦ ∫ a, g a • f (q, φ a) ∂μ)
      (∫ a, g a • (fderiv ℂ f (p, φ a)).comp (ContinuousLinearMap.inl ℂ V Y) ∂μ) p := by
  -- The partial derivative of `f` in the parameter, continuous where `f` is analytic.
  set G : V × Y → V →L[ℂ] E := fun x ↦ (fderiv ℂ f x).comp (ContinuousLinearMap.inl ℂ V Y)
  -- Near `p`, `f` is analytic on `{q} × K` and `G` is bounded there uniformly in `q`.
  obtain ⟨C, hC⟩ := hK.exists_eventually_norm_le (F := G) (x₀ := p) (isOpen_analyticAt ℂ f)
    (fun y hy ↦ (hf y hy).fderiv.continuousAt.clm_comp continuousAt_const) hf
  set s := {q : V | ∀ y ∈ K, AnalyticAt ℂ f (q, y) ∧ ‖G (q, y)‖ ≤ C}
  have hs : s ∈ 𝓝 p := hC
  have hcont : ∀ q ∈ s, Continuous fun a ↦ f (q, φ a) := fun q hq ↦
    continuous_iff_continuousAt.2 fun a ↦
      (hq _ (hφK a)).1.continuousAt.comp_of_eq (f := fun a ↦ (q, φ a))
        (continuous_const.prodMk hφ).continuousAt rfl
  have hGcont : Continuous fun a ↦ G (p, φ a) := continuous_iff_continuousAt.2 fun a ↦
    ((hf _ (hφK a)).fderiv.continuousAt.clm_comp continuousAt_const).comp_of_eq
      (f := fun a ↦ (p, φ a)) (continuous_const.prodMk hφ).continuousAt rfl
  -- The integrand at `p` is bounded by a multiple of `‖g‖`, hence integrable.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun y ↦ f (p, y)) fun y hy ↦
    ((hf y hy).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
      ).continuousWithinAt
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun q a ↦ g a • G (q, φ a))
    (bound := fun a ↦ ‖g a‖ * C) hs
    (eventually_of_mem hs fun q hq ↦
      hg.aestronglyMeasurable.smul (hcont q hq).aestronglyMeasurable) ?_
    (hg.aestronglyMeasurable.smul hGcont.aestronglyMeasurable) ?_ (hg.norm.mul_const C) ?_
  · refine (hg.norm.mul_const B).mono'
      (hg.aestronglyMeasurable.smul (hcont p (mem_of_mem_nhds hs)).aestronglyMeasurable)
      (ae_of_all _ fun a ↦ ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hB _ (hφK a)) (norm_nonneg _)
  · refine ae_of_all _ fun a q hq ↦ ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hq _ (hφK a)).2 (norm_nonneg _)
  · refine ae_of_all _ fun a q hq ↦ ?_
    exact (((hq _ (hφK a)).1.differentiableAt.hasFDerivAt).comp q
      (hasFDerivAt_prodMk_left q (φ a))).const_smul (g a)

/-- **Analytic dependence of an integral on a parameter.** If `f` is jointly analytic at every
point of `{p} × K`, with `K` compact, and `φ` is a continuous map with values in `K`, then for
every integrable weight `g` the integral `q ↦ ∫ a, g a • f (q, φ a) ∂μ` is analytic at `p`. -/
theorem analyticAt_integral_smul [FiniteDimensional ℂ V] {p : V} (hK : IsCompact K)
    (hφ : Continuous φ) (hφK : ∀ a, φ a ∈ K) (hf : ∀ y ∈ K, AnalyticAt ℂ f (p, y))
    (hg : Integrable g μ) :
    AnalyticAt ℂ (fun q ↦ ∫ a, g a • f (q, φ a) ∂μ) p := by
  -- Analyticity of `f` on `{p} × K` persists on `{q} × K` for `q` near `p`, and the integral is
  -- differentiable at each such `q`.
  have h : ∀ᶠ q in 𝓝 p, ∀ y ∈ K, AnalyticAt ℂ f (q, y) :=
    hK.eventually_forall_of_forall_eventually fun y hy ↦ (hf y hy).eventually_analyticAt
  exact DifferentiableOn.analyticAt_of_finiteDimensional (fun q hq ↦
    (hasFDerivAt_integral_smul_of_analyticAt hK hφ hφK hq hg).differentiableAt
      |>.differentiableWithinAt) h

end Integral

variable {f : V × ℂ → E} {c : ℂ} {R : ℝ}

/-- The weight `deriv (circleMap c R)` of a contour integral over `C(c, R)` is integrable on
`Ioc 0 (2π)`. -/
private theorem integrable_deriv_circleMap (c : ℂ) (R : ℝ) :
    Integrable (deriv (circleMap c R)) (volume.restrict (Ioc 0 (2 * π))) := by
  have hderiv : Continuous (deriv (circleMap c R)) := by
    rw [funext (deriv_circleMap c R)]
    fun_prop
  exact (hderiv.integrableOn_Icc (a := 0) (b := 2 * π)).mono_set Ioc_subset_Icc_self

/-- **Differentiation of a contour integral under the integral sign.** If `f` is jointly analytic
at every point of `{p} × sphere c |R|`, then `q ↦ ∮ ζ in C(c, R), f (q, ζ)` has derivative at `p`
the contour integral of the partial derivative of `f` in the parameter. -/
theorem hasFDerivAt_circleIntegral {p : V} (hf : ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ f (p, ζ)) :
    HasFDerivAt (fun q => ∮ ζ in C(c, R), f (q, ζ))
      (∮ ζ in C(c, R), (fderiv ℂ f (p, ζ)).comp (ContinuousLinearMap.inl ℂ V ℂ)) p := by
  simpa only [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le] using
    hasFDerivAt_integral_smul_of_analyticAt (isCompact_sphere c |R|) (continuous_circleMap c R)
      (circleMap_mem_sphere' c R) hf (integrable_deriv_circleMap c R)

variable [FiniteDimensional ℂ V]

/-- **Analytic dependence of a contour integral on a parameter.** If `f` is jointly analytic at
every point of `{p₀} × sphere c |R|`, then `p ↦ ∮ ζ in C(c, R), f (p, ζ)` is analytic at `p₀`. -/
theorem analyticAt_circleIntegral {p₀ : V} (hf : ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ f (p₀, ζ)) :
    AnalyticAt ℂ (fun p => ∮ ζ in C(c, R), f (p, ζ)) p₀ := by
  simpa only [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le] using
    analyticAt_integral_smul (isCompact_sphere c |R|) (continuous_circleMap c R)
      (circleMap_mem_sphere' c R) hf (integrable_deriv_circleMap c R)

/-- **Analytic dependence of a contour integral on a parameter.** If `f` is jointly analytic on a
neighbourhood of `s × sphere c |R|`, then `p ↦ ∮ ζ in C(c, R), f (p, ζ)` is analytic on a
neighbourhood of `s`. -/
theorem analyticOnNhd_circleIntegral {s : Set V} (hf : AnalyticOnNhd ℂ f (s ×ˢ sphere c |R|)) :
    AnalyticOnNhd ℂ (fun p => ∮ ζ in C(c, R), f (p, ζ)) s :=
  fun _p hp => analyticAt_circleIntegral fun _ζ hζ => hf _ ⟨hp, hζ⟩

end Parametric

end TauCeti
