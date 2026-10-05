/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.TorusIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units

/-!
# The Cauchy integral formula on polydiscs and analyticity in several variables

This file proves the iterated Cauchy integral formula on a polydisc, and deduces that a function
of finitely many complex variables which is complex differentiable on an open set is analytic
there. Mathlib proves both facts for functions of one complex variable
(`DifferentiableOn.circleIntegral_sub_inv_smul`, `DifferentiableOn.analyticOnNhd`); the
several-variable statements are the basic tools for proving joint analyticity of functions defined
by parameter-dependent contour integrals.

A polydisc in `ℂⁿ` is the product `Set.univ.pi fun i => ball (c i) (R i)` of open discs, and its
distinguished boundary is the torus `T(c, R)` of Mathlib's `torusIntegral`.

## Main results

* `DifferentiableOn.torusIntegral_prod_sub_inv_smul`: **the Cauchy integral formula on a
  polydisc.** If `f : ℂⁿ → E` is complex differentiable on the closed polydisc with center `c` and
  polyradius `R`, then for `w` in the open polydisc,
  `∯ z in T(c, R), (∏ i, (z i - w i))⁻¹ • f z = (2πi)ⁿ • f w`.
* `DifferentiableOn.analyticAt_of_finiteDimensional`,
  `DifferentiableOn.analyticOnNhd_of_finiteDimensional`: a function on a finite-dimensional complex
  normed space which is complex differentiable on a neighbourhood of a point is analytic there.
* `TauCeti.analyticOnNhd_iff_differentiableOn_of_finiteDimensional`: on an open subset of a
  finite-dimensional complex normed space, analyticity and complex differentiability agree.

## The argument

The Cauchy formula follows by induction on `n` from the one-variable formula, splitting off the
first coordinate of the torus integral with `torusIntegral_succ`.

For analyticity at `z`, choose a closed polydisc `closedBall z R` inside the domain and let `X` be
the torus `∏ sphere (z i) R`. On the Banach algebra `C(X, ℂ)`, the Cauchy kernel
`w ↦ (ζ ↦ ∏ i, (ζ i - w i))` is a polynomial in `w`, and it is a unit at `w = z`, so its inverse
is analytic in `w` near `z` (`analyticAt_inverse`). Integrating against `f` over the torus is a
continuous linear functional on `C(X, ℂ)`, so by the Cauchy formula `f` is a continuous linear
image of an analytic function near `z`. This is the several-variable form of the argument in
`TauCeti.Analysis.Polynomial.RootSum`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter MeasureTheory Metric Real Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

namespace TauCeti

section CauchyFormula

/-- For nonnegative radii, a point of the torus `T(c, R)` lies on the product of the circles
`sphere (c i) (R i)`. -/
theorem torusMap_mem_pi_sphere {c : Fin n → ℂ} {R : Fin n → ℝ} (hR : ∀ i, 0 ≤ R i)
    (θ : Fin n → ℝ) : torusMap c R θ ∈ univ.pi fun i => sphere (c i) (R i) :=
  fun i _ => circleMap_mem_sphere (c i) (hR i) (θ i)

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

/-- **The Cauchy integral formula on a polydisc.** If `f` is complex differentiable on the closed
polydisc with center `c` and polyradius `R`, then for every `w` in the open polydisc, the integral
of `(∏ i, (z i - w i))⁻¹ • f z` over the distinguished boundary `T(c, R)` is `(2πi)ⁿ • f w`. -/
theorem _root_.DifferentiableOn.torusIntegral_prod_sub_inv_smul [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hd : DifferentiableOn ℂ f (univ.pi fun i => closedBall (c i) (R i)))
    (hw : w ∈ univ.pi fun i => ball (c i) (R i)) :
    (∯ z in T(c, R), (∏ i, (z i - w i))⁻¹ • f z) = (2 * π * I) ^ n • f w := by
  induction n with
  | zero => simp [torusIntegral_dim0, Subsingleton.elim c w]
  | succ n ih =>
    have hR0 : 0 < R 0 := pos_of_mem_ball (hw 0 trivial)
    have hwt : Fin.tail w ∈ univ.pi fun i => ball (Fin.tail c i) (Fin.tail R i) :=
      fun i _ => hw i.succ trivial
    -- Slices of `f` along the first coordinate, with the remaining coordinates in the closed
    -- polydisc, are differentiable.
    have hcons : ∀ x ∈ closedBall (c 0) (R 0),
        ∀ y ∈ univ.pi fun i => closedBall (Fin.tail c i) (Fin.tail R i),
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ univ.pi fun i => closedBall (c i) (R i) :=
      fun x hx y hy => by
        simp only [mem_univ_pi, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
        exact ⟨hx, fun i => hy i trivial⟩
    -- Integrate first over the last `n` coordinates, using the formula in dimension `n`.
    have hinner : ∀ x ∈ sphere (c 0) (R 0),
        (∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - w i))⁻¹ • f (Fin.cons x y)) =
          (2 * π * I) ^ n • ((x - w 0)⁻¹ • f (Fin.cons x (Fin.tail w))) := by
      intro x hx
      have hdx : DifferentiableOn ℂ (fun y => f (Fin.cons x y))
          (univ.pi fun i => closedBall (Fin.tail c i) (Fin.tail R i)) :=
        hd.comp (differentiableOn_const x |>.finCons differentiableOn_id) fun y hy =>
          hcons x (sphere_subset_closedBall hx) y hy
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_inv, mul_smul]
      rw [torusIntegral_smul, smul_comm ((2 * π * I) ^ n)]
      congr 1
      exact ih hdx hwt
    rw [torusIntegral_succ (torusIntegrable_prod_sub_inv_smul hd.continuousOn hw),
      circleIntegral.integral_congr hR0.le hinner, circleIntegral.integral_smul]
    have hcw : DifferentiableOn ℂ (fun x : ℂ => (Fin.cons x (Fin.tail w) : Fin (n + 1) → ℂ))
        (closedBall (c 0) (R 0)) := by
      fun_prop
    have hdw : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail w)))
        (closedBall (c 0) (R 0)) :=
      hd.comp hcw fun x hx => hcons x hx _ fun i _ => ball_subset_closedBall (hwt i trivial)
    rw [hdw.circleIntegral_sub_inv_smul (hw 0 trivial), Fin.cons_self_tail, smul_smul, pow_succ]

end CauchyFormula

section Analytic

variable {z : Fin n → ℂ} {R : ℝ}

/-- The parametrization of the torus `∏ sphere (z i) R` by angles. -/
private noncomputable def torusParam (z : Fin n → ℂ) (hR : 0 ≤ R) :
    C(Fin n → ℝ, (i : Fin n) → sphere (z i) R) :=
  ⟨fun θ i => ⟨torusMap z (fun _ => R) θ i, torusMap_mem_pi_sphere (fun _ => hR) θ i trivial⟩,
    continuous_pi fun i =>
      ((continuous_apply i).comp (continuous_torusMap z fun _ => R)).subtype_mk _⟩

/-- Integration over the torus `∏ sphere (z i) R` against a fixed continuous function `F`, as a
continuous linear functional on the continuous functions on the torus. -/
private noncomputable def torusIntegralCLM (z : Fin n → ℂ) (hR : 0 ≤ R)
    (F : C((i : Fin n) → sphere (z i) R, E)) : C((i : Fin n) → sphere (z i) R, ℂ) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π),
        (∏ i : Fin n, (R : ℂ) * exp (θ i * I) * I) •
          (g (torusParam z hR θ) • F (torusParam z hR θ))
      map_add' := fun g h => by
        simp only [ContinuousMap.add_apply, add_smul, smul_add]
        exact integral_add (Continuous.integrableOn_Icc (by fun_prop))
          (Continuous.integrableOn_Icc (by fun_prop))
      map_smul' := fun a g => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul,
          smul_comm _ a]
        exact integral_smul a _ }
    (R ^ n * ‖F‖ * volume.real (Icc (0 : Fin n → ℝ) fun _ => 2 * π)) fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc _ ≤ R ^ n * ‖F‖ * ‖g‖ * volume.real (Icc (0 : Fin n → ℝ) fun _ => 2 * π) :=
            norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun θ _ => by
              simp only [norm_smul, norm_prod, norm_mul, norm_real, norm_exp_ofReal_mul_I,
                norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg hR, Finset.prod_const,
                Finset.card_univ, Fintype.card_fin]
              have h : ‖g (torusParam z hR θ)‖ * ‖F (torusParam z hR θ)‖ ≤ ‖F‖ * ‖g‖ := by
                rw [mul_comm ‖F‖]
                exact mul_le_mul (g.norm_coe_le_norm _) (F.norm_coe_le_norm _) (norm_nonneg _)
                  (norm_nonneg _)
              nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg hR n)]
        _ = _ := by ring

/-- `torusIntegralCLM` computes the torus integral of any functions agreeing with its arguments on
the torus. -/
private theorem torusIntegralCLM_apply (hR : 0 ≤ R) {F : C((i : Fin n) → sphere (z i) R, E)}
    {g : C((i : Fin n) → sphere (z i) R, ℂ)} {f : (Fin n → ℂ) → E} {G : (Fin n → ℂ) → ℂ}
    (hF : ∀ x, F x = f fun i => x i) (hG : ∀ x, g x = G fun i => x i) :
    torusIntegralCLM z hR F g = ∯ ζ in T(z, fun _ => R), G ζ • f ζ := by
  simp only [torusIntegralCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    torusIntegral, hF, hG]
  -- The coordinates of `torusParam z hR θ` are `torusMap z (fun _ => R) θ` by definition.
  rfl

/-- A function of `n` complex variables which is complex differentiable on a neighbourhood of a
point is analytic there. -/
private theorem analyticAt_of_differentiableOn_pi [CompleteSpace E] {f : (Fin n → ℂ) → E}
    {s : Set (Fin n → ℂ)} (hd : DifferentiableOn ℂ f s) (hs : s ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  obtain ⟨R, hR, hRs⟩ := nhds_basis_closedBall.mem_iff.1 hs
  have hd' : DifferentiableOn ℂ f (univ.pi fun i => closedBall (z i) R) := by
    rw [← closedBall_pi z hR.le]
    exact hd.mono hRs
  -- On the torus `X = ∏ sphere (z i) R`, the Cauchy kernel is a unit of `C(X, ℂ)` at `w = z`.
  let F : C((i : Fin n) → sphere (z i) R, E) :=
    ⟨fun x => f fun i => x i, hd'.continuousOn.comp_continuous (by fun_prop) fun x i _ =>
      sphere_subset_closedBall (x i).2⟩
  let K : (Fin n → ℂ) → C((i : Fin n) → sphere (z i) R, ℂ) := fun w =>
    ∏ i, (⟨fun x => (x i : ℂ), by fun_prop⟩ - algebraMap ℂ _ (w i))
  have hKapply : ∀ w x, K w x = ∏ i, ((x i : ℂ) - w i) := fun w x => by
    simp [K, ContinuousMap.prod_apply]
  have hK : AnalyticAt ℂ K z := by
    refine Finset.analyticAt_fun_prod _ fun i _ => analyticAt_const.sub ?_
    exact ((algebraMapCLM ℂ C((i : Fin n) → sphere (z i) R, ℂ)).comp
      (ContinuousLinearMap.proj i)).analyticAt z
  have hunit : IsUnit (K z) := (ContinuousMap.isUnit_iff_forall_ne_zero _).2 fun x => by
    rw [hKapply]
    exact Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 (ne_of_mem_sphere (x i).2 hR.ne')
  have hinv : AnalyticAt ℂ (fun w => Ring.inverse (K w)) z := by
    have h := analyticAt_inverse (𝕜 := ℂ) hunit.unit
    rw [hunit.unit_spec] at h
    exact h.comp hK
  refine ((((torusIntegralCLM z hR.le F).analyticAt _).comp hinv).const_smul
    (c := ((2 * π * I) ^ n)⁻¹)).congr ?_
  -- Near `z`, the kernel is still a unit, and the Cauchy formula recovers `f`.
  filter_upwards [hK.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit),
    ball_mem_nhds z hR] with w hw hwb
  rw [ball_pi z hR] at hwb
  have hinvw : ∀ x, Ring.inverse (K w) x = (∏ i, ((x i : ℂ) - w i))⁻¹ := fun x => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hKapply, ← ContinuousMap.mul_apply, Ring.inverse_mul_cancel _ hw,
      ContinuousMap.one_apply]
  rw [Pi.smul_apply, Function.comp_apply,
    torusIntegralCLM_apply (G := fun ζ => (∏ i, (ζ i - w i))⁻¹) hR.le (fun _ => rfl) hinvw,
    hd'.torusIntegral_prod_sub_inv_smul hwb, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ two_pi_I_ne_zero), one_smul]

variable [CompleteSpace E] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] {f : V → E} {s : Set V} {z : V}

/-- A function on a finite-dimensional complex normed space which is complex differentiable on a
neighbourhood of a point is analytic at that point. This is the several-variable form of
`DifferentiableOn.analyticAt`. -/
theorem _root_.DifferentiableOn.analyticAt_of_finiteDimensional (hd : DifferentiableOn ℂ f s)
    (hs : s ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  let e := (Module.finBasis ℂ V).equivFunL
  have h : AnalyticAt ℂ (f ∘ e.symm) (e z) :=
    analyticAt_of_differentiableOn_pi (hd.comp e.symm.differentiableOn (mapsTo_preimage _ _))
      (e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hs))
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

/-- On an open subset of a finite-dimensional complex normed space, a function is analytic if and
only if it is complex differentiable. This is the several-variable form of
`Complex.analyticOnNhd_iff_differentiableOn`. -/
theorem analyticOnNhd_iff_differentiableOn_of_finiteDimensional (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, fun hd => hd.analyticOnNhd_of_finiteDimensional hs⟩

end Analytic

end TauCeti
