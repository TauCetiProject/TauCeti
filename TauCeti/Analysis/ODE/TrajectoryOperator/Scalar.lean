/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Fredholm
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel

/-!
# Trajectory operators with scalar coefficients

For a scalar function `a : ℝ → ℝ`, the coefficient `A(s) = a(s) • id` turns the trajectory
operator `D_A u = u' + a u` into a scalar equation acting on each vector separately. Its
solutions are explicit once one nonvanishing solution is known: if `φ' = -a φ` and `φ` never
vanishes, every solution of `v' + a v = 0` is `v(s) = (φ(s) / φ(0)) • v(0)`
(`TauCeti.eq_div_smul_of_hasDerivAt`). So the square-integrable solutions are all solutions or
only the zero solution, according as `φ` is square integrable or not
(`TauCeti.squareIntegrableSolutions_smul_id_eq_top`,
`TauCeti.squareIntegrableSolutions_smul_id_eq_bot`).

On `W^{1,2}(ℝ, F)` this computes the kernel of `D_A`. On a finite-dimensional inner product space,
`D_A` is Fredholm when `a` has nonzero limits at both ends and `a'` tends to zero there
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_smul_id`); then the cokernel is the kernel of
the formal adjoint `D_{-A}`, and `D_A` is onto as soon as a nonvanishing solution of `ψ' = a ψ` is
not square integrable (`TauCeti.WeakDerivStep.range_trajectoryOperator_smul_id_eq_top`).

These are the scalar model operators `d/ds ± a(s)` of linear gluing for Floer and Morse
trajectories, whose kernels and cokernels can be computed by hand.

## Main declarations

* `TauCeti.eq_div_smul_of_hasDerivAt`: the solutions of `v' + a v = 0` are multiples of a
  nonvanishing scalar solution.
* `TauCeti.squareIntegrableSolutions_smul_id_eq_top`,
  `TauCeti.squareIntegrableSolutions_smul_id_eq_bot`: the square-integrable solutions.
* `TauCeti.WeakDerivStep.finrank_ker_trajectoryOperator_smul_id`,
  `TauCeti.WeakDerivStep.ker_trajectoryOperator_smul_id_eq_bot`: the kernel of `D_A`.
* `TauCeti.WeakDerivStep.ae_isSymmetric_of_ae_eq_smul_id`,
  `TauCeti.WeakDerivStep.neg_ae_eq_smul_id`: scalar coefficients are symmetric, and negating one
  gives the coefficient `-a` of the operator `D_{-A}` whose kernel is the cokernel of `D_A`.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_smul_id`: the Fredholm property.
* `TauCeti.WeakDerivStep.range_trajectoryOperator_smul_id_eq_top`: surjectivity of `D_A`.

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (kernels and cokernels of
  linearized trajectory operators as spaces of decaying solutions).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a φ : ℝ → ℝ}

/-- **Solutions of a scalar linear equation are multiples of one nonvanishing solution.** If `φ`
is a nowhere vanishing solution of `φ' = -a φ`, every solution of `v' = -a v` with values in a
real normed space is `v(s) = (φ(s) / φ(0)) • v(0)`. -/
theorem eq_div_smul_of_hasDerivAt (hφ : ∀ s, HasDerivAt φ (-(a s * φ s)) s)
    (hφ0 : ∀ s, φ s ≠ 0) {v : ℝ → F} (hv : ∀ s, HasDerivAt v (-(a s • v s)) s) (s : ℝ) :
    v s = (φ s / φ 0) • v 0 := by
  -- The quotient `(φ t)⁻¹ • v t` has derivative zero, so it is constant.
  have hw (t : ℝ) : HasDerivAt (fun t ↦ (φ t)⁻¹ • v t) 0 t := by
    convert ((hφ t).inv (hφ0 t)).smul (hv t) using 1
    have h : -((φ t)⁻¹ * a t) + - -(a t * φ t) / φ t ^ 2 = 0 := by
      field_simp [hφ0 t]
      ring
    rw [Pi.inv_apply, smul_neg, smul_smul, ← neg_smul, ← add_smul, h, zero_smul]
  have hconst := is_const_of_deriv_eq_zero (fun t ↦ (hw t).differentiableAt)
    (fun t ↦ (hw t).deriv) s 0
  calc v s = φ s • ((φ s)⁻¹ • v s) := by rw [smul_smul, mul_inv_cancel₀ (hφ0 s), one_smul]
    _ = φ s • ((φ 0)⁻¹ • v 0) := by rw [hconst]
    _ = (φ s / φ 0) • v 0 := by rw [smul_smul, div_eq_mul_inv]

/-- **A square-integrable scalar solution makes every initial value admissible.** If `φ` is a
square-integrable solution of `φ' = -a φ` with `φ(0) ≠ 0`, then every vector is the initial
value of the square-integrable solution `s ↦ (φ(s) / φ(0)) • x` of `v' + a v = 0`. -/
theorem squareIntegrableSolutions_smul_id_eq_top (hφ : ∀ s, HasDerivAt φ (-(a s * φ s)) s)
    (hφ0 : φ 0 ≠ 0) (h2 : MemLp φ 2) :
    squareIntegrableSolutions (fun s ↦ a s • ContinuousLinearMap.id ℝ F) = ⊤ := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun s ↦ (hφ s).continuousAt
  refine eq_top_iff.2 fun x _ ↦
    mem_squareIntegrableSolutions.2 ⟨fun s ↦ (φ s / φ 0) • x, by simp [hφ0], fun s ↦ ?_, ?_⟩
  · convert ((hφ s).div_const (φ 0)).smul_const x using 1
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, smul_smul,
      ← neg_smul]
    congr 1
    ring
  · refine (h2.const_mul (‖x‖ / φ 0)).congr_norm
      ((hφc.div_const _).smul continuous_const).aestronglyMeasurable (ae_of_all _ fun s ↦ ?_)
    simp only [norm_mul, norm_div, norm_norm, norm_smul]
    ring

/-- **A scalar solution outside `L²` leaves only the zero solution.** If `φ` is a nowhere
vanishing solution of `φ' = -a φ` that is not square integrable, the only square-integrable
solution of `v' + a v = 0` is zero. -/
theorem squareIntegrableSolutions_smul_id_eq_bot (hφ : ∀ s, HasDerivAt φ (-(a s * φ s)) s)
    (hφ0 : ∀ s, φ s ≠ 0) (h2 : ¬MemLp φ 2) :
    squareIntegrableSolutions (fun s ↦ a s • ContinuousLinearMap.id ℝ F) = ⊥ := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun s ↦ (hφ s).continuousAt
  refine eq_bot_iff.2 fun x hxv ↦ (Submodule.mem_bot ℝ).2 ?_
  obtain ⟨v, hv0, hv, hv2⟩ := mem_squareIntegrableSolutions.1 hxv
  by_contra hx
  have heq := eq_div_smul_of_hasDerivAt hφ hφ0 (v := v) fun s ↦ by simpa using hv s
  -- Otherwise `φ` would be a multiple of `‖v‖`, hence square integrable.
  refine h2 ((hv2.const_smul (φ 0 / ‖x‖)).congr_norm hφc.aestronglyMeasurable
    (ae_of_all _ fun s ↦ ?_))
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hφ0' : ‖φ 0‖ ≠ 0 := norm_ne_zero_iff.2 (hφ0 0)
  simp only [Pi.smul_apply, heq s, hv0, norm_smul, norm_div, norm_norm]
  field_simp

end TauCeti

namespace TauCeti.WeakDerivStep

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {a φ : ℝ → ℝ}

/-- **The kernel of `d/ds + a` with a square-integrable scalar solution.** If `a` is continuous
and `φ` is a square-integrable solution of `φ' = -a φ` with `φ(0) ≠ 0`, the kernel of
`u ↦ u' + a u` on `W^{1,2}(ℝ, F)` has the dimension of `F`. -/
theorem finrank_ker_trajectoryOperator_smul_id (ha : Continuous a)
    (hφ : ∀ s, HasDerivAt φ (-(a s * φ s)) s) (hφ0 : φ 0 ≠ 0) (h2 : MemLp φ 2)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a s • ContinuousLinearMap.id ℝ F) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker = Module.finrank ℝ F := by
  rw [finrank_ker_trajectoryOperator (by fun_prop) AL hAL,
    squareIntegrableSolutions_smul_id_eq_top hφ hφ0 h2, finrank_top]

/-- **The kernel of `d/ds + a` with a scalar solution outside `L²`.** If `a` is continuous and
`φ` is a nowhere vanishing solution of `φ' = -a φ` that is not square integrable, then
`u ↦ u' + a u` is injective on `W^{1,2}(ℝ, F)`. -/
theorem ker_trajectoryOperator_smul_id_eq_bot (ha : Continuous a)
    (hφ : ∀ s, HasDerivAt φ (-(a s * φ s)) s) (hφ0 : ∀ s, φ s ≠ 0) (h2 : ¬MemLp φ 2)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a s • ContinuousLinearMap.id ℝ F) :
    (trajectoryOperator (p := 2) AL).ker = ⊥ := by
  have e := kerTrajectoryOperatorEquiv (by fun_prop) AL hAL
  rw [squareIntegrableSolutions_smul_id_eq_bot hφ hφ0 h2] at e
  have : Subsingleton (trajectoryOperator (p := 2) AL).ker := e.toEquiv.subsingleton
  exact Submodule.eq_bot_of_subsingleton

end Banach

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {a φ : ℝ → ℝ}

omit [FiniteDimensional ℝ E] in
/-- A real multiple of the identity is symmetric. -/
private theorem isSymmetric_smul_id (c : ℝ) :
    (c • ContinuousLinearMap.id ℝ E).toLinearMap.IsSymmetric := by
  simpa using LinearMap.IsSymmetric.id.smul (conj_trivial c)

omit [FiniteDimensional ℝ E] in
/-- An `L∞` class of a scalar coefficient `a(s) • id` is almost everywhere symmetric. -/
theorem ae_isSymmetric_of_ae_eq_smul_id
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a s • ContinuousLinearMap.id ℝ E) :
    ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), (AL s).toLinearMap.IsSymmetric := by
  filter_upwards [hAL] with s hs
  rw [hs]
  exact isSymmetric_smul_id _

omit [FiniteDimensional ℝ E] in
/-- The negative of an `L∞` class of `a(s) • id` is an `L∞` class of `(-a(s)) • id`. -/
theorem neg_ae_eq_smul_id {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a s • ContinuousLinearMap.id ℝ E) :
    -AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-a s) • ContinuousLinearMap.id ℝ E := by
  filter_upwards [Lp.coeFn_neg AL, hAL] with s hs hAs
  rw [hs, Pi.neg_apply, hAs, neg_smul]

/-- **Scalar trajectory operators are Fredholm.** If `a` is `C¹` with nonzero limits at `±∞` and
`a'` tends to zero at both ends, then `u ↦ u' + a u` is a Fredholm operator from `W^{1,2}(ℝ, E)`
to `L²(ℝ, E)`. -/
theorem isFredholm_trajectoryOperator_smul_id (ha : ContDiff ℝ 1 a) {am ap : ℝ} (ham : am ≠ 0)
    (hap : ap ≠ 0) (hbot : Tendsto a atBot (𝓝 am)) (htop : Tendsto a atTop (𝓝 ap))
    (hdbot : Tendsto (deriv a) atBot (𝓝 0)) (hdtop : Tendsto (deriv a) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).IsFredholm := by
  have hderiv : deriv (fun s ↦ a s • ContinuousLinearMap.id ℝ E) =
      fun s ↦ deriv a s • ContinuousLinearMap.id ℝ E :=
    funext fun s ↦ ((ha.differentiable one_ne_zero s).hasDerivAt.smul_const
      (ContinuousLinearMap.id ℝ E)).deriv
  have hinj {c : ℝ} (hc : c ≠ 0) : Function.Injective (c • ContinuousLinearMap.id ℝ E) :=
    fun x y h ↦ smul_right_injective E hc (by simpa using h)
  refine (isFredholm_trajectoryOperator_iff (A := fun s ↦ a s • ContinuousLinearMap.id ℝ E)
    (ha.smul contDiff_const)
    (fun s ↦ isSymmetric_smul_id _)
    (hbot.smul_const _) (htop.smul_const _) ?_ ?_ AL hAL).2 ⟨hinj ham, hinj hap⟩ <;>
  · rw [hderiv]
    simpa using (‹Tendsto (deriv a) _ (𝓝 0)›).smul_const (ContinuousLinearMap.id ℝ E)

/-- **Surjectivity of a scalar trajectory operator.** Under the hypotheses of
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_smul_id`, if `ψ` is a nowhere vanishing
solution of the adjoint equation `ψ' = a ψ` that is not square integrable, then `u ↦ u' + a u`
maps `W^{1,2}(ℝ, E)` onto `L²(ℝ, E)`. -/
theorem range_trajectoryOperator_smul_id_eq_top (ha : ContDiff ℝ 1 a) {am ap : ℝ} (ham : am ≠ 0)
    (hap : ap ≠ 0) (hbot : Tendsto a atBot (𝓝 am)) (htop : Tendsto a atTop (𝓝 ap))
    (hdbot : Tendsto (deriv a) atBot (𝓝 0)) (hdtop : Tendsto (deriv a) atTop (𝓝 0))
    {ψ : ℝ → ℝ} (hψ : ∀ s, HasDerivAt ψ (a s * ψ s) s) (hψ0 : ∀ s, ψ s ≠ 0) (h2 : ¬MemLp ψ 2)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ a s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).range = ⊤ := by
  have hclosed :=
    (isFredholm_trajectoryOperator_smul_id ha ham hap hbot htop hdbot hdtop AL hAL).isClosed_range
  refine (range_trajectoryOperator_eq_top_iff (ae_isSymmetric_of_ae_eq_smul_id hAL) hclosed).2
    (ker_trajectoryOperator_smul_id_eq_bot ha.continuous.neg (φ := ψ) (fun s ↦ ?_) hψ0 h2 _
      (neg_ae_eq_smul_id hAL))
  simpa using hψ s

end TauCeti.WeakDerivStep
