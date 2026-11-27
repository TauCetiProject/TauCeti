/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundedDomain
import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
import TauCeti.Analysis.PDE.EnergyForm.LowerOrder
import TauCeti.Analysis.PDE.EnergyForm.SmallDrift
import TauCeti.Analysis.PDE.MaximumPrinciple.HopfLemma
import TauCeti.Analysis.PDE.Regularity.Classical
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
import TauCeti.Analysis.PDE.EnergyForm.Poincare
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.SphereChart
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.LipschitzRepresentative
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Bounds
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Topology.Instances.Matrix

/-!
# Hopf's boundary-point lemma for divergence-form equations with Hölder coefficients

Let `B = ball y R` be a ball in an open set `Ω ⊆ ℝ^{n+1}` and let `x₀` lie on its bounding sphere.
Let `a` be uniformly elliptic on `B` with constants `0 < λ ≤ Λ`, not necessarily symmetric, and
`α`-Hölder on `closedBall y R` for some `α > 0`, and let `b` be a measurable drift, bounded on `B`.
Let `u ∈ H¹(Ω)` be a weak supersolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu ≥ 0` in `Ω`,

that is `a(u, v) + ∫ (b · ∇u) v ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, and suppose that `u`
agrees almost everywhere on `B` with a function `g` continuous on `closedBall y R` that attains a
strict minimum over `B` at `x₀`: `g x₀ < g x` for `x ∈ B`. **Hopf's lemma**
(`TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg`) says that `g` leaves `x₀` at a
positive linear rate along the inward normal: with `ν = (x₀ - y) / R`,

`ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small `t > 0`.

In particular an inward derivative of `g` at `x₀`, if it exists, is positive. In Rosales's sign
convention the drift is the term `cⁱ Dᵢu` with `cⁱ = -bⁱ`, here bounded.

The same conclusion holds with a zeroth-order term
(`TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos`): for a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with `c` measurable and `0 ≤ c ≤ M` on `B`,
provided `g x₀ ≤ 0`. In Rosales's sign convention this is the term `d u` with `d ≤ 0` bounded.
When `g x₀ = 0` a bounded `c` of either sign is allowed, since then `u ≥ 0` on `B` and the negative
part of `c` may be dropped. The sign condition on `g x₀` is needed: on the interval `(0, 2)`,
`cosh` solves `-u'' + u = 0`, and its minimum `cosh 0 = 1 > 0` over `[0, 2)` is attained only at
the boundary point `0`, where its derivative vanishes.

The Hölder continuity of `a` cannot be dropped: for measurable coefficients the lemma fails, by
Meyers' example (`TauCeti.Analysis.PDE.MaximumPrinciple.HalfDisk`). The lemma for operators in
non-divergence form, which needs no regularity of the coefficients, is
`TauCeti.PDE.exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv`.

## The argument

The proof follows Rosales: freeze the coefficients at `x₀`, rescale, and compare `u` with a
barrier for the frozen operator, corrected by the solution of a Dirichlet problem whose gradient is
small by the global `C^{1,β}` estimate.

* **Rescaling.** For `0 < ε ≤ R` the homothety `T z = ε z + y + (R - ε) ν` maps the closed unit ball
  into `closedBall y R`, the open unit ball into `ball y R`, and `ν` to `x₀`. The composition
  `u ∘ T` is a weak supersolution on the annulus `D = {1/2 < ‖z‖ < 1}` for the coefficients
  `a' = a ∘ T`, which are `α`-Hölder with constant `K_a ε^α` and within `K_a (2 ε)^α` of the frozen
  matrix `A = a x₀`, the drift `ε b ∘ T` and the mass coefficient `ε² c ∘ T`.
* **The barrier.** The Gaussian `Φ(z) = e^{-κ‖z‖²} - e^{-κ}` vanishes on the unit sphere, is a
  strict classical subsolution of `div (A ∇·)` on `D`, `div (A ∇Φ) ≥ λ κ e^{-κ}`, once `κ` is large
  compared with `tr A / λ`, and grows like `κ e^{-κ} t` along the inward normal at `ν`. Unlike
  Rosales, who solves the frozen Dirichlet problem and appeals to the classical Hopf lemma, we use
  this explicit barrier, so `A` need not be symmetric.
* **The correction.** Lax–Milgram gives `ψ ∈ H¹₀` of the unit ball with
  `-div (a' ∇ψ) = div ((a' - A) ∇Φ)`, so that `Φ + ψ` is a weak subsolution for `a'` on `D` up to
  the lower-order terms. Its `H¹` norm and the Hölder constant of `(a' - A) ∇Φ` are of order
  `‖a' - A‖ + [a']_α`. The global `C^{1,β}` estimate on the unit ball
  (`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded`), whose boundary charts are
  `TauCeti.exists_affineIsometryEquiv_unitSphereGraph_chart`, bounds `∇ψ` by the same order on the
  whole ball, and gives `ψ` a representative that is Lipschitz with that constant on the closed
  ball and vanishes on the unit sphere
  (`TauCeti.W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le`).
* **The lower-order terms.** After rescaling, the drift is at most `ε ‖b‖` and the mass coefficient
  at most `ε² M`. Since `Φ`, `∇Φ`, `ψ` and `∇ψ` are bounded, for `ε` small the terms
  `ε b ∘ T · ∇(Φ + ψ)` and `ε² c ∘ T (Φ + ψ)` are absorbed by the margin `λ κ e^{-κ}` of the
  barrier, and the term `ε² c g x₀` is nonpositive.
* **Comparison.** On the boundary of `D`, `u ∘ T ≥ g x₀` on the outer sphere, where `Φ + ψ`
  vanishes, and `u ∘ T ≥ g x₀ + θ Φ` on the inner one for some `θ > 0`, which exceeds
  `g x₀ + θ (Φ + ψ) / 2` since `ψ` is small. So `g x₀ + θ (Φ + ψ) / 2` is a weak subsolution below
  `u ∘ T` on the boundary, and the weak comparison principle with a small drift
  (`TauCeti.PDE.UniformlyEllipticOn.value_le_of_small_drift_of_subset_ball`) gives
  `g x₀ + θ (Φ + ψ) / 2 ≤ u ∘ T` on `D`; along the normal at `ν` the left-hand side grows like
  `θ κ e^{-κ} t / 4`.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg`: Hopf's boundary-point lemma
  for weak supersolutions of divergence-form equations with Hölder coefficients and a bounded drift.
* `TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos`: the same with a
  bounded zeroth-order term, nonnegative at a minimum `g x₀ < 0` and of either sign at a minimum
  `g x₀ = 0`.

## References

* L. Rosales, *Generalizing Hopf's boundary point lemma*,
  arXiv:1806.07003, Theorem 4.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4 (the classical boundary-point lemma), Theorem 8.1 (the weak maximum principle) and
  Theorem 8.33 (the global `C^{1,α}` estimate).
-/

public section

noncomputable section

open Filter Function Metric Set TopologicalSpace MeasureTheory TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology InnerProductSpace Gradient Distributions

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### The unit annulus and the unit ball -/

/-- The open annulus `{z | 1/2 < ‖z‖ < 1}`. -/
private def unitAnnulus : Opens E :=
  ⟨ball 0 1 ∩ (closedBall 0 (1 / 2))ᶜ, isOpen_ball.inter isClosed_closedBall.isOpen_compl⟩

private theorem coe_unitAnnulus :
    (unitAnnulus (n := n) : Set E) = ball 0 1 ∩ (closedBall 0 (1 / 2))ᶜ :=
  rfl

private theorem mem_unitAnnulus {z : E} :
    z ∈ (unitAnnulus (n := n) : Set E) ↔ ‖z‖ < 1 ∧ 1 / 2 < ‖z‖ := by
  simp [coe_unitAnnulus]

private theorem unitAnnulus_subset_ball : (unitAnnulus (n := n) : Set E) ⊆ ball 0 1 :=
  fun _ hz => mem_ball_zero_iff.2 (mem_unitAnnulus.1 hz).1

private theorem unitAnnulus_subset_closedBall : (unitAnnulus (n := n) : Set E) ⊆ closedBall 0 1 :=
  unitAnnulus_subset_ball.trans ball_subset_closedBall

private theorem closure_unitAnnulus_subset :
    closure (unitAnnulus (n := n) : Set E) ⊆ closedBall 0 1 :=
  (closure_mono unitAnnulus_subset_ball).trans closure_ball_subset_closedBall

private theorem frontier_unitAnnulus_subset :
    frontier (unitAnnulus (n := n) : Set E) ⊆ sphere 0 1 ∪ sphere 0 (1 / 2) := by
  rw [coe_unitAnnulus]
  exact (frontier_inter_subset _ _).trans (union_subset_union
    (inter_subset_left.trans frontier_ball_subset_sphere)
    (inter_subset_right.trans ((frontier_compl _).subset.trans frontier_closedBall_subset_sphere)))

private instance : IsFiniteMeasure (volume.restrict (unitAnnulus (n := n) : Set E)) :=
  isFiniteMeasure_restrict.2 (measure_ne_top_of_subset unitAnnulus_subset_ball
    measure_ball_lt_top.ne)

/-- The open unit ball, on which the correction of the barrier is solved. -/
private def unitBall : Opens E :=
  ⟨ball 0 1, isOpen_ball⟩

private theorem coe_unitBall : (unitBall (n := n) : Set E) = ball 0 1 :=
  rfl

private theorem unitAnnulus_le_unitBall : unitAnnulus (n := n) ≤ unitBall :=
  fun _ hz => unitAnnulus_subset_ball hz

private theorem closure_unitBall : closure (unitBall (n := n) : Set E) = closedBall 0 1 :=
  closure_ball 0 one_ne_zero

private instance : IsFiniteMeasure (volume.restrict (unitBall (n := n) : Set E)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

private theorem aestronglyMeasurable_restrict_of_subset_closedBall {Ω : Opens E}
    (hΩ : (Ω : Set E) ⊆ closedBall 0 1) {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hbc : ContinuousOn b (closedBall 0 1)) :
    AEStronglyMeasurable b (volume.restrict (Ω : Set E)) :=
  (hbc.mono hΩ).aestronglyMeasurable Ω.isOpen.measurableSet

/-! ### The Gaussian barrier on the annulus -/

/-- The Gaussian barrier `exp (-κ ‖z‖²) - exp (-κ)`, which vanishes on the unit sphere. -/
private def gaussBarrier (κ : ℝ) (z : E) : ℝ :=
  Real.exp (-κ * ‖z‖ ^ 2) - Real.exp (-κ)

private theorem contDiff_gaussBarrier (κ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (gaussBarrier (n := n) κ) := by
  have h : ContDiff ℝ k fun z : E => -κ * ‖z‖ ^ 2 := contDiff_const.mul (contDiff_norm_sq ℝ)
  exact (Real.contDiff_exp.comp h).sub contDiff_const

/-- On the annulus the Gaussian barrier is a strict classical subsolution of `div (A ∇·)`, with
margin `λ κ e^{-κ}`, once `κ ≥ 1` is large compared with the trace of `A` over its ellipticity
constant. -/
private theorem mul_exp_neg_le_divMatrixGradient_gaussBarrier
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam T κ : ℝ} (hlam : 0 ≤ lam)
    (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (hT : A.trace ≤ T) (hκ : 1 ≤ κ)
    (hκT : 2 * |T| + lam ≤ lam * κ) {z : E} (hz : 1 / 2 ≤ ‖z‖) (hz1 : ‖z‖ ≤ 1) :
    lam * κ * Real.exp (-κ) ≤ divMatrixGradient (fun _ => A) (gaussBarrier κ) z := by
  -- The second derivatives of the barrier are those of `exp (-κ ‖·‖²)`, computed explicitly.
  have hD : fderiv ℝ (gaussBarrier (n := n) κ) = fderiv ℝ fun w : E => Real.exp (-κ * ‖w‖ ^ 2) :=
    funext fun w => fderiv_sub_const _
  have hformula := sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq A κ 0 z 0
  simp only [sub_zero, map_zero, add_zero, inner_zero_right, mul_zero, WithLp.ofLp_zero]
    at hformula
  have h : lam * κ * Real.exp (-κ) ≤ ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ (gaussBarrier κ)) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    rw [hD, hformula]
    have hz2 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz1
    have hexp : Real.exp (-κ) ≤ Real.exp (-κ * ‖z‖ ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hz2 (zero_le_one.trans hκ)])
    have hT' : A.trace ≤ |T| := hT.trans (le_abs_self T)
    -- The factor `4 κ² Q(z) - 2 κ tr A` is at least `λ κ`, since `Q(z) ≥ λ ‖z‖² ≥ λ / 4`.
    have hQ : lam / 4 ≤ A.toQuadraticForm' z :=
      le_trans (by nlinarith [mul_le_mul_of_nonneg_left (show 1 / 4 ≤ ‖z‖ ^ 2 by nlinarith) hlam])
        (hA z)
    have hfac : lam * κ ≤ 4 * κ ^ 2 * A.toQuadraticForm' z - 2 * κ * A.trace := by
      nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 4 * κ ^ 2),
        mul_le_mul_of_nonneg_left hT' (by linarith : (0 : ℝ) ≤ 2 * κ),
        mul_le_mul_of_nonneg_left hκT (by linarith : (0 : ℝ) ≤ κ)]
    calc lam * κ * Real.exp (-κ) ≤ lam * κ * Real.exp (-κ * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hexp (by nlinarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
  have hdiff : Differentiable ℝ (fderiv ℝ (gaussBarrier (n := n) κ)) :=
    ((contDiff_gaussBarrier κ (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      one_ne_zero
  rw [divMatrixGradient_eq_sum_fderiv_fderiv_apply (Omega := ⊤)
    ((contDiff_gaussBarrier κ).contDiffOn) (mem_univ z)]
  refine h.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  rw [fderiv_clm_apply (hdiff z) (differentiableAt_const _)]
  simp

/-- **The barrier is a strict weak subsolution.** A Sobolev function on the annulus equal to the
Gaussian barrier satisfies `∫ ⟨A ∇Φ, ∇v⟩ ≤ -λ κ e^{-κ} ∫ v` for every nonnegative `v ∈ H¹₀`. -/
private theorem energyFormH1_gaussBarrier_le {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam T κ : ℝ} (hlam : 0 ≤ lam) (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hT : A.trace ≤ T) (hκ : 1 ≤ κ) (hκT : 2 * |T| + lam ≤ lam * κ)
    {W : W1p volume (unitAnnulus (n := n)) 2}
    (hW : W1p.value W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] gaussBarrier κ)
    (v : W1p0 volume (unitAnnulus (n := n)) 2)
    (hv : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      0 ≤ W1p.value (v : W1p volume (unitAnnulus (n := n)) 2) z) :
    energyFormH1 (fun _ => A) 0 0 W (v : W1p volume (unitAnnulus (n := n)) 2) ≤
      -(lam * κ * Real.exp (-κ)) * ∫ z in (unitAnnulus (n := n) : Set E),
        W1p.value (v : W1p volume (unitAnnulus (n := n)) 2) z := by
  set f : E → ℝ := fun z => -divMatrixGradient (fun _ => A) (gaussBarrier κ) z
  have hcont : ContinuousOn f (closedBall 0 1) :=
    (continuousOn_divMatrixGradient (Omega := ⊤) (A := A)
      (contDiff_gaussBarrier (n := n) κ).contDiffOn).neg.mono (subset_univ _)
  have hf : MemLp f 2 (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    hcont.memLp_restrict_of_subset_isCompact (isCompact_closedBall 0 1)
      unitAnnulus.isOpen.measurableSet unitAnnulus_subset_closedBall 2
  have hweak := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction
    (memLp_energyIntegrand_const_zero_zero A) (hf.toLp f) W).2 (fun φ => by
      rw [ContDiffOn.energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_divMatrixGradient
        (contDiff_gaussBarrier κ).contDiffOn
        (fun i => ((contDiff_gaussBarrier (k := 2) κ).contDiffOn).matrixBilinearForm_gradient _) hW
        φ, ← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with z hz
      rw [hz]
      simp [f, mul_comm]) v
  rw [hweak, ← integral_const_mul]
  refine integral_mono_ae ((Lp.memLp _).integrable_mul (Lp.memLp _))
    (((Lp.memLp _).integrable one_le_two).const_mul _) ?_
  filter_upwards [hf.coeFn_toLp, hv, ae_restrict_mem unitAnnulus.isOpen.measurableSet]
    with z hz hvz hzD
  rw [hz]
  have hmargin := mul_exp_neg_le_divMatrixGradient_gaussBarrier hlam hA hT hκ hκT
    (mem_unitAnnulus.1 hzD).2.le (mem_unitAnnulus.1 hzD).1.le
  simp only [f]
  nlinarith

/-! ### The correction of the frozen barrier -/

private theorem contDiff_gradient_gaussBarrier (κ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (∇ (gaussBarrier (n := n) κ)) :=
  (InnerProductSpace.toDual ℝ E).symm.contDiff.comp
    ((contDiff_gaussBarrier κ (k := k + 1)).fderiv_right le_rfl)

/-- On the closed unit ball the gradient of the barrier is bounded and Hölder continuous. -/
private theorem exists_holderOnWith_gradient_gaussBarrier (κ : ℝ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ K B : ℝ≥0, HolderOnWith K α (∇ (gaussBarrier (n := n) κ)) (closedBall 0 1) ∧
      ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ B := by
  have hc : ContDiff ℝ 1 (∇ (gaussBarrier (n := n) κ)) := contDiff_gradient_gaussBarrier κ
  obtain ⟨L, hL⟩ := hc.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 1)
    (isCompact_closedBall 0 1)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    hc.continuous.continuousOn
  exact ⟨_, B.toNNReal, hL.holderOnWith_of_norm_le
    (fun z hz => (hB z hz).trans (Real.le_coe_toNNReal B)) hα,
    fun z hz => (hB z hz).trans (Real.le_coe_toNNReal B)⟩

/-- The correction field `(b - A) ∇Φ`: the defect of the barrier `Φ` for the frozen matrix `A`
when tested against the coefficients `b`. -/
private def correctionField (b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (κ : ℝ) (z : E) : E :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (b z - A) (∇ (gaussBarrier κ) z)

private theorem inner_correctionField (b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (κ : ℝ) (z η : E) :
    ⟪correctionField b A κ z, η⟫_ℝ = matrixBilinearForm (b z) η (∇ (gaussBarrier κ) z) -
      matrixBilinearForm A η (∇ (gaussBarrier κ) z) := by
  rw [correctionField, real_inner_comm, Matrix.inner_toEuclideanCLM, matrixBilinearForm_apply,
    matrixBilinearForm_apply, Matrix.sub_mulVec, dotProduct_sub]

/-- The correction field is small with the oscillation of `b` about `A`: if
`‖b - A‖ ≤ η` and `b` is `α`-Hölder with constant at most `η` on the closed unit ball, the field
is bounded by `η B` and `α`-Hölder with constant `η (K + B)`, for the bound `B` and Hölder
constant `K` of the gradient of the barrier. -/
private theorem holderOnWith_correctionField {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {κ : ℝ} {α K B Kb : ℝ≥0} {η : ℝ}
    (hK : HolderOnWith K α (∇ (gaussBarrier (n := n) κ)) (closedBall 0 1))
    (hB : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ B)
    (hb : HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1))
    (hKb : (Kb : ℝ) ≤ η)
    (hbA : ∀ z ∈ closedBall (0 : E) 1, ‖matrixBilinearForm (b z) - matrixBilinearForm A‖ ≤ η) :
    HolderOnWith (η * (K + B)).toNNReal α (correctionField b A κ) (closedBall 0 1) ∧
      ∀ z ∈ closedBall (0 : E) 1, ‖correctionField b A κ z‖ ≤ η * B := by
  have hη : 0 ≤ η := Kb.coe_nonneg.trans hKb
  have hnorm (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ = ‖matrixBilinearForm M‖ :=
    (norm_matrixBilinearForm_eq_norm_toEuclideanCLM M).symm
  have hf : HolderOnWith Kb α (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (b z - A))
      (closedBall 0 1) :=
    HolderOnWith.of_dist_le fun x hx y hy => by
      rw [dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right, hnorm, matrixBilinearForm_sub]
      simpa only [dist_eq_norm] using hb.dist_le hx hy
  have hfn : ∀ z ∈ closedBall (0 : E) 1,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (b z - A)‖ ≤ η.toNNReal := fun z hz => by
    rw [hnorm, matrixBilinearForm_sub, Real.coe_toNNReal _ hη]
    exact hbA z hz
  have h := (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).holderOnWith_comp₂ hf hK hfn hB
  refine ⟨h.mono_const ?_, fun z hz => ?_⟩
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
    push_cast
    rw [Real.coe_toNNReal _ hη]
    have hid : ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h0 : 0 ≤ η * K + B * Kb := by positivity
    calc ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ * (η * K + B * Kb) ≤ 1 * (η * K + B * η) :=
          mul_le_mul hid (by gcongr) h0 zero_le_one
      _ = η * (K + B) := by ring
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [hnorm, matrixBilinearForm_sub]
    exact mul_le_mul (hbA z hz) (hB z hz) (norm_nonneg _) hη

/-- The energy form of coefficients uniformly elliptic on an open subset of the unit ball is
coercive on `H¹₀`, with constant `λ / 10` from the Poincaré inequality in the unit ball. -/
private theorem div_ten_mul_norm_sq_le_energyFormH1 {Ω : Opens E} (hΩ : (Ω : Set E) ⊆ ball 0 1)
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (hb : UniformlyEllipticOn (Ω : Set E) b lam Lam)
    (hm : AEStronglyMeasurable b (volume.restrict (Ω : Set E))) (w : W1p0 volume Ω 2) :
    lam / 10 * ‖w‖ ^ 2 ≤ energyFormH1 b 0 0 (w : W1p volume Ω 2) (w : W1p volume Ω 2) := by
  have h := hb.mul_norm_sq_le_energyFormH1_self_of_subset_ball (b := 0) (c := 0) (beta := 0)
    (gamma := 0) hm aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ => le_rfl) hΩ w.property
  refine (le_of_eq ?_).trans h
  have := hb.pos
  congr 1
  field_simp
  ring

/-- **The correction.** For coefficients `b`, uniformly elliptic and continuous on the closed unit
ball, there is `ψ ∈ H¹₀` of the unit ball solving `-div (b ∇ψ) = div ((b - A) ∇Φ)`, with
`‖ψ‖ ≤ (λ / 10)⁻¹ ‖(b - A) ∇Φ‖_{L²}`. -/
private theorem exists_correction_of_uniformlyEllipticOn
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {κ lam Lam : ℝ} (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hbc : ContinuousOn b (closedBall 0 1))
    (hH : ContinuousOn (correctionField b A κ) (closedBall 0 1)) :
    ∃ ψ : W1p0 volume (unitBall (n := n)) 2,
      (∀ v : W1p0 volume (unitBall (n := n)) 2,
        energyFormH1 b 0 0 (ψ : W1p volume unitBall 2) (v : W1p volume unitBall 2) =
          -∫ z in (unitBall (n := n) : Set E),
            ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitBall 2) z⟫_ℝ) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ z ∈ closedBall (0 : E) 1, ‖correctionField b A κ z‖ ≤ M) →
        ‖ψ‖ ≤ 10 / lam * ((measureUnivNNReal (volume.restrict (unitBall (n := n) : Set E)) : ℝ) ^
          ((2 : ℝ≥0∞).toReal⁻¹) * M) := by
  have hbD := hb.mono_set (ball_subset_closedBall : (unitBall (n := n) : Set E) ⊆ closedBall 0 1)
  have hm := aestronglyMeasurable_restrict_of_subset_closedBall (Ω := unitBall)
    ball_subset_closedBall hbc
  have hHL : MemLp (correctionField b A κ) 2 (volume.restrict (unitBall (n := n) : Set E)) :=
    hH.memLp_restrict_of_subset_isCompact (isCompact_closedBall 0 1)
      unitBall.isOpen.measurableSet ball_subset_closedBall 2
  obtain ⟨ψ, hψ⟩ := hbD.exists_forall_energyFormH1_eq_divergence_of_measure_ne_top hm
    measure_ball_lt_top.ne hHL
  refine ⟨ψ, hψ, fun M hM hHM => ?_⟩
  have := hb.pos
  -- The `L²` norm of the field is at most `V M`, and `(λ / 10) ‖ψ‖² ≤ a(ψ, ψ) ≤ ‖H‖_{L²} ‖ψ‖`.
  have hL2 : ‖hHL.toLp (correctionField b A κ)‖ ≤
      (measureUnivNNReal (volume.restrict (unitBall (n := n) : Set E)) : ℝ) ^
        ((2 : ℝ≥0∞).toReal⁻¹) * M := by
    refine Lp.norm_le_of_ae_bound hM ?_
    filter_upwards [hHL.coeFn_toLp, ae_restrict_mem unitBall.isOpen.measurableSet] with z h1 h2
    rw [h1]
    exact hHM z (ball_subset_closedBall h2)
  have hcoer := div_ten_mul_norm_sq_le_energyFormH1 subset_rfl hbD hm ψ
  have henergy : energyFormH1 b 0 0 (ψ : W1p volume unitBall 2) (ψ : W1p volume unitBall 2)
      ≤ ‖hHL.toLp (correctionField b A κ)‖ * ‖ψ‖ := by
    rw [hψ ψ, ← divergenceForcing_toLp_apply hHL ψ]
    exact (le_abs_self _).trans (norm_divergenceForcing_apply_le _ ψ)
  have hX : lam / 10 * ‖ψ‖ ≤ (measureUnivNNReal (volume.restrict (unitBall (n := n) : Set E)) :
      ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * M := by
    rcases (norm_nonneg ψ).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      positivity
    · nlinarith [hcoer.trans henergy]
  calc ‖ψ‖ = 10 / lam * (lam / 10 * ‖ψ‖) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)

/-- **Lipschitz representatives vanish on the unit sphere.** If the gradient of `ψ ∈ H¹₀` of the
unit ball is bounded by `M`, then `ψ` has a representative that is `M`-Lipschitz on the closed unit
ball and vanishes on the unit sphere. -/
private theorem exists_lipschitzOnWith_closedBall_of_ae_norm_gradient_le
    (ψ : W1p0 volume (unitBall (n := n)) 2) {M : ℝ≥0}
    (hM : ∀ᵐ z ∂volume.restrict (unitBall (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume unitBall 2) z‖ ≤ M) :
    ∃ ψ' : E → ℝ,
      W1p.value (ψ : W1p volume unitBall 2) =ᵐ[volume.restrict (unitBall (n := n) : Set E)] ψ' ∧
        LipschitzOnWith M ψ' (closedBall 0 1) ∧ ∀ z ∈ sphere (0 : E) 1, ψ' z = 0 := by
  have hM' : ∀ x : E, ∀ᵐ z ∂volume, z ∈ (unitBall (n := n) : Set E) ∩ ball x 3 →
      ‖W1p.gradient (ψ : W1p volume unitBall 2) z‖ ≤ M := fun x => by
    filter_upwards [(ae_restrict_iff' unitBall.isOpen.measurableSet).1 hM] with z hz hzB
    exact hz hzB.1
  -- At each point `x` of the sphere, a representative vanishing at `x`, Lipschitz on `B(x, 3)`.
  have hrep : ∀ x ∈ sphere (0 : E) 1, ∃ ψ' : E → ℝ,
      W1p.value (ψ : W1p volume unitBall 2) =ᵐ[volume.restrict (unitBall (n := n) : Set E)] ψ' ∧
        LipschitzOnWith M ψ' (closedBall 0 1) ∧ ψ' x = 0 := fun x hx => by
    obtain ⟨ψ', hae, hLip, h0⟩ := W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le
      isClosed_closedBall ball_subset_closedBall ψ (x := x)
      (by rw [closure_compl, interior_closedBall _ one_ne_zero]; simpa using hx.ge) three_pos
      (hM' x)
    refine ⟨ψ', hae, hLip.mono fun z hz => ?_, h0⟩
    rw [mem_ball, dist_comm]
    calc dist x z ≤ ‖x‖ + ‖z‖ := dist_le_norm_add_norm x z
      _ < 3 := by rw [mem_sphere_zero_iff_norm.1 hx]; linarith [mem_closedBall_zero_iff.1 hz]
  obtain ⟨ψ', hae, hLip, -⟩ := hrep (EuclideanSpace.single 0 1) (by simp)
  refine ⟨ψ', hae, hLip, fun x hx => ?_⟩
  obtain ⟨ψx, haex, hLipx, h0x⟩ := hrep x hx
  -- Two representatives continuous on the closed ball agree there.
  have hEq : EqOn ψ' ψx (closedBall 0 1) :=
    (Measure.eqOn_open_of_ae_eq (μ := volume) (hae.symm.trans haex) isOpen_ball
      (hLip.continuousOn.mono ball_subset_closedBall)
      (hLipx.continuousOn.mono ball_subset_closedBall)).of_subset_closure hLip.continuousOn
      hLipx.continuousOn ball_subset_closedBall (closure_ball 0 one_ne_zero).ge
  rw [hEq (sphere_subset_closedBall hx), h0x]

/-- **The correction is small.** Fix an exponent `0 < α ≤ 1`, ellipticity constants and `κ`. There
is `C ≥ 0` such that for every coefficient field `b`, uniformly elliptic on the closed unit ball
with these constants and `α`-Hölder there with constant at most `η ≤ 1`, and every matrix `A` with
`‖b - A‖ ≤ η` there, the correction `ψ ∈ H¹₀` of the unit ball of
`exists_correction_of_uniformlyEllipticOn` has gradient bounded by `C η` almost everywhere, and a
representative that is `C η`-Lipschitz on the closed unit ball and vanishes on the unit sphere.
This is the global `C^{1,β}` estimate on the unit ball applied to the correction. -/
private theorem exists_correction {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) {lam : ℝ} (hlam : 0 < lam)
    (Lam κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Kb : ℝ≥0} {η : ℝ},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ η →
      η ≤ 1 → (∀ z ∈ closedBall (0 : E) 1,
        ‖matrixBilinearForm (b z) - matrixBilinearForm A‖ ≤ η) →
      ∃ ψ : W1p0 volume (unitBall (n := n)) 2, ∃ ψ' : E → ℝ,
        (∀ v : W1p0 volume (unitBall (n := n)) 2,
          energyFormH1 b 0 0 (ψ : W1p volume unitBall 2) (v : W1p volume unitBall 2) =
            -∫ z in (unitBall (n := n) : Set E),
              ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitBall 2) z⟫_ℝ) ∧
        (∀ᵐ z ∂volume.restrict (unitBall (n := n) : Set E),
          ‖W1p.gradient (ψ : W1p volume unitBall 2) z‖ ≤ C * η) ∧
        W1p.value (ψ : W1p volume unitBall 2) =ᵐ[volume.restrict (unitBall (n := n) : Set E)]
          ψ' ∧ LipschitzOnWith (C * η).toNNReal ψ' (closedBall 0 1) ∧
        ∀ z ∈ sphere (0 : E) 1, ψ' z = 0 := by
  obtain ⟨K, B, hK, hB⟩ := exists_holderOnWith_gradient_gaussBarrier (n := n) κ hα1
  have he₀ : ‖(EuclideanSpace.single 0 1 : E)‖ = 1 := by simp
  obtain ⟨Kγ, hγK⟩ := exists_holderWith_fderiv_unitSphereGraph
    (K := (ℝ ∙ (EuclideanSpace.single 0 1 : E))ᗮ) hα1
  set β : ℝ≥0 := min α (1 / 2)
  have hβ : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β < 1 := (min_le_right _ _).trans_lt (by norm_num)
  -- The global `C^{1,β}` estimate on the unit ball, with the sphere charts of one model space.
  obtain ⟨C₀, hC₀, H⟩ := exists_holderOnWith_gradient_closure_of_isBounded (n := n) hβ hβ1
    (min_le_left _ _) (q := ⊤) le_top (by simp [hβ1.le]) (Ω := unitBall) isBounded_ball
    (fun x hx => by
      rw [coe_unitBall, frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hx
      obtain ⟨e, hex, hiff⟩ := exists_affineIsometryEquiv_unitSphereGraph_chart he₀ hx
      exact ⟨e, unitSphereGraph, 1 / 4, 1 / 4, Kγ, hex, by norm_num, by norm_num,
        unitSphereGraph_zero, contDiff_unitSphereGraph, hγK, hiff⟩) lam Lam 1
  -- The volume factor in the `L²` bound of the correction field.
  set V : ℝ := (measureUnivNNReal (volume.restrict (unitBall (n := n) : Set E)) : ℝ) ^
    ((2 : ℝ≥0∞).toReal⁻¹)
  have : 0 ≤ V := by positivity
  set C := C₀ * ((K + B) + 10 / lam * (V * B))
  refine ⟨C, by positivity, fun {b A Kb η} hb hbh hKb hη1 hbA => ?_⟩
  have hη : 0 ≤ η := Kb.coe_nonneg.trans hKb
  obtain ⟨hHh, hHb⟩ := holderOnWith_correctionField (κ := κ) hK hB hbh hKb hbA
  obtain ⟨ψ, hψ, hψn⟩ := exists_correction_of_uniformlyEllipticOn hb
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα)) (hHh.continuousOn hα)
  have hψb := hψn (η * B) (by positivity) hHb
  -- The estimate for the equation `-div (b ∇ψ) = -div (-(b - A) ∇Φ)`.
  obtain ⟨g, hg, -, hgb⟩ := H (u := ψ) (a := b) (G := -correctionField b A κ) (f := 0)
    (Ka := Kb) (KG := (η * (K + B)).toNNReal) (by rw [closure_unitBall]; exact hb)
    (by rw [closure_unitBall]; exact hbh) (hKb.trans hη1)
    (by rw [closure_unitBall]; exact hHh.neg) MemLp.zero (fun φ => by
      rw [hψ ⟨W1p.ofTestFunctionₗ volume unitBall 2 φ, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
      simp only [Pi.neg_apply, inner_neg_left, integral_neg, Pi.zero_apply, zero_mul,
        integral_zero, add_zero]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with z hz
      rw [W1p.gradient_ofTestFunctionₗ, hz])
  have hgrad : ∀ᵐ z ∂volume.restrict (unitBall (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume unitBall 2) z‖ ≤ C * η := by
    filter_upwards [hg, ae_restrict_mem unitBall.isOpen.measurableSet] with z hz hzB
    rw [hz]
    refine (hgb z (subset_closure hzB)).trans ?_
    rw [Real.coe_toNNReal _ (by positivity), eLpNorm_zero, ENNReal.toReal_zero, add_zero]
    calc C₀ * (η * (K + B) + ‖ψ‖) ≤ C₀ * (η * (K + B) + 10 / lam * (V * (η * B))) := by gcongr
      _ = C * η := by ring
  obtain ⟨ψ', hae, hLip, h0⟩ := exists_lipschitzOnWith_closedBall_of_ae_norm_gradient_le ψ
    (M := (C * η).toNNReal) (by
      filter_upwards [hgrad] with z hz
      exact hz.trans (Real.le_coe_toNNReal _))
  exact ⟨ψ, ψ', hψ, hgrad, hae, hLip, h0⟩

/-! ### The comparison -/

/-- The corrected barrier `W + ψ` has, for the coefficients `b`, the energy that the barrier `W`
has for the frozen matrix `A`. -/
private theorem energyFormH1_add_correction {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {κ : ℝ}
    (hcb : MemLp (fun z => energyIntegrand (b z) ((0 : E → E) z) ((0 : E → ℝ) z)) ⊤
      (volume.restrict (unitBall (n := n) : Set E)))
    {W : W1p volume (unitBall (n := n)) 2}
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitBall (n := n) : Set E)] ∇ (gaussBarrier κ))
    {ψ : W1p volume (unitBall (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitBall (n := n)) 2,
      energyFormH1 b 0 0 ψ (v : W1p volume unitBall 2) =
        -∫ z in (unitBall (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitBall 2) z⟫_ℝ)
    (v : W1p0 volume (unitBall (n := n)) 2) :
    energyFormH1 b 0 0 (W + ψ) (v : W1p volume unitBall 2) =
      energyFormH1 (fun _ => A) 0 0 W (v : W1p volume unitBall 2) := by
  have hcA := memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := unitBall (n := n)) A
  have hsub := energyFormH1_sub hcb hcA W (v : W1p volume unitBall 2)
  simp only [sub_self] at hsub
  -- The energy of `W` for `b - A` is the pairing of the correction field with `∇v`.
  have hpair : energyFormH1 (b - fun _ => A) 0 0 W (v : W1p volume unitBall 2) =
      ∫ z in (unitBall (n := n) : Set E),
        ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitBall 2) z⟫_ℝ := by
    rw [energyFormH1_zero_zero_eq_setIntegral]
    refine integral_congr_ae ?_
    filter_upwards [hWg] with z hz
    rw [hz, inner_correctionField, Pi.sub_apply, matrixBilinearForm_sub, sub_apply, sub_apply]
  rw [energyFormH1_add_left hcb, hψ v, ← hpair, hsub]
  ring

/-- Along the inward normal at a point `ν` of the unit sphere the Gaussian barrier grows at least
linearly: `κ e^{-κ} t ≤ Φ((1 - t) ν)` for `0 ≤ t ≤ 1`. -/
private theorem mul_le_gaussBarrier_smul {κ : ℝ} (hκ : 0 ≤ κ) {ν : E} (hν : ‖ν‖ = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : κ * Real.exp (-κ) * t ≤ gaussBarrier κ ((1 - t) • ν) := by
  rw [gaussBarrier, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  simpa using mul_exp_neg_mul_sq_mul_le_exp_neg_mul_sub_sq_sub hκ ht0 ht1

/-- On the closed unit ball the Gaussian barrier is at most `1`. -/
private theorem gaussBarrier_le_one {κ : ℝ} (hκ : 0 ≤ κ) (z : E) : gaussBarrier κ z ≤ 1 := by
  have h1 : Real.exp (-κ * ‖z‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg z])
  have h2 := Real.exp_pos (-κ)
  rw [gaussBarrier]
  linarith

/-- The comparison function `s₀ + θ (W + ψ)` on the annulus, for a Sobolev representative `W` of
the Gaussian barrier `Φ` and the correction `ψ` on the unit ball, is almost everywhere
`s₀ + θ (Φ + ψ)`, and its gradient is almost everywhere `θ (∇Φ + ∇ψ)`. -/
private theorem value_gradient_smul_restrictL_add_add_const_ae {κ : ℝ}
    {W : W1p volume (unitBall (n := n)) 2}
    (hWv : W1p.value W =ᵐ[volume.restrict (unitBall (n := n) : Set E)] gaussBarrier κ)
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitBall (n := n) : Set E)] ∇ (gaussBarrier κ))
    (θ : ℝ) (ψ : W1p volume (unitBall (n := n)) 2) (s₀ : ℝ) :
    (W1p.value (θ • W1p.restrictL unitAnnulus_le_unitBall (W + ψ) + W1p.const s₀)
        =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => θ * (gaussBarrier κ z + W1p.value ψ z) + s₀) ∧
    W1p.gradient (θ • W1p.restrictL unitAnnulus_le_unitBall (W + ψ) + W1p.const s₀)
        =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => θ • (∇ (gaussBarrier κ) z + W1p.gradient ψ z) := by
  have hsub {p : E → Prop} (h : ∀ᵐ z ∂volume.restrict (unitBall (n := n) : Set E), p z) :
      ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E), p z :=
    ae_restrict_of_ae_restrict_of_subset unitAnnulus_subset_ball h
  constructor
  · filter_upwards [W1p.value_add_const_ae (θ • W1p.restrictL unitAnnulus_le_unitBall (W + ψ)) s₀,
      W1p.value_smul_ae θ (W1p.restrictL unitAnnulus_le_unitBall (W + ψ)),
      W1p.value_restrictL_ae unitAnnulus_le_unitBall (W + ψ), hsub (W1p.value_add_ae W ψ),
      hsub hWv] with z e1 e2 e3 e4 e5
    simp only [e1, e2, Pi.smul_apply, smul_eq_mul, e3, e4, Pi.add_apply, e5]
  · rw [W1p.gradient_add_const]
    filter_upwards [W1p.gradient_smul_ae θ (W1p.restrictL unitAnnulus_le_unitBall (W + ψ)),
      W1p.gradient_restrictL_ae unitAnnulus_le_unitBall (W + ψ),
      hsub (W1p.gradient_add_ae W ψ), hsub hWg] with z e1 e2 e3 e4
    simp only [e1, Pi.smul_apply, e2, e3, Pi.add_apply, e4]

/-- **The lower-order terms at the corrected barrier.** For a drift `‖β‖ ≤ δ`, a mass coefficient
`0 ≤ c ≤ γ` with `c s₀ ≤ 0`, and `|ψ|`, `‖∇ψ‖` and `‖∇Φ‖` bounded by `Ψ`, the lower-order terms
of `s₀ + θ (Φ + ψ)`, `θ ≥ 0`, are at most `θ (δ + γ) (1 + 2 Ψ)`. -/
private theorem inner_add_mul_le {κ δ γ Ψ θ s₀ : ℝ} (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) {β ζ : E}
    {c ψ : ℝ} {z : E} (hβ : ‖β‖ ≤ δ) (hc0 : 0 ≤ c) (hcγ : c ≤ γ) (hcs : c * s₀ ≤ 0)
    (hψ : |ψ| ≤ Ψ) (hζ : ‖ζ‖ ≤ Ψ) (hΦ : ‖∇ (gaussBarrier κ) z‖ ≤ Ψ) :
    ⟪β, θ • (∇ (gaussBarrier κ) z + ζ)⟫_ℝ + c * (θ * (gaussBarrier κ z + ψ) + s₀) ≤
      θ * ((δ + γ) * (1 + 2 * Ψ)) := by
  have hΨ : 0 ≤ Ψ := (abs_nonneg _).trans hψ
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hβ
  -- The drift term is at most `θ δ 2Ψ`.
  have hdrift : ⟪β, θ • (∇ (gaussBarrier κ) z + ζ)⟫_ℝ ≤ θ * (δ * (2 * Ψ)) := by
    rw [inner_smul_right]
    refine mul_le_mul_of_nonneg_left ((real_inner_le_norm _ _).trans ?_) hθ
    exact mul_le_mul hβ ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _) hδ
  -- The mass term is at most `θ γ (1 + Ψ)`.
  have hmass : c * (θ * (gaussBarrier κ z + ψ) + s₀) ≤ θ * (γ * (1 + Ψ)) := by
    have h3 : c * (gaussBarrier κ z + ψ) ≤ γ * (1 + Ψ) :=
      (mul_le_mul_of_nonneg_left (by linarith [gaussBarrier_le_one hκ z, le_abs_self ψ]) hc0).trans
        (mul_le_mul_of_nonneg_right hcγ (by linarith))
    nlinarith [mul_le_mul_of_nonneg_left h3 hθ]
  nlinarith [mul_nonneg hθ (mul_nonneg hδ hΨ), mul_nonneg hθ (mul_nonneg (hc0.trans hcγ) hΨ)]

/-- **The lower-order terms at the corrected barrier, integrated.** If `V ∈ H¹` of the annulus has
value `s₀ + θ (Φ + ψ)` and gradient `θ (∇Φ + ∇ψ)`, with `|ψ|`, `‖∇ψ‖` and `‖∇Φ‖` bounded by `Ψ`,
then for a drift `‖β‖ ≤ δ` and a mass coefficient `0 ≤ c ≤ γ` with `c s₀ ≤ 0` the lower-order terms
`∫ c V w + ∫ (β · ∇V) w` are at most `θ (δ + γ) (1 + 2 Ψ) ∫ w` for every nonnegative `w`. -/
private theorem setIntegral_mul_add_setIntegral_inner_le {β : E → E} {c : E → ℝ}
    {κ δ γ Ψ θ s₀ : ℝ} (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hβL : MemLp β ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hcL : MemLp c ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hβδ : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖β z‖ ≤ δ)
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z)
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ)
    (hcs : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0)
    (hΦg : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ Ψ)
    {V : W1p volume (unitAnnulus (n := n)) 2} {ψv : E → ℝ} {ψg : E → E}
    (hVv : W1p.value V =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => θ * (gaussBarrier κ z + ψv z) + s₀)
    (hVg : W1p.gradient V =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => θ • (∇ (gaussBarrier κ) z + ψg z))
    (hψv : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E), |ψv z| ≤ Ψ)
    (hψg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E), ‖ψg z‖ ≤ Ψ)
    (w : W1p0 volume (unitAnnulus (n := n)) 2)
    (hw : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      0 ≤ W1p.value (w : W1p volume unitAnnulus 2) z) :
    (∫ z in (unitAnnulus (n := n) : Set E),
      c z * W1p.value V z * W1p.value (w : W1p volume unitAnnulus 2) z) +
      ∫ z in (unitAnnulus (n := n) : Set E),
        ⟪β z, W1p.gradient V z⟫_ℝ * W1p.value (w : W1p volume unitAnnulus 2) z ≤
      θ * ((δ + γ) * (1 + 2 * Ψ)) * ∫ z in (unitAnnulus (n := n) : Set E),
        W1p.value (w : W1p volume unitAnnulus 2) z := by
  have hcV : MemLp (fun z => c z * W1p.value V z) 2
      (volume.restrict (unitAnnulus (n := n) : Set E)) := hcL.fun_mul (Lp.memLp _)
  have hint1 : Integrable
      (fun z => c z * W1p.value V z * W1p.value (w : W1p volume unitAnnulus 2) z)
      (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    hcV.integrable_mul (Lp.memLp _)
  have hint2 : Integrable (fun z => ⟪β z, W1p.gradient V z⟫_ℝ *
      W1p.value (w : W1p volume unitAnnulus 2) z)
      (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    (memLp_inner_gradient hβL V).integrable_mul (Lp.memLp _)
  rw [← integral_add hint1 hint2, ← integral_const_mul]
  refine integral_mono_ae (hint1.add hint2)
    (((Lp.memLp _).integrable one_le_two).const_mul _) ?_
  filter_upwards [hVv, hVg, hψv, hψg, hw, ae_restrict_mem unitAnnulus.isOpen.measurableSet]
    with z e1 e2 e3 e4 e5 hz
  rw [e1, e2]
  have hpt := inner_add_mul_le hκ hθ (hβδ z hz) (hc0 z hz) (hcγ z hz) (hcs z hz) e3 e4
    (hΦg z (unitAnnulus_subset_closedBall hz))
  linear_combination mul_le_mul_of_nonneg_right hpt e5

/-- **The corrected barrier is a weak subsolution with lower-order terms.** Let `W ∈ H¹` of the
unit ball represent the Gaussian barrier `Φ` and let `ψ` be its correction, with `|ψ|`, `‖∇ψ‖` and
`‖∇Φ‖` bounded by `Ψ`. For a drift `‖β‖ ≤ δ`, a mass coefficient `0 ≤ c ≤ γ` with `c s₀ ≤ 0` and
`(δ + γ) (1 + 2 Ψ) ≤ λ κ e^{-κ}`, the function `s₀ + θ (W + ψ)`, `θ ≥ 0`, restricted to the annulus
satisfies `-div (b ∇·) + β · ∇· + c · ≤ 0` weakly there: the strict margin `λ κ e^{-κ}` of the
barrier absorbs the lower-order terms. -/
private theorem energyFormH1_add_mul_correction_nonpos
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {β : E → E} {c : E → ℝ} {κ lam Lam T δ γ Ψ : ℝ}
    (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hbc : ContinuousOn b (closedBall 0 1))
    (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (hT : A.trace ≤ T) (hκ : 1 ≤ κ)
    (hκT : 2 * |T| + lam ≤ lam * κ)
    (hβm : AEStronglyMeasurable β (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hβδ : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖β z‖ ≤ δ)
    (hcm : AEStronglyMeasurable c (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z)
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ)
    (hγ : (δ + γ) * (1 + 2 * Ψ) ≤ lam * κ * Real.exp (-κ))
    (hΦg : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ Ψ)
    {ψ : W1p0 volume (unitBall (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitBall (n := n)) 2,
      energyFormH1 b 0 0 (ψ : W1p volume unitBall 2) (v : W1p volume unitBall 2) =
        -∫ z in (unitBall (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitBall 2) z⟫_ℝ)
    (hψb : ∀ᵐ z ∂volume.restrict (unitBall (n := n) : Set E),
      |W1p.value (ψ : W1p volume unitBall 2) z| ≤ Ψ)
    (hψg : ∀ᵐ z ∂volume.restrict (unitBall (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume unitBall 2) z‖ ≤ Ψ)
    {W : W1p volume (unitBall (n := n)) 2}
    (hWv : W1p.value W =ᵐ[volume.restrict (unitBall (n := n) : Set E)] gaussBarrier κ)
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitBall (n := n) : Set E)] ∇ (gaussBarrier κ))
    {s₀ θ : ℝ} (hcs : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0) (hθ : 0 ≤ θ)
    (w : W1p0 volume (unitAnnulus (n := n)) 2)
    (hw : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      0 ≤ W1p.value (w : W1p volume unitAnnulus 2) z) :
    energyFormH1 b β c (θ • W1p.restrictL unitAnnulus_le_unitBall
      (W + (ψ : W1p volume unitBall 2)) + W1p.const s₀) (w : W1p volume unitAnnulus 2) ≤ 0 := by
  set Vf := θ • W1p.restrictL unitAnnulus_le_unitBall (W + (ψ : W1p volume unitBall 2)) +
    W1p.const s₀
  have hD : MeasurableSet (unitAnnulus (n := n) : Set E) := unitAnnulus.isOpen.measurableSet
  have hm := aestronglyMeasurable_restrict_of_subset_closedBall unitAnnulus_subset_closedBall hbc
  have hbD := hb.mono_set unitAnnulus_subset_closedBall
  have hcb := hbD.memLp_energyIntegrand_zero_zero hm
  have hbB := hb.mono_set (ball_subset_closedBall : (unitBall (n := n) : Set E) ⊆ closedBall 0 1)
  have hcbB := hbB.memLp_energyIntegrand_zero_zero
    (aestronglyMeasurable_restrict_of_subset_closedBall (Ω := unitBall) ball_subset_closedBall hbc)
  have hβL : MemLp β ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    memLp_top_of_bound hβm δ ((ae_restrict_iff' hD).2 (ae_of_all _ hβδ))
  have hcL : MemLp c ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    memLp_top_of_bound hcm γ ((ae_restrict_iff' hD).2 (ae_of_all _ fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hc0 z hz)]
      exact hcγ z hz))
  -- The principal part is the energy of the barrier for the frozen matrix.
  have hWv' : W1p.value (W1p.restrictL unitAnnulus_le_unitBall W) =ᵐ[volume.restrict
      (unitAnnulus (n := n) : Set E)] gaussBarrier κ :=
    (W1p.value_restrictL_ae unitAnnulus_le_unitBall W).trans
      (ae_restrict_of_ae_restrict_of_subset unitAnnulus_subset_ball hWv)
  have hprin : energyFormH1 b 0 0 Vf (w : W1p volume unitAnnulus 2) = θ *
      energyFormH1 (fun _ => A) 0 0 (W1p.restrictL unitAnnulus_le_unitBall W) w := by
    rw [energyFormH1_add_const_left, energyFormH1_smul_left, energyFormH1_restrictL,
      energyFormH1_add_correction hcbB hWg hψ, ← energyFormH1_restrictL]
  have hΦ := energyFormH1_gaussBarrier_le hb.pos.le hA hT hκ hκT hWv' w hw
  -- The lower-order terms are at most `θ λ κ e^{-κ} ∫ w`.
  obtain ⟨hVv, hVg⟩ := value_gradient_smul_restrictL_add_add_const_ae hWv hWg θ
    (ψ : W1p volume unitBall 2) s₀
  have hlow := setIntegral_mul_add_setIntegral_inner_le (zero_le_one.trans hκ) hθ hβL hcL hβδ hc0
    hcγ hcs hΦg hVv hVg (ae_restrict_of_ae_restrict_of_subset unitAnnulus_subset_ball hψb)
    (ae_restrict_of_ae_restrict_of_subset unitAnnulus_subset_ball hψg) w hw
  have hint : 0 ≤ ∫ z in (unitAnnulus (n := n) : Set E),
      W1p.value (w : W1p volume unitAnnulus 2) z :=
    integral_nonneg_of_ae hw
  rw [energyFormH1_eq_energyFormH1_zero_add_setIntegral_inner hcb hβL hcL,
    energyFormH1_eq_energyFormH1_zero_add_setIntegral (b := 0) hcb hcL, hprin]
  nlinarith [mul_le_mul_of_nonneg_left hΦ hθ, mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hγ hθ) hint]

/-- **Boundary values of the comparison.** If `V ∈ H¹` of the annulus has value
`s₀ + θ (Φ + ψ')`, for `ψ'` continuous on the closed unit ball and vanishing on the unit sphere,
and `uε` has value `ĝ`, continuous on the closed unit ball, with `s₀ ≤ ĝ` on the outer sphere and
`s₀ + θ (Φ + ψ') ≤ ĝ` on the inner one, then `(V - uε)⁺ ∈ H¹₀` of the annulus. -/
private theorem posPart_sub_mem_w1p0Submodule {κ θ s₀ : ℝ} {ψ' ĝ : E → ℝ}
    (hψ'c : ContinuousOn ψ' (closedBall 0 1)) (hψ'0 : ∀ z ∈ sphere (0 : E) 1, ψ' z = 0)
    (hĝ : ContinuousOn ĝ (closedBall 0 1)) (h1 : ∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z)
    (h2 : ∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * (gaussBarrier κ z + ψ' z) ≤ ĝ z)
    {V uε : W1p volume (unitAnnulus (n := n)) 2}
    (hV : W1p.value V =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => s₀ + θ * (gaussBarrier κ z + ψ' z))
    (huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ) :
    W1p.posPart (by norm_num) (V - uε) ∈ w1p0Submodule volume unitAnnulus 2 := by
  have h := W1p.posPart_add_mem_w1p0Submodule (ψ := 0) (G := V - uε) (by norm_num)
    (isBounded_ball.subset unitAnnulus_subset_ball) (zero_mem _)
    (g := fun z => s₀ + θ * (gaussBarrier κ z + ψ' z) - ĝ z)
    (((continuousOn_const.add (continuousOn_const.mul
      ((contDiff_gaussBarrier κ (k := 0)).continuous.continuousOn.add hψ'c))).sub hĝ).mono
      closure_unitAnnulus_subset) (fun z hz => ?_) ?_
  · rwa [zero_add] at h
  · -- On the outer sphere `Φ` and `ψ'` vanish.
    rcases frontier_unitAnnulus_subset hz with h | h
    · have h0 : gaussBarrier κ z = 0 := by
        rw [gaussBarrier, mem_sphere_zero_iff_norm.1 h]
        simp
      rw [h0, hψ'0 z h, add_zero, mul_zero, add_zero]
      linarith [h1 z h]
    · linarith [h2 z h]
  · filter_upwards [W1p.value_sub_ae V uε, hV, huĝ] with z e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3]

/-- **The comparison on the annulus.** Let `uε ∈ H¹` of the annulus be a weak supersolution of
`-div (b ∇uε) + β · ∇uε + c uε ≥ 0` for coefficients `b`, uniformly elliptic and continuous on the
closed unit ball, a measurable drift `‖β‖ ≤ δ` with `2 δ < λ` and a measurable mass coefficient
`0 ≤ c ≤ γ`, and let `uε` equal almost everywhere a function `ĝ` continuous there. Let `ψ` be the
correction of the Gaussian barrier `Φ` on the unit ball, with a representative `ψ'` continuous on
the closed unit ball and vanishing on the unit sphere, and with `|ψ'|`, `‖∇ψ‖` and `‖∇Φ‖` bounded
by `Ψ`, where `(δ + γ) (1 + 2 Ψ) ≤ λ κ e^{-κ}`. If `ĝ ≥ s₀` on the outer sphere and
`ĝ ≥ s₀ + θ (Φ + ψ')` on the inner sphere, with `θ ≥ 0` and `c s₀ ≤ 0`, then
`s₀ + θ (Φ + ψ') ≤ ĝ` almost everywhere on the annulus. -/
private theorem ae_add_mul_le_of_supersolution {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {β : E → E} {c : E → ℝ} {κ lam Lam T δ γ Ψ : ℝ}
    (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hbc : ContinuousOn b (closedBall 0 1)) (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hT : A.trace ≤ T) (hκ : 1 ≤ κ) (hκT : 2 * |T| + lam ≤ lam * κ)
    (hβm : AEStronglyMeasurable β (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hβδ : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖β z‖ ≤ δ) (hδ : δ * 2 < lam)
    (hcm : AEStronglyMeasurable c (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z)
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ)
    (hγ : (δ + γ) * (1 + 2 * Ψ) ≤ lam * κ * Real.exp (-κ))
    (hΦg : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ Ψ)
    {ψ : W1p0 volume (unitBall (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitBall (n := n)) 2,
      energyFormH1 b 0 0 (ψ : W1p volume unitBall 2) (v : W1p volume unitBall 2) =
        -∫ z in (unitBall (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitBall 2) z⟫_ℝ)
    {ψ' : E → ℝ}
    (hψ' : W1p.value (ψ : W1p volume unitBall 2) =ᵐ[volume.restrict (unitBall (n := n) : Set E)]
      ψ')
    (hψ'c : ContinuousOn ψ' (closedBall 0 1)) (hψ'0 : ∀ z ∈ sphere (0 : E) 1, ψ' z = 0)
    (hψ'b : ∀ z ∈ closedBall (0 : E) 1, |ψ' z| ≤ Ψ)
    (hψg : ∀ᵐ z ∂volume.restrict (unitBall (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume unitBall 2) z‖ ≤ Ψ)
    {uε : W1p volume (unitAnnulus (n := n)) 2}
    (huε : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        0 ≤ W1p.value (v : W1p volume unitAnnulus 2) z) →
      0 ≤ energyFormH1 b β c uε (v : W1p volume unitAnnulus 2))
    {ĝ : E → ℝ} (hĝ : ContinuousOn ĝ (closedBall 0 1))
    (huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ) {s₀ θ : ℝ}
    (hcs : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0)
    (hθ : 0 ≤ θ) (h1 : ∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z)
    (h2 : ∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * (gaussBarrier κ z + ψ' z) ≤ ĝ z) :
    ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      s₀ + θ * (gaussBarrier κ z + ψ' z) ≤ ĝ z := by
  obtain ⟨W, hWv, hWg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    (Omega := unitBall (n := n)) (mu := volume) (p := 2) isOpen_univ
    (contDiff_gaussBarrier κ).contDiffOn (isCompact_closedBall 0 1) ball_subset_closedBall
    (subset_univ _)
  have hbD := hb.mono_set unitAnnulus_subset_closedBall
  have hm := aestronglyMeasurable_restrict_of_subset_closedBall unitAnnulus_subset_closedBall hbc
  have hcbd : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖c z‖ ≤ γ := fun z hz => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 z hz)]
    exact hcγ z hz
  have hψb : ∀ᵐ z ∂volume.restrict (unitBall (n := n) : Set E),
      |W1p.value (ψ : W1p volume unitBall 2) z| ≤ Ψ := by
    filter_upwards [hψ', ae_restrict_mem unitBall.isOpen.measurableSet] with z h hz
    rw [h]
    exact hψ'b z (ball_subset_closedBall hz)
  set Vf := θ • W1p.restrictL unitAnnulus_le_unitBall (W + (ψ : W1p volume unitBall 2)) +
    W1p.const s₀
  have huv : ∀ w : W1p0 volume (unitAnnulus (n := n)) 2,
      (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        0 ≤ W1p.value (w : W1p volume unitAnnulus 2) z) →
      energyFormH1 b β c Vf (w : W1p volume unitAnnulus 2) ≤
        energyFormH1 b β c uε (w : W1p volume unitAnnulus 2) := fun w hw =>
    (energyFormH1_add_mul_correction_nonpos hb hbc hA hT hκ hκT hβm hβδ hcm hc0 hcγ hγ hΦg hψ hψb
      hψg hWv hWg hcs hθ w hw).trans (huε w hw)
  have hVf : W1p.value Vf =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => s₀ + θ * (gaussBarrier κ z + ψ' z) := by
    filter_upwards [(value_gradient_smul_restrictL_add_add_const_ae hWv hWg θ
      (ψ : W1p volume unitBall 2) s₀).1,
      ae_restrict_of_ae_restrict_of_subset unitAnnulus_subset_ball hψ'] with z e1 e2
    rw [e1, e2]
    ring
  have hbd := posPart_sub_mem_w1p0Submodule hψ'c hψ'0 hĝ h1 h2 hVf huĝ
  have hcomp := hbD.value_le_of_small_drift_of_subset_ball hm hβm hcm hβδ hcbd hc0 (z := 0)
    (R := 1) unitAnnulus_subset_ball (by linarith) hbd huv
  filter_upwards [hcomp, hVf, huĝ] with z h e1 e2
  rwa [e1, e2] at h

/-- The Gaussian barrier depends only on the norm. -/
private theorem gaussBarrier_eq_of_norm_eq {κ : ℝ} {z w : E} (h : ‖z‖ = ‖w‖) :
    gaussBarrier κ z = gaussBarrier κ w := by
  rw [gaussBarrier, gaussBarrier, h]

/-- **From the comparison on the annulus to growth along the normal.** Let `ĝ` be continuous on
the closed unit ball and let `ψ'` be `L`-Lipschitz there, with `ψ' ν = 0` at a point `ν` of the
unit sphere and `L ≤ κ e^{-κ} / 4`. If `s₀ + θ (Φ + ψ') ≤ ĝ` almost everywhere on the annulus,
`θ ≥ 0`, then `s₀ + θ κ e^{-κ} t / 2 ≤ ĝ ((1 - t) ν)` for `0 < t < 1/2`: the barrier grows like
`κ e^{-κ} t` along the inward normal and the correction decreases at most like `L t`. -/
private theorem add_mul_le_of_ae_add_mul_le {ν : E} (hν : ‖ν‖ = 1) {κ θ s₀ : ℝ} (hκ : 0 ≤ κ)
    (hθ : 0 ≤ θ) {ψ' ĝ : E → ℝ} (hĝ : ContinuousOn ĝ (closedBall 0 1)) {L : ℝ≥0}
    (hLip : LipschitzOnWith L ψ' (closedBall 0 1)) (hψ'ν : ψ' ν = 0)
    (hL : (L : ℝ) ≤ κ * Real.exp (-κ) / 4)
    (hcomp : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      s₀ + θ * (gaussBarrier κ z + ψ' z) ≤ ĝ z) :
    ∀ t ∈ Ioo 0 (1 / 2), s₀ + θ * (κ * Real.exp (-κ) / 2) * t ≤ ĝ ((1 - t) • ν) := by
  intro t ht
  -- On the open annulus the comparison holds pointwise, by continuity.
  set F : E → ℝ := fun z => max (s₀ + θ * (gaussBarrier κ z + ψ' z) - ĝ z) 0
  have hF : ContinuousOn F (unitAnnulus (n := n) : Set E) :=
    (((continuousOn_const.add (continuousOn_const.mul
      ((contDiff_gaussBarrier κ (k := 0)).continuous.continuousOn.add hLip.continuousOn))).sub
      hĝ).mono unitAnnulus_subset_closedBall).sup continuousOn_const
  have hF0 : EqOn F 0 (unitAnnulus (n := n) : Set E) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ unitAnnulus.isOpen hF continuousOn_const
    filter_upwards [hcomp] with z h
    exact max_eq_right (by linarith)
  have ht0 := ht.1
  have hzt : (1 - t) • ν ∈ (unitAnnulus (n := n) : Set E) := by
    refine mem_unitAnnulus.2 ?_
    rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
    constructor <;> linarith [ht.2]
  have hFz := hF0 hzt
  simp only [F, Pi.zero_apply, max_eq_right_iff, sub_nonpos] at hFz
  -- The barrier grows like `κ e^{-κ} t`; the correction is `L`-Lipschitz and vanishes at `ν`.
  have hΦ := mul_le_gaussBarrier_smul hκ hν ht0.le (by linarith [ht.2])
  have hdist : dist ((1 - t) • ν) ν = t := by
    rw [dist_eq_norm, sub_smul, one_smul, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
      Real.norm_eq_abs, abs_of_pos ht0]
  have hψ' : -(L * t) ≤ ψ' ((1 - t) • ν) := by
    have hd := hLip.dist_le_mul ((1 - t) • ν) (unitAnnulus_subset_closedBall hzt) ν
      (by rw [mem_closedBall_zero_iff, hν])
    rw [hψ'ν, dist_zero_right, Real.norm_eq_abs, hdist] at hd
    linarith [neg_abs_le (ψ' ((1 - t) • ν))]
  have hLt : L * t ≤ κ * Real.exp (-κ) / 4 * t := mul_le_mul_of_nonneg_right hL ht0.le
  have hpos : 0 ≤ κ * Real.exp (-κ) * t := mul_nonneg (mul_nonneg hκ (Real.exp_pos _).le) ht0.le
  nlinarith [mul_le_mul_of_nonneg_left (show κ * Real.exp (-κ) / 2 * t ≤
    gaussBarrier κ ((1 - t) • ν) + ψ' ((1 - t) • ν) by linarith) hθ]

/-- **Linear growth along the normal on the annulus.** For coefficients close to a frozen matrix
`A` in the sense of `exists_correction`, closely enough that `C η ≤ κ e^{-κ} / 2`, a drift
`‖β‖ ≤ δ` with `2 δ < λ` and a mass coefficient `0 ≤ c ≤ γ` small enough that
`(δ + γ) (1 + 2 C) ≤ λ κ e^{-κ}`, a weak supersolution of `-div (b ∇uε) + β · ∇uε + c uε ≥ 0` on
the annulus whose continuous representative `ĝ` is at least `s₀` on the outer sphere and at least
`s₀ + θ Φ` on the inner sphere, with `c s₀ ≤ 0`, grows linearly into the annulus along the inward
normal at `ν`: `s₀ + θ κ e^{-κ} t / 4 ≤ ĝ ((1 - t) ν)` for `0 < t < 1/2`. -/
private theorem exists_add_mul_le_of_supersolution (ν : E) (hν : ‖ν‖ = 1) {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α ≤ 1) {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) {κ : ℝ} (hκ : 1 ≤ κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {β : E → E} {c : E → ℝ} {Kb : ℝ≥0}
      {η T δ γ : ℝ} {uε : W1p volume (unitAnnulus (n := n)) 2} {ĝ : E → ℝ} {s₀ θ : ℝ},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ η →
      η ≤ 1 → (∀ z ∈ closedBall (0 : E) 1,
        ‖matrixBilinearForm (b z) - matrixBilinearForm A‖ ≤ η) →
      C * η ≤ κ * Real.exp (-κ) / 2 → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      A.trace ≤ T → 2 * |T| + lam ≤ lam * κ →
      AEStronglyMeasurable β (volume.restrict (unitAnnulus (n := n) : Set E)) →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), ‖β z‖ ≤ δ) → δ * 2 < lam →
      AEStronglyMeasurable c (volume.restrict (unitAnnulus (n := n) : Set E)) →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z) →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ) →
      (δ + γ) * (1 + 2 * C) ≤ lam * κ * Real.exp (-κ) →
      (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
        (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          0 ≤ W1p.value (v : W1p volume unitAnnulus 2) z) →
        0 ≤ energyFormH1 b β c uε (v : W1p volume unitAnnulus 2)) →
      ContinuousOn ĝ (closedBall 0 1) →
      W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0) → 0 ≤ θ →
      (∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z) →
      (∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * gaussBarrier κ z ≤ ĝ z) →
      ∀ t ∈ Ioo 0 (1 / 2), s₀ + θ * (κ * Real.exp (-κ) / 4) * t ≤ ĝ ((1 - t) • ν) := by
  obtain ⟨C₀, hC₀, H⟩ := exists_correction (n := n) hα hα1 hlam Lam κ
  obtain ⟨-, B, -, hB⟩ := exists_holderOnWith_gradient_gaussBarrier (n := n) κ hα1
  refine ⟨2 * C₀ + B, by positivity, fun {b A β c Kb η T δ γ uε ĝ s₀ θ} hb hbh hKb hη1 hbA hCη
    hA hT hκT hβm hβδ hδ hcm hc0 hcγ hγ huε hĝ huĝ hcs hθ h1 h2 t ht => ?_⟩
  have hη : 0 ≤ η := Kb.coe_nonneg.trans hKb
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  obtain ⟨ψ, ψ', hψ, hgrad, hae, hLip, h0⟩ := H hb hbh hKb hη1 hbA
  -- The correction is at most `2 C₀ η` on the closed unit ball, since it vanishes at `ν`.
  have hν1 : ν ∈ closedBall (0 : E) 1 := by rw [mem_closedBall_zero_iff, hν]
  have hψ'ν : ψ' ν = 0 := h0 ν (mem_sphere_zero_iff_norm.2 hν)
  have hψ'b : ∀ z ∈ closedBall (0 : E) 1, |ψ' z| ≤ 2 * C₀ * η := fun z hz => by
    have hd := hLip.dist_le_mul z hz ν hν1
    rw [hψ'ν, dist_zero_right, Real.norm_eq_abs, Real.coe_toNNReal _ (mul_nonneg hC₀ hη)] at hd
    have hzν : dist z ν ≤ 2 := (dist_le_norm_add_norm z ν).trans (by
      rw [hν]
      linarith [mem_closedBall_zero_iff.1 hz])
    nlinarith [mul_nonneg hC₀ hη]
  have hB0 : 0 ≤ (B : ℝ) := B.coe_nonneg
  have h2C : 2 * C₀ * η ≤ (2 * C₀ + B) * η := by nlinarith
  -- On the inner sphere `ψ' ≤ κ e^{-κ} / 2 ≤ Φ`, so `s₀ + (θ / 2) (Φ + ψ') ≤ s₀ + θ Φ ≤ ĝ`.
  have h2' : ∀ z ∈ sphere (0 : E) (1 / 2),
      s₀ + θ / 2 * (gaussBarrier κ z + ψ' z) ≤ ĝ z := fun z hz => by
    have hΦz : κ * Real.exp (-κ) * (1 / 2) ≤ gaussBarrier κ z := by
      have hnorm : ‖z‖ = ‖((1 : ℝ) - 1 / 2) • ν‖ := by
        rw [mem_sphere_zero_iff_norm.1 hz, norm_smul, hν]
        norm_num
      rw [gaussBarrier_eq_of_norm_eq hnorm]
      exact mul_le_gaussBarrier_smul hκ0 hν (by norm_num) (by norm_num)
    have hψz := (le_abs_self _).trans (hψ'b z (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (by norm_num)) hz))
    nlinarith [h2 z hz]
  have hcomp := ae_add_mul_le_of_supersolution (Ψ := 2 * C₀ + B) hb
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα)) hA hT hκ hκT hβm hβδ
    hδ hcm hc0 hcγ hγ (fun z hz => (hB z hz).trans (by nlinarith)) hψ hae hLip.continuousOn h0
    (fun z hz => (hψ'b z hz).trans (by nlinarith)) (by
      filter_upwards [hgrad] with z hz
      exact hz.trans (by nlinarith)) huε hĝ huĝ hcs (by positivity) h1 h2'
  have hL : (((C₀ * η).toNNReal : ℝ≥0) : ℝ) ≤ κ * Real.exp (-κ) / 4 := by
    rw [Real.coe_toNNReal _ (mul_nonneg hC₀ hη)]
    nlinarith
  have h := add_mul_le_of_ae_add_mul_le hν hκ0 (by positivity : 0 ≤ θ / 2) hĝ hLip hψ'ν hL
    hcomp t ht
  linarith

/-! ### Hopf's lemma -/

/-- **Rescaled coefficients.** For a point `y + R ν` of the sphere `∂B(y, R)` and `0 < ε ≤ R`, the
homothety `T z = ε z + y + (R - ε) ν` maps the closed unit ball into `closedBall y R`, with
`T ν = y + R ν`, and the open unit ball into `ball y R`. The coefficients `a ∘ T` keep the
ellipticity constants, are `α`-Hölder with constant `K_a ε^α ≤ K_a (2 ε)^α`, and stay within
`K_a (2 ε)^α` of the frozen coefficient `a (y + R ν)`. -/
private theorem rescaled_coefficient {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {y ν : E}
    {R lam Lam : ℝ} {α Ka : ℝ≥0} (hν : ‖ν‖ = 1)
    (hell : UniformlyEllipticOn (closedBall y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R)) {ε : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R) :
    MapsTo (fun z : E => ε • z + (y + (R - ε) • ν)) (closedBall 0 1) (closedBall y R) ∧
      MapsTo (fun z : E => ε • z + (y + (R - ε) • ν)) (ball 0 1) (ball y R) ∧
      UniformlyEllipticOn (closedBall (0 : E) 1) (fun z => a (ε • z + (y + (R - ε) • ν))) lam
        Lam ∧
      HolderOnWith (Ka * ε.toNNReal ^ (α : ℝ)) α
        (fun z => matrixBilinearForm (a (ε • z + (y + (R - ε) • ν)))) (closedBall 0 1) ∧
      ((Ka * ε.toNNReal ^ (α : ℝ) : ℝ≥0) : ℝ) ≤ Ka * (2 * ε) ^ (α : ℝ) ∧
      ∀ z ∈ closedBall (0 : E) 1, ‖matrixBilinearForm (a (ε • z + (y + (R - ε) • ν))) -
        matrixBilinearForm (a (y + R • ν))‖ ≤ Ka * (2 * ε) ^ (α : ℝ) := by
  -- `‖T z - y‖ ≤ ε ‖z‖ + (R - ε)`.
  have hnorm : ∀ z : E, dist (ε • z + (y + (R - ε) • ν)) y ≤ ε * ‖z‖ + (R - ε) := fun z => by
    rw [dist_eq_norm, show ε • z + (y + (R - ε) • ν) - y = ε • z + (R - ε) • ν by abel]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, hν, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hε, abs_of_nonneg (by linarith)]
  have hmaps : MapsTo (fun z : E => ε • z + (y + (R - ε) • ν)) (closedBall 0 1)
      (closedBall y R) := fun z hz => by
    rw [mem_closedBall_zero_iff] at hz
    exact (hnorm z).trans (by nlinarith)
  have hmapsO : MapsTo (fun z : E => ε • z + (y + (R - ε) • ν)) (ball 0 1) (ball y R) :=
    fun z hz => by
      rw [mem_ball_zero_iff] at hz
      exact (hnorm z).trans_lt (by nlinarith)
  have hdist : ∀ z w : E, dist (ε • z + (y + (R - ε) • ν)) (ε • w + (y + (R - ε) • ν)) =
      ε * dist z w := fun z w => by
    rw [dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos hε]
  obtain ⟨he1, he2, he3⟩ := uniformlyEllipticOn_iff.1 hell
  refine ⟨hmaps, hmapsO, uniformlyEllipticOn_iff.2 ⟨he1, he2, fun z hz => he3 (hmaps hz)⟩,
    HolderOnWith.of_dist_le fun z hz w hw => ?_, ?_, fun z hz => ?_⟩
  · refine (hhol.dist_le (hmaps hz) (hmaps hw)).trans_eq ?_
    rw [hdist, Real.mul_rpow hε.le dist_nonneg, NNReal.coe_mul, NNReal.coe_rpow,
      Real.coe_toNNReal _ hε.le, mul_assoc]
  · rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ hε.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le (by linarith) α.coe_nonneg)
      Ka.coe_nonneg
  · have hν1 : ν ∈ closedBall (0 : E) 1 := by rw [mem_closedBall_zero_iff, hν]
    have hTν : ε • ν + (y + (R - ε) • ν) = y + R • ν := by
      rw [sub_smul]
      abel
    have h := hhol.dist_le (hmaps hz) (hmaps hν1)
    simp only at h
    rw [dist_eq_norm, hdist, hTν] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ α.coe_nonneg)
      Ka.coe_nonneg)
    have hzν : dist z ν ≤ 2 := (dist_le_norm_add_norm z ν).trans (by
      rw [mem_closedBall_zero_iff] at hz
      linarith)
    nlinarith

/-- **Rescaled mass coefficient.** If `c` is measurable on `ball y R` with `0 ≤ c ≤ M` and
`c s₀ ≤ 0` there, and the homothety `T z = ε z + p`, `ε > 0`, maps the annulus into `ball y R`,
then `ε² c ∘ T` is measurable on the annulus, with `0 ≤ ε² c ∘ T ≤ ε² |M|` and
`ε² (c ∘ T) s₀ ≤ 0` there. -/
private theorem rescaled_mass {c : E → ℝ} {y p : E} {R M ε s₀ : ℝ}
    (hcm : AEStronglyMeasurable c (volume.restrict (ball y R)))
    (hc0 : ∀ x ∈ ball y R, 0 ≤ c x) (hcM : ∀ x ∈ ball y R, c x ≤ M)
    (hcs : ∀ x ∈ ball y R, c x * s₀ ≤ 0) (hε : 0 < ε)
    (hmaps : MapsTo (fun z : E => ε • z + p) (unitAnnulus (n := n) : Set E) (ball y R)) :
    AEStronglyMeasurable (fun z => ε ^ 2 * c (ε • z + p))
        (volume.restrict (unitAnnulus (n := n) : Set E)) ∧
      (∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ ε ^ 2 * c (ε • z + p)) ∧
      (∀ z ∈ (unitAnnulus (n := n) : Set E), ε ^ 2 * c (ε • z + p) ≤ ε ^ 2 * |M|) ∧
      ∀ z ∈ (unitAnnulus (n := n) : Set E), ε ^ 2 * c (ε • z + p) * s₀ ≤ 0 := by
  have hcov := Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε p (U := unitAnnulus)
    (V := ⟨ball y R, isOpen_ball⟩) hmaps
  refine ⟨((hcm.mono_ac (Measure.absolutelyContinuous_of_le_smul
      (hcov.map_restrict_le volume))).comp_aemeasurable hcov.aemeasurable).const_mul _,
    fun z hz => mul_nonneg (sq_nonneg ε) (hc0 _ (hmaps hz)),
    fun z hz => mul_le_mul_of_nonneg_left ((hcM _ (hmaps hz)).trans (le_abs_self M))
      (sq_nonneg ε), fun z hz => ?_⟩
  rw [mul_assoc]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ε) (hcs _ (hmaps hz))

/-- **Rescaled drift.** If `β` is measurable on `ball y R` with `‖β‖ ≤ Bβ` there, and the
homothety `T z = ε z + p`, `ε > 0`, maps the annulus into `ball y R`, then `ε β ∘ T` is measurable
on the annulus, with `‖ε β ∘ T‖ ≤ ε |Bβ|` there. -/
private theorem rescaled_drift {β : E → E} {y p : E} {R Bβ ε : ℝ}
    (hβm : AEStronglyMeasurable β (volume.restrict (ball y R)))
    (hβB : ∀ x ∈ ball y R, ‖β x‖ ≤ Bβ) (hε : 0 < ε)
    (hmaps : MapsTo (fun z : E => ε • z + p) (unitAnnulus (n := n) : Set E) (ball y R)) :
    AEStronglyMeasurable (fun z => ε • β (ε • z + p))
        (volume.restrict (unitAnnulus (n := n) : Set E)) ∧
      ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖ε • β (ε • z + p)‖ ≤ ε * |Bβ| := by
  have hcov := Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε p (U := unitAnnulus)
    (V := ⟨ball y R, isOpen_ball⟩) hmaps
  refine ⟨((hβm.mono_ac (Measure.absolutelyContinuous_of_le_smul
      (hcov.map_restrict_le volume))).comp_aemeasurable hcov.aemeasurable).const_smul ε,
    fun z hz => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left ((hβB _ (hmaps hz)).trans (le_abs_self _)) hε.le

/-- A scale `ε ∈ (0, R]` at which `η = K (2 ε)^α` satisfies `η ≤ 1` and `C η ≤ m / 2`. -/
private theorem exists_scale {K C m R α : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hm : 0 < m) (hR : 0 < R)
    (hα : 0 < α) : ∃ ε, 0 < ε ∧ ε ≤ R ∧ K * (2 * ε) ^ α ≤ 1 ∧ C * (K * (2 * ε) ^ α) ≤ m / 2 := by
  set δ := min 1 (m / (2 * (C + 1)))
  have hδ : 0 < δ := by positivity
  set r := (δ / (K + 1)) ^ α⁻¹
  refine ⟨min R (r / 2), lt_min hR (by positivity), min_le_left _ _, ?_⟩
  have hpow : (2 * min R (r / 2)) ^ α ≤ δ / (K + 1) :=
    (Real.rpow_le_rpow (by positivity) (by linarith [min_le_right R (r / 2)]) hα.le).trans
      (Real.rpow_inv_rpow (by positivity) hα.ne').le
  have hη : K * (2 * min R (r / 2)) ^ α ≤ δ :=
    calc K * (2 * min R (r / 2)) ^ α ≤ K * (δ / (K + 1)) := mul_le_mul_of_nonneg_left hpow hK
      _ ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
  have h2 := hη.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h2
  exact ⟨hη.trans (min_le_left _ _), by nlinarith [mul_nonneg hK (Real.rpow_nonneg
    (by positivity : (0 : ℝ) ≤ 2 * min R (r / 2)) α)]⟩

/-- **The scale of the rescaling.** A scale `ε ∈ (0, R]` as in `exists_scale` at which moreover the
rescaled lower-order terms `ε |B_b|` and `ε² |M|` satisfy `(ε |B_b| + ε² |M|) (1 + 2 C) ≤ m'`, and
at which the rescaled drift is small, `2 ε |B_b| < λ`. -/
private theorem exists_scale_of_lowerOrder {K C m m' R α lam Bb M : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hm : 0 < m) (hm' : 0 < m') (hR : 0 < R) (hα : 0 < α) (hlam : 0 < lam) :
    ∃ ε, 0 < ε ∧ ε ≤ R ∧ K * (2 * ε) ^ α ≤ 1 ∧ C * (K * (2 * ε) ^ α) ≤ m / 2 ∧
      (ε * |Bb| + ε ^ 2 * |M|) * (1 + 2 * C) ≤ m' ∧ ε * |Bb| * 2 < lam := by
  set N₁ := (|Bb| + |M|) * (1 + 2 * C) / m'
  set N₂ := (2 * |Bb| + 1) / lam
  have hN₁ : 0 ≤ N₁ := by positivity
  have hN₂ : 0 ≤ N₂ := by positivity
  obtain ⟨ε, hε, hεR, h1, h2⟩ :=
    exists_scale hK hC hm (lt_min hR (inv_pos.2 (by positivity : 0 < N₁ + N₂ + 1))) hα
  have hεN : ε * (N₁ + N₂ + 1) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (hεR.trans (min_le_right _ _))
      (by positivity : (0 : ℝ) ≤ N₁ + N₂ + 1)
    rwa [inv_mul_cancel₀ (by positivity)] at h
  have hε1 : ε ≤ 1 := by nlinarith [mul_nonneg hε.le hN₁, mul_nonneg hε.le hN₂]
  -- `ε N₁ ≤ 1` and `ε N₂ ≤ 1` are the two conditions on the lower-order terms.
  have hεlow : ε * ((|Bb| + |M|) * (1 + 2 * C)) ≤ m' := by
    have h : ε * N₁ ≤ 1 := by nlinarith [mul_nonneg hε.le hN₂]
    rwa [mul_div_assoc', div_le_one hm'] at h
  have hεdrift : ε * (2 * |Bb| + 1) ≤ lam := by
    have h : ε * N₂ ≤ 1 := by nlinarith [mul_nonneg hε.le hN₁]
    rwa [mul_div_assoc', div_le_one hlam] at h
  have hε2 : ε ^ 2 * |M| ≤ ε * |M| := by
    rw [sq, mul_assoc]
    exact mul_le_of_le_one_left (by positivity) hε1
  refine ⟨ε, hε, hεR.trans (min_le_left _ _), h1, h2, ?_, by nlinarith⟩
  calc (ε * |Bb| + ε ^ 2 * |M|) * (1 + 2 * C) ≤ (ε * |Bb| + ε * |M|) * (1 + 2 * C) := by gcongr
    _ = ε * ((|Bb| + |M|) * (1 + 2 * C)) := by ring
    _ ≤ m' := hεlow

/-- **Undoing the rescaling.** Linear growth of `g` along `t ↦ x₀ - ε t ν` for `0 < t < τ` is linear
growth along `s ↦ x₀ - s ν` for `0 < s < ε τ`. -/
private theorem exists_pos_mul_le_sub_of_rescaled {g : E → ℝ} {x₀ ν : E} {ε τ c : ℝ}
    (hε : 0 < ε) (hτ : 0 < τ) (hc : 0 < c)
    (h : ∀ t ∈ Ioo 0 τ, g x₀ + c * t ≤ g (x₀ - (ε * t) • ν)) :
    ∃ ε' > 0, ∃ δ > 0, ∀ s ∈ Ioo 0 δ, ε' * s ≤ g (x₀ - s • ν) - g x₀ := by
  refine ⟨c / ε, div_pos hc hε, ε * τ, mul_pos hε hτ, fun s hs => ?_⟩
  have ht := h (s / ε) ⟨div_pos hs.1 hε, (div_lt_iff₀' hε).2 hs.2⟩
  rw [mul_div_cancel₀ _ hε.ne'] at ht
  have hrw : c / ε * s = c * (s / ε) := by ring
  linarith

/-- **Boundary values on the annulus.** If `g` is continuous on `closedBall y R`, larger on
`ball y R` than at the point `y + R ν` of its sphere, and `T` maps the closed unit ball into
`closedBall y R` and the open unit ball into `ball y R`, then `g ∘ T` is at least `g (y + R ν)` on
the unit sphere, and at least `g (y + R ν) + θ Φ` on the sphere of radius `1/2`, for some `θ > 0`
and every `κ > 0`. -/
private theorem exists_pos_add_mul_gaussBarrier_le {g : E → ℝ} {y x₀ : E} {R : ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (closedBall y R)) (hmin : ∀ x ∈ ball y R, g x₀ < g x) {T : E → E}
    (hT : Continuous T) (hTc : MapsTo T (closedBall 0 1) (closedBall y R))
    (hTo : MapsTo T (ball 0 1) (ball y R)) {κ : ℝ} (hκ : 0 < κ) :
    ∃ θ > 0, (∀ z ∈ sphere (0 : E) 1, g x₀ ≤ g (T z)) ∧
      ∀ z ∈ sphere (0 : E) (1 / 2), g x₀ + θ * gaussBarrier κ z ≤ g (T z) := by
  have hge : ∀ x ∈ closedBall y R, g x₀ ≤ g x := by
    rw [← closure_ball y hR.ne']
    exact le_on_closure (fun x hx => (hmin x hx).le) continuousOn_const
      (by rwa [closure_ball y hR.ne'])
  have hgT : ContinuousOn (fun z => g (T z)) (sphere (0 : E) (1 / 2)) :=
    hg.comp hT.continuousOn fun z hz => hTc (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (by norm_num)) hz)
  obtain ⟨z₀, hz₀, hmin₀⟩ := (isCompact_sphere (0 : E) (1 / 2)).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 (by norm_num)) hgT
  have hz₀b : T z₀ ∈ ball y R :=
    hTo (sphere_subset_closedBall.trans (closedBall_subset_ball (by norm_num)) hz₀)
  set m₀ := Real.exp (-κ * (1 / 2) ^ 2) - Real.exp (-κ)
  have hm₀ : 0 < m₀ := sub_pos.2 (Real.exp_lt_exp.2 (by nlinarith))
  refine ⟨(g (T z₀) - g x₀) / m₀, div_pos (sub_pos.2 (hmin _ hz₀b)) hm₀,
    fun z hz => hge _ (hTc (sphere_subset_closedBall hz)), fun z hz => ?_⟩
  have hΦ : gaussBarrier κ z = m₀ := by rw [gaussBarrier, mem_sphere_zero_iff_norm.1 hz]
  rw [hΦ, div_mul_cancel₀ _ hm₀.ne']
  linarith [isMinOn_iff.1 hmin₀ z hz]

/-- **Normalizing the coefficients.** Coefficients uniformly elliptic on `ball y R` and
`α`-Hölder on `closedBall y R`, `α > 0`, are uniformly elliptic on `closedBall y R`, by continuity,
and `min α 1`-Hölder there, since they are bounded. -/
private theorem uniformlyEllipticOn_closedBall_and_exists_holderOnWith
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {y : E} {R lam Lam : ℝ} {α Ka : ℝ≥0}
    (hα : 0 < α) (hR : 0 < R) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R)) :
    UniformlyEllipticOn (closedBall y R) a lam Lam ∧ ∃ K₁ : ℝ≥0,
      HolderOnWith K₁ (min α 1) (fun x => matrixBilinearForm (a x)) (closedBall y R) := by
  have hell' : UniformlyEllipticOn (closedBall y R) a lam Lam := by
    have h := hell.closure_of_continuousOn
      (by rw [closure_ball y hR.ne']; exact hhol.continuousOn hα)
    rwa [closure_ball y hR.ne'] at h
  exact ⟨hell', _, hhol.of_le_of_norm_le (D := Lam.toNNReal) (fun x hx =>
    (hell'.opNorm_matrixBilinearForm_le hx).trans (Real.le_coe_toNNReal _)) (min_le_left _ _)
    one_pos⟩

/-- **Hopf's lemma with a drift and a mass term, under the sign condition `c g(x₀) ≤ 0`.** This is
the common form of `exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg` (no mass term, no sign
condition on `g x₀`) and `exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos` (`c ≥ 0`
and `g x₀ ≤ 0`). -/
private theorem exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_mul_nonpos {Ω : Opens E}
    {u : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E}
    {c g : E → ℝ} {y x₀ : E} {R lam Lam Bb M : ℝ} {α Ka : ℝ≥0} (hα : 0 < α) (hR : 0 < R)
    (hx₀ : x₀ ∈ sphere y R) (hB : ball y R ⊆ Ω) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R))
    (hbm : AEStronglyMeasurable b (volume.restrict (ball y R)))
    (hbB : ∀ x ∈ ball y R, ‖b x‖ ≤ Bb)
    (hcm : AEStronglyMeasurable c (volume.restrict (ball y R)))
    (hc0 : ∀ x ∈ ball y R, 0 ≤ c x) (hcM : ∀ x ∈ ball y R, c x ≤ M)
    (hu : ∀ v : W1p0 volume Ω 2, (∀ᵐ x ∂volume.restrict (Ω : Set E),
      0 ≤ W1p.value (v : W1p volume Ω 2) x) → 0 ≤ energyFormH1 a b c u (v : W1p volume Ω 2))
    (hg : ContinuousOn g (closedBall y R))
    (hug : W1p.value u =ᵐ[volume.restrict (ball y R)] g)
    (hmin : ∀ x ∈ ball y R, g x₀ < g x) (hcg : ∀ x ∈ ball y R, c x * g x₀ ≤ 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ g (x₀ - t • (R⁻¹ • (x₀ - y))) - g x₀ := by
  set α₁ := min α 1
  have hα₁ : 0 < α₁ := lt_min hα one_pos
  obtain ⟨hell, K₁, hhol₁⟩ := uniformlyEllipticOn_closedBall_and_exists_holderOnWith hα hR hell hhol
  -- The normal, the frozen matrix and the exponent of the barrier.
  set ν : E := R⁻¹ • (x₀ - y)
  have hxy : ‖x₀ - y‖ = R := by rw [← dist_eq_norm]; exact hx₀
  have hν : ‖ν‖ = 1 := by
    rw [norm_smul, hxy, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), inv_mul_cancel₀ hR.ne']
  have hx₀ν : y + R • ν = x₀ := by
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  obtain ⟨hlam, -, hell₃⟩ := uniformlyEllipticOn_iff.1 hell
  have hA := (hell₃ (sphere_subset_closedBall hx₀)).1
  set κ := 2 * |(a x₀).trace| / lam + 1
  have hκ : 0 < κ := by positivity
  have hκ1 : 1 ≤ κ := le_add_of_nonneg_left (by positivity)
  have hκT : 2 * |(a x₀).trace| + lam ≤ lam * κ := by
    rw [mul_add, mul_div_cancel₀ _ hlam.ne', mul_one]
  obtain ⟨C, hC, HF⟩ := exists_add_mul_le_of_supersolution (n := n) ν hν hα₁ (min_le_right _ _)
    hlam Lam hκ1
  -- A scale `ε` at which the rescaled coefficients are close enough to the frozen matrix, and at
  -- which the rescaled lower-order terms `ε b` and `ε² c` are absorbed by the margin
  -- `λ κ e^{-κ}` of the barrier and the drift is small for the comparison principle.
  obtain ⟨ε, hε, hεR, hη1, hCη, hγ, hδ⟩ := exists_scale_of_lowerOrder (Bb := Bb) (M := M)
    (m := κ * Real.exp (-κ)) (m' := lam * κ * Real.exp (-κ)) K₁.coe_nonneg hC (by positivity)
    (by positivity) hR (NNReal.coe_pos.2 hα₁) hlam
  set p : E := y + (R - ε) • ν
  obtain ⟨hmaps, hmapsO, hbell, hbh, hKb, hbA⟩ := rescaled_coefficient hν hell hhol₁ hε hεR
  have hT : Continuous fun z : E => ε • z + p := (continuous_id.const_smul ε).add continuous_const
  have hcov := Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε p (U := unitAnnulus)
    (V := ⟨ball y R, isOpen_ball⟩) (fun z hz => hmapsO (unitAnnulus_subset_ball hz))
  -- The rescaled supersolution on the annulus, its continuous representative and boundary values.
  obtain ⟨uε, huεv, huε⟩ := exists_supersolution_comp_smul_add_const hu hε p unitAnnulus
    (fun z hz => hB (hmapsO (unitAnnulus_subset_ball hz)))
  have huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => g (ε • z + p) := by
    filter_upwards [huεv, hcov.ae_comp hug] with z h1 h2
    rw [h1, h2]
  obtain ⟨θ, hθ, h1, h2⟩ := exists_pos_add_mul_gaussBarrier_le hR hg hmin hT hmaps hmapsO hκ
  -- The rescaled drift `ε b ∘ T` and mass coefficient `ε² c ∘ T`.
  obtain ⟨hbm', hbB'⟩ := rescaled_drift hbm hbB hε
    (fun z hz => hmapsO (unitAnnulus_subset_ball hz))
  obtain ⟨hcm', hc0', hcM', hcs⟩ := rescaled_mass hcm hc0 hcM hcg hε
    (fun z hz => hmapsO (unitAnnulus_subset_ball hz))
  have hlin := HF hbell hbh hKb hη1 (by rw [hx₀ν] at hbA; exact hbA) hCη hA (le_abs_self _)
    (by rwa [abs_abs]) hbm' hbB' hδ hcm' hc0' hcM' hγ huε (hg.comp hT.continuousOn hmaps) huĝ hcs
    hθ.le h1 h2
  -- Undo the rescaling: the point `(1 - t) ν` of the annulus is `x₀ - ε t ν`.
  refine exists_pos_mul_le_sub_of_rescaled (c := θ * (κ * Real.exp (-κ) / 4))
    (τ := 1 / 2) hε (by norm_num) (by positivity) fun t ht => ?_
  have hpt : ε • ((1 - t) • ν) + p = x₀ - (ε * t) • ν := by
    rw [← hx₀ν, smul_smul, mul_sub, mul_one]
    simp only [p, sub_smul]
    abel
  have h := hlin t ht
  rwa [Function.comp_apply, hpt] at h

/-- **Hopf's boundary-point lemma for divergence-form equations with Hölder coefficients.** Let
`B = ball y R ⊆ Ω` and let `x₀` lie on its bounding sphere. Let `a` be uniformly elliptic on `B`
with constants `λ, Λ`, not necessarily symmetric, and `α`-Hölder on `closedBall y R`, `α > 0`, and
let `b` be a measurable drift with `‖b‖ ≤ B_b` on `B`. Let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu ≥ 0` in `Ω`, that is `a(u, v) + ∫ (b · ∇u) v ≥ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, equal almost everywhere on `B` to a function `g` continuous on `closedBall y R` with
`g x₀ < g x` for every `x ∈ B`. Then `g` leaves its minimum `x₀` at a positive linear rate along
the inward normal: with `ν = (x₀ - y) / R` the outer unit normal of `B` at `x₀`,
`ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small `t > 0`. -/
theorem exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg {Ω : Opens E}
    {u : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {g : E → ℝ}
    {y x₀ : E} {R lam Lam Bb : ℝ} {α Ka : ℝ≥0} (hα : 0 < α) (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R)
    (hB : ball y R ⊆ Ω) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R))
    (hbm : AEStronglyMeasurable b (volume.restrict (ball y R)))
    (hbB : ∀ x ∈ ball y R, ‖b x‖ ≤ Bb)
    (hu : ∀ v : W1p0 volume Ω 2, (∀ᵐ x ∂volume.restrict (Ω : Set E),
      0 ≤ W1p.value (v : W1p volume Ω 2) x) → 0 ≤ energyFormH1 a b 0 u (v : W1p volume Ω 2))
    (hg : ContinuousOn g (closedBall y R))
    (hug : W1p.value u =ᵐ[volume.restrict (ball y R)] g)
    (hmin : ∀ x ∈ ball y R, g x₀ < g x) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ g (x₀ - t • (R⁻¹ • (x₀ - y))) - g x₀ :=
  exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_mul_nonpos (M := 0) hα hR hx₀ hB hell hhol
    hbm hbB aestronglyMeasurable_const (fun _ _ => le_rfl) (fun _ _ => le_rfl) hu hg hug hmin
    (fun _ _ => by simp)

/-- **Hopf's boundary-point lemma for divergence-form equations with a drift and a mass term.**
Let `B = ball y R ⊆ Ω` and let `x₀` lie on its bounding sphere. Let `a` be uniformly elliptic on
`B` with constants `λ, Λ`, not necessarily symmetric, and `α`-Hölder on `closedBall y R`, `α > 0`,
let `b` be a measurable drift with `‖b‖ ≤ B_b` on `B`, and let `c` be measurable with `|c| ≤ M` on
`B`. Let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` in `Ω`, that is
`a(u, v) + ∫ (b · ∇u) v + ∫ c u v ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, equal almost everywhere
on `B` to a function `g` continuous on `closedBall y R` with `g x₀ < g x` for every `x ∈ B` and
`g x₀ ≤ 0`. Suppose moreover that `c ≥ 0` on `B` or `g x₀ = 0`. Then, with `ν = (x₀ - y) / R` the
outer unit normal of `B` at `x₀`, `ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small
`t > 0`.

When `g x₀ = 0`, `u ≥ 0` on `B`, so the negative part of `c` may be dropped and `c` may have
either sign. The sign condition `g x₀ ≤ 0` cannot be dropped: on the interval `(0, 2)`, `cosh`
solves `-u'' + u = 0`, and its minimum `cosh 0 = 1` over `[0, 2)` is attained only at the boundary
point `0`, where its derivative vanishes. -/
theorem exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos {Ω : Opens E}
    {u : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E}
    {c g : E → ℝ} {y x₀ : E} {R lam Lam Bb M : ℝ} {α Ka : ℝ≥0} (hα : 0 < α) (hR : 0 < R)
    (hx₀ : x₀ ∈ sphere y R) (hB : ball y R ⊆ Ω) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R))
    (hbm : AEStronglyMeasurable b (volume.restrict (ball y R)))
    (hbB : ∀ x ∈ ball y R, ‖b x‖ ≤ Bb)
    (hcm : AEStronglyMeasurable c (volume.restrict (ball y R)))
    (hcM : ∀ x ∈ ball y R, |c x| ≤ M)
    (hu : ∀ v : W1p0 volume Ω 2, (∀ᵐ x ∂volume.restrict (Ω : Set E),
      0 ≤ W1p.value (v : W1p volume Ω 2) x) → 0 ≤ energyFormH1 a b c u (v : W1p volume Ω 2))
    (hg : ContinuousOn g (closedBall y R))
    (hug : W1p.value u =ᵐ[volume.restrict (ball y R)] g)
    (hmin : ∀ x ∈ ball y R, g x₀ < g x) (hg₀ : g x₀ ≤ 0)
    (hsign : (∀ x ∈ ball y R, 0 ≤ c x) ∨ g x₀ = 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ g (x₀ - t • (R⁻¹ • (x₀ - y))) - g x₀ := by
  rcases hsign with hc0 | hg0
  · exact exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_mul_nonpos hα hR hx₀ hB hell hhol
      hbm hbB hcm hc0 (fun x hx => (le_abs_self _).trans (hcM x hx)) hu hg hug hmin
      fun x hx => mul_nonpos_of_nonneg_of_nonpos (hc0 x hx) hg₀
  -- When `g x₀ = 0`, `u ≥ 0` on `B`, so on `B` the mass coefficient may be replaced by `c⁺`.
  set U : Opens E := ⟨ball y R, isOpen_ball⟩
  have hU : U ≤ Ω := hB
  have hcm' : AEStronglyMeasurable (fun x => max (c x) 0) (volume.restrict (ball y R)) :=
    hcm.sup aestronglyMeasurable_const
  have hcM' : ∀ x ∈ ball y R, ‖max (c x) 0‖ ≤ M := fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hcM x hx)) ((abs_nonneg _).trans (hcM x hx))
  have hbd {f : E → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (ball y R)))
      (hfM : ∀ x ∈ ball y R, ‖f x‖ ≤ M) : MemLp f ⊤ (volume.restrict (ball y R)) :=
    memLp_top_of_bound hf M ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hfM))
  have ham : AEStronglyMeasurable a (volume.restrict (ball y R)) :=
    ((continuousOn_of_continuousOn_matrixBilinearForm (hhol.continuousOn hα)).mono
      ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have ha := memLp_energyIntegrand_of_bounds (b := b) (c := 0) (beta := Bb) (gamma := 0)
    (Omega := U) hell.upper_nonneg ham hbm aestronglyMeasurable_const
    (fun _x hx eta xi => hell.upper_bound hx eta xi) hbB (fun _ _ => by simp)
  have hu0 : ∀ᵐ x ∂volume.restrict (ball y R), 0 ≤ W1p.value u x := by
    filter_upwards [hug, ae_restrict_mem measurableSet_ball] with x h hx
    rw [h, ← hg0]
    exact (hmin x hx).le
  exact exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_mul_nonpos (Ω := U) hα hR hx₀
    le_rfl hell hhol hbm hbB hcm' (fun _ _ => le_max_right _ _)
    (fun x hx => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hcM' x hx)))
    (energyFormH1_restrictL_max_nonneg hU ha
      (hbd hcm fun x hx => (Real.norm_eq_abs _).trans_le (hcM x hx)) hu hu0) hg
    ((W1p.value_restrictL_ae hU u).trans hug) hmin fun x _ => by rw [hg0, mul_zero]

end PDE

end TauCeti
