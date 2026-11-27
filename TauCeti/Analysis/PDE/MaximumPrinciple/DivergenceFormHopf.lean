/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundedDomain
import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.LpDrift
import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundedDomain
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Annulus
import TauCeti.Analysis.PDE.EnergyForm.SmallDrift
import TauCeti.Analysis.PDE.EnergyForm.LowerOrder
import TauCeti.Analysis.PDE.MaximumPrinciple.HopfLemma
import TauCeti.Analysis.PDE.Regularity.Classical
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
import TauCeti.Analysis.PDE.EnergyForm.Poincare
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
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
Let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu ≥ 0` in `Ω`, that is
`a(u, v) + ∫ (b · ∇u) v ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, and suppose that `u` agrees
almost everywhere on `B` with a function `g` continuous on `closedBall y R`, `g x₀ < g x` on `B`.
**Hopf's lemma** (`TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg`) says that
`g` leaves `x₀` at a positive linear rate along the inward normal `-ν`, `ν = (x₀ - y) / R`:
`ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small `t > 0`.

The same holds with lower-order terms. For a drift `β ∈ L^q(B)`, `q > max 2 (n + 1)`, and a
measurable zeroth-order coefficient `0 ≤ c ≤ M` on `B`, a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + βⁱ ∂ᵢu + c u ≥ 0` satisfies the same conclusion as soon as `c g(x₀) ≤ 0`
(`TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_memLp`); in Rosales's sign
convention these are the terms `cⁱ Dᵢu` with `cⁱ ∈ L^q` and `d u` with `d ≤ 0` bounded. With a
bounded drift, a bounded `c` of either sign is allowed when `g x₀ = 0`
(`TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos`). The sign condition
is needed: on `(0, 2)`, `cosh` solves `-u'' + u = 0` and has its minimum `1` over `[0, 2)` only at
`0`, where its derivative vanishes. The Hölder continuity of `a` cannot be dropped, by Meyers'
example (`TauCeti.Analysis.PDE.MaximumPrinciple.HalfDisk`); in non-divergence form no regularity
of the coefficients is needed
(`TauCeti.PDE.exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv`).

## The argument

The proof follows Rosales. For small `ε` the homothety `T z = ε z + y + (R - ε) ν` maps the closed
unit ball into `closedBall y R` and `ν` to `x₀`, and `u ∘ T` is a weak supersolution on the annulus
`D = {1/2 < ‖z‖ < 1}` for coefficients `a ∘ T` close to the frozen matrix `A = a x₀`, the drift
`ε β ∘ T`, small in `L^q(D)` since `q > n + 1`, and the mass `ε² c ∘ T`. The Gaussian
`Φ(z) = e^{-κ‖z‖²} - e^{-κ}` vanishes on the unit sphere and satisfies `div (A ∇Φ) ≥ λ κ e^{-κ}`
on `D` for `κ` large; unlike Rosales we use this explicit barrier, so `A` need not be symmetric.
Lax–Milgram gives corrections `ψ, χ ∈ H¹₀(D)` with `-div (b ∇ψ) = div ((b - A) ∇Φ)` and
`-div (b ∇χ) = -(B + 2) |ε β ∘ T|`, `B` a bound for `|∇Φ|`. The global `C^{1,β}` estimate on the
annulus (`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded`, with the charts
`TauCeti.exists_affineIsometryEquiv_graph_of_mem_frontier_annulus`) makes `∇ψ` and `∇χ` small,
so `χ` absorbs the drift term `β · ∇(Φ + ψ + χ)`, the margin of `Φ` absorbs the mass term, and
`ψ, χ` have representatives vanishing at `ν` with small Lipschitz constants. The weak comparison
principle with a drift in `L^q`
(`TauCeti.PDE.UniformlyEllipticOn.value_le_of_memLp_drift_of_measure_ne_top`) then gives
`g x₀ + θ (Φ + ψ + χ) ≤ u ∘ T` on `D` for some `θ > 0`, and the left-hand side grows like
`θ κ e^{-κ} t / 2` along the normal at `ν`.

## References

* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. **62** (2019),
  arXiv:1806.07003, Theorem 4.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4 (the classical boundary-point lemma), Theorem 8.1 and the remark after Theorem 8.16
  (the weak maximum principle with drifts in `L^q`) and Theorem 8.33 (the global `C^{1,α}`
  estimate).
-/

public section

noncomputable section

open Filter Function Metric Set TopologicalSpace MeasureTheory TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology InnerProductSpace Gradient Distributions

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### The unit annulus and its boundary chart at a point of the outer sphere -/

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

private instance : IsFiniteMeasure (volume.restrict (unitAnnulus (n := n) : Set E)) :=
  isFiniteMeasure_restrict.2 (measure_ne_top_of_subset unitAnnulus_subset_ball
    measure_ball_lt_top.ne)

private theorem aestronglyMeasurable_restrict_unitAnnulus
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hbc : ContinuousOn b (closedBall 0 1)) :
    AEStronglyMeasurable b (volume.restrict (unitAnnulus (n := n) : Set E)) :=
  (hbc.mono unitAnnulus_subset_closedBall).aestronglyMeasurable unitAnnulus.isOpen.measurableSet

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

/-- The energy form of coefficients uniformly elliptic on the annulus is coercive on `H¹₀`, with
constant `λ / 10` from the Poincaré inequality in the unit ball. -/
private theorem div_ten_mul_norm_sq_le_energyFormH1 {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam Lam : ℝ} (hb : UniformlyEllipticOn (unitAnnulus (n := n) : Set E) b lam Lam)
    (hm : AEStronglyMeasurable b (volume.restrict (unitAnnulus (n := n) : Set E)))
    (w : W1p0 volume (unitAnnulus (n := n)) 2) :
    lam / 10 * ‖w‖ ^ 2 ≤
      energyFormH1 b 0 0 (w : W1p volume unitAnnulus 2) (w : W1p volume unitAnnulus 2) := by
  have h := hb.mul_norm_sq_le_energyFormH1_self_of_subset_ball (b := 0) (c := 0) (beta := 0)
    (gamma := 0) hm aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ => le_rfl) unitAnnulus_subset_ball w.property
  refine (le_of_eq ?_).trans h
  have := hb.pos
  congr 1
  field_simp
  ring

/-- **The correction.** For coefficients `b`, uniformly elliptic and continuous on the closed unit
ball, there is `ψ ∈ H¹₀` of the annulus solving `-div (b ∇ψ) = div ((b - A) ∇Φ)`, with
`‖ψ‖ ≤ (λ / 10)⁻¹ ‖(b - A) ∇Φ‖_{L²}`. -/
private theorem exists_correction_of_uniformlyEllipticOn
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {κ lam Lam : ℝ} (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hbc : ContinuousOn b (closedBall 0 1))
    (hH : ContinuousOn (correctionField b A κ) (closedBall 0 1)) :
    ∃ ψ : W1p0 volume (unitAnnulus (n := n)) 2,
      (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
        energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
          -∫ z in (unitAnnulus (n := n) : Set E),
            ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ z ∈ closedBall (0 : E) 1, ‖correctionField b A κ z‖ ≤ M) →
        ‖ψ‖ ≤ 10 / lam * ((measureUnivNNReal (volume.restrict (unitAnnulus (n := n) : Set E)) : ℝ) ^
          ((2 : ℝ≥0∞).toReal⁻¹) * M) := by
  have hbD := hb.mono_set unitAnnulus_subset_closedBall
  have hm := aestronglyMeasurable_restrict_unitAnnulus hbc
  have hHL : MemLp (correctionField b A κ) 2 (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    hH.memLp_restrict_of_subset_isCompact (isCompact_closedBall 0 1)
      unitAnnulus.isOpen.measurableSet unitAnnulus_subset_closedBall 2
  obtain ⟨ψ, hψ⟩ := hbD.exists_forall_energyFormH1_eq_divergence_of_measure_ne_top hm
    (measure_ne_top_of_subset unitAnnulus_subset_ball measure_ball_lt_top.ne) hHL
  refine ⟨ψ, hψ, fun M hM hHM => ?_⟩
  have := hb.pos
  -- The `L²` norm of the field is at most `V M`, and `(λ / 10) ‖ψ‖² ≤ a(ψ, ψ) ≤ ‖H‖_{L²} ‖ψ‖`.
  have hL2 : ‖hHL.toLp (correctionField b A κ)‖ ≤
      (measureUnivNNReal (volume.restrict (unitAnnulus (n := n) : Set E)) : ℝ) ^
        ((2 : ℝ≥0∞).toReal⁻¹) * M := by
    refine Lp.norm_le_of_ae_bound hM ?_
    filter_upwards [hHL.coeFn_toLp, ae_restrict_mem unitAnnulus.isOpen.measurableSet]
      with z h1 h2
    rw [h1]
    exact hHM z (unitAnnulus_subset_closedBall h2)
  have hcoer := div_ten_mul_norm_sq_le_energyFormH1 hbD hm ψ
  have henergy : energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (ψ : W1p volume unitAnnulus 2)
      ≤ ‖hHL.toLp (correctionField b A κ)‖ * ‖ψ‖ := by
    rw [hψ ψ, ← divergenceForcing_toLp_apply hHL ψ]
    exact (le_abs_self _).trans (norm_divergenceForcing_apply_le _ ψ)
  have hX : lam / 10 * ‖ψ‖ ≤ (measureUnivNNReal (volume.restrict (unitAnnulus (n := n) : Set E)) :
      ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * M := by
    rcases (norm_nonneg ψ).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      positivity
    · nlinarith [hcoer.trans henergy]
  calc ‖ψ‖ = 10 / lam * (lam / 10 * ‖ψ‖) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)

/-- **The `C^{1,β}` estimate on the annulus.** For exponents as in
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded`, there is `C ≥ 0` such that for
coefficients `b`, uniformly elliptic on the closed unit ball and `α`-Hölder there with constant at
most one, every solution `w ∈ H¹₀` on the annulus of `-div (b ∇w) = f - div G`, with `G`
`α`-Hölder with constant `K_G` on the closed unit ball and `f ∈ L^q`, has gradient bounded by
`C (K_G + ‖f‖_{L^q} + ‖w‖)` almost everywhere. The annulus has smooth boundary
(`TauCeti.exists_affineIsometryEquiv_graph_of_mem_frontier_annulus`), so this is the global
estimate on a domain with `C^{1,α}` boundary. -/
private theorem exists_ae_norm_gradient_le {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α)
    (hα1 : α ≤ 1) {q : ℝ≥0∞} (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (lam Lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : W1p0 volume (unitAnnulus (n := n)) 2}
      {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {G : E → E} {f : E → ℝ} {Kb KG : ℝ≥0},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ 1 →
      HolderOnWith KG α G (closedBall 0 1) →
      MemLp f q (volume.restrict (unitAnnulus (n := n) : Set E)) →
      (∀ φ : 𝓓(unitAnnulus (n := n), ℝ), energyFormH1 b 0 0 (w : W1p volume unitAnnulus 2)
          (W1p.ofTestFunctionₗ volume unitAnnulus 2 φ) =
        (∫ z in (unitAnnulus (n := n) : Set E), ⟪G z, ∇ (φ : E → ℝ) z⟫_ℝ) +
          ∫ z in (unitAnnulus (n := n) : Set E), f z * φ z) →
      ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        ‖W1p.gradient (w : W1p volume unitAnnulus 2) z‖ ≤
          C * (KG + (eLpNorm f q (volume.restrict (unitAnnulus (n := n) : Set E))).toReal +
            ‖w‖) := by
  obtain ⟨C, hC, H⟩ := exists_holderOnWith_gradient_closure_of_isBounded hβ hβ1 hβα hq hβq
    (Ω := unitAnnulus (n := n)) (isBounded_ball.subset unitAnnulus_subset_ball)
    (fun x hx => by
      rw [coe_unitAnnulus] at hx
      simpa only [← SetLike.mem_coe, coe_unitAnnulus] using
        exists_affineIsometryEquiv_graph_of_mem_frontier_annulus (by norm_num) (by norm_num) hx
          hα1) lam Lam 1
  refine ⟨C, hC, fun {w b G f Kb KG} hb hbh hKb hG hf hw => ?_⟩
  obtain ⟨g, hg, -, hgb⟩ := H (hb.mono_set closure_unitAnnulus_subset)
    (hbh.mono closure_unitAnnulus_subset) hKb (hG.mono closure_unitAnnulus_subset) hf hw
  filter_upwards [hg, ae_restrict_mem unitAnnulus.isOpen.measurableSet] with z hz hzD
  rw [hz]
  exact hgb z (subset_closure hzD)

/-- A function `w ∈ H¹₀` of the annulus with gradient bounded by `L` has a representative that is
`L`-Lipschitz on `B(ν, 3)`, which contains the closed unit ball, vanishes at the point `ν` of the
unit sphere, and is therefore bounded by `2 L` on the closed unit ball. -/
private theorem exists_lipschitzOnWith_of_ae_norm_gradient_le (ν : E) (hν : ‖ν‖ = 1) {L : ℝ}
    (hL : 0 ≤ L) (w : W1p0 volume (unitAnnulus (n := n)) 2)
    (hw : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (w : W1p volume unitAnnulus 2) z‖ ≤ L) :
    ∃ w' : E → ℝ, W1p.value (w : W1p volume unitAnnulus 2) =ᵐ[volume.restrict
        (unitAnnulus (n := n) : Set E)] w' ∧ LipschitzOnWith L.toNNReal w' (ball ν 3) ∧
      w' ν = 0 ∧ ∀ z ∈ closedBall (0 : E) 1, |w' z| ≤ 2 * L := by
  obtain ⟨w', hae, hLip, h0⟩ := W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le
    isClosed_closedBall unitAnnulus_subset_closedBall w (x := ν)
    (by rw [closure_compl, interior_closedBall _ one_ne_zero]; simp [hν])
    (by norm_num : (0 : ℝ) < 3) (M := L.toNNReal) (by
      filter_upwards [(ae_restrict_iff' unitAnnulus.isOpen.measurableSet).1 hw] with z hz hzD
      exact (hz hzD.1).trans (Real.le_coe_toNNReal _))
  refine ⟨w', hae, hLip, h0, fun z hz => ?_⟩
  have hzν : dist z ν ≤ 2 := (dist_le_norm_add_norm z ν).trans (by
    rw [mem_closedBall_zero_iff] at hz
    linarith)
  have hd := hLip.dist_le_mul z (mem_ball.2 (by linarith)) ν (mem_ball_self (by norm_num))
  rw [h0, dist_zero_right, Real.norm_eq_abs, Real.coe_toNNReal _ hL] at hd
  nlinarith

/-- **The correction of the barrier.** Fix a point `ν` of the unit sphere, an exponent
`0 < α ≤ 1`, ellipticity constants and `κ`. There is `C ≥ 0` such that for every coefficient field
`b`, uniformly elliptic on the closed unit ball with these constants and `α`-Hölder there with
constant at most `η ≤ 1`, and every matrix `A` with `‖b - A‖ ≤ η` there, the correction
`ψ ∈ H¹₀` of `exists_correction_of_uniformlyEllipticOn` has gradient bounded by `C η` almost
everywhere, and a representative that is `C η`-Lipschitz on `B(ν, 3)`, vanishes at `ν`, and is
bounded by `C η` on the closed unit ball. This combines the energy bound for `ψ` with the
`C^{1,β}` estimate on the annulus. -/
private theorem exists_correction (ν : E) (hν : ‖ν‖ = 1) {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    {lam : ℝ} (hlam : 0 < lam) (Lam κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Kb : ℝ≥0} {η : ℝ},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ η →
      η ≤ 1 → (∀ z ∈ closedBall (0 : E) 1,
        ‖matrixBilinearForm (b z) - matrixBilinearForm A‖ ≤ η) →
      ∃ ψ : W1p0 volume (unitAnnulus (n := n)) 2, ∃ ψ' : E → ℝ,
        (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
          energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
            -∫ z in (unitAnnulus (n := n) : Set E),
              ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ) ∧
        W1p.value (ψ : W1p volume unitAnnulus 2) =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
          ψ' ∧ LipschitzOnWith (C * η).toNNReal ψ' (ball ν 3) ∧ ψ' ν = 0 ∧
        (∀ z ∈ closedBall (0 : E) 1, |ψ' z| ≤ C * η) ∧
        ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          ‖W1p.gradient (ψ : W1p volume unitAnnulus 2) z‖ ≤ C * η := by
  obtain ⟨K, B, hK, hB⟩ := exists_holderOnWith_gradient_gaussBarrier (n := n) κ hα1
  set β : ℝ≥0 := min α (1 / 2)
  have hβ : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨κ', hκ', H⟩ := exists_ae_norm_gradient_le (n := n) hβ hβ1 (min_le_left _ _) hα1
    (q := ⊤) le_top (by simp [hβ1.le]) lam Lam
  -- The volume factor in the `L²` bound of the correction field.
  set V : ℝ := (measureUnivNNReal (volume.restrict (unitAnnulus (n := n) : Set E)) : ℝ) ^
    ((2 : ℝ≥0∞).toReal⁻¹)
  have : 0 ≤ V := by positivity
  set C₁ := κ' * ((K + B) + 10 / lam * (V * B))
  refine ⟨2 * C₁, by positivity, fun {b A Kb η} hb hbh hKb hη1 hbA => ?_⟩
  have hη : 0 ≤ η := Kb.coe_nonneg.trans hKb
  obtain ⟨hHh, hHb⟩ := holderOnWith_correctionField (κ := κ) hK hB hbh hKb hbA
  obtain ⟨ψ, hψ, hψn⟩ := exists_correction_of_uniformlyEllipticOn hb
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα)) (hHh.continuousOn hα)
  have hψb := hψn (η * B) (by positivity) hHb
  -- The `C^{1,β}` estimate on the annulus for `-div (b ∇ψ) = -div (-(b - A) ∇Φ)`.
  have hgrad := H (w := ψ) (b := b) (G := -correctionField b A κ) (f := 0)
    (Kb := Kb) (KG := (η * (K + B)).toNNReal) hb hbh (hKb.trans hη1) hHh.neg MemLp.zero
    (fun φ => by
      rw [hψ ⟨W1p.ofTestFunctionₗ volume unitAnnulus 2 φ, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
      simp only [Pi.neg_apply, inner_neg_left, integral_neg, Pi.zero_apply, zero_mul,
        integral_zero, add_zero]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with z hz
      rw [W1p.gradient_ofTestFunctionₗ, hz])
  have hC₁ : 0 ≤ C₁ * η := mul_nonneg (by positivity) hη
  have hgrad' : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume unitAnnulus 2) z‖ ≤ C₁ * η := by
    filter_upwards [hgrad] with z hz
    refine hz.trans ?_
    rw [Real.coe_toNNReal _ (by positivity), eLpNorm_zero, ENNReal.toReal_zero, add_zero]
    calc κ' * (η * (K + B) + ‖ψ‖) ≤ κ' * (η * (K + B) + 10 / lam * (V * (η * B))) := by
          gcongr
      _ = C₁ * η := by ring
  obtain ⟨ψ', hae, hLip, h0, hbd⟩ := exists_lipschitzOnWith_of_ae_norm_gradient_le ν hν hC₁ ψ hgrad'
  refine ⟨ψ, ψ', hψ, hae, hLip.weaken (Real.toNNReal_le_toNNReal (by linarith)), h0,
    fun z hz => (hbd z hz).trans_eq (by ring), ?_⟩
  filter_upwards [hgrad'] with z hz
  linarith

/-- **The correction for the drift.** Fix a point `ν` of the unit sphere, an exponent
`0 < α ≤ 1`, ellipticity constants and an exponent `q > max 2 (n + 1)`. There is `C ≥ 0` such that
for every coefficient field `b`, uniformly elliptic on the closed unit ball with these constants
and `α`-Hölder there with constant at most one, and every nonnegative `f ∈ L^q` of the annulus,
the solution `χ ∈ H¹₀` of `-div (b ∇χ) = -f` on the annulus is nonpositive, has gradient bounded by
`C ‖f‖_{L^q}` almost everywhere, and has a representative that is `C ‖f‖_{L^q}`-Lipschitz on
`B(ν, 3)` and vanishes at `ν`. -/
private theorem exists_drift_correction (ν : E) (hν : ‖ν‖ = 1) {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α ≤ 1) {q : ℝ≥0∞} (hq2 : 2 < q) (hqn : (n : ℝ) + 1 < q.toReal) {lam : ℝ}
    (hlam : 0 < lam) (Lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Kb : ℝ≥0} {f : E → ℝ},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ 1 →
      MemLp f q (volume.restrict (unitAnnulus (n := n) : Set E)) →
      (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E), 0 ≤ f z) →
      ∃ χ : W1p0 volume (unitAnnulus (n := n)) 2, ∃ χ' : E → ℝ,
        (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
          energyFormH1 b 0 0 (χ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
            -∫ z in (unitAnnulus (n := n) : Set E),
              f z * W1p.value (v : W1p volume unitAnnulus 2) z) ∧
        (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          W1p.value (χ : W1p volume unitAnnulus 2) z ≤ 0) ∧
        (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          ‖W1p.gradient (χ : W1p volume unitAnnulus 2) z‖ ≤
            C * (eLpNorm f q (volume.restrict (unitAnnulus (n := n) : Set E))).toReal) ∧
        W1p.value (χ : W1p volume unitAnnulus 2) =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
          χ' ∧ LipschitzOnWith (C * (eLpNorm f q
            (volume.restrict (unitAnnulus (n := n) : Set E))).toReal).toNNReal χ' (ball ν 3) ∧
        χ' ν = 0 := by
  have hq0 : 0 < q.toReal := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hqtop : q ≠ ⊤ := (ENNReal.toReal_pos_iff.1 hq0).2.ne
  have hq2r : 2 < q.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hqtop).2 hq2
  have hδ : 0 < 1 - ((n : ℝ) + 1) / q.toReal := by rw [sub_pos, div_lt_one hq0]; exact hqn
  set β : ℝ≥0 := min (min α (1 / 2)) (1 - ((n : ℝ) + 1) / q.toReal).toNNReal
  have hβ : 0 < β := lt_min (lt_min hα (by norm_num)) (Real.toNNReal_pos.2 hδ)
  have hβ1 : β < 1 := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  have hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal :=
    (NNReal.coe_le_coe.2 (min_le_right _ _)).trans (Real.coe_toNNReal _ hδ.le).le
  obtain ⟨κ', hκ', H⟩ := exists_ae_norm_gradient_le (n := n) hβ hβ1
    ((min_le_left _ _).trans (min_le_left _ _)) hα1 hq2.le hβq lam Lam
  -- The factor of the `L²` norm of `f` in terms of its `L^q` norm.
  set V : ℝ := ((volume.restrict (unitAnnulus (n := n) : Set E)) univ ^
    (1 / (2 : ℝ≥0∞).toReal - 1 / q.toReal)).toReal
  set C₁ := κ' * (1 + 10 / lam * V)
  refine ⟨C₁, by positivity, fun {b Kb f} hb hbh hKb hf hf0 => ?_⟩
  have hbD := hb.mono_set unitAnnulus_subset_closedBall
  have hm := aestronglyMeasurable_restrict_unitAnnulus
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα))
  have hfin : volume (unitAnnulus (n := n) : Set E) ≠ ⊤ :=
    measure_ne_top_of_subset unitAnnulus_subset_ball measure_ball_lt_top.ne
  have hf2 : MemLp f 2 (volume.restrict (unitAnnulus (n := n) : Set E)) := hf.mono_exponent hq2.le
  obtain ⟨χ, hχ, -⟩ := hbD.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp (c := 0)
    (gamma := 0) (r := 2) hm aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => le_rfl) hfin (by norm_num) (by simp) hf2.neg
  have hχ' : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 (χ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E), f z * W1p.value (v : W1p volume unitAnnulus 2) z :=
    fun v => by
      rw [hχ v, ← integral_neg]
      simp only [Pi.neg_apply, neg_mul]
  have hcoer : ∀ w : W1p0 volume (unitAnnulus (n := n)) 2, lam / 10 * ‖w‖ ^ 2 ≤
      energyFormH1 b 0 0 (w : W1p volume unitAnnulus 2) (w : W1p volume unitAnnulus 2) :=
    div_ten_mul_norm_sq_le_energyFormH1 hbD hm
  -- `χ ≤ 0`, since `-div (b ∇χ) = -f ≤ 0` and `χ` vanishes on the boundary.
  have hneg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      W1p.value (χ : W1p volume unitAnnulus 2) z ≤ 0 :=
    value_nonpos_of_energyFormH1_nonpos (W1p.posPart_mem_w1p0Submodule (by norm_num) χ.property)
      (C := lam / 10) (by positivity) hcoer fun v hv => by
        rw [hχ' v, neg_nonpos]
        exact integral_nonneg_of_ae (by filter_upwards [hf0, hv] with z h1 h2; positivity)
  -- The energy bound `(λ / 10) ‖χ‖ ≤ ‖f‖_{L²} ≤ V ‖f‖_{L^q}`.
  have hL2 : ‖hf2.toLp f‖ ≤
      V * (eLpNorm f q (volume.restrict (unitAnnulus (n := n) : Set E))).toReal := by
    rw [Lp.norm_toLp, mul_comm, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top (ENNReal.rpow_ne_top_of_nonneg
      (sub_nonneg.2 (by
        rw [ENNReal.toReal_ofNat]
        exact one_div_le_one_div_of_le two_pos hq2r.le)) (measure_ne_top _ _)))
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq2.le hf.aestronglyMeasurable)
  have hH1 : ‖χ‖ ≤ 10 / lam * (V *
      (eLpNorm f q (volume.restrict (unitAnnulus (n := n) : Set E))).toReal) := by
    have henergy : energyFormH1 b 0 0 (χ : W1p volume unitAnnulus 2)
        (χ : W1p volume unitAnnulus 2) ≤ ‖hf2.toLp f‖ * ‖χ‖ := by
      have hint : ∫ z in (unitAnnulus (n := n) : Set E),
          f z * W1p.value (χ : W1p volume unitAnnulus 2) z = dirichletForcing (hf2.toLp f) χ := by
        rw [dirichletForcing_apply_eq_setIntegral]
        refine integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp] with z hz
        rw [hz]
      rw [hχ' χ, hint]
      exact (neg_le_abs _).trans ((Real.norm_eq_abs _).symm.trans_le
        (norm_dirichletForcing_apply_le _ χ))
    have hX : lam / 10 * ‖χ‖ ≤ ‖hf2.toLp f‖ := by
      rcases (norm_nonneg χ).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]
        positivity
      · nlinarith [hcoer χ]
    calc ‖χ‖ = 10 / lam * (lam / 10 * ‖χ‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hX.trans hL2) (by positivity)
  -- The `C^{1,β}` estimate on the annulus for `-div (b ∇χ) = -f`.
  have hgrad := H (w := χ) (b := b) (G := 0) (f := -f) (Kb := Kb) (KG := 0) hb hbh hKb
    (HolderWith.zero.holderOnWith _) hf.neg (fun φ => by
      rw [hχ ⟨W1p.ofTestFunctionₗ volume unitAnnulus 2 φ, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
      simp only [Pi.zero_apply, inner_zero_left, integral_zero, zero_add]
      refine integral_congr_ae ?_
      filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with z hz
      rw [hz])
  have hgrad' : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (χ : W1p volume unitAnnulus 2) z‖ ≤
        C₁ * (eLpNorm f q (volume.restrict (unitAnnulus (n := n) : Set E))).toReal := by
    filter_upwards [hgrad] with z hz
    refine hz.trans ?_
    rw [NNReal.coe_zero, zero_add, eLpNorm_neg]
    calc κ' * ((eLpNorm f q _).toReal + ‖χ‖) ≤ κ' * ((eLpNorm f q _).toReal +
          10 / lam * (V * (eLpNorm f q _).toReal)) := by gcongr
      _ = _ := by ring
  obtain ⟨χ', hae, hLip, h0, -⟩ := exists_lipschitzOnWith_of_ae_norm_gradient_le ν hν
    (by positivity) χ hgrad'
  exact ⟨χ, χ', hχ', hneg, hgrad', hae, hLip, h0⟩

/-! ### The comparison -/

/-- The corrected barrier `W + ψ` has, for the coefficients `b`, the energy that the barrier `W`
has for the frozen matrix `A`. -/
private theorem energyFormH1_add_correction {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {κ : ℝ}
    (hcb : MemLp (fun z => energyIntegrand (b z) ((0 : E → E) z) ((0 : E → ℝ) z)) ⊤
      (volume.restrict (unitAnnulus (n := n) : Set E)))
    {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      ∇ (gaussBarrier κ))
    {ψ : W1p volume (unitAnnulus (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 ψ (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ)
    (v : W1p0 volume (unitAnnulus (n := n)) 2) :
    energyFormH1 b 0 0 (W + ψ) (v : W1p volume unitAnnulus 2) =
      energyFormH1 (fun _ => A) 0 0 W (v : W1p volume unitAnnulus 2) := by
  have hcA := memLp_energyIntegrand_const_zero_zero (mu := volume)
    (Omega := unitAnnulus (n := n)) A
  have hsub := energyFormH1_sub hcb hcA W (v : W1p volume unitAnnulus 2)
  simp only [sub_self] at hsub
  -- The energy of `W` for `b - A` is the pairing of the correction field with `∇v`.
  have hpair : energyFormH1 (b - fun _ => A) 0 0 W (v : W1p volume unitAnnulus 2) =
      ∫ z in (unitAnnulus (n := n) : Set E),
        ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ := by
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

/-- The value of the corrected barrier `θ (W + ψ + χ) + s₀` on the annulus. -/
private theorem value_smul_add_add_const_ae {κ : ℝ} {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWv : W1p.value W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] gaussBarrier κ)
    (θ : ℝ) (ψ χ : W1p volume (unitAnnulus (n := n)) 2) (s₀ : ℝ) :
    W1p.value (θ • (W + ψ + χ) + W1p.const s₀) =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => θ * (gaussBarrier κ z + W1p.value ψ z + W1p.value χ z) + s₀ := by
  filter_upwards [W1p.value_add_const_ae (θ • (W + ψ + χ)) s₀, W1p.value_smul_ae θ (W + ψ + χ),
    W1p.value_add_ae (W + ψ) χ, W1p.value_add_ae W ψ, hWv] with z e1 e2 e3 e4 e5
  simp only [e1, e2, Pi.smul_apply, smul_eq_mul, e3, Pi.add_apply, e4, e5]

/-- The gradient of the corrected barrier `θ (W + ψ + χ) + s₀` on the annulus. -/
private theorem gradient_smul_add_add_const_ae {κ : ℝ} {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      ∇ (gaussBarrier κ)) (θ : ℝ) (ψ χ : W1p volume (unitAnnulus (n := n)) 2) (s₀ : ℝ) :
    W1p.gradient (θ • (W + ψ + χ) + W1p.const s₀) =ᵐ[volume.restrict
      (unitAnnulus (n := n) : Set E)]
      fun z => θ • (∇ (gaussBarrier κ) z + W1p.gradient ψ z + W1p.gradient χ z) := by
  rw [W1p.gradient_add_const]
  filter_upwards [W1p.gradient_smul_ae θ (W + ψ + χ), W1p.gradient_add_ae (W + ψ) χ,
    W1p.gradient_add_ae W ψ, hWg] with z e1 e2 e3 e4
  simp only [e1, Pi.smul_apply, e2, Pi.add_apply, e3, e4]

/-- **The corrected barrier is a weak subsolution with a drift and a mass term.** Let `|∇Φ| ≤ B`
on the closed unit ball, and let the corrections satisfy `|∇ψ| ≤ 1` and `|∇χ| ≤ 1`, where `χ`
solves `-div (b ∇χ) = -(B + 2) |β|`, with `χ ≤ 0`. For a drift `β ∈ L^q`, `q ≥ 2`, a mass
coefficient `0 ≤ c ≤ γ` with `c s₀ ≤ 0`, a bound `|ψ| ≤ Ψ` and `γ (1 + Ψ) ≤ λ κ e^{-κ}`, the
function `s₀ + θ (Φ + ψ + χ)`, `θ ≥ 0`, satisfies `-div (b ∇·) + β · ∇· + c · ≤ 0` weakly on the
annulus. The correction `χ` absorbs the drift, since `|β · ∇(Φ + ψ + χ)| ≤ (B + 2) |β|`, and the
strict margin `λ κ e^{-κ}` of the barrier absorbs the mass term. -/
private theorem energyFormH1_add_mul_correction_nonpos
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {β : E → E} {c : E → ℝ} {κ lam Lam T γ Ψ B : ℝ} {q : ℝ≥0∞}
    (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (hT : A.trace ≤ T) (hκ : 1 ≤ κ)
    (hκT : 2 * |T| + lam ≤ lam * κ)
    (hcb : MemLp (fun z => energyIntegrand (b z) ((0 : E → E) z) ((0 : E → ℝ) z)) ⊤
      (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hcL : MemLp c ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z)
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ)
    (hγ : γ * (1 + Ψ) ≤ lam * κ * Real.exp (-κ))
    (hβ : MemLp β q (volume.restrict (unitAnnulus (n := n) : Set E))) (hq : 2 ≤ q)
    (hB : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ B)
    {ψ χ : W1p0 volume (unitAnnulus (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume (unitAnnulus (n := n)) 2) z⟫_ℝ)
    (hψb : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      |W1p.value (ψ : W1p volume (unitAnnulus (n := n)) 2) z| ≤ Ψ)
    (hψg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume (unitAnnulus (n := n)) 2) z‖ ≤ 1)
    (hχ : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 (χ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E),
          (B + 2) * ‖β z‖ * W1p.value (v : W1p volume (unitAnnulus (n := n)) 2) z)
    (hχ0 : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      W1p.value (χ : W1p volume (unitAnnulus (n := n)) 2) z ≤ 0)
    (hχg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (χ : W1p volume (unitAnnulus (n := n)) 2) z‖ ≤ 1)
    {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWv : W1p.value W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] gaussBarrier κ)
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      ∇ (gaussBarrier κ)) {s₀ θ : ℝ}
    (hcs : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0) (hθ : 0 ≤ θ)
    (w : W1p0 volume (unitAnnulus (n := n)) 2)
    (hw : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      0 ≤ W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z) :
    energyFormH1 b β c
      (θ • (W + (ψ : W1p volume (unitAnnulus (n := n)) 2) +
        (χ : W1p volume (unitAnnulus (n := n)) 2)) + W1p.const s₀) (w : W1p volume unitAnnulus 2)
      ≤ 0 := by
  obtain ⟨Vf, hVf⟩ : ∃ Vf : W1p volume (unitAnnulus (n := n)) 2, Vf = θ • (W +
      (ψ : W1p volume (unitAnnulus (n := n)) 2) + (χ : W1p volume (unitAnnulus (n := n)) 2)) +
        W1p.const s₀ :=
    ⟨_, rfl⟩
  rw [← hVf]
  -- The gradient of `Vf` is at most `θ (B + 2)`, so the drift term is at most `θ (B + 2) |β| w`.
  have hgV : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient Vf z‖ ≤ θ * (B + 2) := by
    rw [hVf]
    filter_upwards [gradient_smul_add_add_const_ae hWg θ (ψ : W1p volume unitAnnulus 2)
      (χ : W1p volume unitAnnulus 2) s₀, hψg, hχg,
      ae_restrict_mem unitAnnulus.isOpen.measurableSet] with z h1 h2 h3 hz
    rw [h1, norm_smul, Real.norm_of_nonneg hθ]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hB z (unitAnnulus_subset_closedBall hz)) h2)) h3)
      |>.trans_eq (by ring)) hθ
  have hβ2 : MemLp β 2 (volume.restrict (unitAnnulus (n := n) : Set E)) := hβ.mono_exponent hq
  have hweight : Integrable (fun z => (B + 2) * ‖β z‖ * W1p.value (w : W1p volume unitAnnulus 2) z)
      (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    (hβ2.norm.const_mul (B + 2)).integrable_mul (Lp.memLp _)
  have hdriftInt : Integrable (fun z => ⟪β z, W1p.gradient Vf z⟫_ℝ *
      W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z)
      (volume.restrict (unitAnnulus (n := n) : Set E)) := by
    refine (hweight.const_mul θ).mono' ((hβ.aestronglyMeasurable.inner
      (Lp.aestronglyMeasurable _)).mul (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [hgV, hw] with z h1 h2
    rw [norm_mul, Real.norm_of_nonneg h2]
    calc ‖⟪β z, W1p.gradient Vf z⟫_ℝ‖ * W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z ≤
          ‖β z‖ * (θ * (B + 2)) * W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z :=
        mul_le_mul_of_nonneg_right ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))) h2
      _ = _ := by ring
  have hdrift : ∫ z in (unitAnnulus (n := n) : Set E), ⟪β z, W1p.gradient Vf z⟫_ℝ *
      W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z ≤
      θ * ∫ z in (unitAnnulus (n := n) : Set E), (B + 2) * ‖β z‖ *
        W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z := by
    rw [← integral_const_mul]
    refine integral_mono_ae hdriftInt (hweight.const_mul θ) ?_
    filter_upwards [hgV, hw] with z h1 h2
    calc ⟪β z, W1p.gradient Vf z⟫_ℝ * W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z ≤
          ‖β z‖ * (θ * (B + 2)) * W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z :=
        mul_le_mul_of_nonneg_right ((real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))) h2
      _ = _ := by ring
  -- The principal part: the barrier for `A`, and `-div (b ∇χ) = -(B + 2) |β|`.
  have hprin : energyFormH1 b 0 0 Vf (w : W1p volume (unitAnnulus (n := n)) 2) =
      θ * energyFormH1 (fun _ => A) 0 0 W (w : W1p volume (unitAnnulus (n := n)) 2) -
        θ * ∫ z in (unitAnnulus (n := n) : Set E), (B + 2) * ‖β z‖ *
          W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z := by
    rw [hVf, energyFormH1_add_const_left, energyFormH1_smul_left, energyFormH1_add_left hcb,
      energyFormH1_add_correction hcb hWg hψ w, hχ w]
    ring
  have hΦ := energyFormH1_gaussBarrier_le hb.pos.le hA hT hκ hκT hWv w hw
  -- The mass term is at most `θ λ κ e^{-κ} ∫ w`, since `χ ≤ 0`.
  have hmass : ∫ z in (unitAnnulus (n := n) : Set E),
      c z * W1p.value Vf z * W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z ≤
      θ * (lam * κ * Real.exp (-κ)) * ∫ z in (unitAnnulus (n := n) : Set E),
        W1p.value (w : W1p volume (unitAnnulus (n := n)) 2) z := by
    have hcV : MemLp (fun z => c z * W1p.value Vf z) 2
        (volume.restrict (unitAnnulus (n := n) : Set E)) := hcL.fun_mul (Lp.memLp _)
    have hV := value_smul_add_add_const_ae hWv θ (ψ : W1p volume (unitAnnulus (n := n)) 2)
      (χ : W1p volume (unitAnnulus (n := n)) 2) s₀
    rw [← hVf] at hV
    rw [← integral_const_mul]
    refine integral_mono_ae (hcV.integrable_mul (Lp.memLp _))
      (((Lp.memLp _).integrable one_le_two).const_mul _) ?_
    filter_upwards [hV, hψb, hχ0, hw, ae_restrict_mem unitAnnulus.isOpen.measurableSet]
      with z e1 e6 e8 e7 hz
    rw [e1]
    have hΦ1 := gaussBarrier_le_one (zero_le_one.trans hκ) z
    have hψz := (le_abs_self _).trans e6
    have hΨ : 0 ≤ Ψ := (abs_nonneg _).trans e6
    -- `c (θ (Φ + ψ + χ) + s₀) ≤ θ γ (1 + Ψ) ≤ θ λ κ e^{-κ}`, tested against `w ≥ 0`.
    have h3 : c z * (gaussBarrier κ z + W1p.value (ψ : W1p volume (unitAnnulus (n := n)) 2) z +
        W1p.value (χ : W1p volume (unitAnnulus (n := n)) 2) z) ≤ γ * (1 + Ψ) :=
      (mul_le_mul_of_nonneg_left (by linarith) (hc0 z hz)).trans
        (mul_le_mul_of_nonneg_right (hcγ z hz) (by linarith))
    have hpt : c z * (θ * (gaussBarrier κ z + W1p.value (ψ : W1p volume unitAnnulus 2) z +
        W1p.value (χ : W1p volume unitAnnulus 2) z) + s₀) ≤
        θ * (lam * κ * Real.exp (-κ)) :=
      calc _ = θ * (c z * (gaussBarrier κ z + W1p.value (ψ : W1p volume unitAnnulus 2) z +
            W1p.value (χ : W1p volume unitAnnulus 2) z)) + c z * s₀ := by ring
        _ ≤ θ * (lam * κ * Real.exp (-κ)) + 0 :=
          add_le_add (mul_le_mul_of_nonneg_left (h3.trans hγ) hθ) (hcs z hz)
        _ = _ := add_zero _
    exact mul_le_mul_of_nonneg_right hpt e7
  rw [energyFormH1_eq_energyFormH1_zero_add_setIntegral_inner_of_integrable hcb hcL hdriftInt,
    energyFormH1_eq_energyFormH1_zero_add_setIntegral hcb hcL, hprin]
  linarith [mul_le_mul_of_nonneg_left hΦ hθ]

/-- **The comparison on the annulus.** Let `uε ∈ H¹` of the annulus be a weak supersolution of
`-div (b ∇uε) + β · ∇uε + c uε ≥ 0` for coefficients `b`, uniformly elliptic and continuous on the
closed unit ball, a drift `β ∈ L^q` with `q > max 2 (n + 1)` and a measurable mass coefficient
`0 ≤ c ≤ γ`, and let `uε` equal almost everywhere a function `ĝ` continuous there. If `ĝ ≥ s₀` on
the outer sphere and `ĝ ≥ s₀ + θ Φ` on the inner sphere, with `θ ≥ 0` and `c s₀ ≤ 0`, then
`s₀ + θ (Φ + ψ + χ) ≤ ĝ` almost everywhere on the annulus, for corrections `ψ` and `χ` as in
`energyFormH1_add_mul_correction_nonpos`. This is the weak comparison principle for drifts in
`L^q`. -/
private theorem ae_add_mul_le_of_supersolution {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {β : E → E} {c : E → ℝ} {κ lam Lam T γ Ψ B : ℝ}
    {q : ℝ≥0∞} (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hbc : ContinuousOn b (closedBall 0 1)) (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hT : A.trace ≤ T) (hκ : 1 ≤ κ) (hκT : 2 * |T| + lam ≤ lam * κ)
    (hcm : AEStronglyMeasurable c (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z)
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ)
    (hγ : γ * (1 + Ψ) ≤ lam * κ * Real.exp (-κ))
    (hβ : MemLp β q (volume.restrict (unitAnnulus (n := n) : Set E))) (hq2 : 2 < q)
    (hqn : (n : ℝ) + 1 < q.toReal)
    (hB : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ B)
    {ψ χ : W1p0 volume (unitAnnulus (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume (unitAnnulus (n := n)) 2) z⟫_ℝ)
    (hψb : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      |W1p.value (ψ : W1p volume (unitAnnulus (n := n)) 2) z| ≤ Ψ)
    (hψg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume (unitAnnulus (n := n)) 2) z‖ ≤ 1)
    (hχ : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 (χ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E),
          (B + 2) * ‖β z‖ * W1p.value (v : W1p volume (unitAnnulus (n := n)) 2) z)
    (hχ0 : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      W1p.value (χ : W1p volume (unitAnnulus (n := n)) 2) z ≤ 0)
    (hχg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (χ : W1p volume (unitAnnulus (n := n)) 2) z‖ ≤ 1)
    {uε : W1p volume (unitAnnulus (n := n)) 2}
    (huε : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        0 ≤ W1p.value (v : W1p volume (unitAnnulus (n := n)) 2) z) →
      0 ≤ energyFormH1 b β c uε (v : W1p volume (unitAnnulus (n := n)) 2))
    {ĝ : E → ℝ} (hĝ : ContinuousOn ĝ (closedBall 0 1))
    (huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ) {s₀ θ : ℝ}
    (hcs : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0)
    (hθ : 0 ≤ θ) (h1 : ∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z)
    (h2 : ∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * gaussBarrier κ z ≤ ĝ z) :
    ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      s₀ + θ * (gaussBarrier κ z + W1p.value (ψ : W1p volume (unitAnnulus (n := n)) 2) z +
        W1p.value (χ : W1p volume (unitAnnulus (n := n)) 2) z) ≤ ĝ z := by
  obtain ⟨W, hWv, hWg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    (Omega := unitAnnulus (n := n)) (mu := volume) (p := 2) isOpen_univ
    (contDiff_gaussBarrier κ).contDiffOn (isCompact_closedBall 0 1) unitAnnulus_subset_closedBall
    (subset_univ _)
  have hbD := hb.mono_set unitAnnulus_subset_closedBall
  have hm := aestronglyMeasurable_restrict_unitAnnulus hbc
  have hcb := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    hbD.upper_nonneg hm aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => hbD.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  -- The mass coefficient is essentially bounded, so the energy form splits off its mass term.
  have hcbd : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖c z‖ ≤ γ := fun z hz => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 z hz)]
    exact hcγ z hz
  have hcL : MemLp c ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    memLp_top_of_bound hcm γ ((ae_restrict_iff' unitAnnulus.isOpen.measurableSet).2
      (ae_of_all _ hcbd))
  have hfin : volume (unitAnnulus (n := n) : Set E) ≠ ⊤ :=
    measure_ne_top_of_subset unitAnnulus_subset_ball measure_ball_lt_top.ne
  have hcard : ((Fintype.card (Fin (n + 1)) : ℕ) : ℝ) < q.toReal := by
    rw [Fintype.card_fin]; push_cast; exact hqn
  obtain ⟨qs, hpq, S, hsob⟩ :=
    exists_inv_add_inv_eq_and_forall_eLpNorm_value_le_of_measure_ne_top (mu := volume)
      (Omega := unitAnnulus (n := n)) hfin hq2 hcard
  obtain ⟨Vf, hVf⟩ : ∃ Vf : W1p volume (unitAnnulus (n := n)) 2, Vf = θ • (W +
      (ψ : W1p volume (unitAnnulus (n := n)) 2) + (χ : W1p volume (unitAnnulus (n := n)) 2)) +
        W1p.const s₀ :=
    ⟨_, rfl⟩
  -- On the frontier `Vf - uε` is at most `0`; the corrections vanish there in the Sobolev sense.
  have hbd : W1p.posPart (by norm_num) (Vf - uε) ∈
      w1p0Submodule volume (unitAnnulus (n := n)) 2 := by
    have hrw : Vf - uε = θ • ((ψ : W1p volume (unitAnnulus (n := n)) 2) +
        (χ : W1p volume (unitAnnulus (n := n)) 2)) + (θ • W + W1p.const s₀ - uε) := by
      simp only [hVf, smul_add]
      abel
    rw [hrw]
    refine W1p.posPart_add_mem_w1p0Submodule _ (isBounded_ball.subset unitAnnulus_subset_ball)
      (Submodule.smul_mem _ θ (add_mem ψ.property χ.property))
      (g := fun z => s₀ + θ * gaussBarrier κ z - ĝ z)
      (((continuousOn_const.add (continuousOn_const.mul
        (contDiff_gaussBarrier κ (k := 0)).continuous.continuousOn)).sub hĝ).mono
        closure_unitAnnulus_subset) (fun z hz => ?_) ?_
    · rcases frontier_ball_inter_compl_closedBall_subset (0 : E) (1 / 2) 1 hz with h | h
      · have h0 : gaussBarrier κ z = 0 := by
          rw [gaussBarrier, mem_sphere_zero_iff_norm.1 h]
          simp
        rw [h0, mul_zero, add_zero]
        linarith [h1 z h]
      · linarith [h2 z h]
    · filter_upwards [W1p.value_sub_ae (θ • W + W1p.const s₀) uε,
        W1p.value_add_ae (θ • W) (W1p.const s₀), W1p.value_smul_ae θ W,
        W1p.value_const_ae (mu := volume) (Omega := unitAnnulus (n := n)) (p := 2) s₀,
        hWv, huĝ] with z e1 e2 e3 e4 e5 e6
      simp only [e1, Pi.sub_apply, e2, Pi.add_apply, e3, e4, Pi.smul_apply, smul_eq_mul, e5, e6]
      ring
  -- The weak forms, with the drift term split off, as the comparison principle takes them.
  have hsplit : ∀ (u : W1p volume (unitAnnulus (n := n)) 2)
      (φ : W1p0 volume (unitAnnulus (n := n)) 2),
      energyFormH1 b 0 c u (φ : W1p volume (unitAnnulus (n := n)) 2) +
          (∫ z in (unitAnnulus (n := n) : Set E), W1p.value u z *
            ⟪(0 : E → E) z, W1p.gradient (φ : W1p volume (unitAnnulus (n := n)) 2) z⟫_ℝ) +
          ∫ z in (unitAnnulus (n := n) : Set E), ⟪β z, W1p.gradient u z⟫_ℝ *
            W1p.value (φ : W1p volume (unitAnnulus (n := n)) 2) z =
        energyFormH1 b β c u (φ : W1p volume (unitAnnulus (n := n)) 2) := fun u φ => by
    rw [energyFormH1_eq_energyFormH1_zero_add_setIntegral_inner_of_integrable hcb hcL
      (integrable_inner_gradient_mul_value (beta := 0) (d := fun z => ‖β z‖)
        hβ.aestronglyMeasurable hβ.norm (fun z _ => by simp) hpq u
        (W1p.memLp_value_of_eLpNorm_le (hsob _ φ.property)))]
    simp only [Pi.zero_apply, inner_zero_left, mul_zero, integral_zero, add_zero]
  have hcomp := hbD.value_le_of_memLp_drift_of_measure_ne_top hm hβ hq2 hcard hcm
    (e := 0) aestronglyMeasurable_const hcbd (sigma := 0) (fun _ _ => by simp)
    (fun φ hφ => integral_nonneg_of_ae (by
      filter_upwards [hφ, ae_restrict_mem unitAnnulus.isOpen.measurableSet] with z h hz
      simp only [Pi.zero_apply, inner_zero_left, add_zero]
      exact mul_nonneg (hc0 z hz) h)) hfin hbd fun φ hφ => by
      refine (hsplit Vf φ).trans_le (le_trans ?_ ((huε φ hφ).trans_eq (hsplit uε φ).symm))
      rw [hVf]
      exact energyFormH1_add_mul_correction_nonpos hb hA hT hκ hκT hcb hcL hc0 hcγ hγ hβ
        hq2.le hB hψ hψb hψg hχ hχ0 hχg hWv hWg hcs hθ φ hφ
  have hV := value_smul_add_add_const_ae hWv θ (ψ : W1p volume (unitAnnulus (n := n)) 2)
    (χ : W1p volume (unitAnnulus (n := n)) 2) s₀
  rw [← hVf] at hV
  filter_upwards [hcomp, hV, huĝ] with z h e2 e7
  rw [e2, e7] at h
  linarith

/-- **Linear growth along the normal on the annulus.** Fix a point `ν` of the unit sphere, an
exponent `0 < α ≤ 1`, an exponent `q > max 2 (n + 1)`, ellipticity constants and `κ ≥ 1`. There are
`C, D ≥ 0` with the following property. Let the coefficients `b` be close to a frozen matrix `A`
in the sense of `exists_correction`, closely enough that `C η ≤ min 1 (κ e^{-κ} / 4)`, let the
drift satisfy `D ‖β‖_{L^q} ≤ min 1 (κ e^{-κ} / 4)`, and let the mass coefficient `0 ≤ c ≤ γ` be
small enough that `γ (1 + C η) ≤ λ κ e^{-κ}`. Then a weak supersolution of
`-div (b ∇uε) + β · ∇uε + c uε ≥ 0` on the annulus whose continuous representative `ĝ` is at least
`s₀` on the outer sphere and at least `s₀ + θ Φ` on the inner sphere, with `c s₀ ≤ 0`, grows
linearly into the annulus along the inward normal at `ν`: `s₀ + θ κ e^{-κ} t / 2 ≤ ĝ ((1 - t) ν)`
for `0 < t < 1/2`. -/
private theorem exists_add_mul_le_of_supersolution (ν : E) (hν : ‖ν‖ = 1) {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α ≤ 1) {q : ℝ≥0∞} (hq2 : 2 < q) (hqn : (n : ℝ) + 1 < q.toReal) {lam : ℝ}
    (hlam : 0 < lam) (Lam : ℝ) {κ : ℝ} (hκ : 1 ≤ κ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {β : E → E} {c : E → ℝ} {Kb : ℝ≥0}
      {η T γ : ℝ} {uε : W1p volume (unitAnnulus (n := n)) 2} {ĝ : E → ℝ} {s₀ θ : ℝ},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ η →
      η ≤ 1 → (∀ z ∈ closedBall (0 : E) 1,
        ‖matrixBilinearForm (b z) - matrixBilinearForm A‖ ≤ η) →
      C * η ≤ min 1 (κ * Real.exp (-κ) / 4) →
      MemLp β q (volume.restrict (unitAnnulus (n := n) : Set E)) →
      D * (eLpNorm β q (volume.restrict (unitAnnulus (n := n) : Set E))).toReal ≤
        min 1 (κ * Real.exp (-κ) / 4) →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      A.trace ≤ T → 2 * |T| + lam ≤ lam * κ →
      AEStronglyMeasurable c (volume.restrict (unitAnnulus (n := n) : Set E)) →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z) →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ) →
      γ * (1 + C * η) ≤ lam * κ * Real.exp (-κ) →
      (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
        (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          0 ≤ W1p.value (v : W1p volume (unitAnnulus (n := n)) 2) z) →
        0 ≤ energyFormH1 b β c uε (v : W1p volume (unitAnnulus (n := n)) 2)) →
      ContinuousOn ĝ (closedBall 0 1) →
      W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0) → 0 ≤ θ →
      (∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z) →
      (∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * gaussBarrier κ z ≤ ĝ z) →
      ∀ t ∈ Ioo (0 : ℝ) (1 / 2), s₀ + θ * (κ * Real.exp (-κ) / 2) * t ≤ ĝ ((1 - t) • ν) := by
  obtain ⟨K, B, -, hB⟩ := exists_holderOnWith_gradient_gaussBarrier (n := n) κ hα1
  obtain ⟨C, hC, Hψ⟩ := exists_correction (n := n) ν hν hα hα1 hlam Lam κ
  obtain ⟨C₂, hC₂, Hχ⟩ := exists_drift_correction (n := n) ν hν hα hα1 hq2 hqn hlam Lam
  refine ⟨C, C₂ * (B + 2), hC, by positivity, fun {b A β c Kb η T γ uε ĝ s₀ θ} hb hbh hKb hη1
    hbA hCη hβ hDβ hA hT hκT hcm hc0 hcγ hγ huε hĝ huĝ hcs hθ h1 h2 t ht => ?_⟩
  have hη : 0 ≤ η := Kb.coe_nonneg.trans hKb
  have hm1 : min 1 (κ * Real.exp (-κ) / 4) ≤ 1 := min_le_left _ _
  have hm2 : min 1 (κ * Real.exp (-κ) / 4) ≤ κ * Real.exp (-κ) / 4 := min_le_right _ _
  obtain ⟨ψ, ψ', hψ, hae, hLip, h0, hψ'b, hψg⟩ := Hψ hb hbh hKb hη1 hbA
  -- The drift correction for the weight `(B + 2) |β|`, whose `L^q` norm is `(B + 2) ‖β‖_{L^q}`.
  have hf : MemLp (fun z => (B + 2) * ‖β z‖) q
      (volume.restrict (unitAnnulus (n := n) : Set E)) := hβ.norm.const_mul (B + 2)
  set Lχ := C₂ * ((B + 2) * (eLpNorm β q
      (volume.restrict (unitAnnulus (n := n) : Set E))).toReal)
  have hfn : C₂ * (eLpNorm (fun z => (B + 2) * ‖β z‖) q
      (volume.restrict (unitAnnulus (n := n) : Set E))).toReal ≤ Lχ := by
    refine mul_le_mul_of_nonneg_left ?_ hC₂
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf.aestronglyMeasurable (c := (B : ℝ) + 2)
      (g := β) (ae_of_all _ fun z => by rw [Real.norm_of_nonneg (by positivity)]) q
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hβ.eLpNorm_ne_top)
      h).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨χ, χ', hχ, hχ0, hχg, hχae, hχLip, hχ0'⟩ := Hχ hb hbh (hKb.trans hη1) hf
    (ae_of_all _ fun z => by positivity)
  have hL : Lχ ≤ min 1 (κ * Real.exp (-κ) / 4) := (mul_assoc _ _ _).symm.trans_le hDβ
  replace hχg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (χ : W1p volume (unitAnnulus (n := n)) 2) z‖ ≤ Lχ := by
    filter_upwards [hχg] with z hz using hz.trans hfn
  replace hχLip := hχLip.weaken (Real.toNNReal_le_toNNReal hfn)
  have hcomp := ae_add_mul_le_of_supersolution hb
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα)) hA hT hκ hκT hcm hc0
    hcγ hγ hβ hq2 hqn hB hψ (Ψ := C * η)
    (by filter_upwards [hae, ae_restrict_mem unitAnnulus.isOpen.measurableSet] with z h hz
        rw [h]
        exact hψ'b z (unitAnnulus_subset_closedBall hz))
    (by filter_upwards [hψg] with z hz; linarith) hχ hχ0
    (by filter_upwards [hχg] with z hz; linarith) huε hĝ huĝ hcs hθ h1 h2
  -- On the annulus the comparison holds pointwise for the representatives, by continuity.
  set O : Set E := (unitAnnulus (n := n) : Set E)
  have hOb : O ⊆ ball ν 3 := fun z hz => mem_ball.2 ((dist_le_norm_add_norm z ν).trans_lt (by
    rw [hν]
    linarith [(mem_unitAnnulus.1 hz).1]))
  set F : E → ℝ := fun z => max (s₀ + θ * (gaussBarrier κ z + ψ' z + χ' z) - ĝ z) 0
  have hF : ContinuousOn F O :=
    ((continuousOn_const.add (continuousOn_const.mul
      ((((contDiff_gaussBarrier κ (k := 0)).continuous.continuousOn).add
        (hLip.continuousOn.mono hOb)).add (hχLip.continuousOn.mono hOb)))).sub
      (hĝ.mono unitAnnulus_subset_closedBall)).sup continuousOn_const
  have hF0 : EqOn F 0 O := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ unitAnnulus.isOpen hF continuousOn_const
    filter_upwards [hcomp, hae, hχae] with z h1 h2 h3
    simp only [F, Pi.zero_apply]
    rw [← h2, ← h3]
    exact max_eq_right (by linarith)
  have ht0 := ht.1
  have hdist : dist ((1 - t) • ν) ν = t := by
    rw [dist_eq_norm, sub_smul, one_smul, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
      Real.norm_eq_abs, abs_of_pos ht0]
  have hzt : (1 - t) • ν ∈ O := by
    refine mem_unitAnnulus.2 ?_
    rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
    constructor <;> linarith [ht.2]
  have hFz := hF0 hzt
  simp only [F, Pi.zero_apply, max_eq_right_iff, sub_nonpos] at hFz
  -- The barrier grows like `κ e^{-κ} t`; the corrections are Lipschitz and vanish at `ν`.
  have hΦ := mul_le_gaussBarrier_smul (zero_le_one.trans hκ) hν ht0.le (by linarith [ht.2])
  have hlip {w : E → ℝ} {L : ℝ} (hL0 : 0 ≤ L) (hw : LipschitzOnWith L.toNNReal w (ball ν 3))
      (hw0 : w ν = 0) : -(L * t) ≤ w ((1 - t) • ν) := by
    have hd := hw.dist_le_mul ((1 - t) • ν) (hOb hzt) ν (mem_ball_self (by norm_num))
    rw [hw0, dist_zero_right, Real.norm_eq_abs, hdist, Real.coe_toNNReal _ hL0] at hd
    linarith [neg_abs_le (w ((1 - t) • ν))]
  have hψ' := hlip (mul_nonneg hC hη) hLip h0
  have hχ' := hlip (by positivity) hχLip hχ0'
  have hsum : C * η * t + Lχ * t ≤ κ * Real.exp (-κ) / 2 * t := by
    have := mul_le_mul_of_nonneg_right (add_le_add (hCη.trans hm2) (hL.trans hm2)) ht0.le
    linarith
  linarith [mul_le_mul_of_nonneg_left (show κ * Real.exp (-κ) / 2 * t ≤
    gaussBarrier κ ((1 - t) • ν) + ψ' ((1 - t) • ν) + χ' ((1 - t) • ν) by linarith) hθ]

/-! ### Hopf's lemma -/

/-- **Rescaled coefficients.** For a point `y + R ν` of the sphere `∂B(y, R)` and `0 < ε ≤ R`, the
homothety `T z = ε z + y + (R - ε) ν` maps the closed unit ball into `closedBall y R`, with
`T ν = y + R ν`, and the open unit ball into `ball y R`. The coefficients `a ∘ T` keep the
ellipticity constants, are `α`-Hölder with constant `K_a ε^α`, and stay within `K_a (2 ε)^α` of the
frozen coefficient `a (y + R ν)`. -/
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
    HolderOnWith.of_dist_le fun z hz w hw => ?_, fun z hz => ?_⟩
  · refine (hhol.dist_le (hmaps hz) (hmaps hw)).trans_eq ?_
    rw [hdist, Real.mul_rpow hε.le dist_nonneg, NNReal.coe_mul, NNReal.coe_rpow,
      Real.coe_toNNReal _ hε.le, mul_assoc]
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

/-- A scale `ε ∈ (0, R]` as in `exists_scale` at which moreover `ε² N ≤ m'`, so that a mass term
of size `N`, rescaled by `ε²`, is at most `m'`. -/
private theorem exists_scale_of_sq_mul_le {K C m R α N m' : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hm : 0 < m) (hR : 0 < R) (hα : 0 < α) (hN : 0 < N) (hm' : 0 < m') :
    ∃ ε, 0 < ε ∧ ε ≤ R ∧ K * (2 * ε) ^ α ≤ 1 ∧ C * (K * (2 * ε) ^ α) ≤ m / 2 ∧
      ε ^ 2 * N ≤ m' := by
  obtain ⟨ε, hε, hεR, h1, h2⟩ :=
    exists_scale hK hC hm (lt_min hR (Real.sqrt_pos.2 (div_pos hm' hN))) hα
  refine ⟨ε, hε, hεR.trans (min_le_left _ _), h1, h2, ?_⟩
  have h := pow_le_pow_left₀ hε.le (hεR.trans (min_le_right _ _)) 2
  rwa [Real.sq_sqrt (div_pos hm' hN).le, le_div_iff₀ hN] at h

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

/-- **Rescaled drift.** If `β ∈ L^q(B(y, R))` and the homothety `T z = ε z + p`,
`ε > 0`, maps the annulus into `B(y, R)`, then `ε (β ∘ T) ∈ L^q` of the annulus, with norm at most
`ε^{1 - (n + 1) / q} ‖β‖_{L^q}`. -/
private theorem memLp_rescaled_drift {β : E → E} {y p : E} {R ε : ℝ} {q : ℝ≥0∞}
    (hβ : MemLp β q (volume.restrict (ball y R))) (hε : 0 < ε)
    (hmaps : MapsTo (fun z : E => ε • z + p) (unitAnnulus (n := n) : Set E) (ball y R)) :
    MemLp (fun z => ε • β (ε • z + p)) q (volume.restrict (unitAnnulus (n := n) : Set E)) ∧
      (eLpNorm (fun z => ε • β (ε • z + p)) q
        (volume.restrict (unitAnnulus (n := n) : Set E))).toReal ≤
        ε ^ (1 - ((n : ℝ) + 1) / q.toReal) *
          (eLpNorm β q (volume.restrict (ball y R))).toReal := by
  have hcov := Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε p (U := unitAnnulus (n := n))
    (V := ⟨ball y R, isOpen_ball⟩) hmaps
  have hD := (unitAnnulus (n := n)).isOpen.measurableSet
  have hm := hcov.memLp_comp hD subset_rfl hmaps hβ
  refine ⟨hm.const_smul ε, ?_⟩
  refine (hcov.lpNorm_le_of_ae_le_mul_comp hD subset_rfl hmaps hε.le
    (hm.aestronglyMeasurable.const_smul ε) hβ (ae_of_all _ fun z => by
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hε.le])).trans_eq ?_
  rw [finrank_euclideanSpace_fin, one_div, ENNReal.toReal_inv, ← mul_assoc]
  congr 1
  rw [show (1 : ℝ) - ((n : ℝ) + 1) / q.toReal = 1 + (-((n + 1 : ℕ) : ℝ)) * q.toReal⁻¹ by
      push_cast; ring, Real.rpow_add hε, Real.rpow_one, Real.rpow_mul hε.le, Real.rpow_neg hε.le,
    Real.rpow_natCast]

/-- **Hopf's lemma with a drift and a mass term, under the sign condition `c g(x₀) ≤ 0`.** Let
`B = ball y R ⊆ Ω ⊆ ℝⁿ⁺¹` and let `x₀` lie on its bounding sphere. Let `a` be uniformly elliptic on
`B` with constants `λ, Λ`, not necessarily symmetric, and `α`-Hölder on `closedBall y R`, `α > 0`,
let the drift `β` lie in `L^q(B)` for some `q > max 2 (n + 1)`, and let `c` be measurable with
`0 ≤ c ≤ M` on `B`. Let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + βⁱ ∂ᵢu + c u ≥ 0` in `Ω`, equal almost everywhere on `B` to a function `g`
continuous on `closedBall y R` with `g x₀ < g x` for every `x ∈ B`, and suppose that
`c g(x₀) ≤ 0` on `B`, for instance `g x₀ ≤ 0`. Then, with `ν = (x₀ - y) / R` the outer unit
normal of `B` at `x₀`, `ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small `t > 0`.

This is the lemma of Rosales for a drift `cⁱ ∈ L^q`, `q > n + 1`, and a bounded zeroth-order term
of the sign there called weakly non-positive. The integrability `q > n + 1` makes the rescaled
drift `ε β(ε ·)` small in `L^q` as `ε → 0`, and it is the integrability under which the weak
maximum principle holds
(`TauCeti.PDE.UniformlyEllipticOn.value_le_of_memLp_drift_of_measure_ne_top`).
The sign condition cannot be dropped: on the interval `(0, 2)`, `cosh` solves `-u'' + u = 0`, and
its minimum `cosh 0 = 1` over `[0, 2)` is attained only at the boundary point `0`, where its
derivative vanishes. -/
theorem exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_memLp {Ω : Opens E}
    {u : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {β : E → E}
    {c g : E → ℝ} {y x₀ : E} {R lam Lam M : ℝ} {α Ka : ℝ≥0} {q : ℝ≥0∞} (hα : 0 < α)
    (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hB : ball y R ⊆ Ω)
    (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R))
    (hβ : MemLp β q (volume.restrict (ball y R))) (hq2 : 2 < q) (hqn : (n : ℝ) + 1 < q.toReal)
    (hcm : AEStronglyMeasurable c (volume.restrict (ball y R)))
    (hc0 : ∀ x ∈ ball y R, 0 ≤ c x) (hcM : ∀ x ∈ ball y R, c x ≤ M)
    (hu : ∀ v : W1p0 volume Ω 2, (∀ᵐ x ∂volume.restrict (Ω : Set E),
      0 ≤ W1p.value (v : W1p volume Ω 2) x) → 0 ≤ energyFormH1 a β c u (v : W1p volume Ω 2))
    (hg : ContinuousOn g (closedBall y R))
    (hug : W1p.value u =ᵐ[volume.restrict (ball y R)] g)
    (hmin : ∀ x ∈ ball y R, g x₀ < g x) (hcg : ∀ x ∈ ball y R, c x * g x₀ ≤ 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ g (x₀ - t • (R⁻¹ • (x₀ - y))) - g x₀ := by
  have hq0 : 0 < q.toReal := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- Ellipticity extends to the closed ball, by continuity of the coefficients.
  replace hell : UniformlyEllipticOn (closedBall y R) a lam Lam := by
    have h := hell.closure_of_continuousOn
      (by rw [closure_ball y hR.ne']; exact hhol.continuousOn hα)
    rwa [closure_ball y hR.ne'] at h
  -- Exponents above one are replaced by one: the coefficients are bounded on the ball.
  set α₁ := min α 1
  have hα₁ : 0 < α₁ := lt_min hα one_pos
  obtain ⟨K₁, hhol₁⟩ : ∃ K₁ : ℝ≥0,
      HolderOnWith K₁ α₁ (fun x => matrixBilinearForm (a x)) (closedBall y R) :=
    ⟨_, hhol.of_le_of_norm_le (D := Lam.toNNReal) (fun x hx =>
      (hell.opNorm_matrixBilinearForm_le hx).trans (Real.le_coe_toNNReal _)) (min_le_left _ _)
      one_pos⟩
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
  obtain ⟨C, D, hC, hD, HF⟩ := exists_add_mul_le_of_supersolution (n := n) ν hν hα₁
    (min_le_right _ _) hq2 hqn hlam Lam hκ1
  -- A scale `ε` at which the rescaled coefficients are close enough to the frozen matrix, at
  -- which the rescaled mass term `ε² c` is absorbed by the margin `λ κ e^{-κ}` of the barrier,
  -- and at which the rescaled drift `ε β ∘ T` is small in `L^q`.
  set m := lam * κ * Real.exp (-κ)
  have hm : 0 < m := by positivity
  set m₁ := min 1 (κ * Real.exp (-κ) / 4)
  have hm₁ : 0 < m₁ := lt_min one_pos (by positivity)
  set N := (|M| + 1) * (1 + C)
  have hN : 0 < N := by positivity
  set δ : ℝ := 1 - ((n : ℝ) + 1) / q.toReal
  have hδ : 0 < δ := by
    rw [sub_pos, div_lt_one hq0]
    exact hqn
  set Kβ := (eLpNorm β q (volume.restrict (ball y R))).toReal
  set ε₂ := (m₁ / (D * Kβ + 1)) ^ δ⁻¹
  have hε₂ : 0 < ε₂ := by positivity
  obtain ⟨ε, hε, hεR, hη1, hCη, hεN⟩ := exists_scale_of_sq_mul_le K₁.coe_nonneg hC
    (by positivity : 0 < 2 * m₁) (lt_min hR hε₂) (NNReal.coe_pos.2 hα₁) hN hm
  set p : E := y + (R - ε) • ν
  obtain ⟨hmaps, hmapsO, hbell, hbh, hbA⟩ :=
    rescaled_coefficient hν hell hhol₁ hε (hεR.trans (min_le_left _ _))
  have hT : Continuous fun z : E => ε • z + p := (continuous_id.const_smul ε).add continuous_const
  have hmapsD : MapsTo (fun z : E => ε • z + p) (unitAnnulus (n := n) : Set E) (ball y R) :=
    fun z hz => hmapsO (unitAnnulus_subset_ball hz)
  -- The rescaled supersolution on the annulus, its continuous representative and boundary values.
  obtain ⟨uε, huεv, huε⟩ := exists_supersolution_comp_smul_add_const hu hε p unitAnnulus
    (fun z hz => hB (hmapsD hz))
  have hcov := Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε p (U := unitAnnulus)
    (V := ⟨ball y R, isOpen_ball⟩) hmapsD
  have huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => g (ε • z + p) := by
    filter_upwards [huεv, hcov.ae_comp hug] with z h1 h2
    rw [h1, h2]
  obtain ⟨θ, hθ, h1, h2⟩ := exists_pos_add_mul_gaussBarrier_le hR hg hmin hT hmaps hmapsO hκ
  have hKb : ((K₁ * ε.toNNReal ^ (α₁ : ℝ) : ℝ≥0) : ℝ) ≤ K₁ * (2 * ε) ^ (α₁ : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ hε.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le (by linarith) α₁.coe_nonneg)
      K₁.coe_nonneg
  -- The rescaled mass coefficient `ε² c ∘ T`, bounded by `ε² |M|`, is absorbed at this scale.
  obtain ⟨hcm', hc0', hcM', hcs⟩ := rescaled_mass hcm hc0 hcM hcg hε hmapsD
  have hγ : ε ^ 2 * |M| * (1 + C * (K₁ * (2 * ε) ^ (α₁ : ℝ))) ≤ m := by
    have hCη1 : C * (K₁ * (2 * ε) ^ (α₁ : ℝ)) ≤ C := by nlinarith
    calc ε ^ 2 * |M| * (1 + C * (K₁ * (2 * ε) ^ (α₁ : ℝ))) ≤ ε ^ 2 * N := by
          simp only [N]
          nlinarith [abs_nonneg M, mul_nonneg (sq_nonneg ε) (abs_nonneg M)]
      _ ≤ m := hεN
  -- The rescaled drift `ε β ∘ T` is small in `L^q` at this scale.
  obtain ⟨hβε, hβεn⟩ := memLp_rescaled_drift hβ hε hmapsD
  have hDβ : D * (eLpNorm (fun z => ε • β (ε • z + p)) q
      (volume.restrict (unitAnnulus (n := n) : Set E))).toReal ≤ m₁ := by
    have hKβ : 0 ≤ Kβ := ENNReal.toReal_nonneg
    have hεδ : ε ^ δ ≤ m₁ / (D * Kβ + 1) := by
      calc ε ^ δ ≤ ε₂ ^ δ :=
            Real.rpow_le_rpow hε.le ((hεR.trans (min_le_right _ _))) hδ.le
        _ = m₁ / (D * Kβ + 1) := Real.rpow_inv_rpow (by positivity) hδ.ne'
    calc D * (eLpNorm (fun z => ε • β (ε • z + p)) q
          (volume.restrict (unitAnnulus (n := n) : Set E))).toReal ≤ D * (ε ^ δ * Kβ) :=
          mul_le_mul_of_nonneg_left hβεn hD
      _ ≤ D * (m₁ / (D * Kβ + 1) * Kβ) := by gcongr
      _ ≤ m₁ := by
          rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hD hKβ]
  have hlin := HF hbell hbh hKb hη1 (by rw [hx₀ν] at hbA; exact hbA) (by linarith) hβε hDβ hA
    (le_abs_self _) (by rwa [abs_abs]) hcm' hc0' hcM' hγ huε (hg.comp hT.continuousOn hmaps)
    huĝ hcs hθ.le h1 h2
  -- Undo the rescaling: the point `(1 - t) ν` of the annulus is `x₀ - ε t ν`.
  refine exists_pos_mul_le_sub_of_rescaled (c := θ * (κ * Real.exp (-κ) / 2))
    (τ := 1 / 2) hε (by norm_num) (by positivity) fun t ht => ?_
  have hpt : ε • ((1 - t) • ν) + p = x₀ - (ε * t) • ν := by
    rw [← hx₀ν, smul_smul, mul_sub, mul_one]
    simp only [p, sub_smul]
    abel
  have h := hlin t ht
  rwa [Function.comp_apply, hpt] at h

/-- A drift bounded on `ball y R` lies in `L^{n+3}` there, and `n + 3 > max 2 (n + 1)`. -/
private theorem memLp_exponent_add_three {b : E → E} {y : E} {R Bb : ℝ}
    (hbm : AEStronglyMeasurable b (volume.restrict (ball y R))) (hbB : ∀ x ∈ ball y R, ‖b x‖ ≤ Bb) :
    MemLp b ((n + 3 : ℕ) : ℝ≥0∞) (volume.restrict (ball y R)) ∧ 2 < ((n + 3 : ℕ) : ℝ≥0∞) ∧
      (n : ℝ) + 1 < ((n + 3 : ℕ) : ℝ≥0∞).toReal := by
  have : IsFiniteMeasure (volume.restrict (ball y R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  exact ⟨(memLp_top_of_bound hbm Bb ((ae_restrict_iff' measurableSet_ball).2
    (ae_of_all _ hbB))).mono_exponent le_top, by exact_mod_cast (by omega : 2 < n + 3),
    by rw [ENNReal.toReal_natCast]; push_cast; linarith⟩

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
  have hb := memLp_exponent_add_three hbm hbB
  exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_memLp (M := 0) hα hR hx₀ hB hell hhol
    hb.1 hb.2.1 hb.2.2 aestronglyMeasurable_const (fun _ _ => le_rfl) (fun _ _ => le_rfl) hu hg
    hug hmin (fun _ _ => by simp)

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
  obtain ⟨hb, hq2, hqn⟩ := memLp_exponent_add_three hbm hbB
  rcases hsign with hc0 | hg0
  · exact exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_memLp hα hR hx₀ hB hell hhol hb
      hq2 hqn hcm hc0 (fun x hx => (le_abs_self _).trans (hcM x hx)) hu hg hug hmin
      fun x hx => mul_nonpos_of_nonneg_of_nonpos (hc0 x hx) hg₀
  -- When `g x₀ = 0`, `u ≥ 0` on `B`, so on `B` the mass coefficient may be replaced by `c⁺`.
  set U : Opens E := ⟨ball y R, isOpen_ball⟩
  have hU : U ≤ Ω := hB
  have hcm' : AEStronglyMeasurable (fun x => max (c x) 0) (volume.restrict (ball y R)) :=
    hcm.sup aestronglyMeasurable_const
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
  exact exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_memLp (Ω := U) hα hR hx₀ le_rfl
    hell hhol hb hq2 hqn hcm' (fun _ _ => le_max_right _ _)
    (fun x hx => max_le ((le_abs_self _).trans (hcM x hx)) ((abs_nonneg _).trans (hcM x hx)))
    (energyFormH1_restrictL_max_nonneg hU ha (memLp_top_of_bound hcm M
      ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ fun x hx =>
        (Real.norm_eq_abs _).trans_le (hcM x hx)))) hu hu0) hg
    ((W1p.value_restrictL_ae hU u).trans hug) hmin fun x _ => by rw [hg0, mul_zero]

end PDE

end TauCeti
