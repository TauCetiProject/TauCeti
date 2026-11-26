/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Global
import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.Basic
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
`α`-Hölder on `closedBall y R` for some `α > 0`, and let `b` be a measurable drift with `‖b‖ ≤ β`
on `B`. Let `u ∈ H¹(Ω)` be a weak supersolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu ≥ 0` in `Ω`,

that is `a(u, v) + ∫ ⟪b, ∇u⟫ v ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, and suppose that `u` agrees
almost everywhere on `B` with a function `g` continuous on `closedBall y R` that attains a strict
minimum over `B` at `x₀`: `g x₀ < g x` for `x ∈ B`. **Hopf's lemma**
(`TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg`) says that `g` leaves `x₀` at a
positive linear rate along the inward normal: with `ν = (x₀ - y) / R`,

`ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small `t > 0`.

In particular an inward derivative of `g` at `x₀`, if it exists, is positive. In Rosales's sign
convention the drift is the first-order term `cⁱ Dᵢu`, here with `cⁱ = -bⁱ` bounded. No
regularity of the drift is needed.

The same conclusion holds with a zeroth-order term as well
(`TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos`): for a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with `c` measurable and `0 ≤ c ≤ M` on `B`,
provided `g x₀ ≤ 0`. In Rosales's sign convention this is the term `d u` with `d ≤ 0` bounded.
When `g x₀ = 0` a bounded `c` of either sign is allowed, since then `u ≥ 0` on `B` and the
negative part of `c` may be dropped. The sign condition on `g x₀` is needed: on the interval
`(0, 2)`, `cosh` solves `-u'' + u = 0`, and its minimum `cosh 0 = 1 > 0` over `[0, 2)` is attained
only at the boundary point `0`, where its derivative vanishes.

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
  `a ∘ T`, which are `α`-Hölder with constant `K_a ε^α` and within `K_a (2 ε)^α` of the frozen
  matrix `A = a x₀`, the drift `ε b ∘ T` and the mass coefficient `ε² c ∘ T`
  (`TauCeti.PDE.exists_supersolution_comp_smul_add_const`).
* **The barrier.** The Gaussian `Φ(z) = e^{-κ‖z‖²} - e^{-κ}` vanishes on the unit sphere, is a
  strict classical subsolution of `div (A ∇·)` on `D`, `div (A ∇Φ) ≥ λ κ e^{-κ}`, once `κ` is large
  compared with `tr A / λ`, and grows like `κ e^{-κ} t` along the inward normal at `ν`. Unlike
  Rosales, who solves the frozen Dirichlet problem and appeals to the classical Hopf lemma, we use
  this explicit barrier, so `A` need not be symmetric.
* **The correction.** Lax–Milgram gives `ψ ∈ H¹₀(D)` with
  `-div ((a ∘ T) ∇ψ) = div ((a ∘ T - A) ∇Φ)`, so that `Φ + ψ` is a weak subsolution for `a ∘ T`.
  Its `H¹` norm and the Hölder constant of `(a ∘ T - A) ∇Φ` are small with `ε`. The global
  `C^{1,β}` estimate on the annulus
  (`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`), in charts in which the two
  bounding spheres are graphs of smooth functions, bounds `∇ψ` on all of `D` by the same order. So
  for `ε` small the correction has a representative that is Lipschitz near `ν` with a constant
  below `κ e^{-κ} / 2` and vanishes at `ν`
  (`TauCeti.W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le`). Stampacchia's global bound
  (`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence`) bounds `ψ` by the same order.
* **The lower-order terms.** Since `Φ ≤ 1`, `ψ` is bounded and `∇Φ`, `∇ψ` are bounded on `D`, for
  `ε` small the drift term `ε ⟪b ∘ T, ∇(Φ + ψ)⟫` and the mass term `ε² c (Φ + ψ)` are absorbed by
  the margin `λ κ e^{-κ}` of the barrier, and the term `ε² c g x₀` is nonpositive.
* **Comparison.** On the boundary of `D`, `u ∘ T ≥ g x₀` on the outer sphere and
  `u ∘ T ≥ g x₀ + θ Φ` on the inner one for some `θ > 0`. So `g x₀ + θ (Φ + ψ)` is a weak
  subsolution below `u ∘ T` on the boundary, and the weak comparison principle
  (`TauCeti.PDE.value_le_of_energyFormH1_le`), for which the small rescaled drift keeps the energy
  form coercive, gives `g x₀ + θ (Φ + ψ) ≤ u ∘ T` on `D`, and along the normal at `ν` the
  right-hand side grows like `θ κ e^{-κ} t / 2`.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg`: Hopf's boundary-point lemma
  for weak supersolutions of divergence-form equations with Hölder coefficients and a bounded
  drift.
* `TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos`: the same with a
  bounded zeroth-order term, nonnegative at a minimum `g x₀ < 0` and of either sign at a minimum
  `g x₀ = 0`.

## References

* L. Rosales, *Generalizing Hopf's boundary point lemma*,
  arXiv:1806.07003, Theorem 4.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4 (the classical boundary-point lemma), Theorem 8.1 (the weak maximum principle),
  Theorem 8.16 (the global bound) and Theorem 8.33 (the global `C^{1,α}` estimate).
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

private theorem frontier_unitAnnulus_subset :
    frontier (unitAnnulus (n := n) : Set E) ⊆ sphere 0 1 ∪ sphere 0 (1 / 2) := by
  rw [coe_unitAnnulus]
  exact (frontier_inter_subset _ _).trans (union_subset_union
    (inter_subset_left.trans frontier_ball_subset_sphere)
    (inter_subset_right.trans ((frontier_compl _).subset.trans frontier_closedBall_subset_sphere)))

private instance : IsFiniteMeasure (volume.restrict (unitAnnulus (n := n) : Set E)) :=
  isFiniteMeasure_restrict.2 (measure_ne_top_of_subset unitAnnulus_subset_ball
    measure_ball_lt_top.ne)

private theorem aestronglyMeasurable_restrict_unitAnnulus
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hbc : ContinuousOn b (closedBall 0 1)) :
    AEStronglyMeasurable b (volume.restrict (unitAnnulus (n := n) : Set E)) :=
  (hbc.mono unitAnnulus_subset_closedBall).aestronglyMeasurable unitAnnulus.isOpen.measurableSet

/-- In the cylinder of half-height and radius `1/4` at a point `ν` of the unit sphere, the
annulus is the region above the cut-off sphere graph: there the points of the unit ball are
automatically outside `closedBall 0 (1/2)`. -/
private theorem unitSphereChart_symm_mem_unitAnnulus_iff (ν : E) (hν : ‖ν‖ = 1)
    {z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)} (hz : z ∈ normalCylinder (1 / 4) (1 / 4)) :
    (unitSphereChart ν hν).symm z ∈ (unitAnnulus (n := n) : Set E) ↔
      unitSphereGraph z.snd < z.fst := by
  rw [← unitSphereChart_symm_mem_ball_iff ν hν hz, coe_unitAnnulus, mem_inter_iff,
    and_iff_left_iff_imp, mem_compl_iff, mem_closedBall_zero_iff, not_le]
  intro _
  have hsq := norm_unitSphereChart_symm_sq ν hν z
  rw [mem_normalCylinder] at hz
  nlinarith [norm_nonneg ((unitSphereChart ν hν).symm z), norm_nonneg z.snd]

/-- The graph of the inner sphere of the annulus, `v ↦ -(1 - √(1 - 4 ‖v‖²)) / 2` near `0`: the
cut-off sphere graph rescaled by `1/2` and reflected, so that the annulus lies above it. -/
private def innerSphereGraph {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] (v : K) :
    ℝ :=
  -(1 / 2) * unitSphereGraph ((-2 : ℝ) • v)

private theorem contDiff_innerSphereGraph {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] {k : ℕ∞} : ContDiff ℝ k (innerSphereGraph (K := K)) :=
  contDiff_const.mul (contDiff_unitSphereGraph.comp (contDiff_const_smul _))

private theorem fderiv_innerSphereGraph {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (v : K) : fderiv ℝ (innerSphereGraph (K := K)) v =
      fderiv ℝ (unitSphereGraph (K := K)) ((-2 : ℝ) • v) := by
  have hd : HasFDerivAt (unitSphereGraph (K := K))
      (fderiv ℝ (unitSphereGraph (K := K)) ((-2 : ℝ) • v)) ((-2 : ℝ) • v) :=
    ((contDiff_unitSphereGraph (k := 1)).differentiable one_ne_zero _).hasFDerivAt
  have h := (hd.comp v ((hasFDerivAt_id v).const_smul (-2 : ℝ))).const_mul (-(1 / 2) : ℝ)
  rw [show innerSphereGraph (K := K) =
    fun y => -(1 / 2) * (unitSphereGraph ∘ HSMul.hSMul (-2 : ℝ)) y from rfl, h.fderiv]
  ext w
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, map_smul]
  ring

/-- In the cylinder of half-height and radius `1/8` about the centre of the coordinates
`(t, v) ↦ x + t p + v` at a point `x = p / 2` of the inner sphere, the annulus is the region above
`innerSphereGraph`, evaluated at any point `w` of a model space with `‖w‖ = ‖v‖`. -/
private theorem mem_unitAnnulus_iff_innerSphereGraph_lt {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] {p : E} (hp : ‖p‖ = 1) {t : ℝ} {v : E} {w : K} (hw : ‖w‖ = ‖v‖)
    (hv : ⟪p, v⟫_ℝ = 0) (ht : |t| < 1 / 8) (hv8 : ‖v‖ < 1 / 8) :
    (2⁻¹ : ℝ) • p + t • p + v ∈ (unitAnnulus (n := n) : Set E) ↔ innerSphereGraph w < t := by
  have hsq : ‖(2⁻¹ : ℝ) • p + t • p + v‖ ^ 2 = (1 / 2 + t) ^ 2 + ‖v‖ ^ 2 := by
    rw [← add_smul, norm_add_sq_real, norm_smul, inner_smul_left, hv, hp, Real.norm_eq_abs]
    simp [sq_abs]
  have hv2 : ‖(-2 : ℝ) • w‖ = 2 * ‖v‖ := by rw [norm_smul, hw]; norm_num
  rw [innerSphereGraph, unitSphereGraph_of_norm_le (by rw [hv2]; linarith), hv2, mem_unitAnnulus]
  have ht' := abs_lt.1 ht
  have hn0 := norm_nonneg ((2⁻¹ : ℝ) • p + t • p + v)
  have hvn := norm_nonneg v
  have hs : (0 : ℝ) ≤ 1 - (2 * ‖v‖) ^ 2 := by nlinarith
  have hsqrt := Real.sq_sqrt hs
  have hsqrt0 := Real.sqrt_nonneg (1 - (2 * ‖v‖) ^ 2)
  constructor
  · rintro ⟨-, h⟩
    -- `(1 + 2t)² > 1 - 4 ‖v‖²` and `1 + 2t > 0`, so `1 + 2t > √(1 - 4 ‖v‖²)`.
    nlinarith
  · intro h
    refine ⟨by nlinarith, ?_⟩
    nlinarith

/-- **Boundary charts of the annulus.** At every frontier point of the annulus there are rigid
coordinates, over the fixed model space `ℝⁿ`, in which the annulus is the region above the graph of
a smooth function with `α`-Hölder derivative inside a normal cylinder: the cut-off sphere graph on
the outer sphere and `innerSphereGraph` on the inner one. These are the charts that the global
`C^{1,β}` estimate takes as input. -/
private theorem exists_frontier_unitAnnulus_chart {α : ℝ≥0} (hα1 : α ≤ 1) :
    ∀ x ∈ frontier (unitAnnulus (n := n) : Set E),
      ∃ (e : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)))
        (γ : EuclideanSpace ℝ (Fin n) → ℝ) (h₀ r₀ : ℝ) (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧
          γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧ HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ (unitAnnulus (n := n) : Set E) ↔
            γ z.snd < z.fst) := by
  have : Fact (Module.finrank ℝ E = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  intro x hx
  rcases frontier_unitAnnulus_subset hx with hx1 | hx2
  · -- The outer sphere: the chart of the unit ball at `x`.
    have hν : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx1
    have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hν]; exact one_ne_zero)
    obtain ⟨Kγ, hγK⟩ := exists_holderWith_fderiv_unitSphereGraph (K := (ℝ ∙ x)ᗮ) hα1
    exact exists_frontier_chart_of_linearIsometryEquiv
      (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n hx0).repr
      ⟨unitSphereChart x hν, unitSphereGraph, 1 / 4, 1 / 4, Kγ, unitSphereChart_apply_self x hν,
        by norm_num, by norm_num, unitSphereGraph_zero, contDiff_unitSphereGraph, hγK,
        fun z hz => unitSphereChart_symm_mem_unitAnnulus_iff x hν hz⟩
  · -- The inner sphere: the chart of the unit ball at `-2x`, moved so that it is centred at `x`,
    -- with the reflected and rescaled graph `innerSphereGraph`.
    have hx' : ‖x‖ = 1 / 2 := mem_sphere_zero_iff_norm.1 hx2
    set p : E := (2 : ℝ) • x
    have hp : ‖p‖ = 1 := by rw [norm_smul, hx']; norm_num
    have hν : ‖-p‖ = 1 := by rw [norm_neg, hp]
    have hν0 : -p ≠ 0 := norm_ne_zero_iff.1 (by rw [hν]; exact one_ne_zero)
    have hxp : x = (2⁻¹ : ℝ) • p := by simp [p, smul_smul]
    obtain ⟨Kγ, hγK⟩ := exists_holderWith_fderiv_unitSphereGraph (K := (ℝ ∙ -p)ᗮ) hα1
    refine exists_frontier_chart_of_linearIsometryEquiv
      (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n hν0).repr
      ⟨(AffineIsometryEquiv.vaddConst ℝ (x + p)).symm.trans (unitSphereChart (-p) hν),
        innerSphereGraph, 1 / 8, 1 / 8, Kγ * 2 ^ (α : ℝ), ?_, by norm_num, by norm_num,
        by simp [innerSphereGraph], contDiff_innerSphereGraph, fun v w => ?_, fun z hz => ?_⟩
    · simp [vsub_eq_sub]
    · -- The derivative of `innerSphereGraph` is that of the sphere graph at `-2v`.
      rw [fderiv_innerSphereGraph, fderiv_innerSphereGraph]
      refine (hγK _ _).trans_eq ?_
      have h2 : ‖(-2 : ℝ)‖₊ = 2 := by norm_num [← NNReal.coe_inj]
      rw [edist_smul₀, h2, ENNReal.smul_def, smul_eq_mul,
        ENNReal.mul_rpow_of_nonneg _ _ α.coe_nonneg, ← mul_assoc, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg]
    · rw [mem_normalCylinder] at hz
      have hv : ⟪p, (z.snd : E)⟫_ℝ = 0 := by
        have h := Submodule.mem_orthogonal_singleton_iff_inner_right.1 z.snd.property
        rwa [inner_neg_left, neg_eq_zero] at h
      have hpt : ((AffineIsometryEquiv.vaddConst ℝ (x + p)).symm.trans
          (unitSphereChart (-p) hν)).symm z = (2⁻¹ : ℝ) • p + z.fst • p + (z.snd : E) := by
        simp only [AffineIsometryEquiv.coe_symm_trans, Function.comp_apply,
          unitSphereChart_symm_apply, AffineIsometryEquiv.symm_symm,
          AffineIsometryEquiv.coe_vaddConst, vadd_eq_add]
        rw [hxp]
        simp only [smul_neg]
        abel
      rw [hpt]
      exact mem_unitAnnulus_iff_innerSphereGraph_lt hp (Submodule.norm_coe z.snd).symm hv
        (abs_lt.2 ⟨hz.1, hz.2.1⟩)
        (by simpa using hz.2.2)

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

/-- **The correction is bounded.** For every bound `B` there is `C ≥ 0` such that for coefficients
`b`, uniformly elliptic with lower constant `λ` and continuous on the closed unit ball, whose
correction field `(b - A) ∇Φ` is continuous and bounded by `η B` there, every solution `ψ ∈ H¹₀` of
`-div (b ∇ψ) = div ((b - A) ∇Φ)` on the annulus satisfies `|ψ| ≤ C η` almost everywhere. This is
Stampacchia's global bound, for a divergence datum in `L^q` with `q = n + 3 > max 2 (n + 1)`. -/
private theorem exists_ae_abs_correction_le {lam : ℝ} (hlam : 0 < lam) (B : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {κ Lam η : ℝ}
      {ψ : W1p0 volume (unitAnnulus (n := n)) 2},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam → ContinuousOn b (closedBall 0 1) →
      ContinuousOn (correctionField b A κ) (closedBall 0 1) → 0 ≤ η →
      (∀ z ∈ closedBall (0 : E) 1, ‖correctionField b A κ z‖ ≤ η * B) →
      (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
        energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
          -∫ z in (unitAnnulus (n := n) : Set E),
            ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ) →
      ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        |W1p.value (ψ : W1p volume unitAnnulus 2) z| ≤ C * η := by
  obtain ⟨CS, hCS, HS⟩ := exists_ae_abs_value_le_mul_div_mul_rpow_divergence
    (mu := volume) (ι := Fin (n + 1)) (q := (n : ℝ≥0) + 3)
    (by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by simp)
  -- The volume factors in Stampacchia's bound and in the `L^q` norm of a bounded field.
  set Vq : ℝ := (measureUnivNNReal (volume.restrict (unitAnnulus (n := n) : Set E)) : ℝ) ^
    (((n : ℝ≥0) + 3 : ℝ≥0) : ℝ≥0∞).toReal⁻¹
  set Vs : ℝ := volume.real (unitAnnulus (n := n) : Set E) ^
    ((Fintype.card (Fin (n + 1)) : ℝ)⁻¹ - (((n : ℝ≥0) + 3 : ℝ≥0) : ℝ)⁻¹)
  have : 0 ≤ Vq := by positivity
  have : 0 ≤ Vs := by positivity
  refine ⟨CS * (Vq * B) / lam * Vs, by positivity, fun {b A κ Lam η ψ} hb hbc hHc hη hHb hψ => ?_⟩
  have hHq : MemLp (correctionField b A κ) (((n : ℝ≥0) + 3 : ℝ≥0) : ℝ≥0∞)
      (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    hHc.memLp_restrict_of_subset_isCompact (isCompact_closedBall 0 1)
      unitAnnulus.isOpen.measurableSet unitAnnulus_subset_closedBall _
  have hFq : (eLpNorm (correctionField b A κ) (((n : ℝ≥0) + 3 : ℝ≥0) : ℝ≥0∞)
      (volume.restrict (unitAnnulus (n := n) : Set E))).toReal ≤ Vq * (η * B) := by
    rw [← Lp.norm_toLp _ hHq]
    refine Lp.norm_le_of_ae_bound (by positivity) ?_
    filter_upwards [hHq.coeFn_toLp, ae_restrict_mem unitAnnulus.isOpen.measurableSet]
      with z h1 h2
    rw [h1]
    exact hHb z (unitAnnulus_subset_closedBall h2)
  have habs := HS (measure_ne_top_of_subset unitAnnulus_subset_ball measure_ball_lt_top.ne)
    (hb.mono_set unitAnnulus_subset_closedBall) (aestronglyMeasurable_restrict_unitAnnulus hbc)
    aestronglyMeasurable_const (fun _ _ => le_of_eq norm_zero) (fun _ _ => le_rfl) hHq hψ
  filter_upwards [habs] with z hz
  refine hz.trans ?_
  calc _ ≤ CS * (Vq * (η * B)) / lam * Vs := by gcongr
    _ = CS * (Vq * B) / lam * Vs * η := by ring

/-- **The gradient of the correction is bounded.** For an exponent `0 < α ≤ 1` and ellipticity
constants there is `C ≥ 0` such that for coefficients `b`, uniformly elliptic on the closed unit
ball and `α`-Hölder there with constant at most `1`, and a correction field `(b - A) ∇Φ` that is
`α`-Hölder there with constant `K_G`, every solution `ψ ∈ H¹₀` of `-div (b ∇ψ) = div ((b - A) ∇Φ)`
on the annulus has `‖∇ψ‖ ≤ C (K_G + ‖ψ‖)` almost everywhere. This is the global `C^{1,β}` estimate
on the annulus, in the charts of `exists_frontier_unitAnnulus_chart`. -/
private theorem exists_ae_norm_gradient_correction_le {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (lam Lam κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Kb KG : ℝ≥0}
      {ψ : W1p0 volume (unitAnnulus (n := n)) 2},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ 1 →
      HolderOnWith KG α (correctionField b A κ) (closedBall 0 1) →
      (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
        energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
          -∫ z in (unitAnnulus (n := n) : Set E),
            ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ) →
      ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        ‖W1p.gradient (ψ : W1p volume unitAnnulus 2) z‖ ≤ C * (KG + ‖ψ‖) := by
  set β : ℝ≥0 := min α (1 / 2)
  have hβ : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨C, -, H⟩ := exists_holderOnWith_gradient_closure_of_forall_graph (n := n) hβ hβ1
    (min_le_left _ _) (q := ⊤) le_top (by simp [hβ1.le])
    (isBounded_ball.subset unitAnnulus_subset_ball) (exists_frontier_unitAnnulus_chart hα1)
    lam Lam 1
  refine ⟨|C|, abs_nonneg C, fun {b A Kb KG ψ} hb hbh hKb hH hψ => ?_⟩
  -- The equation `-div (b ∇ψ) = -div (-(b - A) ∇Φ)`, tested against test functions.
  obtain ⟨g, hg, -, hgb⟩ := H (u := ψ) (a := b) (G := -correctionField b A κ) (f := 0)
    (Ka := Kb) (KG := KG) (hb.mono_set closure_unitAnnulus_subset)
    (hbh.mono closure_unitAnnulus_subset) hKb (hH.neg.mono closure_unitAnnulus_subset)
    MemLp.zero (fun φ => by
      rw [hψ ⟨W1p.ofTestFunctionₗ volume unitAnnulus 2 φ, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
      simp only [Pi.neg_apply, inner_neg_left, integral_neg, Pi.zero_apply, zero_mul,
        integral_zero, add_zero]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with z hz
      rw [W1p.gradient_ofTestFunctionₗ, hz])
  filter_upwards [hg, ae_restrict_mem unitAnnulus.isOpen.measurableSet] with z hz hzD
  rw [hz]
  refine (hgb z (subset_closure hzD)).trans ?_
  rw [eLpNorm_zero, ENNReal.toReal_zero, add_zero]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)

/-- **The correction is small.** Fix a point `ν` of the unit sphere, an exponent `0 < α ≤ 1`,
ellipticity constants and `κ`. There are `ρ > 0` and `C ≥ 0` such that for every coefficient field
`b`, uniformly elliptic on the closed unit ball with these constants and `α`-Hölder there with
constant at most `η ≤ 1`, and every matrix `A` with `‖b - A‖ ≤ η` there, the correction
`ψ ∈ H¹₀` of `exists_correction_of_uniformlyEllipticOn` is bounded by `C η` almost everywhere, has
gradient bounded by `C η` almost everywhere, and has a representative that is `C η`-Lipschitz on
`B(ν, ρ)` and vanishes at `ν`. This combines the energy bound for `ψ` with Stampacchia's global
bound and the global `C^{1,β}` estimate on the annulus. -/
private theorem exists_correction (ν : E) (hν : ‖ν‖ = 1) {α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    {lam : ℝ} (hlam : 0 < lam) (Lam κ : ℝ) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
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
          ψ' ∧ LipschitzOnWith (C * η).toNNReal ψ' (ball ν ρ) ∧ ψ' ν = 0 ∧
        (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          |W1p.value (ψ : W1p volume unitAnnulus 2) z| ≤ C * η) ∧
        ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          ‖W1p.gradient (ψ : W1p volume unitAnnulus 2) z‖ ≤ C * η := by
  obtain ⟨K, B, hK, hB⟩ := exists_holderOnWith_gradient_gaussBarrier (n := n) κ hα1
  obtain ⟨C₂, hC₂, HS⟩ := exists_ae_abs_correction_le (n := n) hlam B
  obtain ⟨κ', hκ', HG⟩ := exists_ae_norm_gradient_correction_le (n := n) hα hα1 lam Lam κ
  -- The volume factor in the `L²` bound of the correction field.
  set V : ℝ := (measureUnivNNReal (volume.restrict (unitAnnulus (n := n) : Set E)) : ℝ) ^
    ((2 : ℝ≥0∞).toReal⁻¹)
  have : 0 ≤ V := by positivity
  set C₁ := κ' * ((K + B) + 10 / lam * (V * B))
  refine ⟨1 / 4, by norm_num, C₁ + C₂, by positivity, fun {b A Kb η} hb hbh hKb hη1 hbA => ?_⟩
  have hη : 0 ≤ η := Kb.coe_nonneg.trans hKb
  obtain ⟨hHh, hHb⟩ := holderOnWith_correctionField (κ := κ) hK hB hbh hKb hbA
  obtain ⟨ψ, hψ, hψn⟩ := exists_correction_of_uniformlyEllipticOn hb
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα)) (hHh.continuousOn hα)
  have hψb := hψn (η * B) (by positivity) hHb
  have hgrad : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume unitAnnulus 2) z‖ ≤ C₁ * η := by
    filter_upwards [HG hb hbh (hKb.trans hη1) hHh hψ] with z hz
    refine hz.trans ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    calc κ' * (η * (K + B) + ‖ψ‖) ≤ κ' * (η * (K + B) + 10 / lam * (V * (η * B))) := by
          gcongr
      _ = C₁ * η := by ring
  obtain ⟨ψ', hae, hLip, h0⟩ := W1p0.exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le
    isClosed_closedBall unitAnnulus_subset_closedBall ψ (x := ν)
    (by rw [closure_compl, interior_closedBall _ one_ne_zero]; simp [hν])
    (by norm_num : (0 : ℝ) < 1 / 4) (M := (C₁ * η).toNNReal) (by
      filter_upwards [(ae_restrict_iff' unitAnnulus.isOpen.measurableSet).1 hgrad] with z hz hzD
      exact (hz hzD.1).trans (Real.le_coe_toNNReal _))
  -- Stampacchia's bound: `|ψ| ≤ C₂ η`, since the correction field is bounded by `η B`.
  have habs := HS hb (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα))
    (hHh.continuousOn hα) hη hHb hψ
  have hC₁η : 0 ≤ C₁ * η := mul_nonneg (by positivity) hη
  have hC₂η : 0 ≤ C₂ * η := mul_nonneg hC₂ hη
  refine ⟨ψ, ψ', hψ, hae, hLip.weaken (Real.toNNReal_le_toNNReal (by linarith)), h0, ?_, ?_⟩
  · filter_upwards [habs] with z hz
    linarith
  · filter_upwards [hgrad] with z hz
    linarith

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

/-- The comparison function `θ (W + ψ) + s₀`, for a Sobolev representative `W` of the Gaussian
barrier `Φ`, is almost everywhere `θ (Φ + ψ) + s₀`. -/
private theorem value_smul_add_add_const_ae {κ : ℝ} {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWv : W1p.value W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] gaussBarrier κ)
    (θ : ℝ) (ψ : W1p volume (unitAnnulus (n := n)) 2) (s₀ : ℝ) :
    W1p.value (θ • (W + ψ) + W1p.const s₀) =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => θ * (gaussBarrier κ z + W1p.value ψ z) + s₀ := by
  filter_upwards [W1p.value_add_const_ae (θ • (W + ψ)) s₀, W1p.value_smul_ae θ (W + ψ),
    W1p.value_add_ae W ψ, hWv] with z e1 e2 e3 e4
  simp only [e1, e2, Pi.smul_apply, smul_eq_mul, e3, Pi.add_apply, e4]

/-- The weak gradient of the comparison function `θ (W + ψ) + s₀`, for a Sobolev representative
`W` of the Gaussian barrier `Φ`, is almost everywhere `θ (∇Φ + ∇ψ)`. -/
private theorem gradient_smul_add_add_const_ae {κ : ℝ} {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      ∇ (gaussBarrier κ)) (θ : ℝ) (ψ : W1p volume (unitAnnulus (n := n)) 2) (s₀ : ℝ) :
    W1p.gradient (θ • (W + ψ) + W1p.const s₀) =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => θ • (∇ (gaussBarrier κ) z + W1p.gradient ψ z) := by
  rw [W1p.gradient_add_const]
  filter_upwards [W1p.gradient_smul_ae θ (W + ψ), W1p.gradient_add_ae W ψ, hWg] with z e1 e2 e3
  simp only [e1, Pi.smul_apply, e2, Pi.add_apply, e3]

/-- **The mass term of the comparison function.** For a mass coefficient `0 ≤ c ≤ γ` with
`c s₀ ≤ 0` and a correction `|ψ| ≤ Ψ`, the mass term of `V = θ (W + ψ) + s₀`, `θ ≥ 0`, tested
against `w ≥ 0`, is at most `γ (1 + Ψ) ∫ θ w`, since `Φ ≤ 1`. -/
private theorem setIntegral_mul_value_smul_add_add_const_le {c : E → ℝ} {κ γ Ψ : ℝ} (hκ : 1 ≤ κ)
    (hcL : MemLp c ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z)
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ)
    {ψ : W1p volume (unitAnnulus (n := n)) 2}
    (hψb : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E), |W1p.value ψ z| ≤ Ψ)
    {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWv : W1p.value W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] gaussBarrier κ)
    {s₀ θ : ℝ} (hcs : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0) (hθ : 0 ≤ θ)
    {w : W1p volume (unitAnnulus (n := n)) 2}
    (hw : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E), 0 ≤ W1p.value w z) :
    ∫ z in (unitAnnulus (n := n) : Set E),
      c z * W1p.value (θ • (W + ψ) + W1p.const s₀) z * W1p.value w z ≤
      γ * (1 + Ψ) * ∫ z in (unitAnnulus (n := n) : Set E), θ * W1p.value w z := by
  have hcV : MemLp (fun z => c z * W1p.value (θ • (W + ψ) + W1p.const s₀) z) 2
      (volume.restrict (unitAnnulus (n := n) : Set E)) := hcL.fun_mul (Lp.memLp _)
  rw [← integral_const_mul]
  refine integral_mono_ae (hcV.integrable_mul (Lp.memLp _))
    ((((Lp.memLp _).integrable one_le_two).const_mul θ).const_mul _) ?_
  filter_upwards [value_smul_add_add_const_ae hWv θ ψ s₀, hψb, hw,
    ae_restrict_mem unitAnnulus.isOpen.measurableSet] with z e1 e6 e7 hz
  rw [e1]
  have hΦ1 := gaussBarrier_le_one (zero_le_one.trans hκ) z
  have hψz := (le_abs_self _).trans e6
  have hΨ : 0 ≤ Ψ := (abs_nonneg _).trans e6
  -- `c (θ (Φ + ψ) + s₀) ≤ θ γ (1 + Ψ)`, tested against `w ≥ 0`.
  have h3 : c z * (gaussBarrier κ z + W1p.value ψ z) ≤ γ * (1 + Ψ) :=
    (mul_le_mul_of_nonneg_left (by linarith) (hc0 z hz)).trans
      (mul_le_mul_of_nonneg_right (hcγ z hz) (by linarith))
  have hpt : c z * (θ * (gaussBarrier κ z + W1p.value ψ z) + s₀) ≤ γ * (1 + Ψ) * θ :=
    calc _ = θ * (c z * (gaussBarrier κ z + W1p.value ψ z)) + c z * s₀ := by ring
      _ ≤ θ * (γ * (1 + Ψ)) + 0 := add_le_add (mul_le_mul_of_nonneg_left h3 hθ) (hcs z hz)
      _ = _ := by ring
  calc _ ≤ γ * (1 + Ψ) * θ * W1p.value w z := mul_le_mul_of_nonneg_right hpt e7
    _ = _ := by ring

/-- **The drift term of the comparison function.** For a drift `‖d‖ ≤ δ`, a correction with
`‖∇ψ‖ ≤ Ψ'` and a bound `‖∇Φ‖ ≤ B` for the barrier, the drift term of `V = θ (W + ψ) + s₀`,
`θ ≥ 0`, tested against `w ≥ 0`, is at most `δ (B + Ψ') ∫ θ w`. -/
private theorem setIntegral_inner_gradient_smul_add_add_const_le {d : E → E} {κ δ B Ψ' : ℝ}
    (hdL : MemLp d ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hdδ : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖d z‖ ≤ δ)
    (hB : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ B)
    {ψ : W1p volume (unitAnnulus (n := n)) 2}
    (hψg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E), ‖W1p.gradient ψ z‖ ≤ Ψ')
    {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      ∇ (gaussBarrier κ)) {s₀ θ : ℝ} (hθ : 0 ≤ θ) {w : W1p volume (unitAnnulus (n := n)) 2}
    (hw : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E), 0 ≤ W1p.value w z) :
    ∫ z in (unitAnnulus (n := n) : Set E),
      ⟪d z, W1p.gradient (θ • (W + ψ) + W1p.const s₀) z⟫_ℝ * W1p.value w z ≤
      δ * (B + Ψ') * ∫ z in (unitAnnulus (n := n) : Set E), θ * W1p.value w z := by
  rw [← integral_const_mul]
  refine integral_mono_ae ((memLp_inner_gradient hdL _).integrable_mul (Lp.memLp _))
    ((((Lp.memLp _).integrable one_le_two).const_mul θ).const_mul _) ?_
  filter_upwards [gradient_smul_add_add_const_ae hWg θ ψ s₀, hψg, hw,
    ae_restrict_mem unitAnnulus.isOpen.measurableSet] with z e1 e2 e3 hz
  rw [e1]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hdδ z hz)
  have h1 : ⟪d z, θ • (∇ (gaussBarrier κ) z + W1p.gradient ψ z)⟫_ℝ ≤ δ * (B + Ψ') * θ := by
    rw [inner_smul_right, mul_comm θ]
    refine mul_le_mul_of_nonneg_right ((real_inner_le_norm _ _).trans ?_) hθ
    exact mul_le_mul (hdδ z hz) ((norm_add_le _ _).trans
      (add_le_add (hB z (unitAnnulus_subset_closedBall hz)) e2)) (norm_nonneg _) hδ
  calc _ ≤ δ * (B + Ψ') * θ * W1p.value w z := mul_le_mul_of_nonneg_right h1 e3
    _ = _ := by ring

/-- **The corrected barrier is a weak subsolution with lower-order terms.** For a drift `‖d‖ ≤ δ`,
a mass coefficient `0 ≤ c ≤ γ` with `c s₀ ≤ 0`, a correction with `|ψ| ≤ Ψ` and `‖∇ψ‖ ≤ Ψ'`, a bound
`‖∇Φ‖ ≤ B` for the barrier and `γ (1 + Ψ) + δ (B + Ψ') ≤ λ κ e^{-κ}`, the function
`s₀ + θ (Φ + ψ)`, `θ ≥ 0`, satisfies `-div (b ∇·) + ⟪d, ∇·⟫ + c · ≤ 0` weakly on the annulus: the
strict margin `λ κ e^{-κ}` of the barrier absorbs the drift and mass terms. -/
private theorem energyFormH1_add_mul_correction_nonpos
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {d : E → E} {c : E → ℝ} {κ lam Lam T δ γ B Ψ Ψ' : ℝ}
    (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (hT : A.trace ≤ T) (hκ : 1 ≤ κ)
    (hκT : 2 * |T| + lam ≤ lam * κ)
    (hcb : MemLp (fun z => energyIntegrand (b z) 0 0) ⊤
      (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hdL : MemLp d ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hdδ : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖d z‖ ≤ δ)
    (hcL : MemLp c ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z)
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ)
    (hB : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ B)
    (hγ : γ * (1 + Ψ) + δ * (B + Ψ') ≤ lam * κ * Real.exp (-κ))
    {ψ : W1p0 volume (unitAnnulus (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ)
    (hψb : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      |W1p.value (ψ : W1p volume unitAnnulus 2) z| ≤ Ψ)
    (hψg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume unitAnnulus 2) z‖ ≤ Ψ')
    {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWv : W1p.value W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] gaussBarrier κ)
    (hWg : W1p.gradient W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      ∇ (gaussBarrier κ)) {s₀ θ : ℝ}
    (hcs : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0) (hθ : 0 ≤ θ)
    (w : W1p0 volume (unitAnnulus (n := n)) 2)
    (hw : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      0 ≤ W1p.value (w : W1p volume unitAnnulus 2) z) :
    energyFormH1 b d c (θ • (W + (ψ : W1p volume unitAnnulus 2)) + W1p.const s₀)
      (w : W1p volume unitAnnulus 2) ≤ 0 := by
  set Vf := θ • (W + (ψ : W1p volume unitAnnulus 2)) + W1p.const s₀
  have hprin : energyFormH1 b 0 0 Vf (w : W1p volume unitAnnulus 2) =
      θ * energyFormH1 (fun _ => A) 0 0 W (w : W1p volume unitAnnulus 2) := by
    rw [energyFormH1_add_const_left, energyFormH1_smul_left,
      energyFormH1_add_correction hcb hWg hψ w]
  have hΦ := mul_le_mul_of_nonneg_left (energyFormH1_gaussBarrier_le hb.pos.le hA hT hκ hκT hWv w
    hw) hθ
  have hmass := setIntegral_mul_value_smul_add_add_const_le hκ hcL hc0 hcγ hψb hWv hcs hθ hw
  have hdrift := setIntegral_inner_gradient_smul_add_add_const_le hdL hdδ hB hψg hWg (s₀ := s₀)
    hθ hw
  have hw0 : 0 ≤ ∫ z in (unitAnnulus (n := n) : Set E),
      θ * W1p.value (w : W1p volume unitAnnulus 2) z := by
    rw [integral_const_mul]
    exact mul_nonneg hθ (integral_nonneg_of_ae hw)
  have hsum := mul_le_mul_of_nonneg_right hγ hw0
  rw [integral_const_mul] at hmass hdrift hsum
  rw [energyFormH1_eq_energyFormH1_zero_add_setIntegral_inner hcb hdL hcL,
    energyFormH1_eq_energyFormH1_zero_add_setIntegral (b := 0) hcb hcL, hprin]
  linarith

/-- **Boundary values of the comparison.** If `ĝ`, continuous on the closed unit ball and almost
everywhere equal to `uε`, is at least `s₀` on the outer sphere and at least `s₀ + θ Φ` on the inner
sphere, then `(θ (W + ψ) + s₀ - uε)⁺` vanishes on the frontier of the annulus in the Sobolev sense,
for a Sobolev representative `W` of the barrier and a correction `ψ ∈ H¹₀`. -/
private theorem posPart_smul_add_add_const_sub_mem_w1p0Submodule {κ : ℝ}
    {W : W1p volume (unitAnnulus (n := n)) 2}
    (hWv : W1p.value W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] gaussBarrier κ)
    (ψ : W1p0 volume (unitAnnulus (n := n)) 2) {uε : W1p volume (unitAnnulus (n := n)) 2}
    {ĝ : E → ℝ} (hĝ : ContinuousOn ĝ (closedBall 0 1))
    (huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ) {s₀ θ : ℝ}
    (h1 : ∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z)
    (h2 : ∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * gaussBarrier κ z ≤ ĝ z) :
    W1p.posPart (by norm_num) (θ • (W + (ψ : W1p volume unitAnnulus 2)) + W1p.const s₀ - uε) ∈
      w1p0Submodule volume unitAnnulus 2 := by
  have hrw : θ • (W + (ψ : W1p volume unitAnnulus 2)) + W1p.const s₀ - uε =
      θ • (ψ : W1p volume unitAnnulus 2) + (θ • W + W1p.const s₀ - uε) := by
    simp only [smul_add]
    abel
  rw [hrw]
  refine W1p.posPart_add_mem_w1p0Submodule _ (isBounded_ball.subset unitAnnulus_subset_ball)
    (Submodule.smul_mem _ θ ψ.property) (g := fun z => s₀ + θ * gaussBarrier κ z - ĝ z)
    (((continuousOn_const.add (continuousOn_const.mul
      (contDiff_gaussBarrier κ (k := 0)).continuous.continuousOn)).sub hĝ).mono
      closure_unitAnnulus_subset) (fun z hz => ?_) ?_
  · rcases frontier_unitAnnulus_subset hz with h | h
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

/-- **Coercivity with a small drift.** For coefficients `b` uniformly elliptic on the annulus with
lower constant `λ`, a drift `‖d‖ ≤ δ` with `4 δ ≤ λ` and a mass coefficient `0 ≤ c ≤ γ`, the energy
form is coercive on `H¹₀` of the annulus. -/
private theorem exists_pos_mul_norm_sq_le_energyFormH1
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {d : E → E} {c : E → ℝ} {lam Lam δ γ : ℝ}
    (hb : UniformlyEllipticOn (unitAnnulus (n := n) : Set E) b lam Lam)
    (hm : AEStronglyMeasurable b (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hdm : AEStronglyMeasurable d (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hdδ : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖d z‖ ≤ δ) (hδ : 4 * δ ≤ lam)
    (hcm : AEStronglyMeasurable c (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖c z‖ ≤ γ)
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z) :
    ∃ C > 0, ∀ w : W1p0 volume (unitAnnulus (n := n)) 2,
      C * ‖w‖ ^ 2 ≤
        energyFormH1 b d c (w : W1p volume unitAnnulus 2) (w : W1p volume unitAnnulus 2) := by
  have hlam := hb.pos
  -- The drift bound `δ` is nonnegative, as the annulus is not empty.
  have hδ0 : 0 ≤ δ := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one
    have hz : (3 / 4 : ℝ) • x ∈ (unitAnnulus (n := n) : Set E) := mem_unitAnnulus.2 (by
      rw [norm_smul, mem_sphere_zero_iff_norm.1 hx]; norm_num)
    exact (norm_nonneg _).trans (hdδ _ hz)
  exact ⟨_, div_pos (by nlinarith) (by positivity), fun w =>
    hb.mul_norm_sq_le_energyFormH1_self_of_subset_ball hm hdm hcm hdδ hcγ hc0
      unitAnnulus_subset_ball w.property⟩

/-- **The comparison on the annulus.** Let `uε ∈ H¹` of the annulus be a weak supersolution of
`-div (b ∇uε) + ⟪d, ∇uε⟫ + c uε ≥ 0` for coefficients `b`, uniformly elliptic and continuous on the
closed unit ball, a measurable drift `‖d‖ ≤ δ` with `4 δ ≤ λ`, and a measurable mass coefficient
`0 ≤ c ≤ γ`, and let `uε` equal almost everywhere a function `ĝ` continuous there. If `ĝ ≥ s₀` on
the outer sphere and `ĝ ≥ s₀ + θ Φ` on the inner sphere, with `θ ≥ 0` and `c s₀ ≤ 0`, then
`s₀ + θ (Φ + ψ) ≤ ĝ` almost everywhere on the annulus, where `Φ` is the Gaussian barrier and `ψ`
its correction, provided `|ψ| ≤ Ψ`, `‖∇ψ‖ ≤ Ψ'`, `‖∇Φ‖ ≤ B` and
`γ (1 + Ψ) + δ (B + Ψ') ≤ λ κ e^{-κ}`: the lower-order terms are then absorbed by the margin of the
barrier. -/
private theorem ae_add_mul_le_of_supersolution {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {d : E → E} {c : E → ℝ}
    {κ lam Lam T δ γ B Ψ Ψ' : ℝ}
    (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hbc : ContinuousOn b (closedBall 0 1)) (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hT : A.trace ≤ T) (hκ : 1 ≤ κ) (hκT : 2 * |T| + lam ≤ lam * κ)
    (hdm : AEStronglyMeasurable d (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hdδ : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖d z‖ ≤ δ) (hδ : 4 * δ ≤ lam)
    (hcm : AEStronglyMeasurable c (volume.restrict (unitAnnulus (n := n) : Set E)))
    (hc0 : ∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z)
    (hcγ : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ)
    (hB : ∀ z ∈ closedBall (0 : E) 1, ‖∇ (gaussBarrier κ) z‖ ≤ B)
    (hγ : γ * (1 + Ψ) + δ * (B + Ψ') ≤ lam * κ * Real.exp (-κ))
    {ψ : W1p0 volume (unitAnnulus (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ)
    (hψb : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      |W1p.value (ψ : W1p volume unitAnnulus 2) z| ≤ Ψ)
    (hψg : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      ‖W1p.gradient (ψ : W1p volume unitAnnulus 2) z‖ ≤ Ψ')
    {uε : W1p volume (unitAnnulus (n := n)) 2}
    (huε : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        0 ≤ W1p.value (v : W1p volume unitAnnulus 2) z) →
      0 ≤ energyFormH1 b d c uε (v : W1p volume unitAnnulus 2))
    {ĝ : E → ℝ} (hĝ : ContinuousOn ĝ (closedBall 0 1))
    (huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ) {s₀ θ : ℝ}
    (hcs : ∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0)
    (hθ : 0 ≤ θ) (h1 : ∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z)
    (h2 : ∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * gaussBarrier κ z ≤ ĝ z) :
    ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      s₀ + θ * (gaussBarrier κ z + W1p.value (ψ : W1p volume unitAnnulus 2) z) ≤ ĝ z := by
  obtain ⟨W, hWv, hWg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    (Omega := unitAnnulus (n := n)) (mu := volume) (p := 2) isOpen_univ
    (contDiff_gaussBarrier κ).contDiffOn (isCompact_closedBall 0 1) unitAnnulus_subset_closedBall
    (subset_univ _)
  have hbD := hb.mono_set unitAnnulus_subset_closedBall
  have hm := aestronglyMeasurable_restrict_unitAnnulus hbc
  have hcb := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    hbD.upper_nonneg hm aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => hbD.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  -- The lower-order coefficients are essentially bounded, so the energy form splits them off.
  have hcbd : ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖c z‖ ≤ γ := fun z hz => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 z hz)]
    exact hcγ z hz
  have hcL : MemLp c ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    memLp_top_of_bound hcm γ ((ae_restrict_iff' unitAnnulus.isOpen.measurableSet).2
      (ae_of_all _ hcbd))
  have hdL : MemLp d ⊤ (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    memLp_top_of_bound hdm δ ((ae_restrict_iff' unitAnnulus.isOpen.measurableSet).2
      (ae_of_all _ hdδ))
  have hcbc := memLp_energyIntegrand_of_bounds hbD.upper_nonneg hm hdm hcm
    (fun _x hx eta xi => hbD.upper_bound hx eta xi) hdδ hcbd
  set Vf := θ • (W + (ψ : W1p volume unitAnnulus 2)) + W1p.const s₀
  have huv : ∀ w : W1p0 volume (unitAnnulus (n := n)) 2,
      (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        0 ≤ W1p.value (w : W1p volume unitAnnulus 2) z) →
      energyFormH1 b d c Vf (w : W1p volume unitAnnulus 2) ≤
        energyFormH1 b d c uε (w : W1p volume unitAnnulus 2) := fun w hw =>
    (energyFormH1_add_mul_correction_nonpos hb hA hT hκ hκT hcb hdL hdδ hcL hc0 hcγ hB hγ hψ hψb
      hψg hWv hWg hcs hθ w hw).trans (huε w hw)
  -- On the frontier `Vf - uε` is at most `0`, and the energy form is coercive.
  obtain ⟨C, hC, hlower⟩ := exists_pos_mul_norm_sq_le_energyFormH1 hbD hm hdm hdδ hδ hcm hcbd hc0
  have hcomp := value_le_of_energyFormH1_le hcbc
    (posPart_smul_add_add_const_sub_mem_w1p0Submodule hWv ψ hĝ huĝ h1 h2) hC hlower huv
  filter_upwards [hcomp, value_smul_add_add_const_ae hWv θ ψ s₀, huĝ] with z h e2 e7
  simp only [e2, e7] at h
  linarith

/-- **Linear growth along the normal on the annulus.** There are `ρ > 0`, `C ≥ 0` and a bound `B`
for the gradient of the barrier such that the following holds. For coefficients close to a frozen
matrix `A` in the sense of `exists_correction`, closely enough that `C η ≤ κ e^{-κ} / 2`, a drift
`‖d‖ ≤ δ` with `4 δ ≤ λ` and a mass coefficient `0 ≤ c ≤ γ` small enough that
`γ (1 + C η) + δ (B + C η) ≤ λ κ e^{-κ}`, a weak supersolution of
`-div (b ∇uε) + ⟪d, ∇uε⟫ + c uε ≥ 0` on the annulus whose continuous representative `ĝ` is at
least `s₀` on the outer sphere and at least `s₀ + θ Φ` on the inner sphere, with `c s₀ ≤ 0`, grows
linearly into the annulus along the inward normal at `ν`: `s₀ + θ κ e^{-κ} t / 2 ≤ ĝ ((1 - t) ν)`
for small `t > 0`. -/
private theorem exists_add_mul_le_of_supersolution (ν : E) (hν : ‖ν‖ = 1) {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α ≤ 1) {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) {κ : ℝ} (hκ : 1 ≤ κ) :
    ∃ ρ > 0, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {d : E → E} {c : E → ℝ} {Kb : ℝ≥0}
      {η T δ γ : ℝ} {uε : W1p volume (unitAnnulus (n := n)) 2} {ĝ : E → ℝ} {s₀ θ : ℝ},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ η →
      η ≤ 1 → (∀ z ∈ closedBall (0 : E) 1,
        ‖matrixBilinearForm (b z) - matrixBilinearForm A‖ ≤ η) →
      C * η ≤ κ * Real.exp (-κ) / 2 → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      A.trace ≤ T → 2 * |T| + lam ≤ lam * κ →
      AEStronglyMeasurable d (volume.restrict (unitAnnulus (n := n) : Set E)) →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), ‖d z‖ ≤ δ) → 4 * δ ≤ lam →
      AEStronglyMeasurable c (volume.restrict (unitAnnulus (n := n) : Set E)) →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), 0 ≤ c z) →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), c z ≤ γ) →
      γ * (1 + C * η) + δ * (B + C * η) ≤ lam * κ * Real.exp (-κ) →
      (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
        (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          0 ≤ W1p.value (v : W1p volume unitAnnulus 2) z) →
        0 ≤ energyFormH1 b d c uε (v : W1p volume unitAnnulus 2)) →
      ContinuousOn ĝ (closedBall 0 1) →
      W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ →
      (∀ z ∈ (unitAnnulus (n := n) : Set E), c z * s₀ ≤ 0) → 0 ≤ θ →
      (∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z) →
      (∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * gaussBarrier κ z ≤ ĝ z) →
      ∀ t ∈ Ioo 0 (min ρ (1 / 2)), s₀ + θ * (κ * Real.exp (-κ) / 2) * t ≤ ĝ ((1 - t) • ν) := by
  obtain ⟨ρ, hρ, C, hC, H⟩ := exists_correction (n := n) ν hν hα hα1 hlam Lam κ
  obtain ⟨-, B, -, hB⟩ := exists_holderOnWith_gradient_gaussBarrier (n := n) κ (α := 1) le_rfl
  refine ⟨ρ, hρ, C, B, hC, B.coe_nonneg, fun {b A d c Kb η T δ γ uε ĝ s₀ θ} hb hbh hKb hη1 hbA hCη
    hA hT hκT hdm hdδ hδ hcm hc0 hcγ hγ huε hĝ huĝ hcs hθ h1 h2 t ht => ?_⟩
  obtain ⟨ψ, ψ', hψ, hae, hLip, h0, hψb, hψg⟩ := H hb hbh hKb hη1 hbA
  have hcomp := ae_add_mul_le_of_supersolution hb
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα)) hA hT hκ hκT hdm hdδ
    hδ hcm hc0 hcγ hB hγ hψ hψb hψg huε hĝ huĝ hcs hθ h1 h2
  -- On the open set `O = annulus ∩ B(ν, ρ)` the comparison holds pointwise, by continuity.
  set O : Set E := (unitAnnulus (n := n) : Set E) ∩ ball ν ρ
  have hO : IsOpen O := unitAnnulus.isOpen.inter isOpen_ball
  set F : E → ℝ := fun z => max (s₀ + θ * (gaussBarrier κ z + ψ' z) - ĝ z) 0
  have hF : ContinuousOn F O :=
    ((continuousOn_const.add (continuousOn_const.mul
      (((contDiff_gaussBarrier κ (k := 0)).continuous.continuousOn).add
        (hLip.continuousOn.mono inter_subset_right)))).sub
      (hĝ.mono (inter_subset_left.trans unitAnnulus_subset_closedBall))
      ).sup continuousOn_const
  have hF0 : EqOn F 0 O := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hO hF continuousOn_const
    refine ae_restrict_of_ae_restrict_of_subset inter_subset_left ?_
    filter_upwards [hcomp, hae] with z h1 h2
    simp only [F, Pi.zero_apply]
    rw [← h2]
    exact max_eq_right (by linarith)
  have ht0 := ht.1
  have htρ : t < ρ := ht.2.trans_le (min_le_left _ _)
  have ht2 : t < 1 / 2 := ht.2.trans_le (min_le_right _ _)
  have hdist : dist ((1 - t) • ν) ν = t := by
    rw [dist_eq_norm, sub_smul, one_smul, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
      Real.norm_eq_abs, abs_of_pos ht0]
  have hzt : (1 - t) • ν ∈ O := by
    refine ⟨mem_unitAnnulus.2 ?_, ?_⟩
    · rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
      constructor <;> linarith
    · rw [mem_ball, hdist]
      exact htρ
  have hFz := hF0 hzt
  simp only [F, Pi.zero_apply, max_eq_right_iff, sub_nonpos] at hFz
  -- The barrier grows like `κ e^{-κ} t`, and the correction is `C η`-Lipschitz and vanishes at `ν`.
  have hΦ := mul_le_gaussBarrier_smul (zero_le_one.trans hκ) hν ht0.le (by linarith)
  have hψ' : -(C * η * t) ≤ ψ' ((1 - t) • ν) := by
    have hd := hLip.dist_le_mul ((1 - t) • ν) hzt.2 ν (mem_ball_self hρ)
    rw [h0, dist_zero_right, Real.norm_eq_abs, hdist,
      Real.coe_toNNReal _ (mul_nonneg hC (hKb.trans' Kb.coe_nonneg))] at hd
    linarith [neg_abs_le (ψ' ((1 - t) • ν))]
  have hCt : C * η * t ≤ κ * Real.exp (-κ) / 2 * t := mul_le_mul_of_nonneg_right hCη ht0.le
  nlinarith [mul_le_mul_of_nonneg_left (show κ * Real.exp (-κ) / 2 * t ≤
    gaussBarrier κ ((1 - t) • ν) + ψ' ((1 - t) • ν) by linarith) hθ]

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

/-- **Rescaled drift.** If `d` is measurable on `ball y R` with `‖d‖ ≤ D` there, and the homothety
`T z = ε z + p`, `ε > 0`, maps the annulus into `ball y R`, then `ε d ∘ T` is measurable on the
annulus, with `‖ε d ∘ T‖ ≤ ε |D|` there. -/
private theorem rescaled_drift {d : E → E} {y p : E} {R D ε : ℝ}
    (hdm : AEStronglyMeasurable d (volume.restrict (ball y R)))
    (hdD : ∀ x ∈ ball y R, ‖d x‖ ≤ D) (hε : 0 < ε)
    (hmaps : MapsTo (fun z : E => ε • z + p) (unitAnnulus (n := n) : Set E) (ball y R)) :
    AEStronglyMeasurable (fun z => ε • d (ε • z + p))
        (volume.restrict (unitAnnulus (n := n) : Set E)) ∧
      ∀ z ∈ (unitAnnulus (n := n) : Set E), ‖ε • d (ε • z + p)‖ ≤ ε * |D| := by
  have hcov := Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε p (U := unitAnnulus)
    (V := ⟨ball y R, isOpen_ball⟩) hmaps
  refine ⟨((hdm.mono_ac (Measure.absolutelyContinuous_of_le_smul
      (hcov.map_restrict_le volume))).comp_aemeasurable hcov.aemeasurable).const_smul ε,
    fun z hz => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left ((hdD _ (hmaps hz)).trans (le_abs_self D)) hε.le

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

/-- **Undoing the rescaling.** For the homothety `T z = ε z + y + (R - ε) ν`, `ε > 0`, which sends
`ν` to `x₀ = y + R ν`, linear growth of `g ∘ T` along `t ↦ (1 - t) ν` for `0 < t < τ` is linear
growth of `g` along `s ↦ x₀ - s ν` for `0 < s < ε τ`. -/
private theorem exists_pos_mul_le_sub_of_rescaled {g : E → ℝ} {y ν : E} {R ε τ c : ℝ}
    (hε : 0 < ε) (hτ : 0 < τ) (hc : 0 < c)
    (h : ∀ t ∈ Ioo 0 τ, g (y + R • ν) + c * t ≤ g (ε • ((1 - t) • ν) + (y + (R - ε) • ν))) :
    ∃ ε' > 0, ∃ δ > 0, ∀ s ∈ Ioo 0 δ, ε' * s ≤ g (y + R • ν - s • ν) - g (y + R • ν) := by
  refine ⟨c / ε, div_pos hc hε, ε * τ, mul_pos hε hτ, fun s hs => ?_⟩
  have ht := h (s / ε) ⟨div_pos hs.1 hε, (div_lt_iff₀' hε).2 hs.2⟩
  have hpt : ε • ((1 - s / ε) • ν) + (y + (R - ε) • ν) = y + R • ν - s • ν := by
    rw [smul_smul, mul_sub, mul_one, mul_div_cancel₀ _ hε.ne', sub_smul, sub_smul]
    abel
  rw [hpt] at ht
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

/-- **The scale.** Given the constants of `exists_add_mul_le_of_supersolution`, a Hölder
constant `K` and exponent `α > 0` of the coefficients and bounds `|M|`, `|β|` for the mass and the
drift, there is a scale `ε ∈ (0, R]` at which the rescaled coefficients oscillate by
`η = K (2 ε)^α ≤ 1` with `C η ≤ κ e^{-κ} / 2`, the rescaled drift `ε β` is small for coercivity,
`4 ε |β| ≤ λ`, and the rescaled lower-order terms are absorbed by the margin `m = λ κ e^{-κ}` of
the barrier: `ε² |M| (1 + C η) + ε |β| (B + C η) ≤ m`. -/
private theorem exists_scale_of_lowerOrder {K C B M β lam κ R α : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hlam : 0 < lam) (hκ : 0 < κ) (hR : 0 < R) (hα : 0 < α) :
    ∃ ε, 0 < ε ∧ ε ≤ R ∧ K * (2 * ε) ^ α ≤ 1 ∧ C * (K * (2 * ε) ^ α) ≤ κ * Real.exp (-κ) / 2 ∧
      4 * (ε * |β|) ≤ lam ∧ ε ^ 2 * |M| * (1 + C * (K * (2 * ε) ^ α)) +
        ε * |β| * (B + C * (K * (2 * ε) ^ α)) ≤ lam * κ * Real.exp (-κ) := by
  set m := lam * κ * Real.exp (-κ)
  have hm : 0 < m := by positivity
  set P := 1 + B + C
  set N := (|M| + 4 * |β| + 1) * P
  -- Shrinking `R` to `min R (min 1 (min m λ / N))` makes `ε ≤ 1` and `ε N ≤ min m λ`.
  obtain ⟨ε, hε, hεR', hη1, hCη⟩ := exists_scale hK hC (by positivity : 0 < κ * Real.exp (-κ))
    (lt_min hR (lt_min one_pos (div_pos (lt_min hm hlam) (by positivity : 0 < N)))) hα
  have hεR := hεR'.trans (min_le_left _ _)
  have hε1 := hεR'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεN : ε * N ≤ min m lam := by
    have h := hεR'.trans ((min_le_right _ _).trans (min_le_right _ _))
    rwa [le_div_iff₀ (by positivity : 0 < N)] at h
  have hP : 1 ≤ P := by simp only [P]; linarith
  have hN : 4 * |β| + |M| ≤ (|M| + 4 * |β| + 1) * P := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ |M| + 4 * |β| + 1) (sub_nonneg.2 hP)]
  refine ⟨ε, hε, hεR, hη1, hCη, ?_, ?_⟩
  · calc 4 * (ε * |β|) ≤ ε * ((|M| + 4 * |β| + 1) * P) := by
          nlinarith [mul_le_mul_of_nonneg_left hN hε.le, abs_nonneg M]
      _ ≤ lam := hεN.trans (min_le_right _ _)
  · have hCη1 : C * (K * (2 * ε) ^ α) ≤ C := mul_le_of_le_one_right hC hη1
    have hε2 : ε ^ 2 ≤ ε := by nlinarith
    have e1 : ε ^ 2 * |M| * (1 + C * (K * (2 * ε) ^ α)) ≤ ε * |M| * P :=
      mul_le_mul (mul_le_mul_of_nonneg_right hε2 (abs_nonneg M)) (by linarith) (by
        nlinarith [mul_nonneg hK (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * ε) α)])
        (by positivity)
    have e2 : ε * |β| * (B + C * (K * (2 * ε) ^ α)) ≤ ε * |β| * P :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [min_le_left m lam, abs_nonneg M, abs_nonneg β]

/-- **Normalizing the principal coefficients.** Coefficients uniformly elliptic on `ball y R` and
`α`-Hölder on `closedBall y R`, `α > 0`, are uniformly elliptic on `closedBall y R`, and also
`min α 1`-Hölder there, since they are bounded. -/
private theorem uniformlyEllipticOn_closedBall_and_exists_holderOnWith
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {y : E} {R lam Lam : ℝ} {α Ka : ℝ≥0}
    (hα : 0 < α) (hR : 0 < R) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R)) :
    UniformlyEllipticOn (closedBall y R) a lam Lam ∧ ∃ K₁ : ℝ≥0,
      HolderOnWith K₁ (min α 1) (fun x => matrixBilinearForm (a x)) (closedBall y R) := by
  have h := hell.closure_of_continuousOn
    (by rw [closure_ball y hR.ne']; exact hhol.continuousOn hα)
  rw [closure_ball y hR.ne'] at h
  exact ⟨h, _, hhol.of_le_of_norm_le (D := Lam.toNNReal) (fun x hx =>
    (h.opNorm_matrixBilinearForm_le hx).trans (Real.le_coe_toNNReal _)) (min_le_left _ _)
    one_pos⟩

/-- **Hopf's lemma with lower-order terms, under the sign condition `c g(x₀) ≤ 0`.** This is the
common form of `exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg` (a drift, no mass term, no
sign condition on `g x₀`) and `exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos`
(a drift, `c ≥ 0` and `g x₀ ≤ 0`). -/
private theorem exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_mul_nonpos {Ω : Opens E}
    {u : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c g : E → ℝ}
    {y x₀ : E} {R lam Lam β M : ℝ} {α Ka : ℝ≥0} (hα : 0 < α) (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R)
    (hB : ball y R ⊆ Ω) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R))
    (hbm : AEStronglyMeasurable b (volume.restrict (ball y R))) (hbβ : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hcm : AEStronglyMeasurable c (volume.restrict (ball y R)))
    (hc0 : ∀ x ∈ ball y R, 0 ≤ c x) (hcM : ∀ x ∈ ball y R, c x ≤ M)
    (hu : ∀ v : W1p0 volume Ω 2, (∀ᵐ x ∂volume.restrict (Ω : Set E),
      0 ≤ W1p.value (v : W1p volume Ω 2) x) → 0 ≤ energyFormH1 a b c u (v : W1p volume Ω 2))
    (hg : ContinuousOn g (closedBall y R))
    (hug : W1p.value u =ᵐ[volume.restrict (ball y R)] g)
    (hmin : ∀ x ∈ ball y R, g x₀ < g x) (hcg : ∀ x ∈ ball y R, c x * g x₀ ≤ 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ g (x₀ - t • (R⁻¹ • (x₀ - y))) - g x₀ := by
  -- Ellipticity extends to the closed ball, and exponents above one are replaced by one.
  obtain ⟨hell, K₁, hhol₁⟩ := uniformlyEllipticOn_closedBall_and_exists_holderOnWith hα hR hell hhol
  set α₁ := min α 1
  have hα₁ : 0 < α₁ := lt_min hα one_pos
  -- The normal, the frozen matrix and the exponent of the barrier.
  set ν : E := R⁻¹ • (x₀ - y)
  have hν : ‖ν‖ = 1 := by
    rw [norm_smul, ← dist_eq_norm, hx₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR),
      inv_mul_cancel₀ hR.ne']
  have hx₀ν : y + R • ν = x₀ := by
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  obtain ⟨hlam, -, hell₃⟩ := uniformlyEllipticOn_iff.1 hell
  set κ := 2 * |(a x₀).trace| / lam + 1
  have hκT : 2 * |(a x₀).trace| + lam ≤ lam * κ := by
    rw [mul_add, mul_div_cancel₀ _ hlam.ne', mul_one]
  obtain ⟨ρ, hρ, C, Bg, hC, hBg, HF⟩ := exists_add_mul_le_of_supersolution (n := n) ν hν hα₁
    (min_le_right _ _) hlam Lam (le_add_of_nonneg_left (by positivity) : 1 ≤ κ)
  -- A scale `ε` at which the rescaled coefficients are close enough to the frozen matrix, and at
  -- which the rescaled lower-order terms are absorbed by the margin of the barrier.
  obtain ⟨ε, hε, hεR, hη1, hCη, hδ, hγ⟩ := exists_scale_of_lowerOrder (M := M) (β := β)
    K₁.coe_nonneg hC hBg hlam (by positivity : 0 < κ) hR (NNReal.coe_pos.2 hα₁)
  set p : E := y + (R - ε) • ν
  obtain ⟨hmaps, hmapsO, hbell, hbh, hbA⟩ := rescaled_coefficient hν hell hhol₁ hε hεR
  have hT : Continuous fun z : E => ε • z + p := (continuous_id.const_smul ε).add continuous_const
  have hmapsD : MapsTo (fun z : E => ε • z + p) (unitAnnulus (n := n) : Set E) (ball y R) :=
    fun z hz => hmapsO (unitAnnulus_subset_ball hz)
  -- The rescaled supersolution on the annulus, its continuous representative and boundary values.
  obtain ⟨uε, huεv, huε⟩ := exists_supersolution_comp_smul_add_const hu hε p unitAnnulus
    (fun z hz => hB (hmapsD hz))
  have huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => g (ε • z + p) := by
    filter_upwards [huεv, (Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε p
      (U := unitAnnulus) (V := ⟨ball y R, isOpen_ball⟩) hmapsD).ae_comp hug] with z h1 h2
    rw [h1, h2]
  obtain ⟨θ, hθ, h1, h2⟩ := exists_pos_add_mul_gaussBarrier_le hR hg hmin hT hmaps hmapsO
    (by positivity : 0 < κ)
  have hKb : ((K₁ * ε.toNNReal ^ (α₁ : ℝ) : ℝ≥0) : ℝ) ≤ K₁ * (2 * ε) ^ (α₁ : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ hε.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le (by linarith) α₁.coe_nonneg)
      K₁.coe_nonneg
  -- The rescaled drift `ε b ∘ T` and mass `ε² c ∘ T`, absorbed at this scale.
  obtain ⟨hbm', hbβ'⟩ := rescaled_drift hbm hbβ hε hmapsD
  obtain ⟨hcm', hc0', hcM', hcs⟩ := rescaled_mass hcm hc0 hcM hcg hε hmapsD
  have hlin := HF hbell hbh hKb hη1 (by rw [hx₀ν] at hbA; exact hbA) hCη
    (hell₃ (sphere_subset_closedBall hx₀)).1 (le_abs_self _) (by rwa [abs_abs]) hbm' hbβ' hδ hcm'
    hc0' hcM' hγ huε (hg.comp hT.continuousOn hmaps) huĝ hcs hθ.le h1 h2
  -- Undo the rescaling: the point `(1 - t) ν` of the annulus is `x₀ - ε t ν`.
  have hres := exists_pos_mul_le_sub_of_rescaled (c := θ * (κ * Real.exp (-κ) / 2))
    (τ := min ρ (1 / 2)) hε (lt_min hρ (by norm_num)) (by positivity) (by rwa [hx₀ν])
  rwa [hx₀ν] at hres

/-- **Hopf's boundary-point lemma for divergence-form equations with Hölder coefficients.** Let
`B = ball y R ⊆ Ω` and let `x₀` lie on its bounding sphere. Let `a` be uniformly elliptic on `B`
with constants `λ, Λ`, not necessarily symmetric, and `α`-Hölder on `closedBall y R`, `α > 0`, and
let the drift `b` be measurable with `‖b‖ ≤ β` on `B`. Let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu ≥ 0` in `Ω`, that is `a(u, v) + ∫ ⟪b, ∇u⟫ v ≥ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, equal almost everywhere on `B` to a function `g` continuous on `closedBall y R` with
`g x₀ < g x` for every `x ∈ B`. Then `g` leaves its minimum `x₀` at a positive linear rate along the
inward normal: with `ν = (x₀ - y) / R` the outer unit normal of `B` at `x₀`,
`ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small `t > 0`. -/
theorem exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg {Ω : Opens E}
    {u : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {g : E → ℝ}
    {y x₀ : E} {R lam Lam β : ℝ} {α Ka : ℝ≥0} (hα : 0 < α) (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R)
    (hB : ball y R ⊆ Ω) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R))
    (hbm : AEStronglyMeasurable b (volume.restrict (ball y R))) (hbβ : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hu : ∀ v : W1p0 volume Ω 2, (∀ᵐ x ∂volume.restrict (Ω : Set E),
      0 ≤ W1p.value (v : W1p volume Ω 2) x) → 0 ≤ energyFormH1 a b 0 u (v : W1p volume Ω 2))
    (hg : ContinuousOn g (closedBall y R))
    (hug : W1p.value u =ᵐ[volume.restrict (ball y R)] g)
    (hmin : ∀ x ∈ ball y R, g x₀ < g x) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ g (x₀ - t • (R⁻¹ • (x₀ - y))) - g x₀ :=
  exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_mul_nonpos (M := 0) hα hR hx₀ hB hell hhol
    hbm hbβ aestronglyMeasurable_const (fun _ _ => le_rfl) (fun _ _ => le_rfl) hu hg hug hmin
    (fun _ _ => by simp)

/-- **Hopf's boundary-point lemma for divergence-form equations with lower-order terms.** Let
`B = ball y R ⊆ Ω` and let `x₀` lie on its bounding sphere. Let `a` be uniformly elliptic on `B`
with constants `λ, Λ`, not necessarily symmetric, and `α`-Hölder on `closedBall y R`, `α > 0`, let
the drift `b` be measurable with `‖b‖ ≤ β` on `B`, and let `c` be measurable with `|c| ≤ M` on `B`.
Let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` in `Ω`, that is
`a(u, v) + ∫ ⟪b, ∇u⟫ v + ∫ c u v ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, equal almost everywhere on
`B` to a function `g` continuous on `closedBall y R` with `g x₀ < g x` for every `x ∈ B` and
`g x₀ ≤ 0`. Suppose moreover that `c ≥ 0` on `B` or `g x₀ = 0`. Then, with `ν = (x₀ - y) / R` the
outer unit normal of `B` at `x₀`, `ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small
`t > 0`.

When `g x₀ = 0`, `u ≥ 0` on `B`, so the negative part of `c` may be dropped and `c` may have
either sign. The sign condition `g x₀ ≤ 0` cannot be dropped: on the interval `(0, 2)`, `cosh`
solves `-u'' + u = 0`, and its minimum `cosh 0 = 1` over `[0, 2)` is attained only at the boundary
point `0`, where its derivative vanishes. -/
theorem exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_nonpos {Ω : Opens E}
    {u : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c g : E → ℝ}
    {y x₀ : E} {R lam Lam β M : ℝ} {α Ka : ℝ≥0} (hα : 0 < α) (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R)
    (hB : ball y R ⊆ Ω) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R))
    (hbm : AEStronglyMeasurable b (volume.restrict (ball y R))) (hbβ : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
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
      hbm hbβ hcm hc0 (fun x hx => (le_abs_self _).trans (hcM x hx)) hu hg hug hmin
      fun x hx => mul_nonpos_of_nonneg_of_nonpos (hc0 x hx) hg₀
  -- When `g x₀ = 0`, `u ≥ 0` on `B`, so on `B` the mass coefficient may be replaced by `c⁺`.
  set U : Opens E := ⟨ball y R, isOpen_ball⟩
  have hU : U ≤ Ω := hB
  have hcM' : ∀ x ∈ ball y R, ‖max (c x) 0‖ ≤ M := fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hcM x hx)) ((abs_nonneg _).trans (hcM x hx))
  have hbd {f : E → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (ball y R)))
      (hfM : ∀ x ∈ ball y R, ‖f x‖ ≤ M) : MemLp f ⊤ (volume.restrict (ball y R)) :=
    memLp_top_of_bound hf M ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hfM))
  have ham : AEStronglyMeasurable a (volume.restrict (ball y R)) :=
    ((continuousOn_of_continuousOn_matrixBilinearForm (hhol.continuousOn hα)).mono
      ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hab := memLp_energyIntegrand_of_bounds (c := 0) (gamma := 0) (Omega := U)
    hell.upper_nonneg ham hbm aestronglyMeasurable_const
    (fun _x hx eta xi => hell.upper_bound hx eta xi) hbβ (fun _ _ => by simp)
  have hu0 : ∀ᵐ x ∂volume.restrict (ball y R), 0 ≤ W1p.value u x := by
    filter_upwards [hug, ae_restrict_mem measurableSet_ball] with x h hx
    rw [h, ← hg0]
    exact (hmin x hx).le
  exact exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg_of_mul_nonpos (Ω := U) hα hR hx₀
    le_rfl hell hhol hbm hbβ (hcm.sup aestronglyMeasurable_const) (fun _ _ => le_max_right _ _)
    (fun x hx => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hcM' x hx)))
    (energyFormH1_restrictL_max_nonneg hU hab
      (hbd hcm fun x hx => (Real.norm_eq_abs _).trans_le (hcM x hx)) hu hu0) hg
    ((W1p.value_restrictL_ae hU u).trans hug) hmin fun x _ => by rw [hg0, mul_zero]

end PDE

end TauCeti
