/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundedDomain
import TauCeti.Analysis.PDE.MaximumPrinciple.Weak
import TauCeti.Analysis.PDE.MaximumPrinciple.HopfLemma
import TauCeti.Analysis.PDE.Regularity.Classical
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
import TauCeti.Analysis.PDE.EnergyForm.Poincare
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.Sobolev.W1p.Convex
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Bounds
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hopf's boundary-point lemma for divergence-form equations with Hölder coefficients

Let `B = ball y R` be a ball in an open set `Ω ⊆ ℝ^{n+1}` and let `x₀` lie on its bounding sphere.
Let `a` be uniformly elliptic on `B` with constants `0 < λ ≤ Λ`, not necessarily symmetric, and
`α`-Hölder on `closedBall y R` for some `α > 0`. Let `u ∈ H¹(Ω)` be a weak supersolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` in `Ω`,

that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, and suppose that `u` agrees almost
everywhere on `B` with a function `g` continuous on `closedBall y R` that attains a strict minimum
over `B` at `x₀`: `g x₀ < g x` for `x ∈ B`. **Hopf's lemma**
(`TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg`) says that `g` leaves `x₀` at a
positive linear rate along the inward normal: with `ν = (x₀ - y) / R`,

`ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small `t > 0`.

In particular an inward derivative of `g` at `x₀`, if it exists, is positive. The Hölder continuity
of `a` cannot be dropped: for measurable coefficients the lemma fails, by Meyers' example
(`TauCeti.Analysis.PDE.MaximumPrinciple.HalfDisk`). The lemma for operators in non-divergence form,
which needs no regularity of the coefficients, is
`TauCeti.PDE.exists_pos_mul_le_sub_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv`.

## The argument

The proof follows Rosales: freeze the coefficients at `x₀`, rescale, and compare `u` with a
barrier for the frozen operator, corrected by the solution of a Dirichlet problem whose gradient is
small by the `C^{1,β}` estimate up to the boundary.

* **Rescaling.** For `0 < ε ≤ R` the homothety `T z = ε z + y + (R - ε) ν` maps the closed unit ball
  into `closedBall y R`, the open unit ball into `ball y R`, and `ν` to `x₀`. The composition
  `u ∘ T` is a weak supersolution on the annulus `D = {1/2 < ‖z‖ < 1}` for the coefficients
  `b = a ∘ T`, which are `α`-Hölder with constant `K_a ε^α` and within `K_a (2 ε)^α` of the frozen
  matrix `A = a x₀`.
* **The barrier.** The Gaussian `Φ(z) = e^{-κ‖z‖²} - e^{-κ}` vanishes on the unit sphere, is a
  classical subsolution of `div (A ∇·)` on `D` once `κ` is large compared with `tr A / λ`, and grows
  like `κ e^{-κ} t` along the inward normal at `ν`. Unlike Rosales, who solves the frozen Dirichlet
  problem and appeals to the classical Hopf lemma, we use this explicit barrier, so `A` need not be
  symmetric.
* **The correction.** Lax–Milgram gives `ψ ∈ H¹₀(D)` with `-div (b ∇ψ) = div ((b - A) ∇Φ)`, so that
  `Φ + ψ` is a weak subsolution for `b`. Its `H¹` norm and the Hölder constant of `(b - A) ∇Φ` are
  of order `‖b - A‖ + [b]_α`. The `C^{1,β}` estimate near the boundary point `ν`, in a chart in
  which the unit sphere is the graph of a smooth function
  (`TauCeti.PDE.exists_holderOnWith_gradient_ball_inter_closure_of_graph`), bounds `∇ψ` near `ν` by
  the same order, so for `ε` small the correction is Lipschitz near `ν` with a constant below
  `κ e^{-κ} / 2`, and it vanishes at `ν`.
* **Comparison.** On the boundary of `D`, `u ∘ T ≥ g x₀` on the outer sphere and
  `u ∘ T ≥ g x₀ + θ Φ` on the inner one for some `θ > 0`. The weak comparison principle
  (`TauCeti.PDE.value_le_of_energyFormH1_le`) gives `g x₀ + θ (Φ + ψ) ≤ u ∘ T` on `D`, and along
  the normal at `ν` the right-hand side grows like `θ κ e^{-κ} t / 2`.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg`: Hopf's boundary-point lemma
  for weak supersolutions of divergence-form equations with Hölder coefficients.

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

/-! ### The unit annulus and a boundary chart at a point of its outer sphere -/

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

/-- Along the line through a unit vector `ν`, the distance from `c • ν` to `ν` is `|c - 1|`. -/
private theorem dist_smul_self_of_norm_eq_one {ν : E} (hν : ‖ν‖ = 1) (c : ℝ) :
    dist (c • ν) ν = |c - 1| := by
  have h : c • ν - ν = (c - 1) • ν := by rw [sub_smul, one_smul]
  rw [dist_eq_norm, h, norm_smul, hν, mul_one, Real.norm_eq_abs]

/-- The bump function equal to one on `closedBall 0 (1/4)` and supported in `ball 0 (1/2)`. -/
private def sphereBump {K : Type*} [NormedAddCommGroup K] :
    ContDiffBump (0 : K) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The lower boundary of the unit ball seen from the tangent space at a point of the sphere,
`v ↦ 1 - √(1 - ‖v‖²)`, cut off by a bump function so that it is smooth with compact support. -/
private def sphereGraph {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] (v : K) : ℝ :=
  sphereBump (K := K) v * (1 - √(1 - ‖v‖ ^ 2))

section SphereGraph

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

private theorem contDiff_sphereGraph : ContDiff ℝ 2 (sphereGraph (K := K)) := by
  refine contDiff_iff_contDiffAt.2 fun v => ?_
  by_cases hv : ‖v‖ < 1
  · refine (sphereBump (K := K)).contDiff.contDiffAt.mul (contDiffAt_const.sub ?_)
    refine ContDiffAt.sqrt (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt) ?_
    nlinarith [norm_nonneg v]
  · -- Off `closedBall 0 (1/2)` the bump function, hence the graph, vanishes nearby.
    have hout : v ∉ closedBall (0 : K) (sphereBump (K := K)).rOut := by
      rw [mem_closedBall, dist_zero_right]
      -- The outer radius of `sphereBump` is `1/2` by definition.
      change ¬ ‖v‖ ≤ 1 / 2
      linarith
    have hev : sphereGraph (K := K) =ᶠ[𝓝 v] fun _ => 0 := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hout] with w hw
      rw [sphereGraph, image_eq_zero_of_notMem_tsupport (f := ⇑(sphereBump (K := K)))
        (by rwa [ContDiffBump.tsupport_eq]), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The cut-off sphere graph has a Hölder continuous derivative, for every exponent at most one. -/
private theorem exists_holderWith_fderiv_sphereGraph {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α (fderiv ℝ (sphereGraph (K := K))) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ (sphereGraph (K := K))) :=
    contDiff_sphereGraph.fderiv_right (by norm_num)
  have hs : HasCompactSupport (fderiv ℝ (sphereGraph (K := K))) := by
    have h : sphereGraph (K := K) = ⇑(sphereBump (K := K)) * fun v : K => 1 - √(1 - ‖v‖ ^ 2) :=
      rfl
    rw [h]
    exact (sphereBump (K := K)).hasCompactSupport.mul_right.fderiv ℝ
  obtain ⟨L, hL⟩ := hd.lipschitzWith_of_hasCompactSupport hs one_ne_zero
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hd.continuous
  exact ⟨_, (holderWith_one.2 hL).of_le_of_norm_le (D := M.toNNReal)
    (fun x => (hM x).trans (Real.le_coe_toNNReal M)) hα one_pos⟩

private theorem sphereGraph_zero : sphereGraph (0 : K) = 0 := by
  simp [sphereGraph]

private theorem sphereGraph_of_norm_le {v : K} (hv : ‖v‖ ≤ 1 / 4) :
    sphereGraph v = 1 - √(1 - ‖v‖ ^ 2) := by
  rw [sphereGraph, (sphereBump (K := K)).one_of_mem_closedBall (by simpa [sphereBump] using hv),
    one_mul]

end SphereGraph

/-- The orthogonal splitting `x ↦ (-⟪x, ν⟫, x - ⟪x, ν⟫ ν)` along a unit vector `ν`. -/
private def unitSplitting (ν : E) (hν : ‖ν‖ = 1) : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ) :=
  (ℝ ∙ ν).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2
      ((LinearIsometryEquiv.toSpanUnitSingleton ν hν).symm.trans (LinearIsometryEquiv.neg ℝ))
      (LinearIsometryEquiv.refl ℝ (ℝ ∙ ν)ᗮ))

private theorem unitSplitting_symm_apply (ν : E) (hν : ‖ν‖ = 1) (z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)) :
    (unitSplitting ν hν).symm z = (-z.fst) • ν + (z.snd : E) := by
  obtain ⟨⟨t, v⟩⟩ := z
  simp [unitSplitting, LinearIsometryEquiv.symm_apply_eq, LinearIsometryEquiv.coe_refl]

/-- The rigid coordinates at a unit vector `ν`: the point `ν` goes to the origin and the inward
normal `-ν` of the unit sphere to the first axis, `e⁻¹ (t, v) = ν - t ν + v`. -/
private def sphereChart (ν : E) (hν : ‖ν‖ = 1) : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ) :=
  (AffineIsometryEquiv.vaddConst ℝ ν).symm.trans (unitSplitting ν hν).toAffineIsometryEquiv

private theorem sphereChart_symm_apply (ν : E) (hν : ‖ν‖ = 1) (z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)) :
    (sphereChart ν hν).symm z = ν - z.fst • ν + (z.snd : E) := by
  rw [AffineIsometryEquiv.symm_apply_eq]
  have h : ν - z.fst • ν + (z.snd : E) -ᵥ ν = (unitSplitting ν hν).symm z := by
    rw [unitSplitting_symm_apply, vsub_eq_sub, neg_smul]
    abel
  simp only [sphereChart, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.coe_vaddConst_symm, LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  rw [h, LinearIsometryEquiv.apply_symm_apply]

private theorem sphereChart_apply_self (ν : E) (hν : ‖ν‖ = 1) : sphereChart ν hν ν = 0 := by
  simp [sphereChart]

/-- In the cylinder of half-height and radius `1/4` at a point `ν` of the unit sphere, the
annulus is the region above the cut-off sphere graph. -/
private theorem sphereChart_symm_mem_unitAnnulus_iff (ν : E) (hν : ‖ν‖ = 1)
    {z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)} (hz : z ∈ normalCylinder (1 / 4) (1 / 4)) :
    (sphereChart ν hν).symm z ∈ (unitAnnulus (n := n) : Set E) ↔ sphereGraph z.snd < z.fst := by
  rw [mem_normalCylinder] at hz
  obtain ⟨ht1, ht2, hv⟩ := hz
  set t := z.fst
  set v : E := (z.snd : E)
  have hvn : ‖(z.snd : E)‖ = ‖z.snd‖ := Submodule.norm_coe _
  have hinner : ⟪ν, v⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 z.snd.property
  -- The squared norm of the point is `(1 - t)² + ‖v‖²`.
  have hsq : ‖ν - t • ν + v‖ ^ 2 = (1 - t) ^ 2 + ‖v‖ ^ 2 := by
    have h1 : ν - t • ν + v = (1 - t) • ν + v := by rw [sub_smul, one_smul]
    rw [h1, norm_add_sq_real, norm_smul, inner_smul_left, hinner, hν, Real.norm_eq_abs]
    simp [sq_abs]
  rw [sphereChart_symm_apply, mem_unitAnnulus, sphereGraph_of_norm_le (by linarith)]
  have : ‖v‖ < 1 / 4 := by rwa [hvn]
  have := norm_nonneg v
  have hn0 := norm_nonneg (ν - t • ν + v)
  constructor
  · rintro ⟨h1, -⟩
    have hlt : (1 - t) ^ 2 < 1 - ‖v‖ ^ 2 := by nlinarith
    have := (Real.lt_sqrt (by linarith)).2 hlt
    rw [← hvn]
    linarith
  · intro h
    have hlt : 1 - t < √(1 - ‖v‖ ^ 2) := by rw [← hvn] at h; linarith
    have hsq' := (Real.lt_sqrt (by linarith)).1 hlt
    refine ⟨?_, ?_⟩
    · nlinarith
    · nlinarith
/-! ### The Gaussian barrier on the annulus -/

/-- The Gaussian barrier `exp (-κ ‖z‖²) - exp (-κ)`, which vanishes on the unit sphere. -/
private def gaussBarrier (κ : ℝ) (z : E) : ℝ :=
  Real.exp (-κ * ‖z‖ ^ 2) - Real.exp (-κ)

private theorem contDiff_gaussBarrier (κ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (gaussBarrier (n := n) κ) := by
  have h : ContDiff ℝ k fun z : E => -κ * ‖z‖ ^ 2 := contDiff_const.mul (contDiff_norm_sq ℝ)
  exact (Real.contDiff_exp.comp h).sub contDiff_const

/-- On the annulus the Gaussian barrier is a classical subsolution of `div (A ∇·)` once `κ ≥ 1` is
large compared with the trace of `A` over its ellipticity constant. -/
private theorem divMatrixGradient_gaussBarrier_nonneg {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam T κ : ℝ} (hlam : 0 ≤ lam) (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hT : A.trace ≤ T) (hκ : 1 ≤ κ) (hκT : 2 * |T| ≤ lam * κ) {z : E} (hz : 1 / 2 ≤ ‖z‖)
    (hz1 : ‖z‖ ≤ 1) :
    0 ≤ divMatrixGradient (fun _ => A) (gaussBarrier κ) z := by
  have h : 0 ≤ ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ (gaussBarrier κ)) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    unfold gaussBarrier
    simpa using mul_le_sum_mul_fderiv_fderiv_add_fderiv_exp_neg_mul_norm_sub_sq_sub
      (y := 0) (x := z) (v := 0) (β := 0) (γ := 0) (R := 1) (c := 0) hlam hA hT (by simp) le_rfl
      le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2) (by simpa using hz) (by simpa using hz1) hκ
      (by norm_num; linarith)
  have hdiff : Differentiable ℝ (fderiv ℝ (gaussBarrier (n := n) κ)) :=
    ((contDiff_gaussBarrier κ (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      one_ne_zero
  rw [divMatrixGradient_eq_sum_fderiv_fderiv_apply (Omega := ⊤)
    ((contDiff_gaussBarrier κ).contDiffOn) (mem_univ z)]
  refine h.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  rw [fderiv_clm_apply (hdiff z) (differentiableAt_const _)]
  simp

/-- **The barrier is a weak subsolution.** A Sobolev function on the annulus equal to the Gaussian
barrier satisfies `∫ ⟨A ∇Φ, ∇v⟩ ≤ 0` for every nonnegative `v ∈ H¹₀`. -/
private theorem energyFormH1_gaussBarrier_nonpos {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam T κ : ℝ} (hlam : 0 ≤ lam) (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hT : A.trace ≤ T) (hκ : 1 ≤ κ) (hκT : 2 * |T| ≤ lam * κ)
    {W : W1p volume (unitAnnulus (n := n)) 2}
    (hW : W1p.value W =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] gaussBarrier κ)
    (v : W1p0 volume (unitAnnulus (n := n)) 2)
    (hv : ∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
      0 ≤ W1p.value (v : W1p volume (unitAnnulus (n := n)) 2) z) :
    energyFormH1 (fun _ => A) 0 0 W (v : W1p volume (unitAnnulus (n := n)) 2) ≤ 0 := by
  set f : E → ℝ := fun z => -divMatrixGradient (fun _ => A) (gaussBarrier κ) z
  have hcont : ContinuousOn f (closedBall 0 1) :=
    (continuousOn_divMatrixGradient (Omega := ⊤) (A := A)
      (contDiff_gaussBarrier (n := n) κ).contDiffOn).neg.mono (subset_univ _)
  have hf : MemLp f 2 (volume.restrict (unitAnnulus (n := n) : Set E)) :=
    hcont.memLp_restrict_of_subset_isCompact (isCompact_closedBall 0 1)
      unitAnnulus.isOpen.measurableSet unitAnnulus_subset_closedBall 2
  have hweak := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction
    (memLp_energyIntegrand_const_zero_zero A) (hf.toLp f) W).2 (fun φ => by
      rw [energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_divMatrixGradient
        (contDiff_gaussBarrier κ).contDiffOn hW φ, ← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with z hz
      rw [hz]
      simp [f, mul_comm]) v
  rw [hweak]
  refine integral_nonpos_of_ae ?_
  filter_upwards [hf.coeFn_toLp, hv, ae_restrict_mem unitAnnulus.isOpen.measurableSet]
    with z hz hvz hzD
  rw [hz]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (divMatrixGradient_gaussBarrier_nonneg hlam
    hA hT hκ hκT (mem_unitAnnulus.1 hzD).2.le (mem_unitAnnulus.1 hzD).1.le)) hvz

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

/-- A function continuous near a point `ν` of the unit sphere that vanishes there outside the
closed unit ball vanishes at `ν`. -/
private theorem eq_zero_of_continuousOn_of_eqOn {f : E → ℝ} {ν : E} (hν : ‖ν‖ = 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hf : ContinuousOn f (ball ν ρ))
    (hzero : EqOn f 0 (ball ν ρ ∩ (closedBall 0 1)ᶜ)) : f ν = 0 := by
  -- `ν` is the limit of the points `(1 + s) ν`, `s → 0⁺`, which lie outside the closed unit ball.
  have hcl : ν ∈ closure (ball ν ρ ∩ (closedBall (0 : E) 1)ᶜ) := by
    have ht : Tendsto (fun s : ℝ => (1 + s) • ν) (𝓝[>] 0) (𝓝 ν) := by
      have hc : Continuous fun s : ℝ => (1 + s) • ν := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hρ] with s hs
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_smul_self_of_norm_eq_one hν, add_sub_cancel_left, abs_of_pos hs.1]
      exact hs.2
    · rw [mem_compl_iff, mem_closedBall_zero_iff, norm_smul, hν, mul_one, Real.norm_eq_abs, not_le]
      exact (lt_add_of_pos_right 1 hs.1).trans_le (le_abs_self _)
  exact hzero.of_subset_closure (hf.mono (insert_subset (mem_ball_self hρ) inter_subset_left))
    continuousOn_const (subset_insert _ _) (insert_subset hcl subset_closure) (mem_insert _ _)

/-- **A representative vanishing at a boundary point.** If the gradient of `ψ ∈ H¹₀` of a subset of
the unit ball is bounded by `M` near a point `ν` of the unit sphere, then `ψ` has a representative
that is `M`-Lipschitz near `ν` and vanishes at `ν`: it is the precise representative of the
extension of `ψ` by zero, which vanishes outside the unit ball. -/
private theorem exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le {D : Opens E}
    (hD : (D : Set E) ⊆ ball 0 1) (ψ : W1p0 volume D 2) {ν : E} (hν : ‖ν‖ = 1) {ρ : ℝ}
    (hρ : 0 < ρ) {M : ℝ≥0}
    (hM : ∀ᵐ z ∂volume, z ∈ (D : Set E) ∩ ball ν ρ → ‖W1p.gradient (ψ : W1p volume D 2) z‖ ≤ M) :
    ∃ ψ' : E → ℝ, W1p.value (ψ : W1p volume D 2) =ᵐ[volume.restrict (D : Set E)] ψ' ∧
      LipschitzOnWith M ψ' (ball ν ρ) ∧ ψ' ν = 0 := by
  set ψ₀ : W1p volume (⊤ : Opens E) 2 := (W1p0.extendByZeroL (Omega' := ⊤) le_top ψ).val
  have hval : W1p.value ψ₀ =ᵐ[volume] (D : Set E).indicator (W1p.value (ψ : W1p volume D 2)) :=
    W1p0.value_extendByZeroL_top_ae ψ
  have hprec : W1p.value ψ₀ =ᵐ[volume] preciseRepresentative volume (W1p.value ψ₀) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using W1p.ae_eq_preciseRepresentative ψ₀
  -- Near `ν` the gradient of the extension is bounded by `M`: it vanishes off `D`.
  have hgrad : ∀ᵐ z ∂volume.restrict (ball ν ρ), ‖W1p.gradient ψ₀ z‖ ≤ M := by
    refine (ae_restrict_iff' isOpen_ball.measurableSet).2 ?_
    filter_upwards [W1p0.gradient_extendByZeroL_top_ae ψ, hM] with z h1 h2 hz
    rw [h1]
    by_cases hzD : z ∈ (D : Set E)
    · rw [indicator_of_mem hzD]
      exact h2 ⟨hzD, hz⟩
    · rw [indicator_of_notMem hzD, norm_zero]
      exact M.coe_nonneg
  set ψ' := preciseRepresentative volume (W1p.value ψ₀)
  have hL : LipschitzOnWith M ψ' (ball ν ρ) :=
    W1p.lipschitzOnWith_preciseRepresentative_of_ae_norm_gradient_le ψ₀
      (V := ⟨ball ν ρ, isOpen_ball⟩) le_top (convex_ball ν ρ) subset_rfl hgrad
  refine ⟨ψ', ?_, hL, ?_⟩
  · refine (ae_restrict_iff' D.isOpen.measurableSet).2 ?_
    filter_upwards [hval, hprec] with z h1 h2 hz
    rw [← h2, h1, indicator_of_mem hz]
  · -- Outside the closed unit ball the representative vanishes, and `ν` is a limit of such points.
    set O : Set E := ball ν ρ ∩ (closedBall 0 1)ᶜ
    have hO : IsOpen O := isOpen_ball.inter isClosed_closedBall.isOpen_compl
    have hOD : ∀ z ∈ O, z ∉ (D : Set E) := fun z hz hzD =>
      hz.2 (ball_subset_closedBall (hD hzD))
    have hzero : EqOn ψ' 0 O := by
      refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hO (hL.continuousOn.mono inter_subset_left)
        continuousOn_const
      refine (ae_restrict_iff' hO.measurableSet).2 ?_
      filter_upwards [hval, hprec] with z h1 h2 hz
      rw [← h2, h1, indicator_of_notMem (hOD z hz), Pi.zero_apply]
    exact eq_zero_of_continuousOn_of_eqOn hν hρ hL.continuousOn hzero

/-- **The correction is small near the boundary point.** Fix a point `ν` of the unit sphere, an
exponent `0 < α ≤ 1`, ellipticity constants and `κ`. There are `ρ > 0` and `C ≥ 0` such that for
every coefficient field `b`, uniformly elliptic on the closed unit ball with these constants and
`α`-Hölder there with constant at most `η ≤ 1`, and every matrix `A` with `‖b - A‖ ≤ η` there, the
correction `ψ ∈ H¹₀` of `exists_correction_of_uniformlyEllipticOn` has a representative that is
`C η`-Lipschitz on `B(ν, ρ)` and vanishes at `ν`. This combines the energy bound for `ψ` with the
`C^{1,β}` estimate up to the boundary of the annulus at `ν`. -/
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
          ψ' ∧ LipschitzOnWith (C * η).toNNReal ψ' (ball ν ρ) ∧ ψ' ν = 0 := by
  obtain ⟨K, B, hK, hB⟩ := exists_holderOnWith_gradient_gaussBarrier (n := n) κ hα1
  obtain ⟨Kγ, hγK⟩ := exists_holderWith_fderiv_sphereGraph (K := (ℝ ∙ ν)ᗮ) hα1
  set β : ℝ≥0 := min α (1 / 2)
  have hβ : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hΩ : Bornology.IsBounded (unitAnnulus (n := n) : Set E) :=
    isBounded_ball.subset unitAnnulus_subset_ball
  obtain ⟨ρ, hρ, κ', H⟩ := exists_holderOnWith_gradient_ball_inter_closure_of_graph (n := n)
    hβ hβ1 (min_le_left _ _) (q := ⊤) le_top (by simp [hβ1.le]) hΩ
    (sphereChart_apply_self ν hν) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 1 / 4)
    sphereGraph_zero (contDiff_sphereGraph.of_le one_le_two) hγK
    (fun z hz => sphereChart_symm_mem_unitAnnulus_iff ν hν hz) lam Lam 1
  -- The volume factor in the `L²` bound of the correction field.
  set V : ℝ := (measureUnivNNReal (volume.restrict (unitAnnulus (n := n) : Set E)) : ℝ) ^
    ((2 : ℝ≥0∞).toReal⁻¹)
  have : 0 ≤ V := by positivity
  refine ⟨ρ, hρ, κ' * ((K + B) + 10 / lam * (V * B)), by positivity,
    fun {b A Kb η} hb hbh hKb hη1 hbA => ?_⟩
  have hη : 0 ≤ η := Kb.coe_nonneg.trans hKb
  obtain ⟨hHh, hHb⟩ := holderOnWith_correctionField (κ := κ) hK hB hbh hKb hbA
  obtain ⟨ψ, hψ, hψn⟩ := exists_correction_of_uniformlyEllipticOn hb
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα)) (hHh.continuousOn hα)
  have hψb := hψn (η * B) (by positivity) hHb
  -- The estimate up to the boundary at `ν`, for the equation `-div (b ∇ψ) = -div (-(b - A) ∇Φ)`.
  obtain ⟨g, hg, -, hgb⟩ := H (u := ψ) (a := b) (G := -correctionField b A κ) (f := 0)
    (Ka := Kb) (KG := (η * (K + B)).toNNReal) (hb.mono_set closure_unitAnnulus_subset)
    (hbh.mono closure_unitAnnulus_subset) (hKb.trans hη1) (hHh.neg.mono closure_unitAnnulus_subset)
    MemLp.zero (fun φ => by
      rw [hψ ⟨W1p.ofTestFunctionₗ volume unitAnnulus 2 φ, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
      simp only [Pi.neg_apply, inner_neg_left, integral_neg, Pi.zero_apply, zero_mul,
        integral_zero, add_zero]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with z hz
      rw [W1p.gradient_ofTestFunctionₗ, hz])
  have hgb' : ∀ z ∈ ball ν ρ ∩ closure (unitAnnulus (n := n) : Set E),
      ‖g z‖ ≤ κ' * ((K + B) + 10 / lam * (V * B)) * η := by
    intro z hz
    refine (hgb z hz).trans ?_
    rw [Real.coe_toNNReal _ (by positivity), eLpNorm_zero, ENNReal.toReal_zero, add_zero]
    calc (κ' : ℝ) * (η * (K + B) + ‖ψ‖) ≤ κ' * (η * (K + B) + 10 / lam * (V * (η * B))) := by
          gcongr
      _ = κ' * ((K + B) + 10 / lam * (V * B)) * η := by ring
  obtain ⟨ψ', hae, hLip, h0⟩ := exists_lipschitzOnWith_ae_eq_of_ae_norm_gradient_le
    unitAnnulus_subset_ball ψ hν hρ
    (M := (κ' * ((K + B) + 10 / lam * (V * B)) * η).toNNReal) (by
      filter_upwards [(ae_restrict_iff' (unitAnnulus.isOpen.inter isOpen_ball).measurableSet).1 hg]
        with z hz hzD
      rw [hz hzD]
      exact (hgb' z ⟨hzD.2, subset_closure hzD.1⟩).trans (Real.le_coe_toNNReal _))
  exact ⟨ψ, ψ', hψ, hae, hLip, h0⟩

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

/-- **The comparison on the annulus.** Let `uε ∈ H¹` of the annulus be a weak supersolution for
coefficients `b`, uniformly elliptic and continuous on the closed unit ball, equal almost
everywhere to a function `ĝ` continuous there. If `ĝ ≥ s₀` on the outer sphere and
`ĝ ≥ s₀ + θ Φ` on the inner sphere, with `θ ≥ 0`, then `s₀ + θ (Φ + ψ) ≤ ĝ` almost everywhere on
the annulus, where `Φ` is the Gaussian barrier and `ψ` its correction. -/
private theorem ae_add_mul_le_of_supersolution {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {κ lam Lam T : ℝ}
    (hb : UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam)
    (hbc : ContinuousOn b (closedBall 0 1)) (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hT : A.trace ≤ T) (hκ : 1 ≤ κ) (hκT : 2 * |T| ≤ lam * κ)
    {ψ : W1p0 volume (unitAnnulus (n := n)) 2}
    (hψ : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      energyFormH1 b 0 0 (ψ : W1p volume unitAnnulus 2) (v : W1p volume unitAnnulus 2) =
        -∫ z in (unitAnnulus (n := n) : Set E),
          ⟪correctionField b A κ z, W1p.gradient (v : W1p volume unitAnnulus 2) z⟫_ℝ)
    {uε : W1p volume (unitAnnulus (n := n)) 2}
    (huε : ∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
      (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        0 ≤ W1p.value (v : W1p volume unitAnnulus 2) z) →
      0 ≤ energyFormH1 b 0 0 uε (v : W1p volume unitAnnulus 2))
    {ĝ : E → ℝ} (hĝ : ContinuousOn ĝ (closedBall 0 1))
    (huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ) {s₀ θ : ℝ}
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
  -- The comparison function `θ (W + ψ) + s₀` is a subsolution: constants have no energy.
  set Vf := θ • (W + (ψ : W1p volume unitAnnulus 2)) + W1p.const s₀
  have huv : ∀ w : W1p0 volume (unitAnnulus (n := n)) 2,
      (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
        0 ≤ W1p.value (w : W1p volume unitAnnulus 2) z) →
      energyFormH1 b 0 0 Vf (w : W1p volume unitAnnulus 2) ≤
        energyFormH1 b 0 0 uε (w : W1p volume unitAnnulus 2) := by
    intro w hw
    rw [energyFormH1_add_const_left, energyFormH1_smul_left,
      energyFormH1_add_correction hcb hWg hψ w]
    have hΦ := energyFormH1_gaussBarrier_nonpos hb.pos.le hA hT hκ hκT hWv w hw
    nlinarith [mul_le_mul_of_nonneg_left hΦ hθ, huε w hw]
  -- On the frontier `Vf - uε` is at most `0`; the correction vanishes there in the Sobolev sense.
  have hbd : W1p.posPart (by norm_num) (Vf - uε) ∈ w1p0Submodule volume unitAnnulus 2 := by
    have hrw : Vf - uε = θ • (ψ : W1p volume unitAnnulus 2) + (θ • W + W1p.const s₀ - uε) := by
      simp only [Vf, smul_add]
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
  have hcomp := value_le_of_energyFormH1_le hcb hbd (C := lam / 10) (by have := hb.pos; positivity)
    (div_ten_mul_norm_sq_le_energyFormH1 hbD hm) huv
  filter_upwards [hcomp, W1p.value_add_ae (θ • (W + (ψ : W1p volume unitAnnulus 2)))
      (W1p.const s₀), W1p.value_smul_ae θ (W + (ψ : W1p volume unitAnnulus 2)),
    W1p.value_add_ae W (ψ : W1p volume unitAnnulus 2),
    W1p.value_const_ae (mu := volume) (Omega := unitAnnulus (n := n)) (p := 2) s₀, hWv,
    huĝ] with z h e2 e3 e4 e5 e6 e7
  simp only [Vf, e2, Pi.add_apply, e3, Pi.smul_apply, smul_eq_mul, e4, e5, e6, e7] at h
  linarith

/-- **Linear growth along the normal on the annulus.** For coefficients close to a frozen matrix
`A` in the sense of `exists_correction`, closely enough that `C η ≤ κ e^{-κ} / 2`, a weak
supersolution on the annulus whose continuous representative `ĝ` is at least `s₀` on the outer
sphere and at least `s₀ + θ Φ` on the inner sphere grows linearly into the annulus along the
inward normal at `ν`: `s₀ + θ κ e^{-κ} t / 2 ≤ ĝ ((1 - t) ν)` for small `t > 0`. -/
private theorem exists_add_mul_le_of_supersolution (ν : E) (hν : ‖ν‖ = 1) {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α ≤ 1) {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) {κ : ℝ} (hκ : 1 ≤ κ) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Kb : ℝ≥0} {η T : ℝ}
      {uε : W1p volume (unitAnnulus (n := n)) 2} {ĝ : E → ℝ} {s₀ θ : ℝ},
      UniformlyEllipticOn (closedBall (0 : E) 1) b lam Lam →
      HolderOnWith Kb α (fun z => matrixBilinearForm (b z)) (closedBall 0 1) → (Kb : ℝ) ≤ η →
      η ≤ 1 → (∀ z ∈ closedBall (0 : E) 1,
        ‖matrixBilinearForm (b z) - matrixBilinearForm A‖ ≤ η) →
      C * η ≤ κ * Real.exp (-κ) / 2 → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      A.trace ≤ T → 2 * |T| ≤ lam * κ →
      (∀ v : W1p0 volume (unitAnnulus (n := n)) 2,
        (∀ᵐ z ∂volume.restrict (unitAnnulus (n := n) : Set E),
          0 ≤ W1p.value (v : W1p volume unitAnnulus 2) z) →
        0 ≤ energyFormH1 b 0 0 uε (v : W1p volume unitAnnulus 2)) →
      ContinuousOn ĝ (closedBall 0 1) →
      W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)] ĝ → 0 ≤ θ →
      (∀ z ∈ sphere (0 : E) 1, s₀ ≤ ĝ z) →
      (∀ z ∈ sphere (0 : E) (1 / 2), s₀ + θ * gaussBarrier κ z ≤ ĝ z) →
      ∀ t ∈ Ioo 0 (min ρ (1 / 2)), s₀ + θ * (κ * Real.exp (-κ) / 2) * t ≤ ĝ ((1 - t) • ν) := by
  obtain ⟨ρ, hρ, C, hC, H⟩ := exists_correction (n := n) ν hν hα hα1 hlam Lam κ
  refine ⟨ρ, hρ, C, hC, fun {b A Kb η T uε ĝ s₀ θ} hb hbh hKb hη1 hbA hCη hA hT hκT huε hĝ huĝ
    hθ h1 h2 t ht => ?_⟩
  obtain ⟨ψ, ψ', hψ, hae, hLip, h0⟩ := H hb hbh hKb hη1 hbA
  have hcomp := ae_add_mul_le_of_supersolution hb
    (continuousOn_of_continuousOn_matrixBilinearForm (hbh.continuousOn hα)) hA hT hκ hκT hψ
    huε hĝ huĝ hθ h1 h2
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
  have hzt : (1 - t) • ν ∈ O := by
    refine ⟨mem_unitAnnulus.2 ?_, ?_⟩
    · rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
      constructor <;> linarith
    · rw [mem_ball, dist_smul_self_of_norm_eq_one hν, sub_sub_cancel_left, abs_neg,
        abs_of_pos ht0]
      exact htρ
  have hFz := hF0 hzt
  simp only [F, Pi.zero_apply, max_eq_right_iff, sub_nonpos] at hFz
  -- The barrier grows like `κ e^{-κ} t`, and the correction is `C η`-Lipschitz and vanishes at `ν`.
  have hΦ := mul_le_gaussBarrier_smul (zero_le_one.trans hκ) hν ht0.le (by linarith)
  have hψ' : -(C * η * t) ≤ ψ' ((1 - t) • ν) := by
    have hd := hLip.dist_le_mul ((1 - t) • ν) hzt.2 ν (mem_ball_self hρ)
    have hdist : dist ((1 - t) • ν) ν = t := by
      rw [dist_smul_self_of_norm_eq_one hν, sub_sub_cancel_left, abs_neg, abs_of_pos ht0]
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

/-- **Hopf's boundary-point lemma for divergence-form equations with Hölder coefficients.** Let
`B = ball y R ⊆ Ω` and let `x₀` lie on its bounding sphere. Let `a` be uniformly elliptic on `B`
with constants `λ, Λ`, not necessarily symmetric, and `α`-Hölder on `closedBall y R`, `α > 0`. Let
`u ∈ H¹(Ω)` be a weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` in `Ω`, that is `a(u, v) ≥ 0` for every
nonnegative `v ∈ H¹₀(Ω)`, equal almost everywhere on `B` to a function `g` continuous on
`closedBall y R` with `g x₀ < g x` for every `x ∈ B`. Then `g` leaves its minimum `x₀` at a positive
linear rate along the inward normal: with `ν = (x₀ - y) / R` the outer unit normal of `B` at `x₀`,
`ε t ≤ g (x₀ - t ν) - g x₀` for some `ε > 0` and all small `t > 0`. -/
theorem exists_pos_mul_le_sub_of_forall_energyFormH1_nonneg {Ω : Opens E}
    {u : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {g : E → ℝ} {y x₀ : E}
    {R lam Lam : ℝ} {α Ka : ℝ≥0} (hα : 0 < α) (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R)
    (hB : ball y R ⊆ Ω) (hell : UniformlyEllipticOn (ball y R) a lam Lam)
    (hhol : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y R))
    (hu : ∀ v : W1p0 volume Ω 2, (∀ᵐ x ∂volume.restrict (Ω : Set E),
      0 ≤ W1p.value (v : W1p volume Ω 2) x) → 0 ≤ energyFormH1 a 0 0 u (v : W1p volume Ω 2))
    (hg : ContinuousOn g (closedBall y R))
    (hug : W1p.value u =ᵐ[volume.restrict (ball y R)] g)
    (hmin : ∀ x ∈ ball y R, g x₀ < g x) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ g (x₀ - t • (R⁻¹ • (x₀ - y))) - g x₀ := by
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
  have hκT : 2 * |(a x₀).trace| ≤ lam * κ := by
    rw [mul_add, mul_div_cancel₀ _ hlam.ne', mul_one]
    linarith
  obtain ⟨ρ, hρ, C, hC, HF⟩ := exists_add_mul_le_of_supersolution (n := n) ν hν hα₁
    (min_le_right _ _) hlam Lam hκ1
  -- A scale `ε` at which the rescaled coefficients are close enough to the frozen matrix.
  obtain ⟨ε, hε, hεR, hη1, hCη⟩ := exists_scale K₁.coe_nonneg hC (by positivity : 0 < κ *
    Real.exp (-κ)) hR (NNReal.coe_pos.2 hα₁)
  set c : E := y + (R - ε) • ν
  obtain ⟨hmaps, hmapsO, hbell, hbh, hbA⟩ := rescaled_coefficient hν hell hhol₁ hε hεR
  have hT : Continuous fun z : E => ε • z + c := (continuous_id.const_smul ε).add continuous_const
  -- The rescaled supersolution on the annulus, its continuous representative and boundary values.
  obtain ⟨uε, huεv, huε⟩ := exists_supersolution_comp_smul_add_const hu hε c unitAnnulus
    (fun z hz => hB (hmapsO (unitAnnulus_subset_ball hz)))
  have huĝ : W1p.value uε =ᵐ[volume.restrict (unitAnnulus (n := n) : Set E)]
      fun z => g (ε • z + c) := by
    filter_upwards [huεv, (Wkp.IsChangeOfVariables.smul_add_const (k := 1) hε c
      (U := unitAnnulus) (V := ⟨ball y R, isOpen_ball⟩)
      (fun z hz => hmapsO (unitAnnulus_subset_ball hz))).ae_comp hug] with z h1 h2
    rw [h1, h2]
  obtain ⟨θ, hθ, h1, h2⟩ := exists_pos_add_mul_gaussBarrier_le hR hg hmin hT hmaps hmapsO hκ
  have hKb : ((K₁ * ε.toNNReal ^ (α₁ : ℝ) : ℝ≥0) : ℝ) ≤ K₁ * (2 * ε) ^ (α₁ : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ hε.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le (by linarith) α₁.coe_nonneg)
      K₁.coe_nonneg
  have hlin := HF hbell hbh hKb hη1 (by rw [hx₀ν] at hbA; exact hbA) hCη hA (le_abs_self _)
    (by rwa [abs_abs]) huε (hg.comp hT.continuousOn hmaps) huĝ hθ.le h1 h2
  -- Undo the rescaling: the point `(1 - t) ν` of the annulus is `x₀ - ε t ν`.
  refine exists_pos_mul_le_sub_of_rescaled (c := θ * (κ * Real.exp (-κ) / 2))
    (τ := min ρ (1 / 2)) hε (lt_min hρ (by norm_num)) (by positivity) fun t ht => ?_
  have hpt : ε • ((1 - t) • ν) + c = x₀ - (ε * t) • ν := by
    rw [← hx₀ν, smul_smul, mul_sub, mul_one]
    simp only [c, sub_smul]
    abel
  have h := hlin t ht
  rwa [Function.comp_apply, hpt] at h

end PDE

end TauCeti
