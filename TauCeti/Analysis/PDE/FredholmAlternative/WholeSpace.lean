/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# Poisson's equation on the line and the plane

On a bounded open set, the energy form of a uniformly elliptic operator satisfies Gårding's
inequality, the inclusion `H¹₀(Ω) → L²(Ω)` is compact, and the Dirichlet problem `B(u, ·) = ℓ` is
solvable exactly when `ℓ` vanishes on the weak adjoint kernel
(`TauCeti.PDE.exists_forall_energyFormH1L0_eq_iff_of_garding`). This file shows that the
boundedness of the domain cannot be dropped: on all of `ℝⁿ`, `n ≤ 2`, the Laplacian satisfies
Gårding's inequality and has zero adjoint kernel, so the compatibility condition holds for every
forcing, yet Poisson's equation `-Δu = f` has no weak solution `u ∈ H¹(ℝⁿ)` for integrable data
with `∫ f ≠ 0`. What fails is the compactness of `H¹(ℝⁿ) → L²(ℝⁿ)`.

* `TauCeti.PDE.eq_zero_of_forall_energyFormH1_one_zero_zero_eq_zero`: in every dimension `n ≥ 1`,
  a function `w ∈ H¹₀(ℝⁿ)` with `∫ ∇v · ∇w = 0` for every `v ∈ H¹₀(ℝⁿ)` vanishes, since its
  gradient vanishes and the only constant in `L²(ℝⁿ)` is zero. So the adjoint kernel of `-Δ` on
  `ℝⁿ` is zero and the compatibility condition holds for every `ℓ`.
* `TauCeti.PDE.abs_integral_inner_gradient_le_of_eqOn_one`: for `n ≤ 2`, `u ∈ H¹(ℝⁿ)` and a
  cutoff `ψ` equal to `1` on the ball of radius `R ≥ 1`, supported in the ball of radius `2 R`
  and with `‖∇ψ‖ ≤ K / R`, the energy pairing `∫ ⟪∇u, ∇ψ⟫` is at most a constant times the `L²`
  norm of `∇u` outside the ball of radius `R`. By Cauchy–Schwarz it is at most `‖∇ψ‖_{L²}` times
  that norm, and `‖∇ψ‖²_{L²}` is of order `R^(n-2)`, bounded exactly when `n ≤ 2`.
* `TauCeti.PDE.not_isWeakSolutionDirichlet_one_zero_zero_of_integral_ne_zero`: for `n ≤ 2` and
  integrable `f ∈ L²(ℝⁿ)` with `∫ f ≠ 0`, no `u ∈ H¹₀(ℝⁿ)` solves `-Δu = f` weakly. Testing the
  equation against such cutoffs `ψ_R` gives `∫ ⟪∇u, ∇ψ_R⟫ = ∫ f ψ_R`, whose left side tends to
  `0` and whose right side tends to `∫ f` as `R → ∞`.

Gårding's inequality holds for every uniformly elliptic operator with bounded coefficients on
every open set, in particular for the Laplacian on `ℝⁿ`
(`TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self_norm_of_norm_le`).

The nonexistence also holds for `n = 3, 4`, by one more integration by parts, and fails for
`n ≥ 5`: there the Newtonian potential of the indicator of a ball has gradient in `L²` and lies in
`L²`, so it is a solution in `H¹(ℝⁿ)`. The case `n ≤ 2` proved here suffices to show that the
compatibility condition is not sufficient on unbounded domains.

## References

* L. C. Evans, *Partial Differential Equations*, Section 6.2.3.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.2.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology Distributions

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]

/-! ### The energy pairing with a cutoff -/

/-- `‖∇ψ‖²_{L²} ≤ (K / R)² μ(B(0, 2R)) = K² 2ⁿ R^(n - 2) μ(B(0, 1)) ≤ K² 2ⁿ μ(B(0, 1))` for a
function `ψ` supported in the closed ball of radius `2 R ≥ 2` with `‖∇ψ‖ ≤ K / R`, in dimension
`n ≤ 2`. -/
private theorem integral_norm_gradient_sq_le_of_tsupport_subset (hn : Fintype.card ι ≤ 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} {R K : ℝ} (hR : 1 ≤ R)
    (hψts : tsupport ψ ⊆ closedBall 0 (2 * R)) (hψg : ∀ x, ‖gradient ψ x‖ ≤ K / R) :
    ∫ x, ‖gradient ψ x‖ ^ 2 ∂mu ≤ K ^ 2 * (2 ^ Fintype.card ι * mu.real (ball 0 1)) := by
  have := setIntegral_norm_gradient_sq_le_of_tsupport_subset_closedBall (mu := mu)
    (s := univ) hψts fun x _ => hψg x
  rw [Measure.restrict_univ] at this
  refine this.trans ?_
  rw [Measure.addHaar_real_closedBall _ _ (by positivity), finrank_euclideanSpace, mul_pow,
    div_pow]
  have hpow : R ^ Fintype.card ι ≤ R ^ 2 := pow_le_pow_right₀ hR hn
  calc K ^ 2 / R ^ 2 * (2 ^ Fintype.card ι * R ^ Fintype.card ι * mu.real (ball 0 1))
      = K ^ 2 * (2 ^ Fintype.card ι * mu.real (ball 0 1)) * (R ^ Fintype.card ι / R ^ 2) := by
        field_simp
    _ ≤ K ^ 2 * (2 ^ Fintype.card ι * mu.real (ball 0 1)) * 1 := by
        gcongr
        exact div_le_one_of_le₀ hpow (by positivity)
    _ = _ := mul_one _

/-- **The energy pairing of `u ∈ H¹(ℝⁿ)` with a wide cutoff, for `n ≤ 2`.** Let `R ≥ 1` and let
`ψ` be a `C¹` function equal to `1` on the closed ball of radius `R`, with topological support in
the closed ball of radius `2 R` and `‖∇ψ‖ ≤ K / R`. Then in dimension `n ≤ 2`

`|∫ ⟪∇u, ∇ψ⟫| ≤ K √(2ⁿ μ(B(0, 1))) (∫_{‖x‖ ≥ R} ‖∇u‖²)^(1/2)`.

By Cauchy–Schwarz the pairing is at most `‖∇ψ‖_{L²}` times the `L²` norm of `∇u` outside the
ball of radius `R`, where `∇ψ` vanishes, and `‖∇ψ‖²_{L²} ≤ K² 2ⁿ R^(n - 2) μ(B(0, 1))` is bounded
uniformly in `R ≥ 1` exactly when `n ≤ 2`. -/
theorem abs_integral_inner_gradient_le_of_eqOn_one (hn : Fintype.card ι ≤ 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} {R K : ℝ} (hR : 1 ≤ R) (hK : 0 ≤ K) (hψ : ContDiff ℝ 1 ψ)
    (hψ1 : EqOn ψ 1 (closedBall 0 R)) (hψts : tsupport ψ ⊆ closedBall 0 (2 * R))
    (hψg : ∀ x, ‖gradient ψ x‖ ≤ K / R) (u : W1p mu ⊤ 2) :
    |∫ x, ⟪W1p.gradient u x, gradient ψ x⟫_ℝ ∂mu| ≤
      K * √(2 ^ Fintype.card ι * mu.real (ball 0 1)) *
        √(∫ x in (ball (0 : EuclideanSpace ℝ ι) R)ᶜ, ‖W1p.gradient u x‖ ^ 2 ∂mu) := by
  set S := (ball (0 : EuclideanSpace ℝ ι) R)ᶜ
  have hS : MeasurableSet S := measurableSet_ball.compl
  set g : EuclideanSpace ℝ ι → ℝ := fun x => ‖gradient ψ x‖
  set h : EuclideanSpace ℝ ι → ℝ := S.indicator fun x => ‖W1p.gradient u x‖
  have hG : MemLp (W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2 mu := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (W1p.gradient u)
  -- `ψ` is constant on the ball of radius `R`, so only the part of `∇u` outside it enters.
  have hpt : ∀ x, |⟪W1p.gradient u x, gradient ψ x⟫_ℝ| ≤ g x * h x := by
    intro x
    refine (abs_real_inner_le_norm _ _).trans_eq ?_
    by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ ι) R
    · have h1 : ψ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_ball.mem_nhds hx] with y hy
        exact hψ1 (ball_subset_closedBall hy)
      simp [g, h1.gradient_eq, gradient_fun_const]
    · simp [g, h, S, hx, mul_comm]
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport ψ) hψts
  have hg : MemLp g 2 mu :=
    ((hψ.continuous_fderiv one_ne_zero).norm.memLp_of_hasCompactSupport (μ := mu)
      (hψc.fderiv ℝ).norm).ae_eq
      (Eventually.of_forall fun x => (norm_gradient_eq_norm_fderiv ψ x).symm)
  have hh : MemLp h 2 mu := hG.norm.indicator hS.nullMeasurableSet
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall fun x => indicator_nonneg (fun _ _ => norm_nonneg _) x)
    (by rwa [ENNReal.ofReal_ofNat]) (by rwa [ENNReal.ofReal_ofNat])
  have hh2 : ∫ x, h x ^ (2 : ℝ) ∂mu = ∫ x in S, ‖W1p.gradient u x‖ ^ 2 ∂mu := by
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S <;> simp [h, hx]
  have hg2 : ∫ x, g x ^ (2 : ℝ) ∂mu ≤ K ^ 2 * (2 ^ Fintype.card ι * mu.real (ball 0 1)) := by
    simpa only [g, Real.rpow_two] using
      integral_norm_gradient_sq_le_of_tsupport_subset hn hR hψts hψg
  calc |∫ x, ⟪W1p.gradient u x, gradient ψ x⟫_ℝ ∂mu|
      ≤ ∫ x, |⟪W1p.gradient u x, gradient ψ x⟫_ℝ| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ x, g x * h x ∂mu := integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
        (hg.integrable_mul hh) (Eventually.of_forall hpt)
    _ ≤ _ := hCS
    _ ≤ √(K ^ 2 * (2 ^ Fintype.card ι * mu.real (ball 0 1))) *
          √(∫ x in S, ‖W1p.gradient u x‖ ^ 2 ∂mu) := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hh2]
        gcongr
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK, mul_assoc]

/-! ### Poisson's equation on the whole space -/

/-- **Poisson's equation on the line and the plane has no finite-energy solution for data of
nonzero mean.** In dimension `n ≤ 2`, let `f ∈ L²(ℝⁿ)` be integrable with `∫ f ≠ 0` (the
integral being nonzero forces integrability). Then no `u ∈ H¹₀(ℝⁿ) = H¹(ℝⁿ)` is a weak solution
of `-Δu = f`, that is, no `u` satisfies `∫ ∇v · ∇u = ∫ f v` for every `v ∈ H¹₀(ℝⁿ)`. On a bounded
domain the same problem is uniquely solvable for every `f ∈ L²`.

The conclusion also holds in dimensions three and four, where one more integration by parts,
`∫ ⟪∇u, ∇ψ_R⟫ = -∫ u Δψ_R`, and `u ∈ L²` give the decay; it fails from dimension five on, where
the Newtonian potential of the indicator of a ball lies in `H¹(ℝⁿ)`. -/
theorem not_isWeakSolutionDirichlet_one_zero_zero_of_integral_ne_zero [DecidableEq ι]
    (hn : Fintype.card ι ≤ 2) {f : Lp ℝ 2 (mu.restrict (⊤ : Opens (EuclideanSpace ℝ ι)))}
    (hf0 : ∫ x, f x ∂mu ≠ 0) (u : W1p0 mu ⊤ 2) :
    ¬ IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u := by
  intro hu
  rw [isWeakSolutionDirichlet_one_zero_zero_iff] at hu
  have hf : Integrable f mu := by
    by_contra h
    exact hf0 (integral_undef h)
  -- Cutoffs `ψ R`, equal to `1` on the ball of radius `max R 1` and with gradient
  -- `O(1 / max R 1)`.
  obtain ⟨c, hc0, hc⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  choose ψ hψ hψr hψ1 hψts hψg _
    using fun R : ℝ => hc 0 (r := max R 1) (R := 2 * max R 1) (by positivity)
      (by linarith [le_max_right R 1])
  have hψc (R : ℝ) : HasCompactSupport (ψ R) :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hψts R)
  let φ (R : ℝ) : 𝓓((⊤ : Opens (EuclideanSpace ℝ ι)), ℝ) := ⟨ψ R, hψ R, hψc R, by simp⟩
  -- Testing the equation against `ψ R` gives `∫ ⟪∇u, ∇ψ R⟫ = ∫ f (ψ R)`.
  have heq (R : ℝ) : ∫ x, ⟪W1p.gradient (u : W1p mu ⊤ 2) x, gradient (ψ R) x⟫_ℝ ∂mu =
      ∫ x, f x * ψ R x ∂mu := by
    have h := hu ⟨W1p.ofTestFunctionₗ mu ⊤ 2 (φ R), W1p.ofTestFunctionₗ_mem_w1p0Submodule _⟩
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    refine (integral_congr_ae ?_).trans (h.trans (integral_congr_ae ?_))
    · filter_upwards [W1p.gradient_ofTestFunctionₗ_top_ae (mu := mu) (p := 2) (φ R)] with x hx
      rw [hx, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      simp only [φ, TestFunction.coe_mk]
    · filter_upwards [W1p.value_ofTestFunctionₗ_top_ae (mu := mu) (p := 2) (φ R)] with x hx
      rw [hx]
      simp only [φ, TestFunction.coe_mk]
  -- The left side tends to `0`.
  have hleft : Tendsto (fun R : ℝ => ∫ x, ⟪W1p.gradient (u : W1p mu ⊤ 2) x,
      gradient (ψ R) x⟫_ℝ ∂mu) atTop (𝓝 0) := by
    -- The `L²` norm of `∇u` outside the ball of radius `max R 1` tends to zero.
    have hG : Integrable (fun x => ‖W1p.gradient (u : W1p mu ⊤ 2) x‖ ^ 2) mu := by
      have := (Lp.memLp (W1p.gradient (u : W1p mu ⊤ 2))).integrable_norm_pow two_ne_zero
      simpa only [Opens.coe_top, Measure.restrict_univ] using this
    have htail := (tendsto_setIntegral_compl_ball hG 0).comp
      (tendsto_atTop_mono (fun R => le_max_left R 1) tendsto_id)
    have hsq := ((Real.continuous_sqrt.tendsto 0).comp htail).const_mul
      (c * √(2 ^ Fintype.card ι * mu.real (ball 0 1)))
    rw [Real.sqrt_zero, mul_zero] at hsq
    refine squeeze_zero_norm' (Eventually.of_forall fun R => ?_) hsq
    rw [Real.norm_eq_abs, Function.comp_apply, Function.comp_apply]
    have hR := le_max_right R 1
    refine abs_integral_inner_gradient_le_of_eqOn_one hn hR hc0 ((hψ R).of_le (by simp)) (hψ1 R)
      (hψts R) (fun x => (hψg R x).trans_eq ?_) (u : W1p mu ⊤ 2)
    rw [two_mul, add_sub_cancel_right]
  -- The right side tends to `∫ f`.
  have hright := tendsto_integral_smul_of_eq_one_ball (R := fun R => max R 1)
    (tendsto_atTop_mono (fun R => le_max_left R 1) tendsto_id)
    (fun R => (hψ R).continuous.aestronglyMeasurable)
    (fun R x hx => (hψ1 R (mem_closedBall_zero_iff.2 hx.le)).trans (Pi.one_apply x))
    (fun R x => hψr R (mem_range_self x)) hf
  refine hf0 (tendsto_nhds_unique (hright.congr fun R => ?_) hleft)
  rw [heq R]
  exact integral_congr_ae (Eventually.of_forall fun x => (smul_eq_mul _ _).trans (mul_comm _ _))

/-- **The Laplacian on `ℝⁿ` has zero adjoint kernel.** In dimension `n ≥ 1`, if `w ∈ H¹₀(ℝⁿ)`
satisfies `∫ ∇v · ∇w = 0` for every `v ∈ H¹₀(ℝⁿ)`, then `w = 0`. Its gradient vanishes, so it is
almost everywhere constant, and the only constant in `L²(ℝⁿ)` is zero. -/
theorem eq_zero_of_forall_energyFormH1_one_zero_zero_eq_zero [DecidableEq ι] [Nonempty ι]
    {w : W1p0 mu ⊤ 2}
    (hw : ∀ v : W1p0 mu ⊤ 2,
      energyFormH1 (fun _ => 1) 0 0 (v : W1p mu ⊤ 2) (w : W1p mu ⊤ 2) = 0) :
    w = 0 := by
  have hgrad : W1p.gradient (w : W1p mu ⊤ 2) = 0 := by
    have := hw w
    rwa [energyFormH1_one_zero_zero_eq_inner, inner_self_eq_zero] at this
  exact Subtype.ext (W1p.eq_zero_of_gradient_eq_zero ENNReal.ofNat_ne_top hgrad)

end PDE

end TauCeti
