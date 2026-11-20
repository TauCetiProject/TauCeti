/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.ClassicalSolution
public import TauCeti.Analysis.PDE.GreenFunction.Ball
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.ParametricIntegral
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential

/-!
# The Green potential of the unit ball

Let `B` be the open unit ball of `ℝⁿ`, `n ≥ 3`, and let `G` be its Dirichlet Green kernel
(`TauCeti.ballGreenKernel`). This file proves **Green's representation formula**: the weak
solution `u ∈ H¹₀(B)` of the Dirichlet problem

`-Δu = f` in `B`, `u = 0` on `∂B`,

with `f ∈ L²(B)` is the Green potential of `f`,

`u(x) = ∫_B G(x, y) f(y) dy` for almost every `x ∈ B`

(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_ballGreenKernel_mul`). So the
variational solution given by Lax--Milgram has an explicit integral kernel.

## Smooth data

For a `C²` function `ψ` with compact support in `B`, the Green kernel splits as the Newtonian
kernel minus the corrector `φˣ` (`TauCeti.ballGreenCorrector`), and the Green potential splits
accordingly as `v = Φ ⋆ ψ - H` with `H(x) = ∫ φˣ(y) ψ(y) dy`. The corrector is jointly smooth
where `‖x‖ ‖y‖ < 1` and harmonic in `x` for `y` in the closed ball, so `H` is smooth on a
neighbourhood of the closed ball and harmonic inside
(`TauCeti.harmonicOnNhd_integral_smul_of_contDiffOn`), while `-Δ(Φ ⋆ ψ) = ψ`
(`TauCeti.laplacian_newtonianKernel_convolution`). Since `G(x, ·)` vanishes for `x` on the sphere,
`v` is the classical solution of the Dirichlet problem: it is smooth in `B`, continuous on the
closed ball, zero on the sphere, and `-Δv = ψ` in `B`.

## `L²` data

The kernel is dominated by the Newtonian kernel, `0 < G(x, y) ≤ Φ(y - x)` for `x ≠ y` in `B`
(`TauCeti.ballGreenKernel_le_newtonianKernel`), and `Φ` is integrable on bounded sets, so
`(x, y) ↦ G(x, y) f(y)` is integrable on `B × B` for every `f ∈ L¹(B)`
(`TauCeti.integrable_ballGreenKernel_mul`). For a test function `ψ` with compact support in `B`,
let `w ∈ H¹₀(B)` be the weak solution with datum `ψ`; it is the classical solution `v` above, by
`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_of_contDiffOn`. Reciprocity of weak solutions
(`TauCeti.PDE.IsWeakSolutionDirichlet.setIntegral_mul_value_eq_of_isSymm_ae`), Fubini's theorem
and the symmetry `G(x, y) = G(y, x)` then give

`∫_B u ψ = ∫_B f w = ∫_B f(y) ∫_B G(x, y) ψ(x) dx dy = ∫_B ψ(x) ∫_B G(x, y) f(y) dy dx`,

and since `ψ` is arbitrary, `u` agrees almost everywhere with the Green potential of `f`.

## Main declarations

* `TauCeti.contDiffOn_integral_ballGreenKernel_mul`,
  `TauCeti.continuousOn_integral_ballGreenKernel_mul` and
  `TauCeti.laplacian_integral_ballGreenKernel_mul`: the Green potential of a `C²` function with
  compact support in the ball is the classical solution of the Dirichlet problem.
* `TauCeti.integrable_ballGreenKernel_mul`: integrability of `G(x, y) f(y)` on `B × B`.
* `TauCeti.setIntegral_mul_setIntegral_ballGreenKernel_mul_comm`: symmetry of the Green
  potential, `∫_B ψ (G f) = ∫_B f (G ψ)`.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_ballGreenKernel_mul`: the weak
  solution of the Dirichlet problem with `L²` data is the Green potential of the data.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.4 (Green's function for a ball,
  Theorem 13 and the representation formula).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Sections 2.5 and 8.2.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace Filter
open scoped Convolution ENNReal Topology RealInnerProductSpace

variable {n : ℕ}

/-! ### The corrector potential -/

/-- Data supported in a closed ball of radius `r < 1` have a corrector potential
`H(x) = ∫ ψ(y) φˣ(y) dy` that is `C^k` on the ball of radius `r⁻¹`, which contains the closed unit
ball, and harmonic on the open unit ball. -/
private theorem contDiffOn_and_harmonicOnNhd_integral_mul_ballGreenCorrector
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : Continuous ψ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hψr : ∀ y, y ∉ closedBall (0 : EuclideanSpace ℝ (Fin n)) r → ψ y = 0) (k : ℕ∞) :
    ContDiffOn ℝ k (fun x => ∫ y, ψ y * ballGreenCorrector n x y)
        (ball (0 : EuclideanSpace ℝ (Fin n)) r⁻¹) ∧
      HarmonicOnNhd (fun x => ∫ y, ψ y * ballGreenCorrector n x y)
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  set K := closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 r)
  set W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {p | 0 < ‖p.1‖ ^ 2 * ‖p.2‖ ^ 2 - 2 * ⟪p.1, p.2⟫_ℝ + 1}
  have hW : IsOpen W := isOpen_lt continuous_const (by fun_prop)
  have hW' : ∀ {x y : EuclideanSpace ℝ (Fin n)}, ‖x‖ * ‖y‖ < 1 → (x, y) ∈ W := fun h =>
    norm_sq_mul_norm_sq_sub_two_mul_inner_add_one_pos h.ne
  have hg : Integrable (fun y : K => ψ y)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_closedBall).1
      (hψ.continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
  -- The integral over `ℝⁿ` is an integral over the compact parameter space `K`.
  have heq : (fun x => ∫ y, ψ y * ballGreenCorrector n x y) = fun x =>
      ∫ y : K, ψ y • Function.uncurry (ballGreenCorrector n) (x, (y : EuclideanSpace ℝ (Fin n)))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).comap Subtype.val) := by
    funext x
    rw [integral_subtype_comap measurableSet_closedBall
      (fun y => ψ y • Function.uncurry (ballGreenCorrector n) (x, y)),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hψr y hy]]
    simp only [smul_eq_mul, Function.uncurry_apply_pair]
  rw [heq]
  refine ⟨contDiffOn_integral_smul_of_contDiffOn hg continuous_subtype_val hW
    contDiffOn_ballGreenCorrector fun x hx y => hW' ?_, harmonicOnNhd_integral_smul_of_contDiffOn
    hg continuous_subtype_val hW contDiffOn_ballGreenCorrector isOpen_ball
    (fun x hx y => hW' ?_) fun y => ?_⟩
  · have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ r := mem_closedBall_zero_iff.mp y.2
    have hx : ‖x‖ < r⁻¹ := mem_ball_zero_iff.mp hx
    calc ‖x‖ * ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ ‖x‖ * r :=
          mul_le_mul_of_nonneg_left hy (norm_nonneg x)
      _ < r⁻¹ * r := mul_lt_mul_of_pos_right hx hr0
      _ = 1 := inv_mul_cancel₀ hr0.ne'
  · have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ r := mem_closedBall_zero_iff.mp y.2
    have hx : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    calc ‖x‖ * ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ 1 * r :=
          mul_le_mul hx.le hy (norm_nonneg _) zero_le_one
      _ < 1 := by linarith
  · have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ 1 :=
      (mem_closedBall_zero_iff.mp y.2).trans hr1.le
    have hfun : (fun x => Function.uncurry (ballGreenCorrector n)
        (x, (y : EuclideanSpace ℝ (Fin n)))) = ballGreenCorrector n y :=
      funext fun x => ballGreenCorrector_comm x y
    rw [hfun]
    exact harmonicOnNhd_ballGreenCorrector hy

/-- A function whose topological support lies in the open unit ball vanishes outside a closed ball
of some radius `0 < r < 1`. -/
private theorem exists_forall_notMem_closedBall_eq_zero {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hsupp : tsupport ψ ⊆ ball 0 1) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ y, y ∉ closedBall (0 : EuclideanSpace ℝ (Fin n)) r → ψ y = 0 := by
  obtain ⟨r, hr1, hr⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hsupp
  refine ⟨max r (1 / 2), by positivity, max_lt hr1 (by norm_num), fun y hy => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hy' => hy ?_
  exact ball_subset_closedBall (ball_subset_ball (le_max_left r (1 / 2)) (hr hy'))

/-- On the closed unit ball, the Green potential of continuous data vanishing outside a closed ball
of radius `r < 1` is the Newtonian potential minus the corrector potential. -/
private theorem integral_ballGreenKernel_mul_eq_newtonianKernel_convolution_sub
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : Continuous ψ) {r : ℝ} (hr1 : r < 1)
    (hψr : ∀ y, y ∉ closedBall (0 : EuclideanSpace ℝ (Fin n)) r → ψ y = 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 1) :
    ∫ y, ballGreenKernel n x y * ψ y =
      (newtonianKernel n ⋆ ψ) x - ∫ y, ψ y * ballGreenCorrector n x y := by
  have h₁ : Integrable fun y => newtonianKernel n (x - y) * ψ y := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      ((HasCompactSupport.intro (isCompact_closedBall 0 r) hψr).convolutionExists_right
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (locallyIntegrable_newtonianKernel n) hψ x).integrable_swap
  have h₂ : Integrable fun y => ψ y * ballGreenCorrector n x y := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall 0 r) ?_
      fun y hy => by simp [hψr y hy]
    refine ContinuousOn.integrableOn_compact (isCompact_closedBall 0 r)
      (hψ.continuousOn.mul ?_)
    refine (contDiffOn_ballGreenCorrector (k := 0)).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn fun y hy => ?_
    have hy : ‖y‖ ≤ r := mem_closedBall_zero_iff.mp hy
    refine norm_sq_mul_norm_sq_sub_two_mul_inner_add_one_pos (ne_of_lt ?_)
    calc ‖x‖ * ‖y‖ ≤ 1 * r := mul_le_mul hx hy (norm_nonneg y) zero_le_one
      _ < 1 := by linarith
  rw [convolution_eq_swap, ← integral_sub (by simpa only [ContinuousLinearMap.lsmul_apply,
    smul_eq_mul] using h₁) h₂]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ballGreenKernel_def,
    newtonianKernel_sub_comm n x y]
  ring

/-! ### Green's representation for smooth data -/

/-- The Green potential `v(x) = ∫ G(x, y) ψ(y) dy` of a `C^k` function `ψ` with compact support in
the open unit ball is `C^k` in the ball. -/
theorem contDiffOn_integral_ballGreenKernel_mul {k : ℕ∞} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ k ψ) (hsupp : tsupport ψ ⊆ ball 0 1) :
    ContDiffOn ℝ k (fun x => ∫ y, ballGreenKernel n x y * ψ y) (ball 0 1) := by
  obtain ⟨r, hr0, hr1, hψr⟩ := exists_forall_notMem_closedBall_eq_zero hsupp
  have hc : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall 0 r) hψr
  have hH := (contDiffOn_and_harmonicOnNhd_integral_mul_ballGreenCorrector hψ.continuous hr0 hr1
    hψr k).1.mono (ball_subset_ball ((one_le_inv₀ hr0).2 hr1.le))
  exact ((contDiff_newtonianKernel_convolution hψ hc).contDiffOn.sub hH).congr fun x hx =>
    integral_ballGreenKernel_mul_eq_newtonianKernel_convolution_sub hψ.continuous hr1 hψr
      (mem_ball_zero_iff.mp hx).le

/-- The Green potential `v(x) = ∫ G(x, y) ψ(y) dy` of a continuous function `ψ` with compact
support in the open unit ball is continuous on the closed unit ball. -/
theorem continuousOn_integral_ballGreenKernel_mul {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : Continuous ψ) (hsupp : tsupport ψ ⊆ ball 0 1) :
    ContinuousOn (fun x => ∫ y, ballGreenKernel n x y * ψ y) (closedBall 0 1) := by
  obtain ⟨r, hr0, hr1, hψr⟩ := exists_forall_notMem_closedBall_eq_zero hsupp
  have hc : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall 0 r) hψr
  have hH := (contDiffOn_and_harmonicOnNhd_integral_mul_ballGreenCorrector hψ hr0 hr1 hψr
    0).1.continuousOn.mono (closedBall_subset_ball ((one_lt_inv₀ hr0).2 hr1))
  exact ((hc.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (locallyIntegrable_newtonianKernel n) hψ).continuousOn.sub hH).congr fun x hx =>
      integral_ballGreenKernel_mul_eq_newtonianKernel_convolution_sub hψ hr1 hψr
        (mem_closedBall_zero_iff.mp hx)

/-- **The Green potential solves Poisson's equation.** For `n ≥ 3` and a `C²` function `ψ` with
compact support in the open unit ball of `ℝⁿ`, the Green potential `v(x) = ∫ G(x, y) ψ(y) dy`
satisfies `-Δv = ψ` in the ball. Since `G(x, ·)` vanishes for `x` on the unit sphere
(`TauCeti.ballGreenKernel_eq_zero_of_norm_eq_one_left`), so does `v`; together with
`TauCeti.contDiffOn_integral_ballGreenKernel_mul` and
`TauCeti.continuousOn_integral_ballGreenKernel_mul`, `v` is the classical solution of the Dirichlet
problem `-Δv = ψ` in the ball, `v = 0` on the sphere. -/
theorem laplacian_integral_ballGreenKernel_mul (hn : 3 ≤ n) {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hsupp : tsupport ψ ⊆ ball 0 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Δ (fun x => ∫ y, ballGreenKernel n x y * ψ y) x = -ψ x := by
  obtain ⟨r, hr0, hr1, hψr⟩ := exists_forall_notMem_closedBall_eq_zero hsupp
  have hc : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall 0 r) hψr
  have hH := contDiffOn_and_harmonicOnNhd_integral_mul_ballGreenCorrector hψ.continuous hr0 hr1
    hψr 2
  have hv := contDiff_newtonianKernel_convolution hψ hc
  have heq : (fun x => ∫ y, ballGreenKernel n x y * ψ y) =ᶠ[𝓝 x]
      newtonianKernel n ⋆ ψ - fun x => ∫ y, ψ y * ballGreenCorrector n x y := by
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    exact integral_ballGreenKernel_mul_eq_newtonianKernel_convolution_sub hψ.continuous hr1
      hψr (mem_ball_zero_iff.mp hz).le
  rw [(laplacian_congr_nhds heq).self_of_nhds, hv.contDiffAt.laplacian_sub (hH.2 x hx).1,
    laplacian_newtonianKernel_convolution hn hψ hc, (hH.2 x hx).2.eq_of_nhds, Pi.zero_apply,
    sub_zero, Pi.neg_apply]

/-! ### Integrability of the Green kernel -/

/-- **The Green kernel is integrable against `L¹` data.** For `n ≥ 3`, a measurable subset `B` of
the open unit ball and `f` integrable on `B`, the function `(x, y) ↦ G(x, y) f(y)` is integrable
on `B × B`. The kernel is dominated by the Newtonian kernel, whose integral over `B` in the pole is
bounded uniformly in `y ∈ B` by its integral over the ball of radius `2`. -/
theorem integrable_ballGreenKernel_mul (hn : 3 ≤ n) {B : Set (EuclideanSpace ℝ (Fin n))}
    (hBm : MeasurableSet B) (hB : B ⊆ ball 0 1) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : IntegrableOn f B) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ballGreenKernel n p.1 p.2 * f p.2) ((volume.restrict B).prod (volume.restrict B)) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  set M := ∫⁻ z in ball (0 : EuclideanSpace ℝ (Fin n)) 2, ‖newtonianKernel n z‖ₑ
  have hM : M < ∞ := (((locallyIntegrable_newtonianKernel n).integrableOn_isCompact
      (isCompact_closedBall 0 2)).mono_set ball_subset_closedBall).2
  -- For `y ∈ B`, the integral of `|G(·, y)|` over `B` is at most `M`.
  have hbound : ∀ y ∈ B, ∫⁻ x in B, ‖ballGreenKernel n x y‖ₑ ≤ M := by
    intro y hy
    have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp (hB hy)
    calc ∫⁻ x in B, ‖ballGreenKernel n x y‖ₑ
        ≤ ∫⁻ x in B, (ball (0 : EuclideanSpace ℝ (Fin n)) 2).indicator
            (fun z => ‖newtonianKernel n z‖ₑ) (x - y) := by
          refine setLIntegral_mono_ae' hBm ?_
          filter_upwards [compl_mem_ae_iff.mpr (measure_singleton y)] with x hxy hx
          have hxy : x ≠ y := hxy
          have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp (hB hx)
          have h0 : 0 ≤ ballGreenKernel n x y :=
            (ballGreenKernel_pos (by omega) hx1 hy1 hxy.symm).le
          have h1 : ballGreenKernel n x y ≤ newtonianKernel n (x - y) :=
            (ballGreenKernel_le_newtonianKernel (by omega) x y).trans_eq
              (newtonianKernel_sub_comm n y x)
          have hxy2 : x - y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
            rw [mem_ball_zero_iff]
            calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
              _ < 2 := by linarith
          rw [indicator_of_mem hxy2, Real.eNorm_eq_ofReal h0, Real.eNorm_eq_ofReal (h0.trans h1)]
          exact ENNReal.ofReal_le_ofReal h1
      _ ≤ ∫⁻ x, (ball (0 : EuclideanSpace ℝ (Fin n)) 2).indicator
            (fun z => ‖newtonianKernel n z‖ₑ) (x - y) := setLIntegral_le_lintegral _ _
      _ = M := by rw [lintegral_sub_right_eq_self, lintegral_indicator measurableSet_ball]
  have hmeas : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ballGreenKernel n p.1 p.2 * f p.2) ((volume.restrict B).prod (volume.restrict B)) :=
    measurable_ballGreenKernel.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm, lintegral_prod_symm _ hmeas.eNorm]
  calc ∫⁻ y in B, ∫⁻ x in B, ‖ballGreenKernel n (x, y).1 (x, y).2 * f (x, y).2‖ₑ
      ≤ ∫⁻ y in B, M * ‖f y‖ₑ := by
        refine setLIntegral_mono_ae' hBm (ae_of_all _ fun y hy => ?_)
        simp_rw [eNorm_mul]
        rw [lintegral_mul_const' _ _ eNorm_ne_top]
        exact mul_le_mul_left (hbound y hy) _
    _ = M * ∫⁻ y in B, ‖f y‖ₑ := lintegral_const_mul' M _ hM.ne
    _ < ∞ := ENNReal.mul_lt_top hM (hasFiniteIntegral_iff_eNorm.mp hf.2)

/-- **Symmetry of the Green potential.** For `n ≥ 3`, a measurable subset `B` of the open unit
ball, `f` integrable on `B` and `ψ` bounded, measurable and integrable on `B`,

`∫_B ψ(x) ∫_B G(x, y) f(y) dy dx = ∫_B f(y) ∫_B G(y, x) ψ(x) dx dy`,

by Fubini's theorem and the symmetry `G(x, y) = G(y, x)` of the Green kernel. -/
theorem setIntegral_mul_setIntegral_ballGreenKernel_mul_comm (hn : 3 ≤ n)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hBm : MeasurableSet B) (hB : B ⊆ ball 0 1)
    {f ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IntegrableOn f B)
    (hψ : AEStronglyMeasurable ψ (volume.restrict B)) {C : ℝ} (hψC : ∀ x, ‖ψ x‖ ≤ C) :
    ∫ x in B, ψ x * ∫ y in B, ballGreenKernel n x y * f y =
      ∫ y in B, f y * ∫ x in B, ballGreenKernel n y x * ψ x := by
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ψ p.1 * (ballGreenKernel n p.1 p.2 * f p.2))
      ((volume.restrict B).prod (volume.restrict B)) :=
    (integrable_ballGreenKernel_mul hn hBm hB hf).bdd_mul hψ.comp_fst
      (ae_of_all _ fun p => hψC p.1)
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine setIntegral_congr_fun hBm fun x _ => ?_
  simp only [ballGreenKernel_comm x y]
  ring

/-! ### Green's representation of weak solutions -/

namespace PDE

variable {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- For a `C²` datum `ψ` with compact support in the unit ball, the weak solution of `-Δw = ψ`
in `H¹₀(B)` is the Green potential of `ψ`. -/
private theorem IsWeakSolutionDirichlet.value_ae_eq_integral_ballGreenKernel_mul_of_contDiff
    (hn : 2 ≤ n) {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hsupp : tsupport ψ ⊆ ball 0 1)
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball 0 1)
    {g : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hg : g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] ψ)
    {w : W1p0 volume Omega 2} (hw : IsWeakSolutionDirichlet (fun _ => 1) 0 0 g w) :
    W1p.value (w : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        fun x => ∫ y, ballGreenKernel (n + 1) x y * ψ y := by
  refine hw.value_ae_eq_of_contDiffOn hΩ.le ?_ ?_ ?_ ?_
  · rw [hΩ]
    exact contDiffOn_integral_ballGreenKernel_mul hψ hsupp
  · rw [hΩ, closure_ball 0 one_ne_zero]
    exact continuousOn_integral_ballGreenKernel_mul hψ.continuous hsupp
  · intro x hx
    rw [hΩ, frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hx
    simp [ballGreenKernel_eq_zero_of_norm_eq_one_left hx]
  · filter_upwards [hg, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
    rw [hx, Pi.neg_apply, laplacian_integral_ballGreenKernel_mul (by omega) hψ hsupp
      (hΩ ▸ hxΩ), neg_neg]

/-- Tested against a smooth function `ψ` with compact support in the unit ball, the weak solution
`u` of `-Δu = f` and the Green potential of `f` have the same integral: with `w` the weak solution
for the datum `ψ`, reciprocity gives `∫_B ψ u = ∫_B f w`, and `w` is the Green potential of `ψ`. -/
private theorem IsWeakSolutionDirichlet.setIntegral_mul_value_eq_setIntegral_mul_setIntegral
    (hn : 2 ≤ n) (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball 0 1)
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψs : tsupport ψ ⊆ Omega) :
    ∫ x in Omega, ψ x * W1p.value (u : W1p volume Omega 2) x =
      ∫ x in Omega, ψ x * ∫ y in Omega, ballGreenKernel (n + 1) x y * f y := by
  have hm : MeasurableSet (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    Omega.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    ⟨by rw [Measure.restrict_apply_univ, hΩ]; exact measure_ball_lt_top⟩
  have hψ0 : ∀ x, x ∉ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) → ψ x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hψs h)
  obtain ⟨r, -, -, hψr⟩ := exists_forall_notMem_closedBall_eq_zero (hΩ ▸ hψs)
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall 0 r) hψr
  obtain ⟨C, hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hψc.norm
  -- The weak solution `w` with datum `ψ` is the Green potential of `ψ`.
  have hψL : MemLp ψ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (hψ.continuous.memLp_of_hasCompactSupport hψc).restrict _
  obtain ⟨w, hw, -⟩ := existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball hΩ.le
    hψL.toLp
  have hwv := hw.value_ae_eq_integral_ballGreenKernel_mul_of_contDiff hn hψ (hΩ ▸ hψs) hΩ
    hψL.coeFn_toLp
  calc ∫ x in Omega, ψ x * W1p.value (u : W1p volume Omega 2) x
      = ∫ x in Omega, f x * W1p.value (w : W1p volume Omega 2) x := by
        rw [hu.setIntegral_mul_value_eq_of_isSymm_ae (ae_of_all _ fun _ => Matrix.isSymm_one) hw]
        refine integral_congr_ae ?_
        filter_upwards [hψL.coeFn_toLp] with x hx
        rw [hx]
    _ = ∫ y in Omega, f y * ∫ x in Omega, ballGreenKernel (n + 1) y x * ψ x := by
        refine integral_congr_ae ?_
        filter_upwards [hwv] with x hx
        rw [hx, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hψ0 y hy]]
    _ = ∫ x in Omega, ψ x * ∫ y in Omega, ballGreenKernel (n + 1) x y * f y :=
        (setIntegral_mul_setIntegral_ballGreenKernel_mul_comm (by omega) hm hΩ.le
          ((Lp.memLp f).integrable one_le_two) hψ.continuous.aestronglyMeasurable
          fun x => hC ⟨x, rfl⟩).symm

/-- **Green's representation formula on the unit ball.** Let `n ≥ 2`, so that the ambient space
`ℝ^{n+1}` has dimension at least three, and let `B` be the open unit ball. The weak solution
`u ∈ H¹₀(B)` of the Dirichlet problem `-Δu = f` in `B`, `u = 0` on `∂B`, with `f ∈ L²(B)`, is the
Green potential of `f`:

`u(x) = ∫_B G(x, y) f(y) dy` for almost every `x ∈ B`,

where `G` is the Green kernel of the unit ball. -/
theorem IsWeakSolutionDirichlet.value_ae_eq_setIntegral_ballGreenKernel_mul (hn : 2 ≤ n)
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball 0 1)
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u) :
    W1p.value (u : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        fun x => ∫ y in Omega, ballGreenKernel (n + 1) x y * f y := by
  have hm : MeasurableSet (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    Omega.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    ⟨by rw [Measure.restrict_apply_univ, hΩ]; exact measure_ball_lt_top⟩
  have hui : Integrable (W1p.value (u : W1p volume Omega 2))
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Lp.memLp _).integrable one_le_two
  have hvi : Integrable (fun x => ∫ y in Omega, ballGreenKernel (n + 1) x y * f y)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (integrable_ballGreenKernel_mul (by omega) hm hΩ.le
      ((Lp.memLp f).integrable one_le_two)).integral_prod_left
  -- The difference integrates to zero against every test function supported in the ball.
  have key := Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (IntegrableOn.locallyIntegrableOn (hui.sub hvi)) fun ψ hψ hψc hψs => by
      have hψ0 : ∀ x, x ∉ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) → ψ x = 0 :=
        fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hψs h)
      obtain ⟨C, hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hψc.norm
      have hψb : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          ‖ψ x‖ ≤ C := ae_of_all _ fun x => hC ⟨x, rfl⟩
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) fun x hx => ?_).symm.trans ?_
      · simp [hψ0 x hx]
      simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
      rw [integral_sub (hui.bdd_mul hψ.continuous.aestronglyMeasurable hψb)
        (hvi.bdd_mul hψ.continuous.aestronglyMeasurable hψb),
        hu.setIntegral_mul_value_eq_setIntegral_mul_setIntegral hn hΩ (hψ.of_le (by simp)) hψs,
        sub_self]
  filter_upwards [(ae_restrict_iff' hm).2 key] with x hx
  exact sub_eq_zero.mp hx

end PDE

end TauCeti
