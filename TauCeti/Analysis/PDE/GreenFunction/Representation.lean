/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Ball
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DirichletBall
import TauCeti.Analysis.InnerProductSpace.Laplacian.ParametricIntegral
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Green's representation formula on the unit ball

Let `B` be the unit ball of `ℝⁿ`, `n = 1` or `n ≥ 3`, and let `G = TauCeti.ballGreenKernel n` be
its Dirichlet Green kernel, `G(x, y) = Φ(y - x) - φ(x, y)`, with `Φ` the Newtonian kernel and `φ`
the reflected corrector `TauCeti.ballGreenCorrector`. This file proves that the Green kernel
inverts the Dirichlet Laplacian on `B`: the weak solution `u ∈ H¹₀(B)` of `-Δu = f` in `B`,
`u = 0` on `∂B`, is

`u(x) = ∫_B G(x, y) f(y) dy`

for almost every `x ∈ B`, for every `f ∈ L²(B)`
(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_ballGreenKernel_mul`).

## Smooth data

For `f` continuous with `tsupport f ⊆ B`, the corrector term `h(x) = ∫ φ(x, y) f(y) dy` is
harmonic in `B` (`TauCeti.harmonicOnNhd_integral_ballGreenCorrector_mul`) and continuous on the
closed ball, and on the unit sphere it equals the Newtonian potential
`Φ ⋆ f`, because `φ(x, ·) = Φ(· - x)` for `‖x‖ = 1`. So `h` is the harmonic function with
boundary values `Φ ⋆ f`, and on the closed ball

`∫ G(x, y) f(y) dy = (Φ ⋆ f)(x) - h(x)`

(`TauCeti.integral_ballGreenKernel_mul_eq_sub`): the Green potential is the Newtonian potential
corrected by the harmonic extension of its own trace on the sphere. Harmonicity of `h` comes from
differentiating under the integral sign over the compact set `tsupport f`: the corrector is
jointly smooth off `‖x‖ ‖y‖ = 1` and harmonic in `x` for every `y` in the ball
(`TauCeti.harmonicOnNhd_integral_smul_of_contDiffOn`). For `f` of class `C²` the Newtonian
potential solves `-Δ(Φ ⋆ f) = f` and the comparison of classical and weak solutions
(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_newtonianKernel_convolution_sub`) identifies the
Green potential with the weak solution
(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_integral_ballGreenKernel_mul`).

## Data in `L²(B)`

For general `f ∈ L²(B)` the argument is by duality. The Green kernel is symmetric, and off the
diagonal of the ball `|G(x, y)| ≤ |Φ(y - x)| + |Φ(z)|` with `‖z‖ = 2`
(`TauCeti.abs_ballGreenKernel_le`). As `Φ` is locally integrable, the integrals of `|G|` over the
ball in either variable are bounded uniformly, so the Green operator acts on `L¹(B)`
(`TauCeti.integrable_ballGreenKernel_mul`) and Fubini's theorem applies to
`(x, y) ↦ f(x) G(x, y) ψ(y)` for a test function `ψ`. Let `w` be the weak solution with datum
`ψ`, which by the smooth case is the Green potential of `ψ`. Testing the equation of `w` with `u`
and that of `u` with `w`, and using the symmetry of the Dirichlet form,

`∫_B ψ u = a(w, u) = a(u, w) = ∫_B f w = ∫_B f(x) ∫_B G(x, y) ψ(y) dy dx`,

and by Fubini's theorem and the symmetry of `G` the last integral is
`∫_B ψ(y) ∫_B G(y, x) f(x) dx dy`. As `ψ` ranges over the test functions on `B`, `u` agrees
almost everywhere with the Green potential of `f`.

As a check, the torsion function of the ball: the weak solution of `-Δu = 1` in `B` is
`(1 - ‖x‖²) / (2n)`, so `∫_B G(x, y) dy = (1 - ‖x‖²) / (2n)` for almost every `x ∈ B`
(`TauCeti.ae_setIntegral_ballGreenKernel_eq`); for `n = 3` this is `(1 - ‖x‖²) / 6`.

## Main declarations

* `TauCeti.harmonicOnNhd_integral_ballGreenCorrector_mul`,
  `TauCeti.continuousOn_integral_ballGreenCorrector_mul`,
  `TauCeti.integral_ballGreenCorrector_mul_eq_convolution`: the harmonic correction and its
  boundary values.
* `TauCeti.integral_ballGreenKernel_mul_eq_sub`: the Green potential is the corrected Newtonian
  potential.
* `TauCeti.integrable_ballGreenKernel_mul`: the Green operator on `L¹(B)`.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_integral_ballGreenKernel_mul`: the
  representation for data of class `C²` supported in the ball.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_ballGreenKernel_mul`: the
  representation for data in `L²(B)`.
* `TauCeti.ae_setIntegral_ballGreenKernel_eq`: the torsion function of the ball.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 2.2.4 (Green's function, and
  Theorem 12 on the representation formula).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Sections 2.4 and 2.5.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set Filter Topology
open scoped Convolution ENNReal

/-! ### The Green operator on `L¹` of the ball -/

section Integrals

variable {n : ℕ}

/-- Translating the unit ball by a point of the ball stays inside the ball of radius `2`, so the
integral of `‖Φ(· - y)‖ₑ` over the unit ball is at most that of `‖Φ‖ₑ` over the ball of radius
`2`. -/
private theorem setLIntegral_enorm_newtonianKernel_sub_le {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : ‖y‖ < 1) :
    ∫⁻ x in ball 0 1, ‖newtonianKernel (n + 1) (x - y)‖ₑ ≤
      ∫⁻ w in ball 0 2, ‖newtonianKernel (n + 1) w‖ₑ := by
  calc ∫⁻ x in ball 0 1, ‖newtonianKernel (n + 1) (x - y)‖ₑ
      ≤ ∫⁻ x, (ball 0 2).indicator (fun w => ‖newtonianKernel (n + 1) w‖ₑ) (x - y) := by
        rw [← lintegral_indicator measurableSet_ball]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
        · have hx2 : x - y ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 := by
            rw [mem_ball_zero_iff] at hx ⊢
            calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
              _ < 2 := by linarith
          rw [indicator_of_mem hx, indicator_of_mem hx2]
        · rw [indicator_of_notMem hx]
          exact bot_le
    _ = ∫⁻ w in ball 0 2, ‖newtonianKernel (n + 1) w‖ₑ := by
        rw [lintegral_sub_right_eq_self
          (fun x => (ball 0 2).indicator (fun w => ‖newtonianKernel (n + 1) w‖ₑ) x) y,
          lintegral_indicator measurableSet_ball]

/-- The integrals of the Green kernel over the unit ball in its first variable are bounded
uniformly in the second variable. -/
private theorem exists_setLIntegral_enorm_ballGreenKernel_le :
    ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∫⁻ x in ball 0 1, ‖ballGreenKernel (n + 1) x y‖ₑ ≤ M := by
  obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℝ (Fin (n + 1)), ‖z‖ = 2 :=
    ⟨EuclideanSpace.single 0 2, by simp⟩
  have hloc := locallyIntegrable_newtonianKernel (n + 1)
  have hΦ : ∫⁻ w in ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 2,
      ‖newtonianKernel (n + 1) w‖ₑ < ∞ :=
    ((hloc.integrableOn_isCompact (isCompact_closedBall 0 2)).mono_set
      ball_subset_closedBall).2
  refine ⟨(∫⁻ w in ball 0 2, ‖newtonianKernel (n + 1) w‖ₑ) +
      ‖newtonianKernel (n + 1) z‖ₑ * volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
    ENNReal.add_lt_top.2 ⟨hΦ, ENNReal.mul_lt_top eNorm_lt_top measure_ball_lt_top⟩,
    fun y hy => ?_⟩
  have hy' : ‖y‖ < 1 := mem_ball_zero_iff.1 hy
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      ‖newtonianKernel (n + 1) (x - y)‖ₑ :=
    by fun_prop
  calc ∫⁻ x in ball 0 1, ‖ballGreenKernel (n + 1) x y‖ₑ
      ≤ ∫⁻ x in ball 0 1, (‖newtonianKernel (n + 1) (x - y)‖ₑ + ‖newtonianKernel (n + 1) z‖ₑ) := by
        refine setLIntegral_mono_ae (hmeas.add measurable_const).aemeasurable ?_
        have hsing : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))), x ≠ y :=
          ae_iff.2 (by simp)
        filter_upwards [hsing] with x hxy hx
        rw [ballGreenKernel_comm]
        have := abs_ballGreenKernel_le hy' (mem_ball_zero_iff.1 hx) hxy hz
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using this)
    _ = (∫⁻ x in ball 0 1, ‖newtonianKernel (n + 1) (x - y)‖ₑ) +
        ‖newtonianKernel (n + 1) z‖ₑ * volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ _ := add_le_add_left (setLIntegral_enorm_newtonianKernel_sub_le hy') _

/-- **The Green operator on `L¹` of the unit ball.** For `g` integrable on the unit ball, the
function `(x, y) ↦ G(x, y) g(y)` is integrable on the square of the ball. -/
theorem integrable_ballGreenKernel_mul {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hg : IntegrableOn g (ball 0 1)) :
    Integrable (Function.uncurry fun x y => ballGreenKernel (n + 1) x y * g y)
      ((volume.restrict (ball 0 1)).prod (volume.restrict (ball 0 1))) := by
  obtain ⟨M, hM, hbound⟩ := exists_setLIntegral_enorm_ballGreenKernel_le (n := n)
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y => ballGreenKernel (n + 1) x y * g y)
      ((volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).prod
        (volume.restrict (ball 0 1))) :=
    (measurable_ballGreenKernel (n + 1)).aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd
  refine ⟨hmeas, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hmeas.eNorm]
  calc ∫⁻ y in ball 0 1, ∫⁻ x in ball 0 1, ‖ballGreenKernel (n + 1) x y * g y‖ₑ
      = ∫⁻ y in ball 0 1, (∫⁻ x in ball 0 1, ‖ballGreenKernel (n + 1) x y‖ₑ) * ‖g y‖ₑ := by
        refine lintegral_congr fun y => ?_
        simp_rw [eNorm_mul]
        exact lintegral_mul_const' _ _ eNorm_ne_top
    _ ≤ ∫⁻ y in ball 0 1, M * ‖g y‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        gcongr
        exact hbound y hy
    _ < ∞ := by
        rw [lintegral_const_mul' _ _ hM.ne]
        exact ENNReal.mul_lt_top hM hg.2

end Integrals

/-! ### The harmonic correction for data supported in the ball -/

section Smooth

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- A function whose topological support lies in the unit ball has compact support. -/
private theorem hasCompactSupport_of_tsupport_subset_ball {β : Type*} [Zero β]
    {g : EuclideanSpace ℝ (Fin n) → β} (h : tsupport g ⊆ ball 0 1) : HasCompactSupport g :=
  (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport g)
    (h.trans ball_subset_closedBall)

/-- The integrand `φ(x, y) f(y)` of the harmonic correction is continuous on
`closedBall 0 1 × ℝⁿ`. -/
private theorem continuousOn_ballGreenCorrector_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ballGreenCorrector n p.1 p.2 * f p.2) (closedBall 0 1 ×ˢ univ) := by
  rintro ⟨x, y⟩ ⟨hx, -⟩
  refine ContinuousAt.continuousWithinAt ?_
  by_cases hy : y ∈ tsupport f
  · have hxy : ‖x‖ * ‖y‖ < 1 :=
      (mul_le_of_le_one_left (norm_nonneg y) (mem_closedBall_zero_iff.1 hx)).trans_lt
        (mem_ball_zero_iff.1 (hsupp hy))
    exact (continuousAt_ballGreenCorrector hxy.ne).mul (hf.continuousAt.comp continuousAt_snd)
  · have h0 : ∀ᶠ z in 𝓝 y, f z = 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [continuousAt_snd.eventually h0] with p hp
    simp only [hp, mul_zero]

/-- The integrand of the harmonic correction vanishes outside the support of `f`. -/
private theorem ballGreenCorrector_mul_eq_zero {x y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∉ tsupport f) : ballGreenCorrector n x y * f y = 0 := by
  rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- **The harmonic correction is continuous up to the boundary.** For `f` continuous with
`tsupport f` inside the unit ball, `x ↦ ∫ φ(x, y) f(y) dy` is continuous on the closed ball. -/
theorem continuousOn_integral_ballGreenCorrector_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    ContinuousOn (fun x => ∫ y, ballGreenCorrector n x y * f y) (closedBall 0 1) :=
  continuousOn_integral_of_compact_support (hasCompactSupport_of_tsupport_subset_ball hsupp)
    (continuousOn_ballGreenCorrector_mul hf hsupp) fun _ _ _ hy =>
      ballGreenCorrector_mul_eq_zero hy

/-- **The harmonic correction is harmonic.** For `f` continuous with `tsupport f` inside the unit
ball, `x ↦ ∫ φ(x, y) f(y) dy` is harmonic in the open unit ball. -/
theorem harmonicOnNhd_integral_ballGreenCorrector_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    HarmonicOnNhd (fun x => ∫ y, ballGreenCorrector n x y * f y) (ball 0 1) := by
  have hK : IsCompact (tsupport f) := hasCompactSupport_of_tsupport_subset_ball hsupp
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
  -- The integral over `ℝⁿ` is an integral over the compact parameter space `tsupport f`.
  have hrestr : ∀ x, ∫ y, ballGreenCorrector n x y * f y =
      ∫ y : tsupport f, f y • ballGreenCorrector n x y ∂volume.comap Subtype.val := fun x => by
    rw [integral_subtype_comap hKm fun y => f y • ballGreenCorrector n x y,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy =>
        ballGreenCorrector_mul_eq_zero hy]
    simp only [smul_eq_mul, mul_comm (f _)]
  have hg : Integrable (fun y : tsupport f => f y) (volume.comap Subtype.val) :=
    (MeasurableEmbedding.subtypeVal hKm).integrable_map_iff.1
      (by rw [map_comap_subtypeVal hKm]; exact hf.continuousOn.integrableOn_compact hK)
  have hUW : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ y : tsupport f,
      (x, (y : EuclideanSpace ℝ (Fin n))) ∈ {p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) | ‖p.1‖ * ‖p.2‖ ≠ 1} := fun x hx y =>
    ((mul_le_of_le_one_left (norm_nonneg _) (mem_ball_zero_iff.1 hx).le).trans_lt
      (mem_ball_zero_iff.1 (hsupp y.property))).ne
  have hharm : ∀ y : tsupport f,
      HarmonicOnNhd (fun x => ballGreenCorrector n x y) (ball 0 1) := fun y => by
    simp_rw [ballGreenCorrector_comm _ (y : EuclideanSpace ℝ (Fin n))]
    exact harmonicOnNhd_ballGreenCorrector (mem_ball_zero_iff.1 (hsupp y.property)).le
  simp_rw [hrestr]
  exact harmonicOnNhd_integral_smul_of_contDiffOn hg continuous_subtypeVal
    (isOpen_ne_fun (by fun_prop) continuous_const) contDiffOn_ballGreenCorrector isOpen_ball
    hUW hharm

/-- **Boundary values of the harmonic correction.** On the unit sphere the corrector is the
Newtonian kernel, so the harmonic correction equals the Newtonian potential `Φ ⋆ f` there. -/
theorem integral_ballGreenCorrector_mul_eq_convolution {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ = 1) :
    ∫ y, ballGreenCorrector n x y * f y = (newtonianKernel n ⋆ f) x := by
  rw [convolution_eq_swap]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ballGreenCorrector_eq_newtonianKernel_sub_of_norm_eq_one_left hx,
    newtonianKernel_sub_comm _ x y, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- **The Green potential is the corrected Newtonian potential.** For `f` continuous with
`tsupport f` inside the unit ball and `x` in the closed ball,
`∫ G(x, y) f(y) dy = (Φ ⋆ f)(x) - ∫ φ(x, y) f(y) dy`. The subtracted term is harmonic in the
ball, continuous on its closure and equal to `Φ ⋆ f` on the sphere. -/
theorem integral_ballGreenKernel_mul_eq_sub (hf : Continuous f) (hsupp : tsupport f ⊆ ball 0 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 1) :
    ∫ y, ballGreenKernel n x y * f y =
      (newtonianKernel n ⋆ f) x - ∫ y, ballGreenCorrector n x y * f y := by
  have hc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_ball hsupp
  have h1 : Integrable fun y => newtonianKernel n (x - y) * f y := by
    simpa using (hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (locallyIntegrable_newtonianKernel n) hf x).integrable_swap
  have h2 : Integrable fun y => ballGreenCorrector n x y * f y := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hc.mul_left
    exact (continuousOn_ballGreenCorrector_mul hf hsupp).comp_continuous
      (continuous_const.prodMk continuous_id) fun _ => ⟨mem_closedBall_zero_iff.2 hx, mem_univ _⟩
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ballGreenKernel_def, newtonianKernel_sub_comm _ x y, sub_mul]

end Smooth

/-! ### Weak solutions of the Dirichlet problem -/

namespace PDE

open TopologicalSpace

section Weak

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- **Green's representation formula for smooth data.** Let `n ≠ 1`, so that the dimension
`n + 1` is `1` or at least `3`, and let `f` be of class `C²` with `tsupport f` inside the unit
ball `B`. The weak solution `u ∈ H¹₀(B)` of `-Δu = f` in `B`, `u = 0` on `∂B`, is the Green
potential of `f`: `u(x) = ∫ G(x, y) f(y) dy` for almost every `x ∈ B`. -/
theorem IsWeakSolutionDirichlet.value_ae_eq_integral_ballGreenKernel_mul (hn : n ≠ 1)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : tsupport f ⊆ ball 0 1)
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball 0 1)
    {g : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hg : g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] f)
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 g u) :
    W1p.value (u : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        fun x => ∫ y, ballGreenKernel (n + 1) x y * f y := by
  refine (hu.value_ae_eq_newtonianKernel_convolution_sub hn hf
    (hasCompactSupport_of_tsupport_subset_ball hsupp)
    (harmonicOnNhd_integral_ballGreenCorrector_mul hf.continuous hsupp)
    (continuousOn_integral_ballGreenCorrector_mul hf.continuous hsupp)
    (fun x hx => integral_ballGreenCorrector_mul_eq_convolution (mem_sphere_zero_iff_norm.1 hx))
    hΩ hg).trans ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
  rw [hΩ, mem_ball_zero_iff] at hx
  exact (integral_ballGreenKernel_mul_eq_sub hf.continuous hsupp hx.le).symm

/-- **Fubini's theorem for the Green kernel.** For `f` integrable on the unit ball and `ψ`
continuous with `tsupport ψ` inside the ball,
`∫_B f(x) ∫ G(x, y) ψ(y) dy dx = ∫_B ψ(y) ∫_B G(y, x) f(x) dx dy`. -/
private theorem setIntegral_mul_integral_ballGreenKernel_mul_comm
    {f ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IntegrableOn f (ball 0 1))
    (hψ : Continuous ψ) (hψsupp : tsupport ψ ⊆ ball 0 1) :
    ∫ x in ball 0 1, f x * ∫ y, ballGreenKernel (n + 1) x y * ψ y =
      ∫ y in ball 0 1, ψ y * ∫ x in ball 0 1, ballGreenKernel (n + 1) y x * f x := by
  obtain ⟨C, hC⟩ :=
    hψ.bounded_above_of_compact_support (hasCompactSupport_of_tsupport_subset_ball hψsupp)
  have hψ0 := Function.support_subset_iff'.1 ((subset_tsupport ψ).trans hψsupp)
  have hprod : Integrable (Function.uncurry fun x y => f x * (ballGreenKernel (n + 1) x y * ψ y))
      ((volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).prod
        (volume.restrict (ball 0 1))) := by
    refine ((integrable_ballGreenKernel_mul hf).swap.mul_bdd (c := C)
      hψ.aestronglyMeasurable.comp_snd (Eventually.of_forall fun p => hC p.2)).congr
      (Eventually.of_forall fun ⟨x, y⟩ => ?_)
    simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair,
      ballGreenKernel_comm x y]
    ring
  calc ∫ x in ball 0 1, f x * ∫ y, ballGreenKernel (n + 1) x y * ψ y
      = ∫ x in ball 0 1, ∫ y in ball 0 1, f x * (ballGreenKernel (n + 1) x y * ψ y) := by
        refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
        rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
          rw [hψ0 y hy, mul_zero]]
    _ = ∫ y in ball 0 1, ∫ x in ball 0 1, f x * (ballGreenKernel (n + 1) x y * ψ y) :=
        integral_integral_swap hprod
    _ = _ := by
        refine setIntegral_congr_fun measurableSet_ball fun y _ => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [ballGreenKernel_comm x y]
        ring

/-- **The duality identity.** If `u` is the weak solution of `-Δu = f` on the unit ball and `ψ`
is a test function on the ball, then `∫_B ψ u = ∫_B f(x) ∫ G(x, y) ψ(y) dy dx`: test the equation
of `u` with the weak solution `w` of `-Δw = ψ`, which is the Green potential of `ψ`, and the
equation of `w` with `u`. -/
private theorem IsWeakSolutionDirichlet.setIntegral_mul_value_eq (hn : n ≠ 1)
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball 0 1)
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψsupp : tsupport ψ ⊆ ball 0 1) :
    ∫ x in ball 0 1, ψ x * W1p.value (u : W1p volume Omega 2) x =
      ∫ x in ball 0 1, f x * ∫ y, ballGreenKernel (n + 1) x y * ψ y := by
  have hψL2 : MemLp ψ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (hψ.continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_of_tsupport_subset_ball hψsupp)).restrict _
  obtain ⟨w, hw, -⟩ := existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball
    (z := 0) (R := 1) hΩ.le (hψL2.toLp ψ)
  have hwG := hw.value_ae_eq_integral_ballGreenKernel_mul hn hψ hψsupp hΩ hψL2.coeFn_toLp
  have h1 := (isWeakSolutionDirichlet_iff _ _).1 hw u
  have h2 := (isWeakSolutionDirichlet_iff _ _).1 hu w
  rw [← hΩ]
  calc ∫ x in Omega, ψ x * W1p.value (u : W1p volume Omega 2) x
      = ∫ x in Omega, hψL2.toLp ψ x * W1p.value (u : W1p volume Omega 2) x := by
        refine integral_congr_ae ?_
        filter_upwards [hψL2.coeFn_toLp] with x hx
        rw [hx]
    _ = ∫ x in Omega, f x * W1p.value (w : W1p volume Omega 2) x := by
        rw [← h1, energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ => Matrix.isSymm_one), h2]
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hwG] with x hx
        rw [hx]

/-- **Green's representation formula.** Let `n ≠ 1`, so that the dimension `n + 1` is `1` or at
least `3`, and let `B` be the unit ball. For every `f ∈ L²(B)`, the weak solution `u ∈ H¹₀(B)`
of `-Δu = f` in `B`, `u = 0` on `∂B`, is the Green potential of `f`:

`u(x) = ∫_B G(x, y) f(y) dy` for almost every `x ∈ B`. -/
theorem IsWeakSolutionDirichlet.value_ae_eq_setIntegral_ballGreenKernel_mul (hn : n ≠ 1)
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball 0 1)
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u) :
    W1p.value (u : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        fun x => ∫ y in ball 0 1, ballGreenKernel (n + 1) x y * f y := by
  have hfin : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 (hΩ ▸ measure_ball_lt_top.ne)
  have hint : ∀ v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))),
      IntegrableOn v (ball 0 1) := fun v => hΩ ▸ (Lp.memLp v).integrable one_le_two
  have hGf : IntegrableOn (fun x => ∫ y in ball 0 1, ballGreenKernel (n + 1) x y * f y)
      (ball 0 1) := (integrable_ballGreenKernel_mul (hint f)).integral_prod_left
  obtain ⟨D, hD⟩ : ∃ D : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, D = fun x =>
      W1p.value (u : W1p volume Omega 2) x - ∫ y in ball 0 1, ballGreenKernel (n + 1) x y * f y :=
    ⟨_, rfl⟩
  suffices h : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      x ∈ ball 0 1 → D x = 0 by
    refine (ae_restrict_iff' Omega.isOpen.measurableSet).2 (h.mono fun x hx hxΩ => ?_)
    have hx' := hx (hΩ ▸ hxΩ)
    rw [hD] at hx'
    exact sub_eq_zero.1 hx'
  have hDint : IntegrableOn D (ball 0 1) := by
    rw [hD]
    exact (hint _).sub hGf
  refine isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero hDint.locallyIntegrableOn
    fun ψ hψ hψc hψsupp => ?_
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hψmeas : AEStronglyMeasurable ψ (volume.restrict (ball 0 1)) :=
    hψ.continuous.aestronglyMeasurable
  have hψ0 := Function.support_subset_iff'.1 ((subset_tsupport ψ).trans hψsupp)
  calc ∫ x, ψ x • D x
      = ∫ x in ball 0 1, ψ x * W1p.value (u : W1p volume Omega 2) x -
          ψ x * ∫ y in ball 0 1, ballGreenKernel (n + 1) x y * f y := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [hψ0 x hx, zero_smul]]
        exact setIntegral_congr_fun measurableSet_ball fun x _ => by rw [hD, smul_eq_mul, mul_sub]
    _ = (∫ x in ball 0 1, ψ x * W1p.value (u : W1p volume Omega 2) x) -
          ∫ x in ball 0 1, ψ x * ∫ y in ball 0 1, ballGreenKernel (n + 1) x y * f y :=
        integral_sub ((hint _).bdd_mul hψmeas (Eventually.of_forall hC))
          (hGf.bdd_mul hψmeas (Eventually.of_forall hC))
    -- The duality identity, then Fubini's theorem.
    _ = (∫ x in ball 0 1, f x * ∫ y, ballGreenKernel (n + 1) x y * ψ y) -
          ∫ y in ball 0 1, ψ y * ∫ x in ball 0 1, ballGreenKernel (n + 1) y x * f x := by
        rw [hu.setIntegral_mul_value_eq hn hΩ (hψ.of_le (by simp)) hψsupp]
    _ = 0 := by
        rw [setIntegral_mul_integral_ballGreenKernel_mul_comm (hint f) hψ.continuous hψsupp,
          sub_self]

end Weak

end PDE

/-- **The torsion function of the ball.** Let `n ≠ 1`, so that the dimension `n + 1` is `1` or at
least `3`. The Green potential of the constant `1` on the unit ball `B` of `ℝⁿ⁺¹` is
`∫_B G(x, y) dy = (1 - ‖x‖²) / (2(n + 1))` for almost every `x ∈ B`: it is the solution of
`-Δu = 1` in `B`, `u = 0` on the sphere. In `ℝ³` (`n = 2`) this is `(1 - ‖x‖²) / 6`. -/
theorem ae_setIntegral_ballGreenKernel_eq (hn : n ≠ 1) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)),
      ∫ y in ball 0 1, ballGreenKernel (n + 1) x y = (1 - ‖x‖ ^ 2) / (2 * ((n : ℝ) + 1)) := by
  let Omega : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball 0 1, isOpen_ball⟩
  have hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball 0 1 := rfl
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have h1 : MemLp (fun _ : EuclideanSpace ℝ (Fin (n + 1)) => (1 : ℝ)) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := memLp_const 1
  obtain ⟨u, hu, -⟩ := PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball
    (z := 0) (R := 1) hΩ.le (h1.toLp _)
  obtain ⟨w, hwdef⟩ : ∃ w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      w = (2 * ((n : ℝ) + 1))⁻¹ • ((fun _ => (1 : ℝ)) - fun y => ‖y‖ ^ 2) := ⟨_, rfl⟩
  have hwx : ∀ x, w x = (1 - ‖x‖ ^ 2) / (2 * ((n : ℝ) + 1)) := fun x => by
    rw [hwdef, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_inv_mul]
  have hw' : ContDiff ℝ 2
      ((fun _ => (1 : ℝ)) - fun y : EuclideanSpace ℝ (Fin (n + 1)) => ‖y‖ ^ 2) :=
    contDiff_const.sub (contDiff_norm_sq ℝ)
  have hw : ContDiff ℝ 2 w := by
    rw [hwdef]
    exact hw'.const_smul (2 * ((n : ℝ) + 1))⁻¹
  -- `Δ (1 - ‖y‖²) = -2 (n + 1)`, by `laplacian_norm_sq`.
  have hΔ : ∀ x, Δ w x = -1 := fun x => by
    simp [hwdef, laplacian_smul _ hw'.contDiffAt,
      contDiffAt_const.laplacian_sub (contDiff_norm_sq ℝ).contDiffAt, laplacian_norm_sq]
    field_simp
  have hwu := hu.value_ae_eq_of_contDiffOn hΩ.le hw.contDiffOn hw.continuous.continuousOn
    (fun x hx => by
      rw [hΩ, frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hx
      simp [hwx, hx])
    (by
      filter_upwards [h1.coeFn_toLp] with x hx
      rw [hx, Pi.neg_apply, hΔ x, neg_neg])
  filter_upwards [hwu.symm.trans (hu.value_ae_eq_setIntegral_ballGreenKernel_mul hn hΩ)]
    with x hx
  rw [← hwx, hx]
  refine integral_congr_ae ?_
  filter_upwards [h1.coeFn_toLp] with y hy
  rw [hy, mul_one]

end TauCeti
