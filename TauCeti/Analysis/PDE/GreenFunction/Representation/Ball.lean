/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Ball
public import TauCeti.Analysis.PDE.GreenFunction.Representation.Basic
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DirichletBall
import TauCeti.Analysis.InnerProductSpace.Laplacian.ParametricIntegral
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.MeasureTheory.Integral.Kernel.Potential
import TauCeti.Topology.Algebra.Support

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
(`TauCeti.harmonicOnNhd_integral_mul_of_contDiffOn`). For `f` of class `C²` the Newtonian
potential solves `-Δ(Φ ⋆ f) = f` and the comparison of classical and weak solutions
(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_newtonianKernel_convolution_sub`) identifies the
Green potential with the weak solution
(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_integral_ballGreenKernel_mul`).

## Data in `L²(B)`

For general `f ∈ L²(B)` the argument is by duality
(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_mul_of_forall_contDiff`). The Green
kernel is symmetric, and off the diagonal of the ball `|G(x, y)| ≤ |Φ(y - x)| + |Φ(z)|` with
`‖z‖ = 2` (`TauCeti.abs_ballGreenKernel_le`). As `Φ` is locally integrable, the Green operator
acts on `L¹(B)` (`TauCeti.integrable_ballGreenKernel_mul`), and the representation for smooth data
extends to `L²(B)`.

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
open scoped Convolution

/-! ### The Green operator on `L¹` of the ball -/

section Integrals

variable {n : ℕ}

/-- **The Green operator on `L¹` of the unit ball.** For `g` integrable on the unit ball, the
function `(x, y) ↦ G(x, y) g(y)` is integrable on the square of the ball. -/
theorem integrable_ballGreenKernel_mul {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hg : IntegrableOn g (ball 0 1)) :
    Integrable (Function.uncurry fun x y => ballGreenKernel (n + 1) x y * g y)
      ((volume.restrict (ball 0 1)).prod (volume.restrict (ball 0 1))) := by
  obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℝ (Fin (n + 1)), ‖z‖ = 2 :=
    ⟨EuclideanSpace.single 0 2, by simp⟩
  refine (locallyIntegrable_newtonianKernel (n + 1)).integrable_uncurry_mul_of_abs_le
    measurableSet_ball isBounded_ball (C := |newtonianKernel (n + 1) z|)
    (measurable_ballGreenKernel _).aestronglyMeasurable (fun x hx y hy hxy => ?_) hg
  rw [newtonianKernel_sub_comm _ x y]
  exact abs_ballGreenKernel_le (mem_ball_zero_iff.1 hx) (mem_ball_zero_iff.1 hy) hxy.symm hz

end Integrals

/-! ### The harmonic correction for data supported in the ball -/

section Smooth

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The integrand `φ(x, y) f(y)` of the harmonic correction is continuous on
`closedBall 0 1 × ℝⁿ`. -/
private theorem continuousOn_ballGreenCorrector_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ballGreenCorrector n p.1 p.2 * f p.2) (closedBall 0 1 ×ˢ univ) := by
  simpa only [smul_eq_mul] using hf.continuousOn_smul_comp_snd_of_continuousAt fun x hx y hy =>
    continuousAt_ballGreenCorrector ((mul_le_of_le_one_left (norm_nonneg y)
      (mem_closedBall_zero_iff.1 hx)).trans_lt (mem_ball_zero_iff.1 (hsupp hy))).ne

/-- The integrand of the harmonic correction vanishes outside the support of `f`. -/
private theorem ballGreenCorrector_mul_eq_zero {x y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∉ tsupport f) : ballGreenCorrector n x y * f y = 0 := by
  rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- **The harmonic correction is continuous up to the boundary.** For `f` continuous with
`tsupport f` inside the unit ball, `x ↦ ∫ φ(x, y) f(y) dy` is continuous on the closed ball. -/
theorem continuousOn_integral_ballGreenCorrector_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    ContinuousOn (fun x => ∫ y, ballGreenCorrector n x y * f y) (closedBall 0 1) :=
  continuousOn_integral_of_compact_support (HasCompactSupport.of_tsupport_subset_ball hsupp)
    (continuousOn_ballGreenCorrector_mul hf hsupp) fun _ _ _ hy =>
      ballGreenCorrector_mul_eq_zero hy

/-- **The harmonic correction is harmonic.** For `f` continuous with `tsupport f` inside the unit
ball, `x ↦ ∫ φ(x, y) f(y) dy` is harmonic in the open unit ball. -/
theorem harmonicOnNhd_integral_ballGreenCorrector_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    HarmonicOnNhd (fun x => ∫ y, ballGreenCorrector n x y * f y) (ball 0 1) :=
  harmonicOnNhd_integral_mul_of_contDiffOn (F := fun p => ballGreenCorrector n p.1 p.2) hf
    (HasCompactSupport.of_tsupport_subset_ball hsupp) (isOpen_ne_fun (by fun_prop)
      continuous_const) contDiffOn_ballGreenCorrector isOpen_ball
    (fun x hx y hy => ((mul_le_of_le_one_left (norm_nonneg _) (mem_ball_zero_iff.1 hx).le).trans_lt
      (mem_ball_zero_iff.1 (hsupp hy))).ne)
    fun y hy => by
      simp_rw [ballGreenCorrector_comm _ y]
      exact harmonicOnNhd_ballGreenCorrector (mem_ball_zero_iff.1 (hsupp hy)).le

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
  have hc : HasCompactSupport f := HasCompactSupport.of_tsupport_subset_ball hsupp
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
    (HasCompactSupport.of_tsupport_subset_ball hsupp)
    (harmonicOnNhd_integral_ballGreenCorrector_mul hf.continuous hsupp)
    (continuousOn_integral_ballGreenCorrector_mul hf.continuous hsupp)
    (fun x hx => integral_ballGreenCorrector_mul_eq_convolution (mem_sphere_zero_iff_norm.1 hx))
    hΩ hg).trans ?_
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
  rw [hΩ, mem_ball_zero_iff] at hx
  exact (integral_ballGreenKernel_mul_eq_sub hf.continuous hsupp hx.le).symm

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
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 (hΩ ▸ measure_ball_lt_top.ne)
  have hf : IntegrableOn f (ball 0 1) := by
    rw [← hΩ]
    exact (Lp.memLp f).integrable one_le_two
  have hGf := integrable_ballGreenKernel_mul hf
  rw [← hΩ] at hGf ⊢
  exact hu.value_ae_eq_setIntegral_mul_of_forall_contDiff hΩ.le ballGreenKernel_comm
    (fun ψ hψ _ hψsupp g hg w hw => hw.value_ae_eq_integral_ballGreenKernel_mul hn
      (hψ.of_le (by simp)) (hΩ ▸ hψsupp) hΩ hg) hGf

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
