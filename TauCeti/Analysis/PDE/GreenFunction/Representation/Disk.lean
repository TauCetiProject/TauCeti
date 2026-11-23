/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Planar
public import TauCeti.Analysis.PDE.GreenFunction.Representation.Basic
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DirichletBall
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.InnerProductSpace.Laplacian.ParametricIntegral
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential
import TauCeti.MeasureTheory.Integral.Kernel.Potential
import TauCeti.Topology.Algebra.Support

/-!
# Green's representation formula on the unit disk

Let `B` be the unit disk of `ℝ²`, identified with the unit disk of `ℂ` by a linear isometry
`e : ℝ² ≃ ℂ`, and let `G(x, y) = TauCeti.planarGreenKernel (e x) (e y)` be its Dirichlet Green
kernel,

`G(x, y) = Φ(e y - e x) - Φ(1 - conj (e x) * e y)`, `Φ(z) = -(2π)⁻¹ log ‖z‖`.

This file proves that the Green kernel inverts the Dirichlet Laplacian on `B`: the weak solution
`u ∈ H¹₀(B)` of `-Δu = f` in `B`, `u = 0` on `∂B`, is

`u(x) = ∫_B G(x, y) f(y) dy`

for almost every `x ∈ B`, for every `f ∈ L²(B)`
(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_planarGreenKernel_mul`). This is
the two-dimensional case of Green's representation formula, whose kernel is logarithmic; for the
other dimensions see
`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_ballGreenKernel_mul`.
The kernel does not depend on the choice of `e`, since `‖e x - e y‖ = ‖x - y‖` and
`‖1 - conj (e x) * e y‖² = 1 - 2 ⟪x, y⟫ + ‖x‖² ‖y‖²`.

## Smooth data

Let `f` be of class `C²` with `tsupport f ⊆ B`. Its Newtonian potential in the coordinates `e` is
`V = (Φ ⋆ (f ∘ e⁻¹)) ∘ e`, so `V(x) = ∫ Φ(e y - e x) f(y) dy` and `-ΔV = f`
(`TauCeti.laplacian_planarNewtonianKernel_convolution`). The corrector term
`h(x) = ∫ Φ(1 - conj (e x) * e y) f(y) dy` is harmonic in `B`, since `Φ(1 - conj (e y) * w)` is
harmonic in `w` on the unit disk for `‖e y‖ < 1`, and it is continuous on the closed disk. On the
unit circle `‖1 - conj (e x) * e y‖ = ‖e x - e y‖`, so `h = V` there, and the weak solution is
`V - h` (`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_sub_of_laplacian_eq_neg`), which is the
Green potential of `f`
(`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_integral_planarGreenKernel_mul`).

## Data in `L²(B)`

At distinct points of the disk `|G(x, y)| ≤ |Φ(e y - e x)| + |Φ(2)|`
(`TauCeti.abs_planarGreenKernel_le`). As `Φ` is locally integrable, the Green operator acts on
`L¹(B)` (`TauCeti.integrable_planarGreenKernel_mul`), and since `G` is symmetric
(`TauCeti.planarGreenKernel_comm`) the representation for smooth data extends to `L²(B)` by
duality (`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_mul_of_forall_contDiff`).

## Main declarations

* `TauCeti.harmonicOnNhd_integral_planarNewtonianKernel_one_sub_conj_mul`,
  `TauCeti.continuousOn_integral_planarNewtonianKernel_one_sub_conj_mul`,
  `TauCeti.integral_planarNewtonianKernel_one_sub_conj_mul_eq`: the harmonic correction and its
  boundary values.
* `TauCeti.integral_planarGreenKernel_mul_eq_sub`: the Green potential is the corrected Newtonian
  potential.
* `TauCeti.integrable_planarGreenKernel_mul`: the Green operator on `L¹(B)`.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_integral_planarGreenKernel_mul`: the
  representation for data of class `C²` supported in the disk.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_setIntegral_planarGreenKernel_mul`: the
  representation for data in `L²(B)`.

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

variable (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ)

/-! ### The Green operator on `L¹` of the disk -/

section Integrals

/-- **The Green operator on `L¹` of the unit disk.** For `g` integrable on the unit disk of `ℝ²`,
the function `(x, y) ↦ G(x, y) g(y)` is integrable on the square of the disk. -/
theorem integrable_planarGreenKernel_mul {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hg : IntegrableOn g (ball 0 1)) :
    Integrable (Function.uncurry fun x y ↦ planarGreenKernel (e x) (e y) * g y)
      ((volume.restrict (ball 0 1)).prod (volume.restrict (ball 0 1))) := by
  refine (locallyIntegrable_planarNewtonianKernel_comp e).integrable_uncurry_mul_of_abs_le
    measurableSet_ball isBounded_ball (C := |planarNewtonianKernel 2|)
    (G := fun x y ↦ planarGreenKernel (e x) (e y))
    (measurable_planarGreenKernel.comp
      (e.continuous.measurable.prodMap e.continuous.measurable)).aestronglyMeasurable
    (fun x hx y hy hxy ↦ ?_) hg
  have h := abs_planarGreenKernel_le (by simpa using hx) (by simpa using hy)
    (e.injective.ne hxy.symm)
  rwa [planarNewtonianKernel_sub_comm, ← map_sub] at h

end Integrals

/-! ### The Newtonian potential and the harmonic correction -/

section Smooth

variable {f : EuclideanSpace ℝ (Fin 2) → ℝ}

/-- The Newtonian potential in the coordinates `e`: `(Φ ⋆ (f ∘ e⁻¹))(e x) = ∫ Φ(e y - e x) f(y) dy`.
-/
private theorem planarNewtonianKernel_convolution_comp_apply (x : EuclideanSpace ℝ (Fin 2)) :
    ((planarNewtonianKernel ⋆ (f ∘ e.symm)) ∘ e) x =
      ∫ y, planarNewtonianKernel (e y - e x) * f y := by
  rw [Function.comp_apply, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp [planarNewtonianKernel_sub_comm (e x)]

/-- The reflected logarithmic term does not vanish at a point of the closed disk and a point of
the open disk. -/
private theorem one_sub_conj_mul_ne_zero {x y : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ ≤ 1)
    (hy : ‖y‖ < 1) : 1 - starRingEnd ℂ (e x) * e y ≠ 0 := by
  rw [← norm_ne_zero_iff, Complex.norm_one_sub_conj_mul_comm, norm_ne_zero_iff]
  exact one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one (by simpa using hx)
    (by simpa using hy)

/-- The map `(x, y) ↦ 1 - conj (e x) * e y` is smooth. -/
private theorem contDiff_one_sub_conj_mul {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      1 - starRingEnd ℂ (e p.1) * e p.2) :=
  contDiff_const.sub ((Complex.conjCLE.contDiff.comp (e.contDiff.comp contDiff_fst)).mul
    (e.contDiff.comp contDiff_snd))

/-- The integrand `Φ(1 - conj (e x) * e y) f(y)` of the harmonic correction is continuous on
`closedBall 0 1 × ℝ²`. -/
private theorem continuousOn_planarNewtonianKernel_one_sub_conj_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      planarNewtonianKernel (1 - starRingEnd ℂ (e p.1) * e p.2) * f p.2)
      (closedBall 0 1 ×ˢ univ) := by
  simpa only [smul_eq_mul] using hf.continuousOn_smul_comp_snd_of_continuousAt
    (F := fun p ↦ planarNewtonianKernel (1 - starRingEnd ℂ (e p.1) * e p.2)) fun x hx y hy ↦
      (contDiffAt_planarNewtonianKernel (n := 0) (one_sub_conj_mul_ne_zero e
        (mem_closedBall_zero_iff.1 hx) (mem_ball_zero_iff.1 (hsupp hy)))).continuousAt.comp
        (f := fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
          1 - starRingEnd ℂ (e p.1) * e p.2)
        (contDiff_one_sub_conj_mul e (k := 0)).continuous.continuousAt

/-- The harmonic correction `x ↦ ∫ Φ(1 - conj (e x) * e y) f(y) dy` is continuous on the closed
unit disk, for `f` continuous with `tsupport f` inside the open unit disk. -/
theorem continuousOn_integral_planarNewtonianKernel_one_sub_conj_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    ContinuousOn (fun x ↦ ∫ y, planarNewtonianKernel (1 - starRingEnd ℂ (e x) * e y) * f y)
      (closedBall 0 1) :=
  continuousOn_integral_of_compact_support
    (HasCompactSupport.of_tsupport_subset_ball hsupp)
    (continuousOn_planarNewtonianKernel_one_sub_conj_mul e hf hsupp) fun _ _ _ hy => by
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- The harmonic correction `x ↦ ∫ Φ(1 - conj (e x) * e y) f(y) dy` is harmonic in the unit
disk, for `f` continuous with `tsupport f` inside the unit disk. -/
theorem harmonicOnNhd_integral_planarNewtonianKernel_one_sub_conj_mul (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) :
    HarmonicOnNhd (fun x ↦ ∫ y, planarNewtonianKernel (1 - starRingEnd ℂ (e x) * e y) * f y)
      (ball 0 1) := by
  refine harmonicOnNhd_integral_mul_of_contDiffOn
    (F := fun p ↦ planarNewtonianKernel (1 - starRingEnd ℂ (e p.1) * e p.2)) hf
    (HasCompactSupport.of_tsupport_subset_ball hsupp)
    (isOpen_ne_fun (contDiff_one_sub_conj_mul e (k := 0)).continuous continuous_const)
    (fun p hp ↦ ((contDiffAt_planarNewtonianKernel hp).comp p
      (contDiff_one_sub_conj_mul e).contDiffAt).contDiffWithinAt)
    isOpen_ball (fun x hx y hy ↦ one_sub_conj_mul_ne_zero e (mem_ball_zero_iff.1 hx).le
      (mem_ball_zero_iff.1 (hsupp hy))) fun y hy x hx ↦ ?_
  -- `Φ(1 - conj (e x) * e y) = Φ(1 - conj (e y) * e x)` is harmonic in `e x` on the unit disk.
  simp_rw [planarNewtonianKernel_one_sub_conj_mul_comm _ (e y)]
  exact (harmonicAt_comp_linearIsometryEquiv_right_iff e
    (f := fun w ↦ planarNewtonianKernel (1 - starRingEnd ℂ (e y) * w))).2
    (harmonicAt_planarNewtonianKernel_one_sub_conj_mul (by simpa using hsupp hy)
      (by simpa using hx))

/-- **Boundary values of the harmonic correction.** On the unit circle
`‖1 - conj (e x) * e y‖ = ‖e x - e y‖`, so the harmonic correction equals the Newtonian
potential there. -/
theorem integral_planarNewtonianKernel_one_sub_conj_mul_eq {x : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x‖ = 1) :
    ∫ y, planarNewtonianKernel (1 - starRingEnd ℂ (e x) * e y) * f y =
      ∫ y, planarNewtonianKernel (e y - e x) * f y := by
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  have h := planarGreenKernel_eq_zero_of_norm_eq_one (a := e y) (z := e x) (by simpa using hx)
  rw [planarGreenKernel_def, sub_eq_zero] at h
  dsimp only
  rw [planarNewtonianKernel_one_sub_conj_mul_comm, ← h, planarNewtonianKernel_sub_comm]

/-- **The Green potential is the corrected Newtonian potential.** For `f` continuous with
`tsupport f` inside the unit disk and `x` in the closed disk,
`∫ G(x, y) f(y) dy = ∫ Φ(e y - e x) f(y) dy - ∫ Φ(1 - conj (e x) * e y) f(y) dy`. -/
theorem integral_planarGreenKernel_mul_eq_sub (hf : Continuous f)
    (hsupp : tsupport f ⊆ ball 0 1) {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ ≤ 1) :
    ∫ y, planarGreenKernel (e x) (e y) * f y =
      (∫ y, planarNewtonianKernel (e y - e x) * f y) -
        ∫ y, planarNewtonianKernel (1 - starRingEnd ℂ (e x) * e y) * f y := by
  have hc : HasCompactSupport f := HasCompactSupport.of_tsupport_subset_ball hsupp
  have h1 : Integrable fun y => planarNewtonianKernel (e y - e x) * f y := by
    refine (hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (locallyIntegrable_planarNewtonianKernel_comp e) hf x).integrable_swap.congr
      (Eventually.of_forall fun y => ?_)
    simp [planarNewtonianKernel_sub_comm (e x)]
  have h2 : Integrable fun y => planarNewtonianKernel (1 - starRingEnd ℂ (e x) * e y) * f y := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hc.mul_left
    exact (continuousOn_planarNewtonianKernel_one_sub_conj_mul e hf hsupp).comp_continuous
      (continuous_const.prodMk continuous_id) fun _ => ⟨mem_closedBall_zero_iff.2 hx, mem_univ _⟩
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [planarGreenKernel_def, sub_mul]

end Smooth

/-! ### Weak solutions of the Dirichlet problem -/

namespace PDE

open TopologicalSpace

variable {Omega : Opens (EuclideanSpace ℝ (Fin 2))}

/-- **Green's representation formula on the disk for smooth data.** Let `f` be of class `C²` with
`tsupport f` inside the unit disk `B` of `ℝ²`. The weak solution `u ∈ H¹₀(B)` of `-Δu = f` in
`B`, `u = 0` on `∂B`, is the Green potential of `f`: `u(x) = ∫ G(x, y) f(y) dy` for almost every
`x ∈ B`, where `G(x, y) = TauCeti.planarGreenKernel (e x) (e y)`. -/
theorem IsWeakSolutionDirichlet.value_ae_eq_integral_planarGreenKernel_mul
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : tsupport f ⊆ ball 0 1)
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin 2))) = ball 0 1)
    {g : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2))))}
    (hg : g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))] f)
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 g u) :
    W1p.value (u : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))]
        fun x => ∫ y, planarGreenKernel (e x) (e y) * f y := by
  have hc0 : HasCompactSupport f := HasCompactSupport.of_tsupport_subset_ball hsupp
  have hc : HasCompactSupport (f ∘ e.symm) := hc0.comp_homeomorph e.symm.toHomeomorph
  have hf' : ContDiff ℝ 2 (f ∘ e.symm) := hf.comp e.symm.contDiff
  have hV : ContDiff ℝ 2 ((planarNewtonianKernel ⋆ (f ∘ e.symm)) ∘ e) :=
    (contDiff_planarNewtonianKernel_convolution hf' hc).comp e.contDiff
  have hΔV : ∀ x, Δ ((planarNewtonianKernel ⋆ (f ∘ e.symm)) ∘ e) x = -f x := fun x => by
    rw [laplacian_comp_linearIsometryEquiv_right,
      laplacian_planarNewtonianKernel_convolution hf' hc]
    simp
  refine (hu.value_ae_eq_sub_of_laplacian_eq_neg hV.contDiffOn hV.continuous.continuousOn
    (fun x _ => hΔV x)
    (harmonicOnNhd_integral_planarNewtonianKernel_one_sub_conj_mul e hf.continuous hsupp)
    (continuousOn_integral_planarNewtonianKernel_one_sub_conj_mul e hf.continuous hsupp)
    (fun x hx => ?_) hΩ hg).trans ?_
  · rw [integral_planarNewtonianKernel_one_sub_conj_mul_eq e (mem_sphere_zero_iff_norm.1 hx),
      planarNewtonianKernel_convolution_comp_apply]
  · filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    rw [hΩ, mem_ball_zero_iff] at hx
    rw [Pi.sub_apply, planarNewtonianKernel_convolution_comp_apply,
      integral_planarGreenKernel_mul_eq_sub e hf.continuous hsupp hx.le]

/-- **Green's representation formula on the disk.** Let `B` be the unit disk of `ℝ²` and
`G(x, y) = TauCeti.planarGreenKernel (e x) (e y)` its Green kernel. For every `f ∈ L²(B)`, the weak
solution `u ∈ H¹₀(B)` of `-Δu = f` in `B`, `u = 0` on `∂B`, is the Green potential of `f`:

`u(x) = ∫_B G(x, y) f(y) dy` for almost every `x ∈ B`. -/
theorem IsWeakSolutionDirichlet.value_ae_eq_setIntegral_planarGreenKernel_mul
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin 2))) = ball 0 1)
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2))))}
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u) :
    W1p.value (u : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))]
        fun x => ∫ y in ball 0 1, planarGreenKernel (e x) (e y) * f y := by
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isFiniteMeasure_restrict.2 (hΩ ▸ measure_ball_lt_top.ne)
  have hf : IntegrableOn f (ball 0 1) := by
    rw [← hΩ]
    exact (Lp.memLp f).integrable one_le_two
  have hGf := integrable_planarGreenKernel_mul e hf
  rw [← hΩ] at hGf ⊢
  exact hu.value_ae_eq_setIntegral_mul_of_forall_contDiff hΩ.le
    (fun x y => planarGreenKernel_comm (e x) (e y))
    (fun ψ hψ _ hψsupp g hg w hw => hw.value_ae_eq_integral_planarGreenKernel_mul e
      (hψ.of_le (by simp)) (hΩ ▸ hψsupp) hΩ hg) hGf

end PDE

end TauCeti
