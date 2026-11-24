/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Topology.MetricSpace.Holder

/-!
# A coefficient with a Hölder cusp

Fix `0 < α ≤ 1` and a coordinate `i` of `ℝᵈ`. This file studies the divergence-form equation

`-div(a ∇u) = 0`, `a(x) = (1 + |xᵢ| ^ α) I`,

whose coefficient `TauCeti.PDE.cuspCoefficient α i` is `α`-Hölder with constant `1`
(`TauCeti.PDE.holderWith_matrixBilinearForm_cuspCoefficient`) and uniformly elliptic on every
slab `|xᵢ| ≤ R` (`TauCeti.PDE.uniformlyEllipticOn_cuspCoefficient`), but no better than
`α`-Hölder across the hyperplane `xᵢ = 0`. The equation depends on `xᵢ` only, and the function

`u(x) = ∫₀^{xᵢ} (1 + |t| ^ α)⁻¹ dt`

solves it: its flux `a ∇u` is the constant unit vector `eᵢ`, which is divergence free. Its
gradient `∇u(x) = (1 + |xᵢ| ^ α)⁻¹ eᵢ` is `α`-Hölder, and no better: it moves by
`t ^ α / (1 + t ^ α)` between `0` and `t eᵢ`. So `u ∈ C^{1,α}` exactly
(`exists_energyFormH1_cuspCoefficient_eq_zero_and_holderWith_and_not_holderOnWith_gradient`
in `TauCeti.PDE`).

This shows that the interior Schauder estimate for divergence-form equations
(`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`
in `TauCeti.PDE`) is sharp in the Hölder exponent of the coefficients: for `α`-Hölder
coefficients with `0 < α < 1` it makes `∇u` `α`-Hölder, and the example shows that no exponent
`β > α` can replace `α` in its conclusion. The example itself holds for every `0 < α ≤ 1`, and
works in every dimension, including `d = 1`, where it is the equation
`-((1 + |x| ^ α) u')' = 0` on an interval.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.32 (the interior `C^{1,α}` estimate in divergence form).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates for equations in
  divergence form with Hölder continuous coefficients).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open InnerProductSpace MeasureTheory Metric Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal Distributions Gradient RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ≥0}

/-! ### The coefficient -/

/-- The coefficient field `(1 + |xᵢ| ^ α) I` on `ℝᵈ`: uniformly elliptic on bounded sets and,
for `α ≤ 1`, `α`-Hölder, with a cusp along the hyperplane `xᵢ = 0`. -/
def cuspCoefficient (α : ℝ≥0) (i : ι) (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  (1 + |x i| ^ (α : ℝ)) • 1

omit [Fintype ι] in
/-- Unfolding `TauCeti.PDE.cuspCoefficient`. -/
theorem cuspCoefficient_apply (α : ℝ≥0) (i : ι) (x : EuclideanSpace ℝ ι) :
    cuspCoefficient α i x = (1 + |x i| ^ (α : ℝ)) • 1 :=
  (rfl)

omit [DecidableEq ι] in
/-- For `α ≤ 1` the cusp `x ↦ |xᵢ| ^ α` is `α`-Hölder with constant `1`. -/
private theorem abs_sub_le_dist_rpow (hα : α ≤ 1) (i : ι) (x y : EuclideanSpace ℝ ι) :
    |(|x i| ^ (α : ℝ)) - |y i| ^ (α : ℝ)| ≤ dist x y ^ (α : ℝ) := by
  have h := ((holderWith_norm_rpow (E := ℝ) hα).comp_lipschitzWith_one
    (LipschitzWith.of_dist_le_mul fun x y : EuclideanSpace ℝ ι ↦ by
      simpa only [NNReal.coe_one, one_mul] using PiLp.dist_apply_le x y i)).dist_le x y
  simpa only [Function.comp_apply, Real.norm_eq_abs, Real.dist_eq, NNReal.coe_one,
    one_mul] using h

/-- The cusp coefficient is uniformly elliptic with constants `1` and `1 + R ^ α` on the slab
`|xᵢ| ≤ R`, in particular on the ball of radius `R` about the origin. -/
theorem uniformlyEllipticOn_cuspCoefficient (α : ℝ≥0) (i : ι) {R : ℝ} (hR : 0 ≤ R) :
    UniformlyEllipticOn {x : EuclideanSpace ℝ ι | |x i| ≤ R} (cuspCoefficient α i) 1
      (1 + R ^ (α : ℝ)) :=
  uniformlyEllipticOn_smul_one _ (fun x : EuclideanSpace ℝ ι ↦ 1 + |x i| ^ (α : ℝ)) one_pos
    (le_add_of_nonneg_right (by positivity)) fun x hx ↦
      ⟨le_add_of_nonneg_right (by positivity), by
        have hx : |x i| ≤ R := hx
        gcongr⟩

/-- For `α ≤ 1` the cusp coefficient is `α`-Hölder with constant `1`, measured in the operator
norm of the attached bilinear forms, as in the divergence-form Schauder estimate. -/
theorem holderWith_matrixBilinearForm_cuspCoefficient (hα : α ≤ 1) (i : ι) :
    HolderWith 1 α fun x : EuclideanSpace ℝ ι ↦ matrixBilinearForm (cuspCoefficient α i x) := by
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  -- The two coefficients differ by the scalar `|xᵢ| ^ α - |yᵢ| ^ α`.
  have hdiff : matrixBilinearForm (cuspCoefficient α i x) -
      matrixBilinearForm (cuspCoefficient α i y) =
      matrixBilinearForm ((|x i| ^ (α : ℝ) - |y i| ^ (α : ℝ)) • 1) := by
    rw [← matrixBilinearForm_sub, cuspCoefficient_apply, cuspCoefficient_apply, ← sub_smul,
      add_sub_add_left_eq_sub]
  rw [dist_eq_norm, NNReal.coe_one, one_mul, hdiff]
  exact (ContinuousLinearMap.opNorm_le_bound₂ _ (abs_nonneg _) fun η ξ ↦
    norm_matrixBilinearForm_smul_one_le_of_abs_le le_rfl η ξ).trans (abs_sub_le_dist_rpow hα i x y)

/-! ### The solution -/

/-- The slope `(1 + |t| ^ α)⁻¹` of the solution along `eᵢ`. -/
private def cuspSlope (α : ℝ≥0) (t : ℝ) : ℝ :=
  (1 + |t| ^ (α : ℝ))⁻¹

private theorem one_add_abs_rpow_pos (t : ℝ) : 0 < 1 + |t| ^ (α : ℝ) := by
  positivity

private theorem continuous_cuspSlope (α : ℝ≥0) : Continuous (cuspSlope α) :=
  (continuous_const.add ((Real.continuous_rpow_const α.coe_nonneg).comp continuous_abs)).inv₀
    fun t ↦ (one_add_abs_rpow_pos t).ne'

/-- The solution `u(x) = ∫₀^{xᵢ} (1 + |t| ^ α)⁻¹ dt`. -/
private def cuspSolution (α : ℝ≥0) (i : ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫ t in 0..x i, cuspSlope α t

/-- The gradient `(1 + |xᵢ| ^ α)⁻¹ eᵢ` of the solution. -/
private def cuspGradient (α : ℝ≥0) (i : ι) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  cuspSlope α (x i) • EuclideanSpace.single i 1

omit [Fintype ι] in
private theorem continuous_cuspGradient [Finite ι] (α : ℝ≥0) (i : ι) :
    Continuous (cuspGradient α i) :=
  have := Fintype.ofFinite ι
  ((continuous_cuspSlope α).comp (EuclideanSpace.proj i).continuous).smul continuous_const

private theorem hasGradientAt_cuspSolution (i : ι) (x : EuclideanSpace ℝ ι) :
    HasGradientAt (cuspSolution α i) (cuspGradient α i x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((continuous_cuspSlope α).integral_hasStrictDerivAt 0 (x i)).hasDerivAt.comp_hasFDerivAt
    x (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).hasFDerivAt
  convert h using 1
  · -- `cuspSolution α i` is the primitive of the slope composed with the coordinate `xᵢ`.
    funext y
    simp [cuspSolution, EuclideanSpace.coe_proj]
  · ext v
    simp [cuspGradient, EuclideanSpace.inner_single_left]

/-- On a bounded open set the solution lies in `H¹(Ω)`, with gradient `(1 + |xᵢ| ^ α)⁻¹ eᵢ`. -/
private theorem exists_w1p_cuspSolution (i : ι) {Ω : Opens (EuclideanSpace ℝ ι)}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) :
    ∃ u : W1p volume Ω 2, W1p.value u =ᵐ[volume.restrict Ω] cuspSolution α i ∧
      W1p.gradient u =ᵐ[volume.restrict Ω] cuspGradient α i := by
  have hC1 : ContDiff ℝ 1 (cuspSolution α i) := contDiff_one_iff_hasFDerivAt.2
    ⟨_, (toDual ℝ (EuclideanSpace ℝ ι)).continuous.comp (continuous_cuspGradient α i),
      fun x ↦ (hasGradientAt_cuspSolution i x).hasFDerivAt⟩
  rw [← gradient_eq (hasGradientAt_cuspSolution i)]
  exact W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact isOpen_univ hC1.contDiffOn
    hb.isCompact_closure subset_closure (subset_univ _)

/-- **The weak equation.** The flux `a ∇u` of the solution is the constant vector `eᵢ`, so every
element of `H¹(Ω)` with the gradient of the solution is a weak solution of `-div(a ∇u) = 0`. -/
private theorem energyFormH1_cuspCoefficient_eq_zero (i : ι) {Ω : Opens (EuclideanSpace ℝ ι)}
    {u : W1p volume Ω 2} (hu : W1p.gradient u =ᵐ[volume.restrict Ω] cuspGradient α i)
    (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 (cuspCoefficient α i) 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) = 0 := by
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  have hflux : ∫ x in Ω, matrixBilinearForm (cuspCoefficient α i x)
      (W1p.gradient (W1p.ofTestFunctionₗ volume Ω 2 φ) x) (W1p.gradient u x) =
      ∫ x in Ω, ⟪e, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ, hu] with x hx hx'
    rw [W1p.gradient_ofTestFunctionₗ, hx, hx', cuspCoefficient_apply,
      matrixBilinearForm_smul_one_apply, cuspGradient, cuspSlope]
    simp only [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul,
      mul_inv_cancel_left₀ (one_add_abs_rpow_pos (α := α) (x i)).ne']
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  -- `⟪eᵢ, ∇φ⟫` is the directional derivative `∂ᵢφ`, whose integral vanishes.
  have hpt : ∀ x, ⟪e, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫ = lineDeriv ℝ (φ : _ → ℝ) x e :=
    fun x ↦ by
      rw [(φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv, ← toDual_gradient,
        toDual_apply_apply, real_inner_comm]
  rw [energyFormH1_zero_zero_eq_setIntegral, hflux,
    φ.setIntegral_inner_gradient_eq_integral_inner_gradient _ φ.tsupport_subset]
  simpa only [hpt] using TestFunction.integral_lineDeriv_eq_zero (μ := volume) φ e

/-! ### The gradient is `α`-Hölder and no better -/

/-- The gradient moves only along the unit vector `eᵢ`, by the change of the slope. -/
private theorem dist_cuspGradient (i : ι) (x y : EuclideanSpace ℝ ι) :
    dist (cuspGradient α i x) (cuspGradient α i y) = |cuspSlope α (x i) - cuspSlope α (y i)| := by
  rw [dist_eq_norm, cuspGradient, cuspGradient, ← sub_smul, norm_smul, PiLp.norm_single, norm_one,
    mul_one, Real.norm_eq_abs]

/-- For `α ≤ 1` the gradient of the solution is `α`-Hölder with constant `1`. -/
private theorem holderWith_cuspGradient (hα : α ≤ 1) (i : ι) :
    HolderWith 1 α (cuspGradient α i) := by
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  have hx := one_add_abs_rpow_pos (α := α) (x i)
  have hy := one_add_abs_rpow_pos (α := α) (y i)
  have hsub : cuspSlope α (x i) - cuspSlope α (y i) =
      (|y i| ^ (α : ℝ) - |x i| ^ (α : ℝ)) / ((1 + |x i| ^ (α : ℝ)) * (1 + |y i| ^ (α : ℝ))) := by
    unfold cuspSlope
    field_simp
    ring
  rw [dist_cuspGradient, NNReal.coe_one, one_mul, hsub, abs_div, abs_of_pos (mul_pos hx hy),
    abs_sub_comm]
  refine (div_le_self (abs_nonneg _) ?_).trans (abs_sub_le_dist_rpow hα i x y)
  exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity))
    (le_add_of_nonneg_right (by positivity))

/-- For `α < β` the gradient of the solution is not `β`-Hölder on any ball about the origin: it
moves by `t ^ α / (1 + t ^ α) ≥ t ^ α / 2` between `0` and `t eᵢ`, `0 < t < 1`. -/
private theorem not_holderOnWith_cuspGradient (hα : 0 < α) {β : ℝ≥0} (hαβ : α < β) (i : ι)
    {r : ℝ} (hr : 0 < r) (C : ℝ≥0) :
    ¬ HolderOnWith C β (cuspGradient α i) (ball 0 r) := by
  intro h
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  set ε : ℝ := β - α with hε
  have hε0 : 0 < ε := by rw [hε]; exact sub_pos.2 (NNReal.coe_lt_coe.2 hαβ)
  -- `2 C t ^ ε → 0` as `t → 0⁺`, so for small `t > 0` it is below `1`.
  have hlim : Tendsto (fun t : ℝ ↦ 2 * (C : ℝ) * t ^ ε) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 ε (Or.inr hε0.le)).tendsto).const_mul (2 * (C : ℝ))
    rw [Real.zero_rpow hε0.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, htr⟩ := ((hlim.eventually (gt_mem_nhds one_pos)).and
    (Ioo_mem_nhdsGT (lt_min hr one_pos))).exists
  have ht0 : 0 < t := htr.1
  have ht1 : t < 1 := htr.2.trans_le (min_le_right _ _)
  have hnorm : ‖t • e‖ = t := by
    rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_of_nonneg ht0.le]
  have hmem : t • e ∈ ball (0 : EuclideanSpace ℝ ι) r := by
    rw [mem_ball_zero_iff, hnorm]
    exact htr.2.trans_le (min_le_left _ _)
  have hdist := h.dist_le hmem (mem_ball_self hr)
  -- The two values of the gradient.
  have hα' : (α : ℝ) ≠ 0 := (NNReal.coe_pos.2 hα).ne'
  have hte : (t • e) i = t := by simp [e]
  have hval : dist (cuspGradient α i (t • e)) (cuspGradient α i 0) =
      t ^ (α : ℝ) / (1 + t ^ (α : ℝ)) := by
    have hsub : 1 - (1 + t ^ (α : ℝ))⁻¹ = t ^ (α : ℝ) / (1 + t ^ (α : ℝ)) := by
      field_simp
      ring
    rw [dist_cuspGradient, hte]
    simp only [cuspSlope, PiLp.zero_apply, abs_zero, Real.zero_rpow hα', add_zero, inv_one,
      abs_of_pos ht0]
    rw [abs_sub_comm, hsub, abs_of_nonneg (by positivity)]
  rw [hval, dist_zero_right, hnorm, show (β : ℝ) = ε + α by rw [hε]; ring,
    Real.rpow_add ht0] at hdist
  have hpow : 0 < t ^ (α : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hpow1 : t ^ (α : ℝ) ≤ 1 := Real.rpow_le_one ht0.le ht1.le α.coe_nonneg
  -- `t ^ α / 2 ≤ t ^ α / (1 + t ^ α) ≤ C t ^ ε t ^ α` forces `1 ≤ 2 C t ^ ε`.
  have hhalf : t ^ (α : ℝ) / 2 ≤ t ^ (α : ℝ) / (1 + t ^ (α : ℝ)) :=
    div_le_div_of_nonneg_left hpow.le (by positivity) (by linarith)
  have hkey : t ^ (α : ℝ) * 1 ≤ t ^ (α : ℝ) * (2 * (C : ℝ) * t ^ ε) := by
    nlinarith
  linarith [le_of_mul_le_mul_left hkey hpow]

/-- **The coefficient exponent of the divergence-form Schauder estimate is sharp.** Let
`0 < α ≤ 1`, let `α < β`, let `i` be a coordinate of `ℝᵈ`, and let `Ω ⊆ ℝᵈ` be a bounded open set.
For the coefficient `a(x) = (1 + |xᵢ| ^ α) I` (`TauCeti.PDE.cuspCoefficient α i`), which is
`α`-Hölder (`TauCeti.PDE.holderWith_matrixBilinearForm_cuspCoefficient`) and uniformly elliptic on
bounded sets (`TauCeti.PDE.uniformlyEllipticOn_cuspCoefficient`), the function
`u(x) = ∫₀^{xᵢ} (1 + |t| ^ α)⁻¹ dt` lies in `H¹(Ω)` and is a weak solution of `-div(a ∇u) = 0`,
that is `∫_Ω ⟨a ∇u, ∇φ⟩ = 0` for every test function `φ`. Its gradient has an `α`-Hölder
representative with constant `1`, but no representative of it is `β`-Hölder on any ball about the
origin contained in `Ω`.

So the interior Schauder estimate
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`,
which makes `∇u` `α`-Hölder for `α`-Hölder coefficients when `0 < α < 1`, cannot conclude any
exponent larger than the Hölder exponent of the coefficients. -/
theorem exists_energyFormH1_cuspCoefficient_eq_zero_and_holderWith_and_not_holderOnWith_gradient
    (hα : 0 < α) (hα1 : α ≤ 1) {β : ℝ≥0} (hαβ : α < β) (i : ι)
    {Ω : Opens (EuclideanSpace ℝ ι)} (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) :
    ∃ u : W1p volume Ω 2,
      W1p.value u =ᵐ[volume.restrict Ω] (fun x ↦ ∫ t in 0..x i, (1 + |t| ^ (α : ℝ))⁻¹) ∧
      (∀ φ : 𝓓(Ω, ℝ),
        energyFormH1 (cuspCoefficient α i) 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) = 0) ∧
      (∃ g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
        g =ᵐ[volume.restrict Ω] W1p.gradient u ∧ HolderWith 1 α g) ∧
      ∀ r : ℝ, 0 < r → ball (0 : EuclideanSpace ℝ ι) r ⊆ (Ω : Set (EuclideanSpace ℝ ι)) →
        ∀ (C : ℝ≥0) (g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι),
          g =ᵐ[volume.restrict (ball 0 r)] W1p.gradient u → ¬ HolderOnWith C β g (ball 0 r) := by
  obtain ⟨u, hvu, hgu⟩ := exists_w1p_cuspSolution (α := α) i hb
  refine ⟨u, hvu, energyFormH1_cuspCoefficient_eq_zero i hgu,
    ⟨cuspGradient α i, hgu.symm, holderWith_cuspGradient hα1 i⟩, ?_⟩
  intro r hr hball C g hg hH
  -- On the ball, `g` agrees almost everywhere with the continuous gradient, hence everywhere.
  have hae : g =ᵐ[volume.restrict (ball 0 r)] cuspGradient α i :=
    hg.trans (ae_restrict_of_ae_restrict_of_subset hball hgu)
  have heq : EqOn g (cuspGradient α i) (ball 0 r) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_ball (hH.continuousOn (hα.trans hαβ))
      (continuous_cuspGradient α i).continuousOn
  exact not_holderOnWith_cuspGradient hα hαβ i hr C fun x hx y hy ↦ by
    rw [← heq hx, ← heq hy]
    exact hH x hx y hy

end PDE

end TauCeti
