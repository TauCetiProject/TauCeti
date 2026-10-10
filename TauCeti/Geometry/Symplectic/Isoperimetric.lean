/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Wirtinger
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Area

/-!
# The isoperimetric inequality in a symplectic vector space

Let `V` be a finite-dimensional real inner product space carrying a symplectic form `ω` and an
almost complex structure `J` whose metric `ω(·, J ·)` is the inner product of `V`, as for the
standard triple `(ω₀, J₀, ⟪·, ·⟫)` on `ℝ²ⁿ`. The symplectic area enclosed by a loop
`γ : [a, b] → V` is `a(γ) = ½ ∫ ω(γ, γ')`: it is `∫ γ^*λ` for the primitive
`λ_x(v) = ½ ω(x, v)` of `ω`, hence the symplectic area of any disc bounding `γ`. The
**isoperimetric inequality** bounds it by the energy of the loop,

`|∫ x in a..b, ω (γ x) (γ' x)| ≤ (b - a) / (2π) * ∫ x in a..b, ‖γ' x‖ ^ 2`
(`TauCeti.SymplecticForm.abs_integral_apply_le`),

that is `|a(γ)| ≤ (b - a) / (4π) * ∫ ‖γ'‖²`. For a loop on `[0, 1]` traversed at constant speed
the right side is `ℓ(γ)² / (4π)`, where `ℓ(γ)` is the length; the constant is attained by round
circles in a complex line. This is the estimate behind removal of singularities for holomorphic
curves: the energy of a holomorphic curve `u` on a disc is the symplectic area enclosed by the
boundary loop `θ ↦ u(r e^{iθ})`, so it is bounded by the energy of that loop.

The inequality comes from Wirtinger's inequality
(`ContinuousLinearMap.norm_integral_apply_apply_le`) and the Cauchy--Schwarz bound
`|ω(v, w)| ≤ ‖v‖ ‖w‖` of a compatible triple (`TauCeti.SymplecticForm.abs_apply_le_norm_mul_norm`,
in `CompatibleMetric.lean`).

## Main results

* `TauCeti.SymplecticForm.abs_integral_apply_le`: the isoperimetric inequality.
* `TauCeti.SymplecticForm.abs_integral_fderiv_apply_annulus_le`: the area of an annulus is
  bounded by half the sum of the energies of its two boundary loops.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Sections 4.4 and 4.5.
-/

public section

open MeasureTheory Set
open scoped Real Interval RealInnerProductSpace

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {a b : ℝ}

/-- **The isoperimetric inequality.** If the inner product of `V` is the metric `ω(·, J ·)`, then
for a loop `γ` on `[a, b]` with square-integrable derivative, twice the symplectic area
`∫ ω(γ, γ')` it encloses is bounded by `(b - a) / (2π)` times its energy `∫ ‖γ'‖²`. -/
theorem abs_integral_apply_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hab : a < b) {γ γ' : ℝ → V}
    (hγ : ∀ x ∈ [[a, b]], HasDerivAt γ (γ' x) x) (hγab : γ a = γ b)
    (hγ' : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    |∫ x in a..b, ω (γ x) (γ' x)| ≤ (b - a) / (2 * π) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.mkContinuous₂ ω.toBilinForm 1 fun v w => by
    rw [one_mul, Real.norm_eq_abs]
    exact abs_apply_le_norm_mul_norm hg v w
  have hB : ‖B‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  have hE : 0 ≤ ∫ x in a..b, ‖γ' x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => by positivity
  calc |∫ x in a..b, ω (γ x) (γ' x)| = ‖∫ x in a..b, B (γ x) (γ' x)‖ := by
        simp [B, Real.norm_eq_abs]
    _ ≤ ‖B‖ * ((b - a) / (2 * π)) * ∫ x in a..b, ‖γ' x‖ ^ 2 :=
      B.norm_integral_apply_apply_le hab hγ hγab hγ'
    _ ≤ 1 * ((b - a) / (2 * π)) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by gcongr
    _ = (b - a) / (2 * π) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by rw [one_mul]

/-- The absolute symplectic area of a `C²` map on an annulus is at most half the sum of the
energies of its boundary loops parametrized on `[-π, π]`. The map need not extend over the
inner disc, and no holomorphicity assumption is imposed. -/
theorem abs_integral_fderiv_apply_annulus_le {u : ℂ → V} (z₀ : ℂ)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z) :
    |∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I)| ≤
      (1 / 2 : ℝ) * ((∫ θ in -π..π,
        ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) +
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ a θ)) θ‖ ^ 2) := by
  have hloop (r : ℝ) (hr : r ∈ Icc a b) :
      |∫ θ in -π..π, ω (u (circleMap z₀ r θ))
        (deriv (fun θ ↦ u (circleMap z₀ r θ)) θ)| ≤
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2 := by
    have hmem (θ : ℝ) :
        circleMap z₀ r θ ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
      simpa only [mem_ofPred_eq, circleMap_sub_center, norm_circleMap_zero,
        abs_of_nonneg (ha.le.trans hr.1)] using (mem_Icc.mp hr)
    have hc (θ : ℝ) : ContDiffAt ℝ 2 (fun θ ↦ u (circleMap z₀ r θ)) θ :=
      (hu _ (hmem θ)).comp θ (contDiff_circleMap z₀ r).contDiffAt
    have hd : Continuous (deriv (fun θ ↦ u (circleMap z₀ r θ))) :=
      (contDiff_iff_contDiffAt.mpr hc).continuous_deriv (by norm_num)
    have hLp : MemLp (deriv (fun θ ↦ u (circleMap z₀ r θ))) 2
        (volume.restrict (Ioc (-π) π)) :=
      (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mpr
        (hd.norm.pow 2).integrableOn_Ioc
    have hends : circleMap z₀ r (-π) = circleMap z₀ r π := by
      convert (periodic_circleMap z₀ r (-π)).symm using 1
      congr 1
      ring
    have h := ω.abs_integral_apply_le hg (by linarith [Real.pi_pos])
      (fun θ _ ↦ ((hc θ).differentiableAt (by norm_num)).hasDerivAt)
      (congrArg u hends) hLp
    have hfactor : (π - -π) / (2 * π) = (1 : ℝ) := by
      field_simp
      ring
    simpa only [hfactor, one_mul] using h
  rw [ω.integral_fderiv_apply_annulus z₀ ha hab hu, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  gcongr
  exact (abs_sub _ _).trans (add_le_add (hloop b ⟨hab, le_rfl⟩)
    (hloop a ⟨le_rfl, hab⟩))

end SymplecticForm

end TauCeti
