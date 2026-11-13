/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Wirtinger
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Area.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.MeasureTheory.Integral.Circle.LIntegral
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

For an arc `γ : [a, b] → V` that is not closed, the action `∫ ω(γ, γ')` is corrected by the
chord term `ω(γ a, γ b)`, which vanishes when both endpoints lie in an isotropic subspace. Every
point of the arc lies within half its length `ℓ` of the midpoint of its endpoints, so the corrected
action is at most `ℓ² / 2 ≤ (b - a) / 2 * ∫ ‖γ'‖²`
(`TauCeti.SymplecticForm.abs_integral_apply_sub_apply_le`). This is the estimate for the boundary
half-circles of a holomorphic half-disc with Lagrangian boundary condition, whose area is the
difference of their actions.

## Main results

* `TauCeti.SymplecticForm.abs_integral_apply_le`: the isoperimetric inequality.
* `TauCeti.SymplecticForm.abs_integral_fderiv_apply_annulus_le`: the area of an annulus is
  bounded by half the sum of the energies of its two boundary loops.
* `TauCeti.SymplecticForm.abs_integral_apply_sub_apply_le`: the isoperimetric inequality for
  arcs.
* `TauCeti.SymplecticForm.abs_integral_fderiv_apply_halfAnnulus_le`: the area of a half-annulus
  whose straight edges map into an isotropic subspace is bounded by `π / 4` times the sum of the
  energies of its two boundary half-circles.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Sections 4.4 and 4.5.
-/

public section

open MeasureTheory Set TauCeti
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

/-- **The isoperimetric inequality for arcs.** If the inner product of `V` is the metric
`ω(·, J ·)`, then for a path `γ` on `[a, b]` with square-integrable derivative, the action
`∫ ω(γ, γ')` differs from `ω(γ a, γ b)` by at most `(b - a) / 2` times the energy `∫ ‖γ'‖²`.
The difference is twice the symplectic area enclosed by `γ` followed by the chord from `γ b` back
to `γ a`. When the endpoints lie in an isotropic subspace the correction `ω(γ a, γ b)` vanishes,
which is the case of arcs on the boundary of a half-disc with Lagrangian boundary condition. -/
theorem abs_integral_apply_sub_apply_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hab : a ≤ b)
    {γ γ' : ℝ → V} (hγ : ∀ x ∈ Icc a b, HasDerivAt γ (γ' x) x)
    (hγ' : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    |(∫ x in a..b, ω (γ x) (γ' x)) - ω (γ a) (γ b)| ≤
      (b - a) / 2 * ∫ x in a..b, ‖γ' x‖ ^ 2 := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let B : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.mkContinuous₂ ω.toBilinForm 1 fun v w => by
    rw [one_mul, Real.norm_eq_abs]
    exact abs_apply_le_norm_mul_norm hg v w
  have hB : ‖B‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  have hγ'i : IntervalIntegrable γ' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (hγ'.integrable one_le_two)
  have hsq : IntervalIntegrable (fun x => ‖γ' x‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      ((memLp_two_iff_integrable_sq_norm hγ'.aestronglyMeasurable).1 hγ')
  -- For the skew form `ω`, the midpoint correction is `ω(γ a, γ b)`.
  have hmid : B (midpoint ℝ (γ a) (γ b)) (γ b - γ a) = ω (γ a) (γ b) := by
    simp [B, midpoint_eq_smul_add, map_sub, ω.self_eq_zero]
    linarith [ω.neg_eq (γ a) (γ b)]
  have h := B.norm_intervalIntegral_apply_apply_sub_apply_midpoint_le hab hγ hγ'i
  rw [hmid, Real.norm_eq_abs] at h
  -- Cauchy–Schwarz bounds the squared length by `(b - a)` times the energy.
  have hℓ := TauCeti.integral_le_sqrt_mul_sqrt_integral_sq hab (g := fun x ↦ ‖γ' x‖) hsq
  have hℓ0 : 0 ≤ ∫ x in a..b, ‖γ' x‖ :=
    intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _
  have hE : 0 ≤ ∫ x in a..b, ‖γ' x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ ↦ by positivity
  have hℓsq : (∫ x in a..b, ‖γ' x‖) ^ 2 ≤ (b - a) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by
    calc (∫ x in a..b, ‖γ' x‖) ^ 2 ≤ (√(b - a) * √(∫ x in a..b, ‖γ' x‖ ^ 2)) ^ 2 := by
          gcongr
      _ = (b - a) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (sub_nonneg.2 hab), Real.sq_sqrt hE]
  calc |(∫ x in a..b, ω (γ x) (γ' x)) - ω (γ a) (γ b)|
      = |(∫ x in a..b, B (γ x) (γ' x)) - ω (γ a) (γ b)| := by simp [B]
    _ ≤ ‖B‖ / 2 * (∫ x in a..b, ‖γ' x‖) ^ 2 := h
    _ ≤ 1 / 2 * ((b - a) * ∫ x in a..b, ‖γ' x‖ ^ 2) := by gcongr
    _ = (b - a) / 2 * ∫ x in a..b, ‖γ' x‖ ^ 2 := by ring

/-- The absolute symplectic area of a `C²` map on an annulus is at most half the sum of the
energies of its boundary loops parametrized on `[-π, π]`. The map need not extend over the
inner disc, and no holomorphicity assumption is imposed. -/
theorem abs_integral_fderiv_apply_annulus_le {u : ℂ → V} (z₀ : ℂ)
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z) :
    |∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I)| ≤
      (1 / 2 : ℝ) * ((∫ θ in -π..π,
        ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) +
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ a θ)) θ‖ ^ 2) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.mkContinuous₂ ω.toBilinForm 1 fun v w ↦ by
    rw [one_mul, Real.norm_eq_abs]
    exact abs_apply_le_norm_mul_norm hg v w
  have hB : ‖B‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  have hloop (r : ℝ) (hr : r ∈ Icc a b) :
      |∫ θ in -π..π, ω (u (circleMap z₀ r θ))
        (deriv (fun θ ↦ u (circleMap z₀ r θ)) θ)| ≤
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2 := by
    have hmem (θ : ℝ) :
        circleMap z₀ r θ ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
      simpa only [mem_ofPred_eq, circleMap_sub_center, norm_circleMap_zero,
        abs_of_nonneg (ha.trans hr.1)] using (mem_Icc.mp hr)
    have hE : 0 ≤ ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ ↦ sq_nonneg _
    have h := norm_integral_apply_apply_circleMap_le u (B := B) z₀ r
      (fun θ ↦ (hu _ (hmem θ)).of_le one_le_two)
    simpa only [B, LinearMap.mkContinuous₂_apply, Real.norm_eq_abs, one_mul] using
      h.trans (mul_le_mul_of_nonneg_right hB hE)
  rw [ω.integral_fderiv_apply_annulus z₀ ha hab hu, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  gcongr
  exact (abs_sub _ _).trans (add_le_add (hloop b ⟨hab, le_rfl⟩)
    (hloop a ⟨le_rfl, hab⟩))

/-- The absolute symplectic area of a `C²` map on a closed upper half-annulus whose two straight
boundary segments `z₀ ± r`, `a ≤ r ≤ b`, map into an isotropic subspace is at most `π / 4` times
the sum of the energies of its two boundary half-circles parametrized on `[0, π]`. This is the
boundary counterpart of `TauCeti.SymplecticForm.abs_integral_fderiv_apply_annulus_le`. -/
theorem abs_integral_fderiv_apply_halfAnnulus_le {L : Submodule ℝ V} (hL : ω.IsIsotropic L)
    {u : ℂ → V} (z₀ : ℂ) (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im}, ContDiffAt ℝ 2 u z)
    (huL : ∀ r ∈ Icc a b, u (z₀ + r) ∈ L ∧ u (z₀ - r) ∈ L) :
    |∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im},
      ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I)| ≤
      π / 4 * ((∫ θ in 0..π, ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) +
        ∫ θ in 0..π, ‖deriv (fun θ ↦ u (circleMap z₀ a θ)) θ‖ ^ 2) := by
  have hπ : (0 : ℝ) ≤ π := Real.pi_pos.le
  -- Each boundary half-circle is an arc with endpoints `u (z₀ + r)` and `u (z₀ - r)` in `L`.
  have harc (r : ℝ) (hr : r ∈ Icc a b) :
      |∫ θ in 0..π, ω (u (circleMap z₀ r θ)) (deriv (fun θ ↦ u (circleMap z₀ r θ)) θ)| ≤
        π / 2 * ∫ θ in 0..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2 := by
    have hcd (θ : ℝ) (hθ : θ ∈ Icc 0 π) : ContDiffAt ℝ 2 (fun θ ↦ u (circleMap z₀ r θ)) θ :=
      (hu _ (circleMap_mem_halfAnnulus z₀ ha hr hθ)).comp θ (contDiff_circleMap z₀ r).contDiffAt
    have hcont : ContinuousOn (deriv fun θ ↦ u (circleMap z₀ r θ)) (Icc 0 π) := fun θ hθ ↦ by
      have h := ((hcd θ hθ).continuousAt_fderiv two_ne_zero).clm_apply
        (continuousAt_const (y := (1 : ℝ)))
      simp only [fderiv_apply_one_eq_deriv] at h
      exact h.continuousWithinAt
    have hLp : MemLp (deriv fun θ ↦ u (circleMap z₀ r θ)) 2 (volume.restrict (Ioc 0 π)) :=
      (memLp_two_iff_integrable_sq_norm ((hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc)).mpr
        ((hcont.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    have h := abs_integral_apply_sub_apply_le hg hπ
      (fun θ hθ ↦ ((hcd θ hθ).differentiableAt two_ne_zero).hasDerivAt) hLp
    have hend : ω (u (circleMap z₀ r 0)) (u (circleMap z₀ r π)) = 0 := by
      rw [circleMap_zero_angle, circleMap_pi]
      exact (ω.isIsotropic_iff.mp hL) _ (huL r hr).1 _ (huL r hr).2
    rwa [hend, sub_zero, sub_zero] at h
  rw [ω.integral_fderiv_apply_halfAnnulus hL z₀ ha hab hu huL, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum := (abs_sub _ _).trans (add_le_add (harc b ⟨hab, le_rfl⟩) (harc a ⟨le_rfl, hab⟩))
  linarith

end SymplecticForm

end TauCeti
