/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.PuncturedDisc
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Analysis.Calculus.FDeriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.RingTheory.Complex
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Finite-energy planes in a symplectic vector space have zero area

Let `(V, ω)` be a symplectic vector space and let `u : ℂ → V` be a `C²` map of finite energy, in
the sense that `‖du‖²` is integrable over the plane. Then the symplectic area of `u` vanishes:

`∫_ℂ ω(∂ₛu, ∂ₜu) = 0`

(`TauCeti.SymplecticForm.integral_fderiv_apply_eq_zero`). This is Stokes' formula on the sphere
`ℂ ∪ {∞}` for the exact form `ω = dλ`, `λₓ = ½ ω(x, ·)`, but no extension of `u` across `∞` is
assumed, and `u` need not be bounded. The area of the disc of radius `R` is half the action of its
boundary circle (`TauCeti.SymplecticForm.integral_fderiv_apply_closedBall`). In the coordinate
`w = z⁻¹` at infinity the map `w ↦ u w⁻¹` has finite energy on the punctured unit disc, because
the inversion is conformal (`TauCeti.integrableOn_norm_fderiv_comp_inv_sq`), and its circle of
radius `r` is the circle of `u` of radius `r⁻¹` traversed backwards
(`TauCeti.SymplecticForm.integral_apply_deriv_comp_inv_circleMap`). Finite energy near the
puncture gives arbitrarily small circles with arbitrarily small action
(`TauCeti.SymplecticForm.exists_tendsto_integral_apply_circleMap_nhds_zero`). So `u` has
arbitrarily large circles with arbitrarily small action, and the areas of the discs they bound
converge to the total area.

The same holds in the real coordinates `ℝ × ℝ ≃ ℂ` used for Floer equations
(`TauCeti.SymplecticForm.integral_fderiv_stdComplexLine_eq_zero`). For a solution of the
Cauchy–Riemann equation `∂ₜu = J ∂ₛu` with `ω`-tame `J`, which may depend on the domain point and
hence also on the value of `u`, the area density `ω(∂ₛu, J ∂ₛu)` is nonnegative. So a finite-energy
solution on the whole plane has zero area density everywhere and is constant
(`TauCeti.SymplecticForm.exists_eq_const_of_integrable_norm_fderiv_sq`): a symplectic vector space
contains no nonconstant finite-energy pseudoholomorphic planes, and in particular no nonconstant
pseudoholomorphic spheres.

## Main results

* `TauCeti.integrableOn_norm_fderiv_comp_inv_sq`: the energy of `w ↦ u w⁻¹` on the punctured unit
  disc is finite when the energy of `u` outside the unit disc is.
* `TauCeti.SymplecticForm.integral_fderiv_apply_eq_zero`: a `C²` finite-energy map `ℂ → V` has
  zero symplectic area.
* `TauCeti.SymplecticForm.integral_fderiv_stdComplexLine_eq_zero`: the same for maps
  `ℝ × ℝ → V`.
* `TauCeti.SymplecticForm.exists_eq_const_of_integrable_norm_fderiv_sq`: a `C²` finite-energy
  solution of `∂ₜu = J ∂ₛu` for `ω`-tame `J` is constant.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.1
  (energy and area) and Section 4.5 (the end of a finite-energy plane).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Real

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The energy near infinity is the energy near zero of the inverted map.** If `u` is
differentiable outside the open unit disc and `‖du‖²` is integrable there, then the map
`w ↦ u w⁻¹` has integrable `‖d(u ∘ inv)‖²` on the punctured closed unit disc. The real Jacobian
`‖w‖⁻⁴` of the inversion is the square of its conformal factor `‖w‖⁻²`, so the two energies are
equal. -/
theorem integrableOn_norm_fderiv_comp_inv_sq {u : ℂ → V}
    (hu : ∀ z ∈ {z : ℂ | 1 ≤ ‖z‖}, DifferentiableAt ℝ u z)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) {z : ℂ | 1 ≤ ‖z‖}) :
    IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w‖ ^ 2) {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ ≤ 1} := by
  set D : Set ℂ := {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ ≤ 1}
  have hDm : MeasurableSet D :=
    (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isClosed_le continuous_norm continuous_const).measurableSet
  have hDE : MapsTo (·⁻¹) D {z : ℂ | 1 ≤ ‖z‖} := fun w hw ↦ by
    simpa [norm_inv] using one_le_inv₀ hw.1 |>.2 hw.2
  have hw0 {w : ℂ} (hw : w ∈ D) : w ≠ 0 := norm_pos_iff.1 hw.1
  -- The change of variables `z = w⁻¹`, whose real Jacobian is `‖-(w ^ 2)⁻¹‖ ^ 2`.
  set f' : ℂ → ℂ →L[ℝ] ℂ := fun w ↦
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(w ^ 2)⁻¹)).restrictScalars ℝ
  have hdet (w : ℂ) : |(f' w).det| = ‖-(w ^ 2)⁻¹‖ ^ 2 := by
    have : (f' w : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ (-(w ^ 2)⁻¹) := by
      ext h
      simp [f', mul_comm]
    rw [ContinuousLinearMap.det, this, ← Algebra.norm_apply, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  have hchange := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (f' := f') volume hDm
    (fun w hw ↦ ((hasDerivAt_inv (hw0 hw)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    inv_injective.injOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2)).1 (henergy.mono_set hDE.image_subset)
  refine hchange.congr_fun (fun w hw ↦ ?_) hDm
  beta_reduce
  rw [norm_fderiv_comp_inv (hw0 hw) (hu _ (hDE hw)), hdet, smul_eq_mul, norm_neg, norm_inv,
    norm_pow, div_pow, inv_pow, div_eq_mul_inv, mul_comm]

namespace SymplecticForm

variable [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- **Inversion reverses the boundary circles.** The circle of radius `r` of `w ↦ u w⁻¹` is the
circle of radius `r⁻¹` of `u` traversed backwards, so their actions for the primitive
`λₓ = ½ ω(x, ·)` are opposite. -/
theorem integral_apply_deriv_comp_inv_circleMap (ω : SymplecticForm V) (u : ℂ → V) (r : ℝ) :
    ∫ θ in -π..π, ω (u (circleMap 0 r θ)⁻¹) (deriv (fun θ ↦ u (circleMap 0 r θ)⁻¹) θ) =
      -∫ θ in -π..π, ω (u (circleMap 0 r⁻¹ θ)) (deriv (fun θ ↦ u (circleMap 0 r⁻¹ θ)) θ) := by
  simp_rw [circleMap_zero_inv]
  simp only [deriv_comp_neg (fun θ ↦ u (circleMap 0 r⁻¹ θ)), map_neg, intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg (fun θ ↦ ω (u (circleMap 0 r⁻¹ θ))
      (deriv (fun θ ↦ u (circleMap 0 r⁻¹ θ)) θ)), neg_neg]

/-- **A finite-energy plane has zero symplectic area.** For a `C²` map `u : ℂ → V` into a
symplectic vector space with `‖du‖²` integrable over the plane, the integral of the area density
`ω(∂ₛu, ∂ₜu)` over the plane is zero. No boundedness of `u` and no extension across `∞` is
assumed. -/
theorem integral_fderiv_apply_eq_zero (ω : SymplecticForm V) {u : ℂ → V} (hu : ContDiff ℝ 2 u)
    (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2) :
    ∫ z, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) = 0 := by
  let action (r : ℝ) := ∫ θ in -π..π, ω (u (circleMap 0 r θ))
    (deriv (fun θ ↦ u (circleMap 0 r θ)) θ)
  -- The map `w ↦ u w⁻¹` has finite energy on the punctured unit disc.
  have hD (w : ℂ) : (0 < ‖w - 0‖ ∧ ‖w - 0‖ ≤ 1) ↔ (0 < ‖w‖ ∧ ‖w‖ ≤ 1) := by rw [sub_zero]
  have hv : ∀ w ∈ {w : ℂ | 0 < ‖w - 0‖ ∧ ‖w - 0‖ ≤ 1}, ContDiffAt ℝ 1 (fun w ↦ u w⁻¹) w :=
    fun w hw ↦ (hu.contDiffAt.of_le one_le_two).comp w
      (contDiffAt_inv ℝ (norm_pos_iff.1 ((hD w).1 hw).1))
  have henergy' : IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w‖ ^ 2)
      {w : ℂ | 0 < ‖w - 0‖ ∧ ‖w - 0‖ ≤ 1} := by
    simpa only [sub_zero] using integrableOn_norm_fderiv_comp_inv_sq
      (fun z _ ↦ hu.differentiable two_ne_zero z) henergy.integrableOn
  -- So `u` has arbitrarily large circles of arbitrarily small action.
  obtain ⟨r, hr, hr0, hlim⟩ :=
    ω.exists_tendsto_integral_apply_circleMap_nhds_zero 0 one_pos hv henergy'
  have hR : Tendsto (fun n ↦ (r n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.2 ⟨hr0, Eventually.of_forall fun n ↦ (hr n).1⟩)
  have haction : Tendsto (fun n ↦ action (r n)⁻¹) atTop (𝓝 0) := by
    simpa only [integral_apply_deriv_comp_inv_circleMap, neg_neg, neg_zero] using hlim.neg
  -- The areas of the discs these circles bound converge to the total area.
  have harea : Integrable fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z I) :=
    integrableOn_univ.1 (ω.integrableOn_fderiv_apply_of_integrableOn_norm_fderiv_sq
      henergy.integrableOn)
  have hcover : AECover volume atTop fun n ↦ closedBall (0 : ℂ) (r n)⁻¹ :=
    ⟨ae_of_all _ fun z ↦ (hR.eventually_ge_atTop ‖z‖).mono fun _ hn ↦
      mem_closedBall_zero_iff.2 hn, fun _ ↦ measurableSet_closedBall⟩
  have hdisc (n : ℕ) : ∫ z in closedBall (0 : ℂ) (r n)⁻¹, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      (1 / 2 : ℝ) * action (r n)⁻¹ :=
    ω.integral_fderiv_apply_closedBall 0 (inv_pos.2 (hr n).1) fun z _ ↦ hu.contDiffAt
  refine tendsto_nhds_unique (hcover.integral_tendsto_of_countably_generated harea) ?_
  simpa only [hdisc, mul_zero] using haction.const_mul (1 / 2 : ℝ)

omit [FiniteDimensional ℝ V] in
/-- The energy of a map of `ℝ × ℝ` controls the energy of its reading in the complex coordinate
`ℝ × ℝ ≃ ℂ`. -/
private theorem integrable_norm_fderiv_comp_equivRealProdCLM_sq {u : ℝ × ℝ → V}
    (hu : ContDiff ℝ 1 u) (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2) :
    Integrable fun w ↦ ‖fderiv ℝ (u ∘ equivRealProdCLM) w‖ ^ 2 := by
  set e : ℂ →L[ℝ] ℝ × ℝ := (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)
  have hv : ContDiff ℝ 1 (u ∘ equivRealProdCLM) := hu.comp equivRealProdCLM.contDiff
  have hu' : Integrable fun w : ℂ ↦ ‖e‖ ^ 2 * ‖fderiv ℝ u (equivRealProdCLM w)‖ ^ 2 :=
    ((volume_preserving_equiv_real_prod.integrable_comp_emb
      measurableEquivRealProd.measurableEmbedding).2 henergy).const_mul _
  refine hu'.mono' ((hv.continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← mul_pow]
  gcongr
  rw [ContinuousLinearEquiv.comp_right_fderiv, mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- **A finite-energy plane has zero symplectic area, in real coordinates.** For a `C²` map
`u : ℝ × ℝ → V` into a symplectic vector space with `‖du‖²` integrable over the plane, the
integral of `ω(∂ₛu, ∂ₜu)` over the plane is zero. -/
theorem integral_fderiv_stdComplexLine_eq_zero (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    (hu : ContDiff ℝ 2 u) (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2) :
    ∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) = 0 := by
  have h := ω.integral_fderiv_apply_eq_zero (hu.comp equivRealProdCLM.contDiff)
    (integrable_norm_fderiv_comp_equivRealProdCLM_sq (hu.of_le one_le_two) henergy)
  simp only [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I] at h
  -- `measurableEquivRealProd` is `equivRealProdCLM` as a measurable equivalence.
  rwa [← volume_preserving_equiv_real_prod.integral_comp' fun z ↦
    ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)]

/-- **Finite-energy pseudoholomorphic planes in a symplectic vector space are constant.** Let
`u : ℝ × ℝ → V` be a `C²` solution of the Cauchy–Riemann equation `∂ₜu = J(z) ∂ₛu`, where each
`J(z)` is tamed by `ω`. If `‖du‖²` is integrable over the plane, then `u` is constant. The structure
may depend on the domain point, and through `u` on the target point. -/
theorem exists_eq_const_of_integrable_norm_fderiv_sq (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    {J : ℝ × ℝ → AlmostComplexStructure V} (hu : ContDiff ℝ 2 u) (hJ : ∀ z, ω.Tames (J z))
    (hCR : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (fderiv ℝ u z : ℝ × ℝ →ₗ[ℝ] V))
    (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2) :
    ∃ c, u = fun _ ↦ c := by
  set a : ℝ × ℝ → ℝ := fun z ↦ ω (fderiv ℝ u z stdComplexLineReal)
    (fderiv ℝ u z stdComplexLineImag)
  have hnonneg (z : ℝ × ℝ) : 0 ≤ a z :=
    (hCR z).symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg (hJ z)
  have hcont : Continuous a := by
    have hd := hu.continuous_fderiv two_ne_zero
    exact ω.toBilinForm.toContinuousBilinearMap.continuous₂.comp
      ((hd.clm_apply continuous_const).prodMk (hd.clm_apply continuous_const))
  have hint : Integrable a := by
    have h := ω.integrableOn_fderiv_apply_of_integrableOn_norm_fderiv_sq (D := univ)
      (integrable_norm_fderiv_comp_equivRealProdCLM_sq (hu.of_le one_le_two) henergy).integrableOn
    refine (volume_preserving_equiv_real_prod.integrable_comp_emb
      measurableEquivRealProd.measurableEmbedding).1 ?_
    -- `measurableEquivRealProd` is `equivRealProdCLM` as a measurable equivalence.
    exact (by simpa only [integrableOn_univ, fderiv_comp_equivRealProdCLM_one,
      fderiv_comp_equivRealProdCLM_I] using h : Integrable fun w ↦ a (equivRealProdCLM w))
  -- The area density is a nonnegative continuous function with zero integral, so it vanishes.
  have hzero : a = 0 := by
    have hae := (integral_eq_zero_iff_of_nonneg hnonneg hint).1
      (ω.integral_fderiv_stdComplexLine_eq_zero hu henergy)
    exact (hcont.ae_eq_iff_eq volume continuous_const).1 hae
  -- A vanishing area density forces a vanishing derivative.
  have hderiv (z : ℝ × ℝ) : fderiv ℝ u z = 0 := by
    have hreal : fderiv ℝ u z stdComplexLineReal = 0 := by
      by_contra h
      exact (((hCR z).symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_pos (hJ z)
        h).ne' (congrFun hzero z))
    have h0 := ((hCR z).eq_zero_iff_apply_stdComplexLineReal).2 hreal
    exact ContinuousLinearMap.coe_injective h0
  exact ⟨u 0, funext fun z ↦ is_const_of_fderiv_eq_zero (hu.differentiable two_ne_zero) hderiv z 0⟩

end SymplecticForm

end TauCeti
