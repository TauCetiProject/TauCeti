/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Cusp
public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.ModularInvariant
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Meromorphic

/-!
# The modular invariant on the compactified level-one quotient

The descended modular invariant extends meromorphically to the compact Riemann surface
obtained by adjoining the unique modular cusp. Its order at that cusp is exactly `-1`:
in the normalized width-one chart it is `q⁻¹` times the analytic cusp function of `q j`,
whose value at zero is `1`. On the coarse quotient the extension agrees with `jQuotient`,
and its local multiplicities agree with those already computed there.

`jCompactified` is complex-valued, using value zero at the pole as a representative of its
meromorphic germ. Meromorphy and order depend only on punctured neighbourhoods, so this
assigned value does not remove the pole. The target surface is the constructed compactified
orbit quotient; no identification with the Riemann sphere is used.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.4–2.5.
* Jean-Pierre Serre, *A Course in Arithmetic*, Chapter VII, §§3–4.
-/

public noncomputable section

open Filter Function MulAction Set Topology UpperHalfPlane
open TauCeti.ModularForm TauCeti.RiemannSurface TauCeti.Subgroup.CuspDatum
open _root_.Subgroup.CompactifiedQuotient
open scoped Manifold MatrixGroups

namespace TauCeti.ModularGroup

/-- The modular invariant on the compactified effective level-one quotient. At its unique pole
the assigned value is zero; its meromorphic germ there is independent of this value. -/
def jCompactified : psl2zToPSL2R.range.CompactifiedQuotient → ℂ
  | .ofQuotient p => jQuotient p
  | .ofCusp _ => 0

@[simp]
theorem jCompactified_ofQuotient (p : orbitRel.Quotient psl2zToPSL2R.range ℍ) :
    jCompactified (ofQuotient p) = jQuotient p := (rfl)

@[simp]
theorem jCompactified_ofCusp (C : psl2zToPSL2R.range.CuspOrbit) :
    jCompactified (ofCusp C) = 0 := (rfl)

/-- The compactified function restricts to the descended modular invariant. -/
@[simp]
theorem jCompactified_comp_ofQuotient : jCompactified ∘ ofQuotient = jQuotient :=
  funext jCompactified_ofQuotient

private theorem cuspFunction_qParam_mul_j_zero :
    cuspFunction 1 (fun τ : ℍ ↦ Periodic.qParam 1 τ * j τ) 0 = 1 := by
  rw [cuspFunction_apply_zero one_pos analyticAt_cuspFunction_qParam_mul_j
    periodic_qParam_mul_j_comp_ofComplex]
  exact tendsto_qParam_mul_j_atImInfty.limUnder_eq

private theorem cuspFunction_j_eventuallyEq :
    cuspFunction 1 j =ᶠ[𝓝[≠] 0]
      fun q ↦ cuspFunction 1 (fun τ : ℍ ↦ Periodic.qParam 1 τ * j τ) q / q := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hqn
  simp only [mem_compl_iff, mem_singleton_iff] at hq
  simp only [UpperHalfPlane.cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply]
  have hpos := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
    (mem_ball_zero_iff.mp hqn) hq
  rw [ofComplex_apply_of_im_pos hpos, Periodic.qParam_right_inv one_ne_zero hq]
  exact (mul_div_cancel_left₀ _ hq).symm

private theorem meromorphicAt_cuspFunction_j : _root_.MeromorphicAt (cuspFunction 1 j) 0 :=
  (analyticAt_cuspFunction_qParam_mul_j.meromorphicAt.div analyticAt_id.meromorphicAt).congr
    cuspFunction_j_eventuallyEq.symm

private theorem meromorphicOrderAt_cuspFunction_j :
    _root_.meromorphicOrderAt (cuspFunction 1 j) 0 = -1 := by
  have hdiv := _root_.meromorphicOrderAt_div
    analyticAt_cuspFunction_qParam_mul_j.meromorphicAt
    (g := id) analyticAt_id.meromorphicAt
  simp only [Pi.div_def, id_eq] at hdiv
  rw [_root_.meromorphicOrderAt_congr cuspFunction_j_eventuallyEq, hdiv]
  have hzero := analyticAt_cuspFunction_qParam_mul_j.analyticOrderAt_eq_zero.mpr
    (by rw [cuspFunction_qParam_mul_j_zero]; exact one_ne_zero)
  rw [analyticAt_cuspFunction_qParam_mul_j.meromorphicOrderAt_eq, hzero]
  simp [meromorphicOrderAt_id]

/-- The extended modular invariant is meromorphic at every point of the constructed compact
level-one surface, including its cusp. -/
theorem meromorphicAt_jCompactified (x : psl2zToPSL2R.range.CompactifiedQuotient) :
    RiemannSurface.MeromorphicAt jCompactified x := by
  cases x with
  | ofQuotient p =>
    rw [meromorphicAt_ofQuotient_iff, jCompactified_comp_ofQuotient]
    exact meromorphicAt_of_eventually_mdifferentiableAt (.of_forall mdifferentiable_jQuotient)
  | ofCusp C =>
    have hC : C = cuspDatumInfty.cuspOrbit := Subsingleton.elim _ _
    rw [hC, meromorphicAt_ofCusp_iff (f := j) cuspDatumInfty (fun z ↦ by simp),
      cuspExtension_cuspDatumInfty]
    exact meromorphicAt_cuspFunction_j

/-- The extended modular invariant has a simple pole at the unique modular cusp. The order is
computed in the normalized identity-scaling, width-one q-coordinate. -/
@[simp]
theorem meromorphicOrderAt_jCompactified_ofCusp (C : psl2zToPSL2R.range.CuspOrbit) :
    RiemannSurface.meromorphicOrderAt jCompactified (ofCusp C) = -1 := by
  have hC : C = cuspDatumInfty.cuspOrbit := Subsingleton.elim _ _
  rw [hC, meromorphicOrderAt_ofCusp (f := j) cuspDatumInfty (fun z ↦ by simp),
    cuspExtension_cuspDatumInfty]
  exact meromorphicOrderAt_cuspFunction_j

/-- At points of the original quotient, compactification preserves the local multiplicity of
the descended modular invariant. -/
@[simp]
theorem localMultiplicity_jCompactified_ofQuotient
    (p : orbitRel.Quotient psl2zToPSL2R.range ℍ) :
    localMultiplicity jCompactified (ofQuotient p) = localMultiplicity jQuotient p := by
  rw [localMultiplicity_def, localMultiplicity_def, chartAt_ofQuotient,
    ofQuotientChart_ofQuotient]
  simp only [ofQuotientChart_symm_apply, jCompactified_ofQuotient]

/-- The unique cusp is the only pole of the modular invariant on the compactified surface. -/
@[simp]
theorem meromorphicOrderAt_jCompactified_nonneg_iff
    (x : psl2zToPSL2R.range.CompactifiedQuotient) :
    0 ≤ RiemannSurface.meromorphicOrderAt jCompactified x ↔ x ≠ ofCusp cuspOrbitInfty := by
  cases x with
  | ofQuotient p =>
    constructor
    · intro _
      simp
    · intro _
      rw [meromorphicOrderAt_ofQuotient, jCompactified_comp_ofQuotient,
        RiemannSurface.meromorphicOrderAt_def]
      have ha : AnalyticAt ℂ (jQuotient ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) := by
        simpa only [mfld_simps, Function.comp_def] using
          TauCeti.analyticAt_chartAt_comp_comp_chartAt_symm
            (x := p) (.of_forall mdifferentiable_jQuotient)
      exact ha.meromorphicOrderAt_nonneg
  | ofCusp C =>
    rw [Subsingleton.elim C cuspOrbitInfty]
    simp only [meromorphicOrderAt_jCompactified_ofCusp, ne_self_iff_false, iff_false, not_le]
    exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)

end TauCeti.ModularGroup
