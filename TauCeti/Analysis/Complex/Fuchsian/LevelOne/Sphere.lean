/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Extension
public import TauCeti.Analysis.Complex.RiemannSurface.Degree
public import TauCeti.Geometry.Manifold.Instances.OnePoint

/-!
# The modular invariant identifies the level-one surface with the sphere

The normalized modular invariant defines a holomorphic map `jSphere` from the constructed
compactified modular quotient to `OnePoint ℂ`. It sends the unique cusp to infinity and restricts
to `jQuotient` on the coarse quotient. In the cusp q-coordinate, its reciprocal is `q / F(q)`,
where `F` is the analytic cusp function of `q j` and `F(0) = 1`. Thus its only point above infinity
has local multiplicity one. The fibre-counting degree theorem gives degree one, and
`jBiholomorph` is the resulting biholomorphism, normalized by the images of the cusp and the two
elliptic orbits.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.4–2.5.
* Jean-Pierre Serre, *A Course in Arithmetic*, Chapter VII, §§3–4.
* Otto Forster, *Lectures on Riemann Surfaces*, §4, Theorem 4.24.
-/

public noncomputable section

open Filter Function MulAction OnePoint Set Topology UpperHalfPlane
open TauCeti.ModularForm TauCeti.RiemannSurface TauCeti.Subgroup.CuspDatum
open _root_.Subgroup.CompactifiedQuotient
open scoped ContDiff Manifold MatrixGroups

namespace TauCeti.ModularGroup

/-- The normalized modular invariant as a map from the compactified level-one modular quotient
to the Riemann sphere, with its pole assigned the value infinity. -/
def jSphere : psl2zToPSL2R.range.CompactifiedQuotient → OnePoint ℂ
  | .ofQuotient p => (jQuotient p : OnePoint ℂ)
  | .ofCusp _ => (∞ : OnePoint ℂ)

@[simp]
theorem jSphere_ofQuotient (p : orbitRel.Quotient psl2zToPSL2R.range ℍ) :
    jSphere (ofQuotient p) = (jQuotient p : OnePoint ℂ) := (rfl)

@[simp]
theorem jSphere_ofCusp (C : psl2zToPSL2R.range.CuspOrbit) :
    jSphere (ofCusp C) = (∞ : OnePoint ℂ) := (rfl)

/-- The fibre of infinity consists precisely of the modular cusp. -/
@[simp]
theorem jSphere_eq_infty_iff (x : psl2zToPSL2R.range.CompactifiedQuotient) :
    jSphere x = (∞ : OnePoint ℂ) ↔ x = ofCusp cuspOrbitInfty := by
  cases x with
  | ofQuotient p => simp
  | ofCusp C => simp [Subsingleton.elim C cuspOrbitInfty]

private def reciprocalCusp : ℂ → ℂ :=
  fun q ↦ q / cuspFunction 1 (fun τ : ℍ ↦ Periodic.qParam 1 τ * j τ) q

private theorem analyticAt_reciprocalCusp : AnalyticAt ℂ reciprocalCusp 0 :=
  analyticAt_id.div analyticAt_cuspFunction_qParam_mul_j (by simp)

private theorem jSphere_comp_cuspChart_symm_eventuallyEq :
    jSphere ∘ (cuspChart cuspDatumInfty le_rfl).symm =ᶠ[𝓝 0]
      OnePoint.invChart.symm ∘ reciprocalCusp := by
  -- The punctured q-expansion describes the reciprocal; both chart inverses assign infinity
  -- at q = 0, so the identity holds on a full neighbourhood.
  have hj := comp_cuspChart_symm_eventuallyEq cuspDatumInfty le_rfl
    (F := jCompactified) (f := j) (fun z ↦ by simp)
  rw [cuspExtension_cuspDatumInfty] at hj
  have hF := analyticAt_cuspFunction_qParam_mul_j.continuousAt.eventually_ne
    (by simp : cuspFunction 1 (fun τ : ℍ ↦ Periodic.qParam 1 τ * j τ) 0 ≠ 0)
  simp only [Filter.EventuallyEq]
  rw [← nhdsWithin_univ, ← compl_union_self {(0 : ℂ)}, nhdsWithin_union,
    eventually_sup, nhdsWithin_singleton, eventually_pure]
  constructor
  · filter_upwards [hj, cuspFunction_j_eventuallyEq, nhdsWithin_le_nhds hF,
      self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((cuspChart cuspDatumInfty le_rfl).open_target.mem_nhds
        (by simp [cuspChart_target, cuspRadius_pos]))] with q hjq hqj hFq hq hqt
    have hq0 : q ≠ 0 := hq
    have hqR : reciprocalCusp q ≠ 0 := div_ne_zero hq0 hFq
    rw [comp_apply, cuspChart_symm_of_ne_zero cuspDatumInfty le_rfl hqt hq0,
      jSphere_ofQuotient, comp_apply, OnePoint.invChart_symm_of_ne_zero hqR]
    apply congrArg ((↑) : ℂ → OnePoint ℂ)
    have h := hjq.trans hqj
    rw [comp_apply, cuspChart_symm_of_ne_zero cuspDatumInfty le_rfl hqt hq0,
      jCompactified_ofQuotient] at h
    simpa [reciprocalCusp, inv_div] using h
  · simp [comp_apply, cuspChart_symm_zero, reciprocalCusp]

/-- The sphere-valued modular invariant is holomorphic, including at the cusp. -/
theorem mdifferentiable_jSphere : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jSphere := by
  intro x
  cases x with
  | ofQuotient p =>
    apply mdifferentiableAt_comp_ofQuotient_iff.mp
    exact OnePoint.mdifferentiableAt_coe_comp_iff.mpr (mdifferentiable_jQuotient p)
  | ofCusp C =>
    rw [Subsingleton.elim C cuspDatumInfty.cuspOrbit]
    rw [← mdifferentiableWithinAt_univ,
      mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (cuspChart_mem_atlas cuspDatumInfty le_rfl))
        (ofCusp_mem_cuspChart_source cuspDatumInfty le_rfl)]
    simp only [mfld_simps, cuspChart_ofCusp, mdifferentiableWithinAt_univ]
    have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) reciprocalCusp 0 :=
      mdifferentiableAt_iff_differentiableAt.mpr analyticAt_reciprocalCusp.differentiableAt
    -- The inverse sphere chart is holomorphic even at its zero, which represents infinity.
    exact ((mdifferentiableAt_atlas_symm
      (OnePoint.mem_atlas_iff.mpr (Or.inr rfl)) (by simp)).comp 0 hg).congr_of_eventuallyEq
        jSphere_comp_cuspChart_symm_eventuallyEq

/-- The sphere-valued modular invariant has local multiplicity one at the unique cusp. -/
@[simp]
theorem localMultiplicity_jSphere_ofCusp (C : psl2zToPSL2R.range.CuspOrbit) :
    localMultiplicity jSphere (ofCusp C) = 1 := by
  rw [Subsingleton.elim C cuspDatumInfty.cuspOrbit,
    localMultiplicity_eq_analyticOrderNatAt
      (IsManifold.subset_maximalAtlas (cuspChart_mem_atlas cuspDatumInfty le_rfl))
      (IsManifold.subset_maximalAtlas (OnePoint.mem_atlas_iff.mpr (Or.inr rfl)))
      (ofCusp_mem_cuspChart_source cuspDatumInfty le_rfl) (by simp)
      (.of_forall mdifferentiable_jSphere), cuspChart_ofCusp]
  have heq : (fun q ↦ OnePoint.invChart
      (jSphere ((cuspChart cuspDatumInfty le_rfl).symm q)) -
      OnePoint.invChart (jSphere (ofCusp cuspDatumInfty.cuspOrbit))) =ᶠ[𝓝 0]
      reciprocalCusp := by
    filter_upwards [jSphere_comp_cuspChart_symm_eventuallyEq] with q hq
    simp only [comp_apply] at hq
    rw [hq]
    simp
  rw [TauCeti.analyticOrderNatAt_congr heq, analyticOrderNatAt]
  have hinv : AnalyticAt ℂ
      (fun q ↦ (cuspFunction 1 (fun τ : ℍ ↦ Periodic.qParam 1 τ * j τ) q)⁻¹) 0 :=
    analyticAt_cuspFunction_qParam_mul_j.inv (by simp)
  have hord : analyticOrderAt reciprocalCusp 0 = 1 := by
    -- The reciprocal is q times an analytic unit, so the q factor accounts for the whole order.
    unfold reciprocalCusp
    simp only [div_eq_mul_inv]
    exact (analyticOrderAt_mul analyticAt_id hinv).trans (by
      rw [hinv.analyticOrderAt_eq_zero.mpr (by simp)]
      simp)
  simp [hord]

/-- The modular invariant, bundled as a finite holomorphic map of compact Riemann surfaces. -/
def jFiniteHolomorphicMap :
    FiniteHolomorphicMap psl2zToPSL2R.range.CompactifiedQuotient (OnePoint ℂ) :=
  FiniteHolomorphicMap.ofMDifferentiable mdifferentiable_jSphere
    ⟨ofQuotient (Quotient.mk _ I), ofCusp cuspOrbitInfty, by simp⟩

@[simp]
theorem coe_jFiniteHolomorphicMap : ⇑jFiniteHolomorphicMap = jSphere := by
  simp [jFiniteHolomorphicMap]

/-- The normalized modular invariant has degree one on the constructed modular surface. -/
@[simp]
theorem degree_jSphere : degree jSphere = 1 := by
  have hfiber : jFiniteHolomorphicMap ⁻¹' {(∞ : OnePoint ℂ)} =
      {ofCusp cuspOrbitInfty} := by
    ext x
    simp
  have hfinset : (jFiniteHolomorphicMap.finite_fiber (∞ : OnePoint ℂ)).toFinset =
      {ofCusp cuspOrbitInfty} := by
    ext x
    simp only [Set.Finite.mem_toFinset, hfiber, mem_singleton_iff, Finset.mem_singleton]
  rw [← coe_jFiniteHolomorphicMap,
    degree_eq_fiber_sum jFiniteHolomorphicMap (∞ : OnePoint ℂ), hfinset]
  simp

/-- The normalized modular invariant identifies the compactified level-one modular quotient
biholomorphically with the Riemann sphere. -/
def jBiholomorph : psl2zToPSL2R.range.CompactifiedQuotient ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ :=
  biholomorphOfDegreeEqOne jFiniteHolomorphicMap (by simp)

/-- The identifying biholomorphism has the normalized modular invariant as its forward map. -/
@[simp]
theorem coe_jBiholomorph : ⇑jBiholomorph = jSphere := by
  simp [jBiholomorph]

@[simp]
theorem jBiholomorph_ofQuotient (p : orbitRel.Quotient psl2zToPSL2R.range ℍ) :
    jBiholomorph (ofQuotient p) = (jQuotient p : OnePoint ℂ) := by simp

@[simp]
theorem jBiholomorph_ofCusp (C : psl2zToPSL2R.range.CuspOrbit) :
    jBiholomorph (ofCusp C) = (∞ : OnePoint ℂ) := by simp

/-- The elliptic orbit of order three maps to zero. -/
theorem jBiholomorph_ρ :
    jBiholomorph (ofQuotient (Quotient.mk _ ρ)) = ((0 : ℂ) : OnePoint ℂ) := by
  simp [j_ρ]

/-- The elliptic orbit of order two maps to `1728`. -/
theorem jBiholomorph_I :
    jBiholomorph (ofQuotient (Quotient.mk _ I)) = ((1728 : ℂ) : OnePoint ℂ) := by
  simp [j_I]

end TauCeti.ModularGroup
