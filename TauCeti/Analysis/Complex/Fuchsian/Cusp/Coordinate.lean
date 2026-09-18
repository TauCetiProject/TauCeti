/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Datum
public import TauCeti.Analysis.Complex.UpperHalfPlane.CuspCoordinate
public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.Topology.Homeomorph.Quotient

/-!
# The q-coordinate of a normalized cusp datum

For a cusp datum with scaling `σ` and width `w`, the coordinate is
`q(z) = exp (2 * π * I * σ(z) / w)`. Its fibres are exactly the orbits of the full cusp
stabilizer. It therefore identifies the stabilizer quotient of the upper half-plane with the
punctured unit disc. The forward map is the q-coordinate and the inverse is the orbit of a
logarithmic lift transported back by `σ⁻¹`.

This uses the translation quotient computed in
`TauCeti.Analysis.Complex.UpperHalfPlane.CuspCoordinate`. No discreteness assumption is needed
once a normalized cusp datum is given: its primitive-generator condition identifies the full
stabilizer. The coordinate is holomorphic, and scaled horodiscs correspond exactly to smaller
punctured discs. This is a local model for cusp charts; embedding such a neighbourhood into the
full group quotient additionally requires precise invariance of the horodisc.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Filter Function MulAction UpperHalfPlane
open scoped Complex.UnitDisc ContDiff Manifold MatrixGroups Topology

namespace TauCeti.Subgroup.CuspDatum

open TauCeti.UpperHalfPlane

variable {Γ : Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum)

/-- In the scaling coordinate, powers of the primitive cusp generator are integral-width
translations. -/
theorem scaling_smul_generator_zpow (n : ℤ) (z : ℍ) :
    D.scaling • (D.generator ^ n • z) = ((n : ℝ) * D.width) +ᵥ (D.scaling • z) := by
  have h := congrArg (fun g : PSL(2, ℝ) ↦ g • (D.scaling • z))
    (D.scaling_mul_generator_zpow_mul_inv n)
  simpa only [mul_smul, inv_smul_smul, upperRightHom_smul, Subgroup.smul_def,
    Subgroup.coe_zpow] using h

/-- The normalized q-coordinate, valued in the punctured unit disc. -/
def qCoordinate (z : ℍ) : {q : 𝔻 // q ≠ 0} :=
  qParamPuncturedUnitDisc D.width D.width_pos (D.scaling • z)

@[simp]
theorem coe_qCoordinate (z : ℍ) :
    ((qCoordinate D z : 𝔻) : ℂ) = Function.Periodic.qParam D.width (D.scaling • z : ℍ) := by
  rw [qCoordinate, coe_qParamPuncturedUnitDisc]

/-- The q-coordinate has exactly the full cusp-stabilizer orbits as its fibres. -/
theorem orbitRel_iff_qCoordinate_eq (z z' : ℍ) :
    orbitRel (stabilizer Γ D.cusp) ℍ z z' ↔ qCoordinate D z = qCoordinate D z' := by
  rw [qCoordinate, qCoordinate, qParamPuncturedUnitDisc_eq_iff, orbitRel_apply,
    mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨n, hn⟩ := D.mem_stabilizer_iff.mp g.property
    exact ⟨n, by simpa [hn, Subgroup.smul_def] using scaling_smul_generator_zpow D n z'⟩
  · rintro ⟨n, hn⟩
    refine ⟨⟨D.generator ^ n, D.mem_stabilizer_iff.mpr ⟨n, rfl⟩⟩, ?_⟩
    apply (MulAction.injective D.scaling)
    exact (scaling_smul_generator_zpow D n z').trans hn.symm

/-- The q-coordinate is invariant under the full stabilizer, not just the selected generator. -/
@[simp]
theorem qCoordinate_smul (g : stabilizer Γ D.cusp) (z : ℍ) :
    qCoordinate D (g • z) = qCoordinate D z :=
  (orbitRel_iff_qCoordinate_eq D _ _).mp (orbitRel_apply.mpr ⟨g, rfl⟩)

/-- Scaling carries the cusp-stabilizer orbit relation to the integral-width translation
relation. -/
private theorem orbitRel_iff_cuspTranslationOrbitRel (z z' : ℍ) :
    orbitRel (stabilizer Γ D.cusp) ℍ z z' ↔
      AddAction.orbitRel (AddSubgroup.zmultiples D.width) ℍ
        (D.scaling • z) (D.scaling • z') := by
  rw [orbitRel_iff_qCoordinate_eq,
    cuspTranslationOrbitRel_iff_qParam_eq D.width D.width_pos]
  rfl

/-- The q-coordinate identifies the quotient by the full cusp stabilizer with the punctured
unit disc. -/
def quotientHomeomorph :
    orbitRel.Quotient (stabilizer Γ D.cusp) ℍ ≃ₜ {q : 𝔻 // q ≠ 0} :=
  (Homeomorph.Quotient.congr (Homeomorph.smul D.scaling)
    (fun z z' ↦ by
      simpa only [Homeomorph.smul_apply] using orbitRel_iff_cuspTranslationOrbitRel D z z')).trans
    (cuspTranslationQuotientHomeomorph D.width D.width_pos)

@[simp]
theorem quotientHomeomorph_mk (z : ℍ) :
    quotientHomeomorph D (Quotient.mk'' z) = qCoordinate D z := by
  rw [quotientHomeomorph, Homeomorph.trans_apply, Quotient.mk''_eq_mk,
    Homeomorph.Quotient.congr_mk, cuspTranslationQuotientHomeomorph_mk]
  rfl

@[simp]
theorem quotientHomeomorph_symm_apply (q : {q : 𝔻 // q ≠ 0}) :
    (quotientHomeomorph D).symm q =
      Quotient.mk'' (D.scaling⁻¹ • invQParamUpperHalfPlane D.width D.width_pos q) := by
  apply (quotientHomeomorph D).injective
  simp [quotientHomeomorph_mk, qCoordinate]

/-- The normalized q-coordinate is an open quotient map. -/
theorem isOpenQuotientMap_qCoordinate : IsOpenQuotientMap (qCoordinate D) :=
  (isOpenQuotientMap_qParamPuncturedUnitDisc D.width D.width_pos).comp
    (Homeomorph.smul D.scaling).isOpenQuotientMap

/-- The complex-valued q-coordinate is holomorphic on the upper half-plane. -/
theorem mdifferentiable_qCoordinate :
    MDiff (fun z : ℍ ↦ ((qCoordinate D z : 𝔻) : ℂ)) := by
  simp only [coe_qCoordinate]
  exact Function.Periodic.differentiable_qParam.mdifferentiable.comp
    (UpperHalfPlane.mdifferentiable_coe.comp
      ((contMDiff_const_smul (I := 𝓘(ℂ, ℂ)) (n := ∞) D.scaling).mdifferentiable (by simp)))

/-- A scaled horodisc is exactly the inverse image of a punctured disc under the
q-coordinate. -/
theorem norm_qCoordinate_lt_iff (A : ℝ) (z : ℍ) :
    ‖((qCoordinate D z : 𝔻) : ℂ)‖ < Real.exp (-2 * Real.pi * A / D.width) ↔
      A < (D.scaling • z).im := by
  rw [coe_qCoordinate]
  exact Function.Periodic.norm_qParam_lt_iff D.width_pos A (D.scaling • z : ℍ)

/-- The image of a scaled horodisc is the punctured disc of the corresponding exponential
radius. -/
theorem image_qCoordinate_horodisc (A : ℝ) :
    qCoordinate D '' {z : ℍ | A < (D.scaling • z).im} =
      {q : {q : 𝔻 // q ≠ 0} | ‖((q : 𝔻) : ℂ)‖ <
        Real.exp (-2 * Real.pi * A / D.width)} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (norm_qCoordinate_lt_iff D A z).mpr hz
  · intro hq
    obtain ⟨z, rfl⟩ := (isOpenQuotientMap_qCoordinate D).surjective q
    exact ⟨z, (norm_qCoordinate_lt_iff D A z).mp hq, rfl⟩

/-- The q-coordinate tends to zero whenever the height in the scaling coordinate tends to
infinity. The limit is through nonzero values, as required for a punctured cusp chart. -/
theorem tendsto_qCoordinate {α : Type*} {l : Filter α} {f : α → ℍ}
    (h : Tendsto (fun a ↦ (D.scaling • f a).im) l atTop) :
    Tendsto (fun a ↦ ((qCoordinate D (f a) : 𝔻) : ℂ)) l (𝓝[≠] 0) := by
  simp only [coe_qCoordinate]
  exact (Function.Periodic.qParam_tendsto D.width_pos).comp
    (tendsto_comap_iff.mpr h)

end TauCeti.Subgroup.CuspDatum
