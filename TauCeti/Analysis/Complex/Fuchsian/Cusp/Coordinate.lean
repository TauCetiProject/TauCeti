/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Datum
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import Mathlib.Analysis.Complex.Periodic
public import TauCeti.Analysis.Complex.UpperHalfPlane.CuspCoordinate
-- Supplies the continuous PSL action required by `Homeomorph.smul`.
public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
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
stabilizer. The coordinate is holomorphic, and scaled horodiscs of positive height correspond
exactly to smaller punctured discs. This is a local model for cusp charts; embedding such a
neighbourhood into the full group quotient additionally requires precise invariance of the horodisc.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Filter Function Matrix.ProjectiveSpecialLinearGroup MulAction UpperHalfPlane
open scoped Complex.UnitDisc ContDiff Manifold MatrixGroups Topology

namespace TauCeti.Subgroup.CuspDatum

open TauCeti.UpperHalfPlane

variable {Γ : Subgroup PSL(2, ℝ)}

/-- The exponential coordinate of a normalized cusp datum on the upper half-plane. -/
noncomputable def coordinate (D : Γ.CuspDatum) (z : ℍ) : ℂ :=
  Function.Periodic.qParam D.width (↑(D.scaling • z) : ℂ)

/-- The cusp coordinate is the q-parameter of the scaled point, with the datum's width. -/
theorem coordinate_apply (D : Γ.CuspDatum) (z : ℍ) :
    coordinate D z = Function.Periodic.qParam D.width (↑(D.scaling • z) : ℂ) := (rfl)

/-- Applying the inverse scaling before the cusp coordinate recovers the ordinary q-parameter. -/
theorem coordinate_inv_smul (D : Γ.CuspDatum) (z : ℍ) :
    coordinate D (D.scaling⁻¹ • z) = Function.Periodic.qParam D.width z := by
  rw [coordinate_apply, smul_inv_smul]

/-- The exponential cusp coordinate never vanishes on the upper half-plane. -/
@[simp]
theorem coordinate_ne_zero (D : Γ.CuspDatum) (z : ℍ) : coordinate D z ≠ 0 := by
  rw [coordinate_apply]
  exact Function.Periodic.qParam_ne_zero _

/-- The exponential cusp coordinate lies in the open unit disc. -/
theorem norm_coordinate_lt_one (D : Γ.CuspDatum) (z : ℍ) : ‖coordinate D z‖ < 1 := by
  rw [coordinate_apply]
  exact Function.Periodic.norm_qParam_lt_one D.width_pos (D.scaling • z).im_pos

/-- In scaling coordinates, the selected generator acts by translation through the width. -/
theorem coe_scaling_smul_generator (D : Γ.CuspDatum) (z : ℍ) :
    (↑(D.scaling • (D.generator : PSL(2, ℝ)) • z) : ℂ) =
      (↑(D.scaling • z) : ℂ) + D.width := by
  have heq : D.scaling • (D.generator : PSL(2, ℝ)) • z =
      upperRightHom D.width • (D.scaling • z) := by
    rw [← D.scaling_mul_generator_mul_inv, mul_smul, mul_smul, inv_smul_smul]
  rw [heq, upperRightHom_apply, UpperHalfPlane.pslMk_smul, coe_specialLinearGroup_apply]
  simp [Matrix.SpecialLinearGroup.transvection_coe]

/-- The exponential cusp coordinate is invariant under the full cusp stabilizer. -/
@[simp]
theorem coordinate_smul (D : Γ.CuspDatum) {g : Γ}
    (hg : g ∈ MulAction.stabilizer Γ D.cusp) (z : ℍ) :
    coordinate D (g • z) = coordinate D z := by
  obtain ⟨n, hn⟩ := D.mem_stabilizer_iff_conj.mp hg
  have heq : D.scaling • (g • z) = upperRightHom (n * D.width) • (D.scaling • z) := by
    rw [← hn, mul_smul, mul_smul, inv_smul_smul, Subgroup.smul_def]
  have hcoe : (↑(D.scaling • (g • z)) : ℂ) =
      (↑(D.scaling • z) : ℂ) + (n : ℝ) * D.width := by
    rw [heq, upperRightHom_apply, UpperHalfPlane.pslMk_smul, coe_specialLinearGroup_apply]
    simp [Matrix.SpecialLinearGroup.transvection_coe]
  rw [coordinate_apply, coordinate_apply, hcoe]
  simp only [Function.Periodic.qParam]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨n, ?_⟩
  push_cast
  field_simp [D.width_pos.ne']

variable (D : Γ.CuspDatum)

/-- In the scaling coordinate, powers of the primitive cusp generator are integral-width
translations. -/
theorem scaling_smul_generator_zpow (n : ℤ) (z : ℍ) :
    D.scaling • (D.generator ^ n • z) = ((n : ℝ) * D.width) +ᵥ (D.scaling • z) := by
  simpa only [Subgroup.smul_def, Subgroup.coe_zpow] using
    smul_zpow_smul D.scaling_mul_generator_mul_inv n z

/-- The exponential `coordinate`, regarded as a map into the punctured unit disc. -/
def qCoordinate (z : ℍ) : {q : 𝔻 // q ≠ 0} :=
  ⟨Complex.UnitDisc.mk (coordinate D z) (norm_coordinate_lt_one D z), by
    intro h
    exact coordinate_ne_zero D z (congrArg (fun q : 𝔻 ↦ (q : ℂ)) h)⟩

/-- Evaluation of the normalized q-coordinate as the width parameter after scaling. -/
theorem qCoordinate_eq (z : ℍ) :
    qCoordinate D z = qParamPuncturedUnitDisc D.width D.width_pos (D.scaling • z) := by
  apply Subtype.ext
  apply Complex.UnitDisc.coe_injective
  exact (coe_qParamPuncturedUnitDisc D.width D.width_pos (D.scaling • z)).symm

/-- The normalized q-coordinate is the width parameter composed with scaling. -/
theorem qCoordinate_eq_comp :
    qCoordinate D = qParamPuncturedUnitDisc D.width D.width_pos ∘ (D.scaling • ·) :=
  funext (qCoordinate_eq D)

@[simp]
theorem coe_qCoordinate (z : ℍ) :
    ((qCoordinate D z : 𝔻) : ℂ) = coordinate D z :=
  (rfl)

/-- The q-coordinate has exactly the full cusp-stabilizer orbits as its fibres. -/
theorem orbitRel_iff_qCoordinate_eq (z z' : ℍ) :
    orbitRel (stabilizer Γ D.cusp) ℍ z z' ↔ qCoordinate D z = qCoordinate D z' := by
  rw [qCoordinate_eq, qCoordinate_eq, qParamPuncturedUnitDisc_eq_iff, orbitRel_apply,
    mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨n, hn⟩ := D.mem_stabilizer_iff.mp g.property
    exact ⟨n, by simpa [hn, Subgroup.smul_def] using scaling_smul_generator_zpow D n z'⟩
  · rintro ⟨n, hn⟩
    refine ⟨⟨D.generator ^ n, D.mem_stabilizer_iff.mpr ⟨n, rfl⟩⟩, ?_⟩
    apply (MulAction.injective D.scaling)
    exact (scaling_smul_generator_zpow D n z').trans hn.symm

/-- Two points have the same q-coordinate exactly when they differ by an integer power of
the selected generator. -/
theorem qCoordinate_eq_iff (z z' : ℍ) :
    qCoordinate D z = qCoordinate D z' ↔ ∃ n : ℤ, z = (D.generator ^ n : Γ) • z' := by
  rw [← orbitRel_iff_qCoordinate_eq, orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨n, hn⟩ := D.mem_stabilizer_iff.mp g.property
    exact ⟨n, by simp only [Subgroup.smul_def, ← hn]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨D.generator ^ n, D.mem_stabilizer_iff.mpr ⟨n, rfl⟩⟩, rfl⟩

/-- The q-coordinate is invariant under the full stabilizer, not just the selected generator. -/
@[simp]
theorem qCoordinate_smul (g : stabilizer Γ D.cusp) (z : ℍ) :
    qCoordinate D (g • z) = qCoordinate D z :=
  (orbitRel_iff_qCoordinate_eq D _ _).mp (orbitRel_apply.mpr ⟨g, rfl⟩)

/-- The q-coordinate is invariant under any group element fixing the cusp. -/
@[simp]
theorem qCoordinate_smul_of_mem {g : Γ} (hg : g ∈ stabilizer Γ D.cusp) (z : ℍ) :
    qCoordinate D (g • z) = qCoordinate D z :=
  qCoordinate_smul D ⟨g, hg⟩ z

/-- The scaled logarithmic lift is a right inverse of the q-coordinate. -/
@[simp]
theorem qCoordinate_smul_invQParamUpperHalfPlane (q : {q : 𝔻 // q ≠ 0}) :
    qCoordinate D (D.scaling⁻¹ • invQParamUpperHalfPlane D.width D.width_pos q) = q := by
  simp [qCoordinate_eq]

/-- Scaling carries the cusp-stabilizer orbit relation to the integral-width translation
relation. -/
private theorem orbitRel_iff_cuspTranslationOrbitRel (z z' : ℍ) :
    orbitRel (stabilizer Γ D.cusp) ℍ z z' ↔
      AddAction.orbitRel (AddSubgroup.zmultiples D.width) ℍ
        (D.scaling • z) (D.scaling • z') := by
  rw [orbitRel_iff_qCoordinate_eq,
    cuspTranslationOrbitRel_iff_qParam_eq D.width D.width_pos]
  simp only [qCoordinate_eq]

/-- The q-coordinate identifies the quotient by the full cusp stabilizer with the punctured
unit disc. -/
def quotientHomeomorph :
    orbitRel.Quotient (stabilizer Γ D.cusp) ℍ ≃ₜ {q : 𝔻 // q ≠ 0} :=
  (Homeomorph.Quotient.congr (Homeomorph.smul D.scaling)
    (fun z z' ↦ by
      simpa only [Homeomorph.smul_apply] using orbitRel_iff_cuspTranslationOrbitRel D z z')).trans
    (cuspTranslationQuotientHomeomorph D.width D.width_pos)

/-- The quotient homeomorphism sends the orbit of a point to its q-coordinate. -/
@[simp]
theorem quotientHomeomorph_mk (z : ℍ) :
    quotientHomeomorph D (Quotient.mk'' z) = qCoordinate D z := by
  rw [quotientHomeomorph, Homeomorph.trans_apply, Quotient.mk''_eq_mk,
    Homeomorph.Quotient.congr_mk, cuspTranslationQuotientHomeomorph_mk]
  simp only [Homeomorph.smul_apply, qCoordinate_eq]

/-- The inverse quotient homeomorphism sends a punctured-disc point to the orbit of its
width-dependent logarithmic lift transported back by the inverse scaling. -/
@[simp]
theorem quotientHomeomorph_symm_apply (q : {q : 𝔻 // q ≠ 0}) :
    (quotientHomeomorph D).symm q =
      Quotient.mk'' (D.scaling⁻¹ • invQParamUpperHalfPlane D.width D.width_pos q) := by
  apply (quotientHomeomorph D).injective
  simp only [Homeomorph.apply_symm_apply, quotientHomeomorph_mk,
    qCoordinate_smul_invQParamUpperHalfPlane]

/-- The normalized q-coordinate is an open quotient map. -/
theorem isOpenQuotientMap_qCoordinate : IsOpenQuotientMap (qCoordinate D) := by
  rw [qCoordinate_eq_comp]
  have hsmul : IsOpenQuotientMap ((D.scaling • ·) : ℍ → ℍ) := by
    have heq : ⇑(Homeomorph.smul D.scaling) = ((D.scaling • ·) : ℍ → ℍ) :=
      funext (Homeomorph.smul_apply D.scaling)
    rw [← heq]
    exact (Homeomorph.smul D.scaling).isOpenQuotientMap
  exact (isOpenQuotientMap_qParamPuncturedUnitDisc D.width D.width_pos).comp hsmul

/-- The normalized q-coordinate is holomorphic as a map into the punctured unit disc. -/
theorem mdifferentiable_qCoordinate :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qCoordinate D) := by
  rw [qCoordinate_eq_comp]
  exact (mdifferentiable_qParamPuncturedUnitDisc D.width D.width_pos).comp
    ((contMDiff_const_smul (I := 𝓘(ℂ, ℂ)) (n := ∞) D.scaling).mdifferentiable (by simp))

/-- The normalized q-coordinate, regarded as a complex-valued function, is holomorphic. -/
theorem mdifferentiable_coordinate :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (coordinate D) := by
  have hcoordinate : coordinate D =
      (fun q : {q : 𝔻 // q ≠ 0} ↦ ((q : 𝔻) : ℂ)) ∘ qCoordinate D :=
    funext fun z ↦ (coe_qCoordinate D z).symm
  rw [hcoordinate]
  exact TauCeti.Complex.UnitDisc.mdifferentiable_coe_punctured.comp
    (mdifferentiable_qCoordinate D)

/-- A scaled horodisc is exactly the inverse image of a punctured disc under the
q-coordinate. -/
theorem norm_qCoordinate_lt_iff (A : ℝ) (z : ℍ) :
    ‖((qCoordinate D z : 𝔻) : ℂ)‖ < Real.exp (-2 * Real.pi * A / D.width) ↔
      A < (D.scaling • z).im := by
  rw [qCoordinate_eq]
  exact norm_qParamPuncturedUnitDisc_lt_iff D.width D.width_pos A (D.scaling • z)

/-- The image of a scaled horodisc is the punctured disc of the corresponding exponential
radius. -/
theorem image_qCoordinate_setOf_lt_im (A : ℝ) :
    qCoordinate D '' {z : ℍ | A < (D.scaling • z).im} =
      {q : {q : 𝔻 // q ≠ 0} | ‖((q : 𝔻) : ℂ)‖ <
        Real.exp (-2 * Real.pi * A / D.width)} := by
  rw [qCoordinate_eq_comp, ← Set.preimage_ofPred_eq (p := fun z : ℍ ↦ A < z.im),
    Set.image_comp, Set.image_preimage_eq _ (MulAction.surjective D.scaling),
    image_qParamPuncturedUnitDisc_setOf_lt_im]

/-- The q-coordinate tends to zero whenever the height in the scaling coordinate tends to
infinity. The limit is through nonzero values, as required for a punctured cusp chart. -/
theorem tendsto_qCoordinate {α : Type*} {l : Filter α} {f : α → ℍ}
    (h : Tendsto (fun a ↦ D.scaling • f a) l atImInfty) :
    Tendsto (fun a ↦ ((qCoordinate D (f a) : 𝔻) : ℂ)) l (𝓝[≠] 0) := by
  simp only [qCoordinate_eq]
  simpa only [Function.comp_def] using
    (tendsto_qParamPuncturedUnitDisc D.width D.width_pos).comp h

end TauCeti.Subgroup.CuspDatum
