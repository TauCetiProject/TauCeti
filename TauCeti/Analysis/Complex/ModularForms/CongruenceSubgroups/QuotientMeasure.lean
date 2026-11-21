/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.MeasureTheory.Group.OrbitQuotient
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Gamma

/-!
# Hyperbolic measure on congruence quotients

For `Γ ≤ SL(2, ℤ)`, the orbit space `Γ \ ℍ` is also the orbit space of the projective image of
`Γ`. The hyperbolic measure on it comes from restricting `dx dy / y²` to a fundamental domain
for the **projective** action. In particular, the central element `-I` contributes no extra
multiplicity. The measure has full support and is finite for congruence subgroups. Its total
mass is `π / 3` at level one and `2π` at principal level two.

The normalization uses `TauCeti.ModularGroup.covolume_psl2zToPSL2RRange` and
`Subgroup.relIndex_map_sl2zToPSL2R` to compute the mass from the effective index.
-/

public noncomputable section

open MeasureTheory MulAction Set UpperHalfPlane
open scoped ENNReal MatrixGroups

namespace Subgroup

variable (Γ : Subgroup SL(2, ℤ))

/-- The raw and projective orbit spaces of a modular subgroup have the same measurable
quotient, with the class of each point sent to the class of that point. -/
def orbitRelQuotientMeasurableEquivPSL2R :
    orbitRel.Quotient Γ ℍ ≃ᵐ orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ where
  toEquiv := Quotient.congrRight fun _ _ ↦ by
    simpa only [orbitRel_apply, mem_orbit_iff, Subtype.exists, Subgroup.mk_smul,
      exists_prop] using (Γ.orbitRel_map_sl2zToPSL2R_iff).symm
  measurable_toFun := measurable_from_quotient.mpr measurable_quotient_mk''
  measurable_invFun := measurable_from_quotient.mpr measurable_quotient_mk''

/-- Passing to the projective quotient preserves the point represented by a class. -/
@[simp]
theorem orbitRelQuotientMeasurableEquivPSL2R_mk (z : ℍ) :
    Γ.orbitRelQuotientMeasurableEquivPSL2R (Quotient.mk (orbitRel Γ ℍ) z) =
      Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) z :=
  (rfl)

/-- The inverse projective comparison also preserves the point represented by a class. -/
@[simp]
theorem orbitRelQuotientMeasurableEquivPSL2R_symm_mk (z : ℍ) :
    Γ.orbitRelQuotientMeasurableEquivPSL2R.symm
      (Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) z) = Quotient.mk (orbitRel Γ ℍ) z :=
  Γ.orbitRelQuotientMeasurableEquivPSL2R.symm_apply_eq.mpr
    (Γ.orbitRelQuotientMeasurableEquivPSL2R_mk z)

private theorem projectiveQuotient_symm_comp_mk : Γ.orbitRelQuotientMeasurableEquivPSL2R.symm ∘
    Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) = Quotient.mk (orbitRel Γ ℍ) :=
  funext Γ.orbitRelQuotientMeasurableEquivPSL2R_symm_mk

/-- The hyperbolic measure on `Γ \ ℍ`, transported from the effective projective action. -/
def hyperbolicQuotientMeasure : Measure (orbitRel.Quotient Γ ℍ) :=
  (orbitQuotientMeasure (Γ.map sl2zToPSL2R) volume).map
    Γ.orbitRelQuotientMeasurableEquivPSL2R.symm

/-- The projective comparison from the effective quotient preserves hyperbolic measure. -/
theorem measurePreserving_orbitRelQuotientMeasurableEquivPSL2R_symm :
    MeasurePreserving Γ.orbitRelQuotientMeasurableEquivPSL2R.symm
      (orbitQuotientMeasure (Γ.map sl2zToPSL2R) volume) Γ.hyperbolicQuotientMeasure :=
  ⟨Γ.orbitRelQuotientMeasurableEquivPSL2R.symm.measurable, rfl⟩

/-- Projection onto `Γ \ ℍ` from any effective fundamental domain preserves measure. -/
theorem measurePreserving_quotientMk_hyperbolicQuotientMeasure {F : Set ℍ}
    (hF : IsFundamentalDomain (Γ.map sl2zToPSL2R) F) :
    MeasurePreserving (Quotient.mk (orbitRel Γ ℍ)) (volume.restrict F)
      Γ.hyperbolicQuotientMeasure := by
  rw [← Γ.projectiveQuotient_symm_comp_mk]
  exact Γ.measurePreserving_orbitRelQuotientMeasurableEquivPSL2R_symm.comp
    (hF.measurePreserving_quotient_mk (orbitQuotientMeasure (Γ.map sl2zToPSL2R) volume))

/-- The total hyperbolic measure is the covolume of the effective image. -/
theorem hyperbolicQuotientMeasure_univ :
    Γ.hyperbolicQuotientMeasure univ = covolume (Γ.map sl2zToPSL2R) ℍ := by
  simp [hyperbolicQuotientMeasure, MeasurableEquiv.map_apply]

/-- A set in the modular quotient has zero hyperbolic measure exactly when its full
preimage in the upper half-plane has zero hyperbolic measure. -/
theorem hyperbolicQuotientMeasure_apply_eq_zero_iff (s : Set (orbitRel.Quotient Γ ℍ)) :
    Γ.hyperbolicQuotientMeasure s = 0 ↔
      (volume : Measure ℍ) (Quotient.mk (orbitRel Γ ℍ) ⁻¹' s) = 0 := by
  rw [hyperbolicQuotientMeasure, MeasurableEquiv.map_apply, orbitQuotientMeasure_apply_eq_zero_iff,
    ← preimage_comp, Γ.projectiveQuotient_symm_comp_mk]

/-- Hyperbolic quotient measure gives positive mass to every nonempty open set. -/
instance instIsOpenPosMeasureHyperbolicQuotientMeasure :
    Γ.hyperbolicQuotientMeasure.IsOpenPosMeasure where
  open_pos s hs hne := by
    rw [ne_eq, Γ.hyperbolicQuotientMeasure_apply_eq_zero_iff]
    exact ((hs.preimage continuous_quotient_mk').measure_pos volume
      (hne.preimage Quotient.mk_surjective)).ne'

/-- Every finite-index modular subgroup has finite quotient area. -/
instance instIsFiniteMeasureHyperbolicQuotientMeasure [Γ.FiniteIndex] :
    IsFiniteMeasure Γ.hyperbolicQuotientMeasure where
  measure_univ_lt_top := Γ.hyperbolicQuotientMeasure_univ ▸
    Γ.isCofinite_map_sl2zToPSL2R.covolume_ne_top.lt_top

/-- Quotient area is the level-one area multiplied by the index after adjoining the center. -/
theorem hyperbolicQuotientMeasure_univ_eq_index_mul [Γ.FiniteIndex] :
    Γ.hyperbolicQuotientMeasure univ = Γ.withCenter.index * ENNReal.ofReal (Real.pi / 3) := by
  rw [hyperbolicQuotientMeasure_univ,
    covolume_eq_index_mul_covolume Γ.map_sl2zToPSL2R_le_range_psl2zToPSL2R,
    ← Subgroup.relIndex, Γ.relIndex_map_sl2zToPSL2R,
    TauCeti.ModularGroup.covolume_psl2zToPSL2RRange]

end Subgroup

namespace CongruenceSubgroup

/-- The hyperbolic measure on a congruence quotient is finite. -/
theorem IsCongruenceSubgroup.isFiniteMeasure_hyperbolicQuotientMeasure {Γ : Subgroup SL(2, ℤ)}
    (hΓ : IsCongruenceSubgroup Γ) : IsFiniteMeasure Γ.hyperbolicQuotientMeasure := by
  let := hΓ.finiteIndex
  infer_instance

/-- The hyperbolic area of the level-one quotient is `π / 3`. -/
@[simp]
theorem hyperbolicQuotientMeasure_Gamma_one_univ :
    (Gamma 1).hyperbolicQuotientMeasure univ = ENNReal.ofReal (Real.pi / 3) := by
  rw [Subgroup.hyperbolicQuotientMeasure_univ, Gamma_one_top, Subgroup.map_top,
    TauCeti.range_sl2zToPSL2R_eq_range_psl2zToPSL2R,
    TauCeti.ModularGroup.covolume_psl2zToPSL2RRange]

/-- The hyperbolic area of the principal level-two quotient is `2π`. -/
@[simp]
theorem hyperbolicQuotientMeasure_Gamma_two_univ :
    (Gamma 2).hyperbolicQuotientMeasure univ = ENNReal.ofReal (2 * Real.pi) := by
  have h := TauCeti.mul_card_cuspOrbit_Gamma 2
  rw [TauCeti.card_cuspOrbit_Gamma_two] at h
  rw [Subgroup.hyperbolicQuotientMeasure_univ_eq_index_mul, ← h, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  norm_num
  ring

end CongruenceSubgroup
