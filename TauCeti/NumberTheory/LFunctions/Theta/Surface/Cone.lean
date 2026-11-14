/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar
public import TauCeti.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Radial integration over a surface cone

The cone above a set `D` of norm-one archimedean parameters consists of the positive parameters
whose surface part lies in `D`. Restricting `archHaar` to this cone gives the image of
`(surfaceHaar.restrict D) × multHaar` under radial scaling. Consequently integration over the
cone splits into a surface integral and a radial Mellin transform.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5).
-/

public section
noncomputable section

open MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The cone of positive parameters above `D`: their surface coordinate belongs to `D`.
For a unit fundamental domain this is the domain of Hecke's unfolding integral. -/
def unitCone (D : Set (realSpace K)) : Set (realSpace K) :=
  {y | (∀ w, 0 < y w) ∧ surfacePart y ∈ D}

/-- Cone membership requires positivity and membership of the normalized parameter in `D`. -/
@[simp]
theorem mem_unitCone {D : Set (realSpace K)} {y : realSpace K} :
    y ∈ unitCone D ↔ (∀ w, 0 < y w) ∧ surfacePart y ∈ D := Iff.rfl

/-- Membership in the cone in norm-one and radial coordinates. -/
theorem surfaceScale_mem_unitCone_iff (D : Set (realSpace K)) (x : normOneSurface K)
    {t : ℝ} (ht : 0 < t) : surfaceScale (x : realSpace K) t ∈ unitCone D ↔
      (x : realSpace K) ∈ D := by
  rw [mem_unitCone, surfacePart_surfaceScale x.2 ht]
  exact and_iff_right (surfaceScale_pos (mem_normOneSurface.mp x.2).1 ht)

/-- A measurable surface set has a measurable cone. -/
theorem measurableSet_unitCone {D : Set (realSpace K)} (hD : MeasurableSet D) :
    MeasurableSet (unitCone D) := by
  have hpos : MeasurableSet {y : realSpace K | ∀ w, 0 < y w} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter fun w : InfinitePlace K ↦
      measurableSet_lt (measurable_const (a := (0 : ℝ))) (measurable_pi_apply w)
  exact hpos.inter (measurable_surfacePart hD)

/-- **The measure on the cone splits into surface and radial measures.** There is no extra
Jacobian: the radial coordinate is the archimedean norm and its measure is `dt / t`. -/
theorem archHaar_restrict_unitCone {D : Set (realSpace K)} (hD : MeasurableSet D) :
    (archHaar K).restrict (unitCone D) =
      (((surfaceHaar K).restrict (Subtype.val ⁻¹' D)).prod multHaar).map
        (fun p : normOneSurface K × ℝ ↦ surfaceScale (p.1 : realSpace K) p.2) := by
  rw [archHaar_eq_map, Measure.restrict_map measurable_surfaceScale_prod
    (measurableSet_unitCone hD)]
  congr 1
  conv_rhs => rw [← Measure.restrict_univ (μ := multHaar), Measure.prod_restrict]
  apply Measure.restrict_congr_set
  have hpos : ∀ᵐ p : normOneSurface K × ℝ ∂(surfaceHaar K).prod multHaar, 0 < p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
      (Filter.Eventually.of_forall fun _ ↦ ae_pos_multHaar)
  filter_upwards [hpos] with p hp
  simpa only [mem_preimage, mem_prod, mem_univ, and_true] using
    surfaceScale_mem_unitCone_iff D p.1 hp

section Integral

variable {E : Type*} [NormedAddCommGroup E]

/-- Integrability on the cone is precisely integrability in the surface and radial coordinates.
The measurability hypothesis is only on the original cone. -/
theorem integrableOn_unitCone_iff {D : Set (realSpace K)} (hD : MeasurableSet D)
    {f : realSpace K → E} (hf : AEStronglyMeasurable f ((archHaar K).restrict (unitCone D))) :
    IntegrableOn f (unitCone D) (archHaar K) ↔
      Integrable (fun p : normOneSurface K × ℝ ↦ f (surfaceScale (p.1 : realSpace K) p.2))
        (((surfaceHaar K).restrict (Subtype.val ⁻¹' D)).prod multHaar) := by
  rw [archHaar_restrict_unitCone hD] at hf
  rw [IntegrableOn, archHaar_restrict_unitCone hD]
  exact integrable_map_measure hf measurable_surfaceScale_prod.aemeasurable

variable [NormedSpace ℝ E]

/-- Fubini on the cone, with the radial coordinate integrated last. -/
theorem integral_unitCone_eq_integral_surfaceScale {D : Set (realSpace K)}
    (hD : MeasurableSet D) {f : realSpace K → E}
    (hf : IntegrableOn f (unitCone D) (archHaar K)) :
    ∫ y in unitCone D, f y ∂archHaar K =
      ∫ t, ∫ x in Subtype.val ⁻¹' D, f (surfaceScale (x : realSpace K) t)
        ∂surfaceHaar K ∂multHaar := by
  have hprod := (integrableOn_unitCone_iff hD hf.aestronglyMeasurable).mp hf
  rw [IntegrableOn, archHaar_restrict_unitCone hD] at hf
  rw [archHaar_restrict_unitCone hD]
  rw [integral_map measurable_surfaceScale_prod.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod_symm _ hprod

end Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- A norm-weighted cone integral is the convergent Mellin transform of its surface average. -/
theorem hasMellin_integral_surfaceScale {D : Set (realSpace K)} (hD : MeasurableSet D)
    {f : realSpace K → E} (s : ℂ)
    (hf : IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ s • f y) (unitCone D) (archHaar K)) :
    HasMellin (fun t ↦ ∫ x in Subtype.val ⁻¹' D, f (surfaceScale (x : realSpace K) t)
        ∂surfaceHaar K) s
      (∫ y in unitCone D, (archNorm y : ℂ) ^ s • f y ∂archHaar K) := by
  have havg : (fun t ↦ ∫ x in Subtype.val ⁻¹' D,
      (archNorm (surfaceScale (x : realSpace K) t) : ℂ) ^ s •
        f (surfaceScale (x : realSpace K) t) ∂surfaceHaar K) =ᵐ[multHaar]
      (fun t ↦ (t : ℂ) ^ s • ∫ x in Subtype.val ⁻¹' D,
        f (surfaceScale (x : realSpace K) t) ∂surfaceHaar K) := by
    filter_upwards [ae_pos_multHaar] with t ht
    simp_rw [archNorm_surfaceScale_of_mem_normOneSurface (Subtype.property _) ht.le,
      integral_smul]
  constructor
  · exact integrable_multHaar_cpow_smul_iff.mp
      (((integrableOn_unitCone_iff hD hf.aestronglyMeasurable).mp hf).integral_prod_right.congr
        havg)
  · rw [← integral_multHaar_cpow_smul, integral_unitCone_eq_integral_surfaceScale hD hf]
    exact (integral_congr_ae havg).symm

end TauCeti.LFunctions
