/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.MellinKernel
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.MellinTransform

/-!
# Radial integration over a unit cone

The cone above a set `D` of norm-one archimedean parameters consists of the positive parameters
whose surface part lies in `D`. Restricting `archHaar` to this cone gives the image of
`(surfaceHaar.restrict D) × multHaar` under radial scaling. Consequently integration over the
cone splits into a surface integral and a radial Mellin transform.

For a lattice theta series, `hasMellin_mellinKernel_sub` identifies the Mellin transform of the
existing covolume-rescaled kernel, minus its constant term, with the weighted theta integral over
the cone. Absolute integrability of that cone integral is an explicit hypothesis: this change of
variables does not perform the separate arithmetic unfolding of unit orbits. In particular it
does not identify a radial lattice-point sum with a partial zeta function.

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
theorem mem_unitCone_iff {D : Set (realSpace K)} {y : realSpace K} :
    y ∈ unitCone D ↔ (∀ w, 0 < y w) ∧ surfacePart y ∈ D := Iff.rfl

/-- Membership in the cone in norm-one and radial coordinates. -/
theorem surfaceScale_mem_unitCone_iff (D : Set (realSpace K)) (x : normOneSurface K)
    {t : ℝ} (ht : 0 < t) : surfaceScale (x : realSpace K) t ∈ unitCone D ↔
      (x : realSpace K) ∈ D := by
  rw [mem_unitCone_iff, surfacePart_surfaceScale x.2 ht]
  exact and_iff_right (surfaceScale_pos (mem_normOneSurface.mp x.2).1 ht)

/-- A measurable surface set has a measurable cone. -/
theorem measurableSet_unitCone {D : Set (realSpace K)} (hD : MeasurableSet D) :
    MeasurableSet (unitCone D) := by
  have hpos : MeasurableSet {y : realSpace K | ∀ w, 0 < y w} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter fun w : InfinitePlace K ↦
      measurableSet_lt (measurable_const (a := (0 : ℝ))) (measurable_pi_apply w)
  exact hpos.inter (measurable_surfacePart hD)

/-- Radial scaling is measurable in the surface point and the radial parameter. -/
private theorem measurable_surfaceScale_prod :
    Measurable fun p : normOneSurface K × ℝ ↦ surfaceScale (p.1 : realSpace K) p.2 :=
  continuous_surfaceScale.measurable.comp (measurable_subtype_coe.prodMap measurable_id)

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
    propext (surfaceScale_mem_unitCone_iff D p.1 hp)

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
/-- A norm-weighted cone integral is the convergent Mellin transform of its surface average.
This formula precedes the covolume rescaling used in `mellinKernel`. -/
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

open scoped Classical in
/-- For a bounded measurable surface set, the theta series at a positive radial parameter is
integrable over that set. Boundedness on the norm-one surface bounds every coordinate away from
zero, so a single Gaussian theta value dominates it. -/
theorem integrableOn_latticeTheta_surfaceScale {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : normOneSurface K ↦ latticeTheta L (surfaceScale (x : realSpace K) t))
      (Subtype.val ⁻¹' D) (surfaceHaar K) := by
  obtain ⟨C, hC1, hC⟩ := exists_forall_mem_Icc_of_isBounded hD
  let δ := C⁻¹ * t ^ (1 / (Module.finrank ℚ K : ℝ))
  have hδ : 0 < δ := by positivity
  have hmeas : AEStronglyMeasurable
      (fun x : normOneSurface K ↦ latticeTheta L (surfaceScale (x : realSpace K) t))
      ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) := by
    apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousAt]
    intro x
    exact ContinuousAt.comp (g := latticeTheta L) (continuousAt_latticeTheta L
      (surfaceScale_pos (mem_normOneSurface.mp x.2).1 ht))
        (continuous_surfaceScale.comp
          (continuous_subtype_val.prodMk continuous_const)).continuousAt
  have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  refine (integrable_const (‖latticeTheta L fun _ ↦ δ‖ : ℝ)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem (measurable_subtype_coe hDm)] with x hx
  refine norm_latticeTheta_le L (fun _ ↦ hδ) fun w ↦ ?_
  rw [surfaceScale_apply]
  exact mul_le_mul_of_nonneg_right (hC x hx x.2 w).1 (Real.rpow_pos_of_pos ht _).le

open scoped Classical in
/-- Subtracting the constant term of the kernel subtracts `1` from the theta series before
averaging. The constant is the surface mass times `2^r₂ / w`. -/
theorem mellinKernel_sub_eq_integral_sub_one {D : Set (realSpace K)}
    (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    {u : ℝ} (hu : 0 < u) :
    mellinKernel D L u - (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (surfaceHaar K).real (Subtype.val ⁻¹' D) =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ∫ x in Subtype.val ⁻¹' D,
          (latticeTheta L (surfaceScale (x : realSpace K)
            (u / ZLattice.covolume L ^ 2)) - 1) ∂surfaceHaar K := by
  have hV : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  rw [integral_sub (integrableOn_latticeTheta_surfaceScale hDm hD L (by positivity))
    (integrable_const _), integral_const, measureReal_restrict_apply_univ, ← Complex.coe_smul,
    smul_eq_mul, mul_one, mellinKernel_def]
  ring

open scoped Classical in
/-- **The radial Mellin substitution in Hecke's integral.** If the norm-weighted theta series
minus its constant term is absolutely integrable over the cone, then the Mellin transform of
its kernel is that cone integral times `(2^r₂ / w) V_L^s`. The power of the covolume comes from
the substitution `u = V_L² t`, not from a Jacobian factor in `dt / t`. -/
theorem hasMellin_mellinKernel_sub {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (s : ℂ)
    (h : IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1))
      (unitCone D) (archHaar K)) :
    HasMellin (fun u ↦ mellinKernel D L u -
        (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          (surfaceHaar K).real (Subtype.val ⁻¹' D)) (s / 2)
      ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume L ^ 2 : ℂ) ^ (s / 2) *
          ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1)
            ∂archHaar K) := by
  let F : ℝ → ℂ := fun t ↦ ∫ x in Subtype.val ⁻¹' D,
    (latticeTheta L (surfaceScale (x : realSpace K) t) - 1) ∂surfaceHaar K
  let c : ℂ := (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ)
  have hV : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have hF : HasMellin F (s / 2)
      (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1) ∂archHaar K) :=
    hasMellin_integral_surfaceScale hDm (s / 2) h
  have hscaled := hF.comp_mul_right (a := (ZLattice.covolume L ^ 2)⁻¹) (by positivity)
  have havg (u : ℝ) (hu : 0 < u) : mellinKernel D L u -
      c * (surfaceHaar K).real (Subtype.val ⁻¹' D) =
        c • F (u * (ZLattice.covolume L ^ 2)⁻¹) := by
    rw [mellinKernel_sub_eq_integral_sub_one hDm hD L hu]
    simp only [F, c, smul_eq_mul, div_eq_mul_inv]
  constructor
  · exact (hscaled.1.const_smul c).congr_fun
      (fun u hu ↦ congrArg ((u : ℂ) ^ (s / 2 - 1) • ·) (havg u hu).symm)
      measurableSet_Ioi
  have hrescale : mellin (fun u ↦ mellinKernel D L u -
      c * (surfaceHaar K).real (Subtype.val ⁻¹' D)) (s / 2) =
        mellin (fun u ↦ c • F (u * (ZLattice.covolume L ^ 2)⁻¹)) (s / 2) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    exact congrArg ((u : ℂ) ^ (s / 2 - 1) • ·) (havg u hu)
  rw [hrescale, mellin_const_smul, hscaled.2]
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (sq_nonneg _),
    Complex.cpow_neg, inv_inv]
  simp only [c, smul_eq_mul, Complex.ofReal_pow, mul_assoc]

end TauCeti.LFunctions
