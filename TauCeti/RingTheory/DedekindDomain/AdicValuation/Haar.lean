/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.MeasureTheory.Group.LocalFieldScaling
import TauCeti.MeasureTheory.Measure.Subtype
import TauCeti.NumberTheory.LocalField.Topology

/-!
# Normalized additive Haar measures on adic completions

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R` with
finite residue field `R ⧸ v`. The completion `K_v = v.adicCompletion K` is a nonarchimedean local
field whose ring of integers `𝒪_v = v.adicCompletionIntegers K` is compact and open. This file
packages `𝒪_v` as a `TopologicalSpace.PositiveCompacts`, defines the additive Haar measure
`v.addHaar K` on `K_v` normalized so that `v.addHaar K 𝒪_v = 1`, characterizes when rescaled
pullbacks to `𝒪_v` are probability measures, and proves uniformizer dilation on `π⁻¹ • 𝒪_v`.

## Main definitions and results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersPositiveCompacts`: `𝒪_v` as a compact
  subset of `K_v` with nonempty interior.
* `IsDedekindDomain.HeightOneSpectrum.addHaar`: additive Haar measure on `K_v` normalized so that
  `v.addHaar K 𝒪_v = 1` (`addHaar_adicCompletionIntegers`), with uniqueness (`eq_addHaar_iff`),
  making the subtype pullback to `𝒪_v` a probability measure (`isProbabilityMeasure_comap_addHaar`,
  while `(c • v.addHaar K).comap (↑)` is a probability measure if and only if `c = 1` by
  `isProbabilityMeasure_comap_smul_addHaar_iff`).
* `IsDedekindDomain.HeightOneSpectrum.addHaar_inv_smul_adicCompletionIntegers`: for a uniformizer
  `π` of `K_v`, the fractional ideal `π⁻¹ • 𝒪_v` has `v.addHaar K`-mass `Ideal.absNorm v.asIdeal`
  (at least `2` by `two_le_addHaar_inv_smul_adicCompletionIntegers`).

## References

* J. T. Tate, *Fourier analysis in number fields, and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press, 1967, §2.2.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Graduate Texts in
  Mathematics 186, Springer, 1999, Chapters 5 and 7.
-/

public section
noncomputable section

open MeasureTheory Set TopologicalSpace Topology ValuativeRel
open scoped ENNReal Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

section LocalHaar

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]

/-- The local integer ring `𝒪_v` packaged as a compact subset of `K_v` with nonempty interior. -/
def adicCompletionIntegersPositiveCompacts : PositiveCompacts (v.adicCompletion K) where
  carrier := v.adicCompletionIntegers K
  isCompact' := isCompact_iff_compactSpace.mpr
    (inferInstanceAs (CompactSpace (v.adicCompletionIntegers K)))
  interior_nonempty' := by
    have hopen : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      Valued.isOpen_valuationSubring _
    rw [hopen.interior_eq]
    exact ⟨0, zero_mem _⟩

/-- Coercion of `adicCompletionIntegersPositiveCompacts` to a set is `𝒪_v`. -/
@[simp]
theorem coe_adicCompletionIntegersPositiveCompacts :
    (v.adicCompletionIntegersPositiveCompacts K : Set (v.adicCompletion K)) =
      v.adicCompletionIntegers K := by
  rfl

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

/-- The additive Haar measure on `K_v` normalized so that `𝒪_v` has measure `1`. -/
def addHaar : Measure (v.adicCompletion K) :=
  Measure.addHaarMeasure (v.adicCompletionIntegersPositiveCompacts K)

/-- `v.addHaar K` is an additive Haar measure on `K_v`. -/
instance isAddHaarMeasure_addHaar : (v.addHaar K).IsAddHaarMeasure := by
  exact Measure.isAddHaarMeasure_addHaarMeasure _

/-- `v.addHaar K` is σ-finite. -/
instance sigmaFinite_addHaar : SigmaFinite (v.addHaar K) := by
  exact Measure.sigmaFinite_addHaarMeasure

/-- The local integer ring `𝒪_v` has `v.addHaar K`-measure `1`. -/
@[simp]
theorem addHaar_adicCompletionIntegers :
    v.addHaar K (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
  exact Measure.addHaarMeasure_self

/-- A σ-finite left-invariant measure on `K_v` equals `v.addHaar K` iff it gives `𝒪_v` mass `1`. -/
theorem eq_addHaar_iff (μ : Measure (v.adicCompletion K)) [SigmaFinite μ] [μ.IsAddLeftInvariant] :
    μ = v.addHaar K ↔ μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
  exact eq_comm.trans (Measure.addHaarMeasure_eq_iff (v.adicCompletionIntegersPositiveCompacts K) μ)

/-- Pulling `v.addHaar K` back to `𝒪_v` yields a probability measure. -/
instance isProbabilityMeasure_comap_addHaar :
    IsProbabilityMeasure
      ((v.addHaar K).comap ((↑) : v.adicCompletionIntegers K → v.adicCompletion K)) := by
  have hopen : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isOpen_valuationSubring _
  exact (Measure.isProbabilityMeasure_comap_subtype_iff hopen.measurableSet _).2
    (v.addHaar_adicCompletionIntegers K)

/-- Pulling `c • v.addHaar K` back to `𝒪_v` gives a probability measure if and only if `c = 1`. -/
theorem isProbabilityMeasure_comap_smul_addHaar_iff {c : ℝ≥0∞} :
    IsProbabilityMeasure
      ((c • v.addHaar K).comap ((↑) : v.adicCompletionIntegers K → v.adicCompletion K)) ↔
      c = 1 := by
  have hopen : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isOpen_valuationSubring _
  refine (Measure.isProbabilityMeasure_comap_subtype_iff hopen.measurableSet
    (c • v.addHaar K)).trans ?_
  rw [smul_apply, smul_eq_mul, v.addHaar_adicCompletionIntegers K, mul_one]

/-- **Scaling of `v.addHaar K` on `π⁻¹ • 𝒪_v`.** For a uniformizer `π` of `K_v`, the inverse
fractional ideal `π⁻¹ • 𝒪_v` has measure `Ideal.absNorm v.asIdeal`. -/
theorem addHaar_inv_smul_adicCompletionIntegers {π : (v.adicCompletion K)ˣ}
    (hπ : TauCeti.IsUniformizer (v.adicCompletion K) π) :
    v.addHaar K ((π⁻¹ : (v.adicCompletion K)ˣ) •
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))) =
      Ideal.absNorm v.asIdeal := by
  obtain ⟨ϖ, hϖ, hϖπ⟩ := (TauCeti.isUniformizer_iff_exists_irreducible _ π).1 hπ
  let e : v.adicCompletion K ≃ᵐ (Unit → v.adicCompletion K) :=
    (MeasurableEquiv.funUnique Unit (v.adicCompletion K)).symm
  let ν : Measure (Unit → v.adicCompletion K) := (v.addHaar K).map e
  have _ : ν.IsAddLeftInvariant :=
    isAddLeftInvariant_map
      (AddEquiv.funUnique Unit (v.adicCompletion K)).symm.toAddMonoidHom.toAddHom
      e.measurable e.surjective
  have h := Measure.measure_image_mulVec_vadd_smul_integerBox ν hϖ
    (A := Matrix.diagonal fun _ : Unit ↦ ϖ) (k := 1) (by simp) 0 (Units.ne_zero π⁻¹)
  have himg : ((Matrix.diagonal fun _ : Unit ↦ ϖ).map
      (algebraMap 𝒪[v.adicCompletion K] (v.adicCompletion K))).mulVec ''
      ((0 : Unit → v.adicCompletion K) +ᵥ
        ((π⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
          TauCeti.integerBox (v.adicCompletion K) Unit) =
      TauCeti.integerBox (v.adicCompletion K) Unit := by
    have hmul : ((Matrix.diagonal fun _ : Unit ↦ ϖ).map
        (algebraMap 𝒪[v.adicCompletion K] (v.adicCompletion K))).mulVec =
        fun y : Unit → v.adicCompletion K ↦ (π : v.adicCompletion K) • y := by
      funext y u
      cases u
      rw [Matrix.diagonal_map (map_zero _), Matrix.mulVec_diagonal,
        Algebra.algebraMap_ofSubsemiring_apply, hϖπ]
      rfl
    rw [hmul, zero_vadd, image_smul, smul_smul, Units.mul_inv, one_smul]
  have hpre1 : e ⁻¹' TauCeti.integerBox (v.adicCompletion K) Unit =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    simp [e, MeasurableEquiv.funUnique, v.integer_eq_adicCompletionIntegers]
  have hpre2 : e ⁻¹' ((0 : Unit → v.adicCompletion K) +ᵥ
      ((π⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
        TauCeti.integerBox (v.adicCompletion K) Unit) =
      (π⁻¹ : (v.adicCompletion K)ˣ) •
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    rw [zero_vadd, mem_preimage, Units.smul_def,
      mem_smul_set_iff_inv_smul_mem₀ (Units.ne_zero π⁻¹),
      mem_smul_set_iff_inv_smul_mem₀ (Units.ne_zero π⁻¹)]
    simp [e, MeasurableEquiv.funUnique, v.integer_eq_adicCompletionIntegers]
  rw [himg, e.map_apply, e.map_apply, hpre1, hpre2, v.addHaar_adicCompletionIntegers K,
    pow_one, v.natCard_residueField_adicCompletion_eq_absNorm (K := K)] at h
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
    rw [← v.natCard_residueField_adicCompletion_eq_absNorm (K := K)]
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hmul := congrArg ((Ideal.absNorm v.asIdeal : ℝ≥0∞) * ·) h.symm
  rwa [← mul_assoc, one_div, ENNReal.mul_inv_cancel hq0 (ENNReal.natCast_ne_top _), one_mul,
    mul_one] at hmul

/-- At every height-one prime `v` with finite residue field, `π⁻¹ • 𝒪_v` has `v.addHaar K`-measure
at least `2` (since the residue field has at least two elements). -/
theorem two_le_addHaar_inv_smul_adicCompletionIntegers {π : (v.adicCompletion K)ˣ}
    (hπ : TauCeti.IsUniformizer (v.adicCompletion K) π) :
    2 ≤ v.addHaar K ((π⁻¹ : (v.adicCompletion K)ˣ) •
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
  rw [v.addHaar_inv_smul_adicCompletionIntegers K hπ,
    ← v.natCard_residueField_adicCompletion_eq_absNorm (K := K)]
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[v.adicCompletion K])

end LocalHaar

end IsDedekindDomain.HeightOneSpectrum

end
