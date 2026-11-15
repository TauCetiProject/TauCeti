/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import TauCeti.MeasureTheory.Group.RestrictedProduct
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocallyCompact
import Mathlib.Data.Nat.PrimeFin
import TauCeti.MeasureTheory.Group.LocalFieldScaling

/-!
# Normalized Haar measures on adic completions and finite adele rings

Let `R` be a Dedekind domain with fraction field `K` whose height-one primes `v` have finite
residue fields `R ⧸ v`. Each completion `K_v = v.adicCompletion K` is a nonarchimedean local field
with compact open integer ring `𝒪_v = v.adicCompletionIntegers K`. This file equips `K_v` with the
additive Haar measure `v.addHaar K` giving `𝒪_v` mass `1`, equips the finite adele ring
`𝔸ᶠ[R, K] = FiniteAdeleRing R K` with the restricted product `FiniteAdeleRing.restrictedAddHaar` of
any family of local Haar measures normalized on `𝒪_v` at almost all places, and specializes to the
canonical measure `FiniteAdeleRing.addHaar R K`.

## Main definitions and results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersPositiveCompacts`: `𝒪_v` as a compact
  subset of `K_v` with nonempty interior.
* `IsDedekindDomain.HeightOneSpectrum.addHaar`: additive Haar measure on `K_v` normalized so that
  `v.addHaar K 𝒪_v = 1` (`addHaar_adicCompletionIntegers`), making the subtype pullback to `𝒪_v`
  a probability measure (`isProbabilityMeasure_comap_addHaar`, while `(c • v.addHaar K).comap (↑)`
  is a probability measure if and only if `c = 1` by `isProbabilityMeasure_comap_smul_addHaar_iff`).
* `IsDedekindDomain.HeightOneSpectrum.addHaar_inv_smul_adicCompletionIntegers`: for a uniformizer
  `π` of `K_v`, the fractional ideal `π⁻¹ • 𝒪_v` has `v.addHaar K`-mass `Ideal.absNorm v.asIdeal`
  (at least `2` by `two_le_addHaar_inv_smul_adicCompletionIntegers`).
* `IsDedekindDomain.FiniteAdeleRing.restrictedAddHaar` and
  `IsDedekindDomain.FiniteAdeleRing.addHaar`:
  the restricted product of local Haar measures on `FiniteAdeleRing R K`, and the canonical Haar
  measure giving the integral finite adeles `∏_v 𝒪_v` mass `1` (`addHaar_integralAdeles`),
  satisfying the box formula `addHaar_forall_mem` and uniqueness `exists_unique_addHaar` whenever
  `HeightOneSpectrum R` is countable.
* `IsDedekindDomain.FiniteAdeleRing.restrictedAddHaar_eq_smul`: rescaling one local Haar measure by
  `c : ℝ≥0` scales the restricted Haar measure on `FiniteAdeleRing R K` by `c` (so `∏_v 𝒪_v` has
  mass `c` by `restrictedAddHaar_eq_smul_integralAdeles`).
* `IsDedekindDomain.FiniteAdeleRing.addHaar_forall_mem_invUniformizer` and its rational
  specialization `addHaar_forall_mem_invUniformizer_rat`: replacing `𝒪_{v₀}` at one place `v₀` by
  `π⁻¹ • 𝒪_{v₀}` multiplies the box mass by `Ideal.absNorm v₀.asIdeal` (mass
  `Rat.HeightOneSpectrum.natGenerator v` over `ℚ`), whereas doing so at infinitely many places
  simultaneously yields infinite `addHaar` mass even though `∏ᶠ v, … = 1`
  (`addHaar_forall_mem_invUniformizer_eq_top`, `exists_forall_mem_addHaar_eq_top_rat`).

## References

* J. T. Tate, *Fourier analysis in number fields, and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press, 1967, §§2.2 and 3.3.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Graduate Texts in
  Mathematics 186, Springer, 1999, Chapters 5 and 7.
-/

public section
noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace Topology ValuativeRel
open scoped ENNReal NNReal Pointwise RestrictedProduct

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

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Private helper: `𝒪_v` as an `AddSubgroup` with carrier definitionally equal to
`(v.adicCompletionIntegers K : Set (v.adicCompletion K))`, so `Πʳ v, [K_v, intAddSubgroup K v]` is
definitionally equal to `FiniteAdeleRing R K` along with its topology. -/
private abbrev intAddSubgroup (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) : AddSubgroup (v.adicCompletion K) where
  carrier := (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  add_mem' ha hb := add_mem ha hb
  zero_mem' := zero_mem _
  neg_mem' ha := neg_mem ha

variable [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

private theorem isCompact_intAddSubgroup :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      IsCompact (intAddSubgroup K v : Set (v.adicCompletion K)) :=
  Eventually.of_forall fun v ↦
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers K)))

variable [∀ v : HeightOneSpectrum R, MeasurableSpace (v.adicCompletion K)]
variable [∀ v : HeightOneSpectrum R, BorelSpace (v.adicCompletion K)]
variable [MeasurableSpace (FiniteAdeleRing R K)] [BorelSpace (FiniteAdeleRing R K)]

/-- **Restricted product of local additive Haar measures on `FiniteAdeleRing R K`** (`𝔸ᶠ[R, K]`),
for any family `μ` of local additive Haar measures giving `𝒪_v` mass `1` at almost all places (such
as `v.addHaar K`, or local self-dual Haar measures). -/
def restrictedAddHaar (μ : ∀ v : HeightOneSpectrum R, Measure (v.adicCompletion K))
    (hμ : ∀ᶠ v in Filter.cofinite,
      μ v (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1) :
    Measure (FiniteAdeleRing R K) := by
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (intAddSubgroup K v : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let _ : MeasurableSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹MeasurableSpace (FiniteAdeleRing R K)›
  let _ : BorelSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹BorelSpace (FiniteAdeleRing R K)›
  exact Measure.restrictedAddHaar (intAddSubgroup K) isCompact_intAddSubgroup μ hμ

/-- `FiniteAdeleRing.restrictedAddHaar μ hμ` is an additive Haar measure on `FiniteAdeleRing R K`.
-/
instance isAddHaarMeasure_restrictedAddHaar
    (μ : ∀ v : HeightOneSpectrum R, Measure (v.adicCompletion K)) [∀ v, (μ v).IsAddHaarMeasure]
    (hμ : ∀ᶠ v in Filter.cofinite,
      μ v (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1) :
    (restrictedAddHaar μ hμ).IsAddHaarMeasure := by
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (intAddSubgroup K v : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let _ : MeasurableSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹MeasurableSpace (FiniteAdeleRing R K)›
  let _ : BorelSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹BorelSpace (FiniteAdeleRing R K)›
  exact Measure.isAddHaarMeasure_restrictedAddHaar (intAddSubgroup K) isCompact_intAddSubgroup μ hμ

variable (R K) in
/-- **The canonical additive Haar measure on `FiniteAdeleRing R K`**, normalized so that the
integral finite adeles `∏_v 𝒪_v` have measure `1`. -/
def addHaar : Measure (FiniteAdeleRing R K) :=
  restrictedAddHaar (fun v ↦ v.addHaar K)
    (Eventually.of_forall fun v ↦ v.addHaar_adicCompletionIntegers K)

variable (R K) in
/-- `FiniteAdeleRing.addHaar R K` is an additive Haar measure on `FiniteAdeleRing R K`. -/
instance isAddHaarMeasure_addHaar : (addHaar R K).IsAddHaarMeasure := by
  exact isAddHaarMeasure_restrictedAddHaar _ _

variable [Countable (HeightOneSpectrum R)]

variable (R K) in
/-- `FiniteAdeleRing.addHaar R K` is σ-finite when `HeightOneSpectrum R` is countable. -/
instance sigmaFinite_addHaar : SigmaFinite (addHaar R K) :=
  inferInstance

/-- **The box formula for `FiniteAdeleRing.restrictedAddHaar`.** -/
theorem restrictedAddHaar_forall_mem
    (μ : ∀ v : HeightOneSpectrum R, Measure (v.adicCompletion K)) [∀ v, (μ v).IsAddHaarMeasure]
    (hμ : ∀ᶠ v in Filter.cofinite,
      μ v (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1)
    {C : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hC : ∀ᶠ v in Filter.cofinite,
      C v = (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :
    restrictedAddHaar μ hμ {a : FiniteAdeleRing R K | ∀ v, a v ∈ C v} = ∏ᶠ v, μ v (C v) := by
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (intAddSubgroup K v : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let _ : MeasurableSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹MeasurableSpace (FiniteAdeleRing R K)›
  let _ : BorelSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹BorelSpace (FiniteAdeleRing R K)›
  exact Measure.restrictedAddHaar_forall_mem (intAddSubgroup K) isCompact_intAddSubgroup μ hμ hC

/-- **The box formula for `FiniteAdeleRing.addHaar`.** Every box `{a | ∀ v, a v ∈ C v}` with
`C v = 𝒪_v` for all but finitely many places `v` has mass `∏ᶠ v, v.addHaar K (C v)`. -/
theorem addHaar_forall_mem {C : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K)}
    (hC : ∀ᶠ v in Filter.cofinite,
      C v = (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :
    addHaar R K {a : FiniteAdeleRing R K | ∀ v, a v ∈ C v} =
      ∏ᶠ v : HeightOneSpectrum R, v.addHaar K (C v) := by
  exact restrictedAddHaar_forall_mem _ _ hC

/-- Any additive Haar measure on `FiniteAdeleRing R K` giving every Borel box `{a | ∀ v, a v ∈ C v}`
with `C v = 𝒪_v` cofinitely the product `∏ᶠ v, v.addHaar K (C v)` equals `addHaar R K`. -/
theorem eq_addHaar_of_forall_mem {ν : Measure (FiniteAdeleRing R K)} [ν.IsAddHaarMeasure]
    (hν : ∀ C : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K),
      (∀ v, MeasurableSet (C v)) →
      (∀ᶠ v in Filter.cofinite, C v = (v.adicCompletionIntegers K : Set (v.adicCompletion K))) →
      ν {a | ∀ v, a v ∈ C v} = ∏ᶠ v : HeightOneSpectrum R, v.addHaar K (C v)) :
    ν = addHaar R K := by
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (intAddSubgroup K v : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let _ : MeasurableSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹MeasurableSpace (FiniteAdeleRing R K)›
  let _ : BorelSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹BorelSpace (FiniteAdeleRing R K)›
  let _ : @Measure.IsAddHaarMeasure
      (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) _ _ _ ν :=
    ‹ν.IsAddHaarMeasure›
  exact Measure.eq_restrictedAddHaar_of_forall_mem (intAddSubgroup K) isCompact_intAddSubgroup
    (fun v ↦ v.addHaar K) (Eventually.of_forall fun v ↦ v.addHaar_adicCompletionIntegers K) hν

variable (R K) in
/-- **Existence and uniqueness of the normalized Haar measure on `FiniteAdeleRing R K`.** -/
theorem exists_unique_addHaar :
    ∃! ν : Measure (FiniteAdeleRing R K), ν.IsAddHaarMeasure ∧
      ∀ C : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K),
        (∀ v, MeasurableSet (C v)) →
        (∀ᶠ v in Filter.cofinite,
          C v = (v.adicCompletionIntegers K : Set (v.adicCompletion K))) →
        ν {a | ∀ v, a v ∈ C v} = ∏ᶠ v : HeightOneSpectrum R, v.addHaar K (C v) :=
  ⟨addHaar R K, ⟨inferInstance, fun _ _ hC ↦ addHaar_forall_mem hC⟩,
    fun _ ⟨hHaar, hbox⟩ ↦
      letI := hHaar
      eq_addHaar_of_forall_mem hbox⟩

variable (R K) in
/-- The integral finite adeles `∏_v 𝒪_v` have `addHaar R K`-measure `1`. -/
@[simp]
theorem addHaar_integralAdeles :
    addHaar R K (integralAdeles R K : Set (FiniteAdeleRing R K)) = 1 := by
  rw [coe_integralAdeles]
  simp_rw [← SetLike.mem_coe]
  rw [addHaar_forall_mem (Eventually.of_forall fun _ ↦ rfl)]
  simp

/-- **Rescaling one local Haar measure on `FiniteAdeleRing R K`.** Scaling `μ v₀` by `c : ℝ≥0` while
leaving `μ v` unchanged for `v ≠ v₀` scales `restrictedAddHaar` globally by `c`. -/
theorem restrictedAddHaar_eq_smul
    (μ μ' : ∀ v : HeightOneSpectrum R, Measure (v.adicCompletion K))
    [∀ v, (μ v).IsAddHaarMeasure] [∀ v, (μ' v).IsAddHaarMeasure]
    (hμ : ∀ᶠ v in Filter.cofinite,
      μ v (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1)
    (hμ' : ∀ᶠ v in Filter.cofinite,
      μ' v (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1)
    (v₀ : HeightOneSpectrum R) {c : ℝ≥0} (hv₀ : μ' v₀ = c • μ v₀)
    (hne : ∀ v ≠ v₀, μ' v = μ v) :
    restrictedAddHaar μ' hμ' = c • restrictedAddHaar μ hμ := by
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (intAddSubgroup K v : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let _ : MeasurableSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹MeasurableSpace (FiniteAdeleRing R K)›
  let _ : BorelSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹BorelSpace (FiniteAdeleRing R K)›
  exact Measure.restrictedAddHaar_eq_smul_of_eq_away (intAddSubgroup K) isCompact_intAddSubgroup
    μ μ' hμ hμ' v₀ hv₀ hne

/-- Scaling `v₀.addHaar K` by `c : ℝ≥0` at one place `v₀` gives `integralAdeles R K` restricted-Haar
mass `c` (whereas for `c ≠ 1`, the local pullback `(c • v₀.addHaar K).comap (↑)` is not a
probability measure on `𝒪_{v₀}` by `HeightOneSpectrum.isProbabilityMeasure_comap_smul_addHaar_iff`).
-/
theorem restrictedAddHaar_eq_smul_integralAdeles (v₀ : HeightOneSpectrum R) {c : ℝ≥0}
    (μ' : ∀ v : HeightOneSpectrum R, Measure (v.adicCompletion K)) [∀ v, (μ' v).IsAddHaarMeasure]
    (hμ' : ∀ᶠ v in Filter.cofinite,
      μ' v (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1)
    (hv₀ : μ' v₀ = c • v₀.addHaar K) (hne : ∀ v ≠ v₀, μ' v = v.addHaar K) :
    restrictedAddHaar μ' hμ' (integralAdeles R K : Set (FiniteAdeleRing R K)) = c := by
  have hsmul : restrictedAddHaar μ' hμ' = c • addHaar R K :=
    restrictedAddHaar_eq_smul (fun v ↦ v.addHaar K) μ'
      (Eventually.of_forall fun v ↦ v.addHaar_adicCompletionIntegers K) hμ' v₀ hv₀ hne
  rw [hsmul, smul_apply, Measure.nnreal_smul_coe_apply, addHaar_integralAdeles, mul_one]

/-- **Single-place inverse-uniformizer box.** Replacing `𝒪_{v₀}` at one place `v₀` by `π⁻¹ • 𝒪_{v₀}`
for a uniformizer `π` of `K_{v₀}` yields a box of `addHaar`-mass `Ideal.absNorm v₀.asIdeal`. -/
theorem addHaar_forall_mem_invUniformizer (v₀ : HeightOneSpectrum R)
    {π : (v₀.adicCompletion K)ˣ} (hπ : TauCeti.IsUniformizer (v₀.adicCompletion K) π) :
    addHaar R K {a : FiniteAdeleRing R K |
        a v₀ ∈ (π⁻¹ : (v₀.adicCompletion K)ˣ) •
          (v₀.adicCompletionIntegers K : Set (v₀.adicCompletion K)) ∧
          ∀ v ≠ v₀, a v ∈ v.adicCompletionIntegers K} =
      Ideal.absNorm v₀.asIdeal := by
  classical
  let C : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K) :=
    Function.update (fun v ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) v₀
      ((π⁻¹ : (v₀.adicCompletion K)ˣ) • (v₀.adicCompletionIntegers K : Set (v₀.adicCompletion K)))
  have hset : {a : FiniteAdeleRing R K |
      a v₀ ∈ (π⁻¹ : (v₀.adicCompletion K)ˣ) •
        (v₀.adicCompletionIntegers K : Set (v₀.adicCompletion K)) ∧
        ∀ v ≠ v₀, a v ∈ v.adicCompletionIntegers K} =
      {a | ∀ v, a v ∈ C v} := by
    ext a
    simp only [mem_ofPred_eq, C]
    refine ⟨fun ⟨h0, hne⟩ v ↦ ?_,
      fun h ↦ ⟨by simpa [C] using h v₀, fun v hv ↦ by simpa [C, hv] using h v⟩⟩
    by_cases hv : v = v₀
    · obtain rfl := hv
      simpa [C] using h0
    · simpa [C, hv] using hne v hv
  have hC : ∀ᶠ v in Filter.cofinite,
      C v = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Filter.Eventually.mono (Set.finite_singleton v₀).compl_mem_cofinite fun v (hv : v ≠ v₀) ↦
      Function.update_of_ne hv ..
  rw [hset, addHaar_forall_mem hC, finprod_eq_single _ v₀]
  · simp [C, v₀.addHaar_inv_smul_adicCompletionIntegers K hπ]
  · intro v hv
    simp [C, hv]

/-- **Necessity of `C v = 𝒪_v` cofinitely.** When `HeightOneSpectrum R` is infinite and `π v` is a
uniformizer of `K_v` at every place `v`, the set of finite adeles lying in `(π v)⁻¹ • 𝒪_v` at every
place has infinite `addHaar R K`-measure, whereas `∏ᶠ v, v.addHaar K ((π v)⁻¹ • 𝒪_v) = 1`. -/
theorem addHaar_forall_mem_invUniformizer_eq_top [Infinite (HeightOneSpectrum R)]
    {π : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ}
    (hπ : ∀ v, TauCeti.IsUniformizer (v.adicCompletion K) (π v)) :
    addHaar R K {a : FiniteAdeleRing R K |
        ∀ v, a v ∈ ((π v)⁻¹ : (v.adicCompletion K)ˣ) •
          (v.adicCompletionIntegers K : Set (v.adicCompletion K))} = ∞ ∧
      (∏ᶠ v : HeightOneSpectrum R, v.addHaar K (((π v)⁻¹ : (v.adicCompletion K)ˣ) •
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)))) = 1 := by
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (intAddSubgroup K v : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let _ : MeasurableSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹MeasurableSpace (FiniteAdeleRing R K)›
  let _ : BorelSpace (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, intAddSubgroup K v]) :=
    ‹BorelSpace (FiniteAdeleRing R K)›
  have hBC (v : HeightOneSpectrum R) :
      (intAddSubgroup K v : Set (v.adicCompletion K)) ⊆ ((π v)⁻¹ : (v.adicCompletion K)ˣ) •
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro x hx
    obtain ⟨ϖ, _, hϖπ⟩ := (TauCeti.isUniformizer_iff_exists_irreducible _ (π v)).1 (hπ v)
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def]
    have hϖmem : ((π v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
        v.adicCompletionIntegers K := by
      rw [← hϖπ, ← ValuationSubring.mem_toSubring, ← v.integer_eq_adicCompletionIntegers]
      exact ϖ.2
    exact mul_mem hϖmem hx
  have hge2 (v : HeightOneSpectrum R) :
      2 ≤ v.addHaar K (((π v)⁻¹ : (v.adicCompletion K)ˣ) •
        (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    v.two_le_addHaar_inv_smul_adicCompletionIntegers K (hπ v)
  have hinf : {v : HeightOneSpectrum R | 2 ≤ v.addHaar K (((π v)⁻¹ : (v.adicCompletion K)ˣ) •
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)))}.Infinite :=
    infinite_univ.mono fun v _ ↦ hge2 v
  refine ⟨Measure.restrictedAddHaar_forall_mem_eq_top_of_infinite (intAddSubgroup K)
      isCompact_intAddSubgroup (fun v ↦ v.addHaar K)
      (Eventually.of_forall fun v ↦ v.addHaar_adicCompletionIntegers K) hBC hinf,
    finprod_of_infinite_mulSupport (hinf.mono fun v hv h1 ↦ ?_)⟩
  exact absurd (hv.trans_eq h1) (by norm_num)

end General

section Rat

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
variable [IsIntegralClosure R ℤ ℚ] [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
variable [∀ v : HeightOneSpectrum R, MeasurableSpace (v.adicCompletion ℚ)]
variable [∀ v : HeightOneSpectrum R, BorelSpace (v.adicCompletion ℚ)]
variable [MeasurableSpace (FiniteAdeleRing R ℚ)] [BorelSpace (FiniteAdeleRing R ℚ)]

/-- Over an integral closure `R` of `ℤ` in `ℚ` (such as `ℤ` or `𝓞 ℚ`), the box replacing `𝒪_v` at a
single prime `v` by `π⁻¹ • 𝒪_v` has `addHaar R ℚ`-mass equal to the rational prime
`Rat.HeightOneSpectrum.natGenerator v`. -/
theorem addHaar_forall_mem_invUniformizer_rat (v : HeightOneSpectrum R)
    {π : (v.adicCompletion ℚ)ˣ} (hπ : TauCeti.IsUniformizer (v.adicCompletion ℚ) π) :
    addHaar R ℚ {a : FiniteAdeleRing R ℚ |
        a v ∈ (π⁻¹ : (v.adicCompletion ℚ)ˣ) •
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ∧
          ∀ w ≠ v, a w ∈ w.adicCompletionIntegers ℚ} =
      Rat.HeightOneSpectrum.natGenerator v := by
  let _ : Countable (HeightOneSpectrum R) :=
    Function.Injective.countable (Rat.HeightOneSpectrum.primesEquiv (R := R)).injective
  rw [addHaar_forall_mem_invUniformizer v hπ]
  have hspan : Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)} ≠ ⊥ := by
    simpa using (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero
  have heq : (R ⧸ v.asIdeal) ≃+*
      (ℤ ⧸ Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)}) :=
    Ideal.quotientEquiv v.asIdeal _ (Rat.IsIntegralClosure.intEquiv R)
      ((Rat.HeightOneSpectrum.span_natGenerator v).trans (by unfold Ideal.map; simp))
  have hnorm : Ideal.absNorm v.asIdeal = Rat.HeightOneSpectrum.natGenerator v := by
    rw [Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply, Nat.card_congr heq.toEquiv,
      ← Submodule.cardQuot_apply, ← Ideal.absNorm_of_ne_bot hspan, Ideal.absNorm_span_natCast,
      Module.finrank_self, pow_one]
  exact congrArg Nat.cast hnorm

/-- Over an integral closure `R` of `ℤ` in `ℚ` (such as `ℤ` or `𝓞 ℚ`), there exists a family of
open compact sets `C v` (namely `(π v)⁻¹ • 𝒪_v` at every rational prime) for which
`{a ∈ 𝔸ᶠ[R, ℚ] | ∀ v, a v ∈ C v}` has infinite `addHaar R ℚ`-mass while
`∏ᶠ v, v.addHaar ℚ (C v) = 1`. -/
theorem exists_forall_mem_addHaar_eq_top_rat :
    ∃ C : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion ℚ),
      (∀ v, MeasurableSet (C v)) ∧
      addHaar R ℚ {a : FiniteAdeleRing R ℚ | ∀ v, a v ∈ C v} = ∞ ∧
      (∏ᶠ v : HeightOneSpectrum R, v.addHaar ℚ (C v)) = 1 := by
  let _ : Countable (HeightOneSpectrum R) :=
    Function.Injective.countable (Rat.HeightOneSpectrum.primesEquiv (R := R)).injective
  let _ : Infinite (HeightOneSpectrum R) :=
    Infinite.of_injective (⇑(Rat.HeightOneSpectrum.primesEquiv (R := R)).symm) (Equiv.injective _)
  choose π hπ using fun v : HeightOneSpectrum R ↦ TauCeti.exists_isUniformizer (v.adicCompletion ℚ)
  refine ⟨fun v ↦ ((π v)⁻¹ : (v.adicCompletion ℚ)ˣ) •
      (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)),
    fun v ↦ ((Homeomorph.smul ((π v)⁻¹ : (v.adicCompletion ℚ)ˣ)).isOpenMap _
      (Valued.isOpen_valuationSubring _)).measurableSet,
    addHaar_forall_mem_invUniformizer_eq_top hπ⟩

end Rat

end IsDedekindDomain.FiniteAdeleRing

end
