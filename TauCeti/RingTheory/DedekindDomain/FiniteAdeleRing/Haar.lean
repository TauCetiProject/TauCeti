/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct
public import TauCeti.NumberTheory.LocalField.HaarCharacter
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.BorelSpace
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocalUnits
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place

/-!
# The normalized Haar measure on the finite adeles

Let `R` be a Dedekind domain with fraction field `K`, countably many places and finite residue
fields, for instance the ring of integers of a number field. The integral finite adeles
`Ô = ∏_v 𝒪_v` are a compact open subring of the finite adele ring `𝔸ᶠ = FiniteAdeleRing R K`, so
there is exactly one additive Haar measure `μ_f` on `𝔸ᶠ` with `μ_f(Ô) = 1`, namely Mathlib's
`MeasureTheory.Measure.addHaarMeasure` at `Ô`. This file shows that it is the restricted product
of the local Haar measures `μ_v` normalized by `μ_v(𝒪_v) = 1`, and computes how it scales under
multiplication by a finite idele.

For a finite idele `a`, the set `a • Ô` is the coordinate box with factors `a_v • 𝒪_v`, which
equal `𝒪_v` at all but finitely many places. Evaluating the restricted product of the `μ_v` on this
box, each factor contributes the normalized absolute value `|a_v|_v` of the local field, so the
Haar character of `a` on the additive group of `𝔸ᶠ` is the finite product `∏ᶠ v, |a_v|_v`, and
multiplication by `a` pushes every additive Haar measure `μ` on `𝔸ᶠ` forward to
`(∏ᶠ v, |a_v|_v)⁻¹ • μ`. At a finite place of a number field, `|·|_v` is the usual norm
`(N v) ^ (-v(·))` (`IsDedekindDomain.HeightOneSpectrum.coe_normalizedAbsoluteValue_adicCompletion`).

Two consequences fix the normalization. For a nonzero ideal `N` of `R` with `R ⧸ N` finite, the
completion `NÔ` of `N` in `Ô` has index `#(R ⧸ N)` in `Ô`, so it has measure `#(R ⧸ N)⁻¹`; for the
ring of integers of a number field `#(R ⧸ N)` is the absolute norm of `N`. And when `R` has a
place, `μ_f` is not finite: multiplication by a uniformizer at one place scales it by
`q_v⁻¹ ≠ 1` while preserving the whole space.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.integralAdelesPositiveCompacts`: the integral finite adeles
  `Ô` as a compact set with nonempty interior, at which `addHaarMeasure` is normalized.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.coe_integralAdeles_eq_box`,
  `IsDedekindDomain.FiniteAdeleRing.smul_integralAdeles`: `Ô` and its translate `a • Ô` by a
  finite idele are the coordinate boxes with factors `𝒪_v` and `a_v • 𝒪_v`.
* `IsDedekindDomain.FiniteAdeleRing.addHaarMeasure_eq_restrictedAddHaar`: the Haar measure giving
  `Ô` mass one is the restricted product of local additive Haar measures giving each `𝒪_v` mass
  one.
* `IsDedekindDomain.FiniteAdeleRing.distribHaarChar_eq_finprod`: the Haar character of a finite
  idele `a` is `∏ᶠ v, |a_v|_v`; for the idele concentrated at one place it is the local Haar
  character (`IsDedekindDomain.FiniteAdeleRing.distribHaarChar_unitsOfAdicCompletion`).
* `IsDedekindDomain.FiniteAdeleRing.map_mul_left_eq_inv_finprod_smul`: multiplication by a finite
  idele `a` pushes an additive Haar measure `μ` forward to `(∏ᶠ v, |a_v|_v)⁻¹ • μ`.
* `IsDedekindDomain.FiniteAdeleRing.natCard_mul_measure_image_completedIdeal`,
  `IsDedekindDomain.FiniteAdeleRing.addHaarMeasure_image_completedIdeal`: the completion `NÔ` of a
  nonzero ideal `N` has `#(R ⧸ N)⁻¹` times the measure of `Ô`, hence mass `#(R ⧸ N)⁻¹`.
* `IsDedekindDomain.FiniteAdeleRing.addHaar_univ_eq_top`: an additive Haar measure on the finite
  adele ring is infinite as soon as `R` has a place.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), §3.5, pp. 186–189 (the modulus of an automorphism
  and Lemma 3.63 with the restricted product of Haar measures following it).
* A. V. Sutherland, *Number Theory I*, MIT 18.785 lecture notes, Lecture 23, §23.3, p. 6.
-/

public section
noncomputable section

open MeasureTheory Measure RestrictedProduct TauCeti
open scoped NNReal ENNReal Pointwise

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

section PositiveCompacts

variable [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- The integral finite adeles `Ô = ∏_v 𝒪_v`, as a compact set with nonempty interior: they are
compact since every `𝒪_v` is, and open. Mathlib's `MeasureTheory.Measure.addHaarMeasure` at this
set is the additive Haar measure on the finite adele ring giving `Ô` mass one. -/
def integralAdelesPositiveCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing R K) where
  carrier := integralAdeles R K
  isCompact' := isCompact_integralAdeles
  interior_nonempty' := ⟨0, by
    rw [(isOpen_integralAdeles R K).interior_eq]
    exact zero_mem _⟩

/-- The compact set `integralAdelesPositiveCompacts R K` is the set of integral finite adeles. -/
@[simp]
theorem coe_integralAdelesPositiveCompacts :
    (integralAdelesPositiveCompacts R K : Set (FiniteAdeleRing R K)) = integralAdeles R K :=
  (rfl)

end PositiveCompacts

/-- The integral finite adeles are the coordinate box with factors the local integer rings. -/
theorem coe_integralAdeles_eq_box :
    (integralAdeles R K : Set (FiniteAdeleRing R K)) =
      box fun v : HeightOneSpectrum R ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  -- Both sides read the coordinates of a finite adele, through the coercions of
  -- `FiniteAdeleRing R K` and of the underlying restricted product, which agree by definition.
  Set.ext fun _ ↦ mem_integralAdeles.trans mem_box.symm

variable {R K} in
/-- Multiplying the integral finite adeles by a finite idele `a` gives the coordinate box with
factors `a_v • 𝒪_v`. -/
theorem smul_integralAdeles (a : (FiniteAdeleRing R K)ˣ) :
    a • (integralAdeles R K : Set (FiniteAdeleRing R K)) =
      box fun v : HeightOneSpectrum R ↦
        (a : FiniteAdeleRing R K) v • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, mem_integralAdeles, Units.smul_def,
    smul_eq_mul]
  simp_rw [mul_apply, coe_units_inv_apply]
  refine Iff.trans (forall_congr' fun v ↦ ?_) mem_box.symm
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (coe_units_apply_ne_zero a v), smul_eq_mul]
  -- The two sides differ only in the coercion through which the coordinate `x v` is read, that of
  -- `FiniteAdeleRing R K` or that of the underlying restricted product; they agree by definition.
  exact Iff.rfl

/-! ### The restricted product of the local Haar measures -/

section Restricted

variable [Countable (HeightOneSpectrum R)] [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- **The normalized Haar measure on the finite adeles is a restricted product.** The additive
Haar measure on the finite adele ring giving the integral finite adeles `Ô` mass one is the
restricted product of local additive Haar measures `μ v` with `μ v 𝒪_v = 1`. -/
theorem addHaarMeasure_eq_restrictedAddHaar
    [∀ v : HeightOneSpectrum R, MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum R, BorelSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum R, Measure (v.adicCompletion K))
    [∀ v, (μ v).IsAddHaarMeasure] (hμ : ∀ v, μ v (v.adicCompletionIntegers K) = 1) :
    addHaarMeasure (integralAdelesPositiveCompacts R K) =
      restrictedAddHaar (fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers K) μ
        (.of_forall hμ) := by
  -- `FiniteAdeleRing R K` is the restricted product, but instance search does not see through
  -- that definition, so the restricted product measure is named at the type of finite adeles.
  let ν : Measure (FiniteAdeleRing R K) :=
    restrictedAddHaar (fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers K) μ (.of_forall hμ)
  have : ν.IsAddHaarMeasure := isAddHaarMeasure_restrictedAddHaar _ _ _
  refine (addHaarMeasure_eq_iff (integralAdelesPositiveCompacts R K) ν).2 ?_
  rw [coe_integralAdelesPositiveCompacts, coe_integralAdeles_eq_box]
  exact (restrictedAddHaar_box_self _ _ _).trans (by simp [hμ])

variable {R K}

/-- **The Haar character of a finite idele.** Multiplication by a finite idele `a` scales additive
Haar measure on the finite adele ring by `∏ᶠ v, |a_v|_v`, the finite product of the normalized
absolute values of its components. -/
@[simp]
theorem distribHaarChar_eq_finprod (a : (FiniteAdeleRing R K)ˣ) :
    distribHaarChar (FiniteAdeleRing R K) a =
      ∏ᶠ v : HeightOneSpectrum R,
        (normalizedAbsoluteValue (v.adicCompletion K) ((a : FiniteAdeleRing R K) v) : ℝ≥0) := by
  -- Compute with the local Haar measures giving each `𝒪_v` mass one.
  let _ (v : HeightOneSpectrum R) : MeasurableSpace (v.adicCompletion K) := borel _
  have _ (v : HeightOneSpectrum R) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  let μ (v : HeightOneSpectrum R) := addHaarMeasure (integerPositiveCompacts (v.adicCompletion K))
  have hμ (v : HeightOneSpectrum R) : μ v (v.adicCompletionIntegers K) = 1 := by
    have h : (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =
        integerPositiveCompacts (v.adicCompletion K) := by
      ext x
      rw [coe_integerPositiveCompacts, v.integer_eq_adicCompletionIntegers, SetLike.mem_coe,
        SetLike.mem_coe, ValuationSubring.mem_toSubring]
    rw [h]
    exact addHaarMeasure_self
  -- The local factor at `v` is `|a_v|_v`, and it is `1` at all but finitely many places.
  have hloc (v : HeightOneSpectrum R) :
      μ v ((a : FiniteAdeleRing R K) v • (v.adicCompletionIntegers K : Set (v.adicCompletion K))) =
        (normalizedAbsoluteValue (v.adicCompletion K) ((a : FiniteAdeleRing R K) v) : ℝ≥0) := by
    rw [addHaar_smul_eq_normalizedAbsoluteValue_mul, hμ, mul_one]
  have hsupp : Function.HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
      (normalizedAbsoluteValue (v.adicCompletion K) ((a : FiniteAdeleRing R K) v) : ℝ≥0) := by
    refine hasFiniteMulSupport_iff_eventually_eq_one.mpr ?_
    filter_upwards [eventually_smul_adicCompletionIntegers a] with v hv
    have h := hloc v
    rw [hv, hμ] at h
    exact_mod_cast h.symm
  have hÔ : addHaarMeasure (integralAdelesPositiveCompacts R K) (integralAdeles R K) = 1 :=
    addHaarMeasure_self
  refine distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := addHaarMeasure (integralAdelesPositiveCompacts R K))
    (s := (integralAdeles R K : Set (FiniteAdeleRing R K))) (by simp [hÔ]) (by simp [hÔ]) ?_
  rw [hÔ, mul_one, addHaarMeasure_eq_restrictedAddHaar R K μ hμ, smul_integralAdeles]
  refine (restrictedAddHaar_box_eq_finprod _ _ _
    (eventually_smul_adicCompletionIntegers a)).trans ?_
  rw [finprod_congr hloc]
  exact (map_finprod ENNReal.ofNNRealHom hsupp).symm

/-- **Scaling of Haar measure on the finite adeles.** Multiplication by a finite idele `a` pushes
every additive Haar measure `μ` on the finite adele ring forward to `(∏ᶠ v, |a_v|_v)⁻¹ • μ`. -/
theorem map_mul_left_eq_inv_finprod_smul (μ : Measure (FiniteAdeleRing R K))
    [μ.IsAddHaarMeasure] (a : (FiniteAdeleRing R K)ˣ) :
    μ.map ((a : FiniteAdeleRing R K) * ·) =
      (∏ᶠ v : HeightOneSpectrum R,
        (normalizedAbsoluteValue (v.adicCompletion K) ((a : FiniteAdeleRing R K) v) : ℝ≥0))⁻¹ •
        μ := by
  rw [← distribHaarChar_eq_finprod, ← map_smul_eq_inv_distribHaarChar_smul]
  simp only [Units.smul_def, smul_eq_mul]

/-- The finite idele concentrated at a place `v` with component `u` scales additive Haar measure
on the finite adele ring by the Haar character of `u` on the completion `K_v`. -/
theorem distribHaarChar_unitsOfAdicCompletion (v : HeightOneSpectrum R)
    (u : (v.adicCompletion K)ˣ) :
    distribHaarChar (FiniteAdeleRing R K) (unitsOfAdicCompletion K v u) =
      distribHaarChar (v.adicCompletion K) u := by
  classical
  rw [distribHaarChar_eq_finprod, finprod_eq_single _ v fun w hw ↦ by
      rw [coe_unitsOfAdicCompletion_apply, ofAdicCompletion_apply_of_ne K hw, map_one,
        NNRat.cast_one],
    coe_unitsOfAdicCompletion_apply, ofAdicCompletion_apply_self,
    distribHaarChar_eq_normalizedAbsoluteValue]

/-- **The finite adeles have infinite Haar measure.** When `R` has a place `v`, every additive
Haar measure on the finite adele ring gives it infinite mass: multiplication by a uniformizer at
`v` scales the measure by `q_v⁻¹ ≠ 1` but preserves the whole space. -/
theorem addHaar_univ_eq_top [Nonempty (HeightOneSpectrum R)] (μ : Measure (FiniteAdeleRing R K))
    [μ.IsAddHaarMeasure] : μ Set.univ = ∞ := by
  obtain ⟨v⟩ := ‹Nonempty (HeightOneSpectrum R)›
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := v.adicCompletion K)
  have hchar : distribHaarChar (FiniteAdeleRing R K) (unitsOfAdicCompletion K v π) ≠ 1 := by
    rw [distribHaarChar_unitsOfAdicCompletion, distribHaarChar_of_isUniformizer hπ, ne_eq,
      inv_eq_one]
    exact_mod_cast Finite.one_lt_card.ne'
  have h := distribHaarChar_mul μ (unitsOfAdicCompletion K v π) Set.univ
  rw [Set.smul_set_univ] at h
  by_contra htop
  have h0 : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ ⟨0, Set.mem_univ _⟩).ne'
  exact hchar (by exact_mod_cast (ENNReal.mul_eq_right h0 htop).1 h)

end Restricted

/-! ### The normalization on completed ideals -/

section CompletedIdeal

variable {R K}

/-- **The measure of a completed ideal.** For a nonzero ideal `N` of `R` with `R ⧸ N` finite, the
completion `NÔ` of `N` in the integral finite adeles has `#(R ⧸ N)` times smaller measure than `Ô`
for every additively left-invariant measure on the finite adele ring: it has index `#(R ⧸ N)` in
`Ô`. -/
theorem natCard_mul_measure_image_completedIdeal (μ : Measure (FiniteAdeleRing R K))
    [μ.IsAddLeftInvariant] {N : Ideal R} (hN : N ≠ ⊥) [Finite (R ⧸ N)] :
    Nat.card (R ⧸ N) * μ (((↑) : integralAdeles R K → FiniteAdeleRing R K) ''
      (completedIdeal K N : Set (integralAdeles R K))) = μ (integralAdeles R K) := by
  have hemb : MeasurableEmbedding ((↑) : integralAdeles R K → FiniteAdeleRing R K) :=
    MeasurableEmbedding.subtypeVal (isOpen_integralAdeles R K).measurableSet
  have hindex : (completedIdeal K N).toAddSubgroup.index = Nat.card (R ⧸ N) :=
    (Submodule.cardQuot_apply _).trans
      (Nat.card_congr (quotientEquivQuotientCompletedIdeal K hN).toEquiv).symm
  have _ : (completedIdeal K N).toAddSubgroup.FiniteIndex := ⟨hindex ▸ Nat.card_pos.ne'⟩
  have h := (completedIdeal K N).toAddSubgroup.index_mul_measure
    (isOpen_completedIdeal K hN).measurableSet
    (μ.comap ((↑) : integralAdeles R K → FiniteAdeleRing R K))
  rwa [hindex, hemb.comap_apply, hemb.comap_apply, Set.image_univ, Subtype.range_coe] at h

/-- **The normalization on completed ideals.** For a nonzero ideal `N` of `R` with `R ⧸ N` finite,
the completion `NÔ` of `N` in the integral finite adeles has mass `#(R ⧸ N)⁻¹` for the additive
Haar measure giving `Ô` mass one. Over the ring of integers of a number field, `#(R ⧸ N)` is the
absolute norm `Ideal.absNorm N`. -/
theorem addHaarMeasure_image_completedIdeal [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
    {N : Ideal R} (hN : N ≠ ⊥) [Finite (R ⧸ N)] :
    addHaarMeasure (integralAdelesPositiveCompacts R K)
        (((↑) : integralAdeles R K → FiniteAdeleRing R K) ''
          (completedIdeal K N : Set (integralAdeles R K))) =
      (Nat.card (R ⧸ N) : ℝ≥0∞)⁻¹ := by
  have h := natCard_mul_measure_image_completedIdeal
    (addHaarMeasure (integralAdelesPositiveCompacts R K)) hN
  rw [← coe_integralAdelesPositiveCompacts, addHaarMeasure_self, mul_comm] at h
  exact ENNReal.eq_inv_of_mul_eq_one_left h

end CompletedIdeal

end IsDedekindDomain.FiniteAdeleRing
