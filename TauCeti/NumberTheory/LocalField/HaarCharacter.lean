/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.MeasureTheory.Group.LocalFieldScaling
import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.RingTheory.Valuation.Integers
import TauCeti.RingTheory.Valuation.ValuationRing

/-!
# The Haar character of a nonarchimedean local field

Let `K` be a nonarchimedean local field whose residue field has `q` elements. The ring of
integers `𝒪[K]` is a compact open subgroup of `K`, so there is exactly one additive Haar measure
on `K` giving it mass one; at a finite place of a number field this is the local measure `dx_v`
from which the Haar measures of the adeles are assembled.

Multiplication by a unit `a` of `K` carries additive Haar measure to a multiple of itself, and
the factor is Mathlib's distributive Haar character `MeasureTheory.distribHaarChar K a`. This
file identifies that character with the normalized absolute value:

`distribHaarChar K a = |a|_K = q ^ (-v_K(a))`,

where `v_K` is the normalized valuation, so that a uniformizer scales Haar measure by `q⁻¹`
and the units of `𝒪[K]` preserve it. Equivalently, `μ (a • s) = |a|_K * μ s` for every additive
Haar measure `μ` and every set `s`, and `a ≠ 0` pushes `μ` forward to `|a|_K⁻¹ • μ`. The
statements hold in every characteristic: no argument here uses characteristic zero.

The computation reduces to a uniformizer `ϖ`. The maximal ideal `ϖ • 𝒪[K]` has index `q` in
`𝒪[K]`, so it has `q⁻¹` times the mass of `𝒪[K]`
(`MeasureTheory.Measure.measure_univ_pi_image_maximalIdeal_pow` in one coordinate); a unit of
`𝒪[K]` maps `𝒪[K]` onto itself; and every unit of `K` is a unit of `𝒪[K]` times a power of `ϖ`.

## Main definitions

* `TauCeti.integerPositiveCompacts`: the ring of integers as a compact set with nonempty
  interior, the normalizing set of Mathlib's `MeasureTheory.Measure.addHaarMeasure`.

## Main results

* `TauCeti.existsUnique_isAddHaarMeasure_measure_integer_eq_one`: there is exactly one additive
  Haar measure on `K` giving `𝒪[K]` mass one.
* `MeasureTheory.distribHaarChar_eq_normalizedAbsoluteValue`: the Haar character of `a ∈ Kˣ`
  is `|a|_K`; `MeasureTheory.distribHaarChar_eq_zpow` writes it as `q ^ (-v_K(a))`.
* `MeasureTheory.distribHaarChar_of_isUniformizer`: a uniformizer has character `q⁻¹`.
* `MeasureTheory.distribHaarChar_eq_one_iff`: the kernel of the character is the unit group
  of `𝒪[K]`.
* `MeasureTheory.Measure.addHaar_smul_eq_normalizedAbsoluteValue_mul`: `μ (a • s) = |a|_K μ s`
  for every `a ∈ K`, including `a = 0`.
* `MeasureTheory.Measure.map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul`: for `a ≠ 0`,
  multiplication by `a` pushes `μ` forward to `|a|_K⁻¹ • μ`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., §3.5, pp. 186–187 (the modulus of an automorphism of a local field).
* A. V. Sutherland, *Number Theory I*, MIT 18.785 lecture notes, Lecture 23, §23.3, p. 6.
-/

public section

open MeasureTheory Measure ValuativeRel TopologicalSpace
open scoped NNReal ENNReal Pointwise

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The ring of integers `𝒪[K]` of a nonarchimedean local field, as a compact set with nonempty
interior: it is compact, and open since the topology of `K` is valuative. Mathlib's
`MeasureTheory.Measure.addHaarMeasure` at this set is the additive Haar measure giving `𝒪[K]`
mass one. -/
noncomputable def integerPositiveCompacts : PositiveCompacts K where
  carrier := 𝒪[K]
  isCompact' := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[K]))
  interior_nonempty' := ⟨0, by
    rw [Valuation.isOpen_integer.interior_eq]
    exact zero_mem 𝒪[K]⟩

@[simp]
theorem coe_integerPositiveCompacts : (integerPositiveCompacts K : Set K) = 𝒪[K] :=
  (rfl)

/-- **The normalized Haar measure of a local field.** There is exactly one additive Haar measure
on `K` giving the ring of integers `𝒪[K]` mass one, namely
`MeasureTheory.Measure.addHaarMeasure (integerPositiveCompacts K)`. -/
theorem existsUnique_isAddHaarMeasure_measure_integer_eq_one [MeasurableSpace K]
    [BorelSpace K] : ∃! μ : Measure K, μ.IsAddHaarMeasure ∧ μ 𝒪[K] = 1 :=
  ⟨addHaarMeasure (integerPositiveCompacts K), ⟨inferInstance, addHaarMeasure_self⟩,
    fun μ ⟨_, hμ⟩ ↦ ((addHaarMeasure_eq_iff (integerPositiveCompacts K) μ).2 hμ).symm⟩

end TauCeti

namespace MeasureTheory

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For every additive Haar measure on `K` and every uniformizer `ϖ`, the maximal ideal
`ϖ • 𝒪[K]` has `q⁻¹` times the mass of `𝒪[K]`, where `q` is the cardinality of the residue field:
the box formula `MeasureTheory.Measure.measure_univ_pi_image_maximalIdeal_pow` in one
coordinate. -/
private theorem measure_smul_integer_of_irreducible [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    μ ((ϖ : K) • (𝒪[K] : Set K)) = (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹ * μ 𝒪[K] := by
  have hm : ((↑) : 𝒪[K] → K) '' ↑𝓂[K] = (ϖ : K) • (𝒪[K] : Set K) := by
    simpa using hϖ.image_maximalIdeal_pow_eq_smul (A := K) 1
  simpa [integerBox_def, pi_pi, hm] using
    measure_univ_pi_image_maximalIdeal_pow (Measure.pi fun _ : Unit ↦ μ) (fun _ ↦ 1)

/-- **The Haar character of a local field.** Multiplication by `x ∈ Kˣ` scales additive Haar
measure on `K` by `q ^ (-v_K(x))`, where `q` is the cardinality of the residue field and `v_K`
the normalized valuation. -/
theorem distribHaarChar_eq_zpow (x : Kˣ) :
    distribHaarChar K x = (Nat.card 𝓀[K] : ℝ≥0) ^ (-(normalizedValuation K x).toAdd) := by
  borelize K
  -- Read the character off the mass of `x • 𝒪[K]` for the Haar measure normalized on `𝒪[K]`.
  let μ := addHaarMeasure (integerPositiveCompacts K)
  have h𝒪 : μ 𝒪[K] = 1 := addHaarMeasure_self
  have hchar (y : Kˣ) (r : ℝ≥0) (h : μ (y • (𝒪[K] : Set K)) = r * μ 𝒪[K]) :
      distribHaarChar K y = r :=
    distribHaarChar_eq_of_measure_smul_eq_mul (by simp [h𝒪]) (by simp [h𝒪]) h
  -- Write `x = u * ϖ ^ n` with `u` a unit of `𝒪[K]` and `ϖ` a uniformizer.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨u, n, hu, rfl⟩ := exists_eq_mul_zpow_of_irreducible hϖ x
  have hu' : distribHaarChar K u = 1 :=
    hchar u 1 (by rw [(valuation K).units_smul_integer hu, ENNReal.coe_one, one_mul])
  have hϖ' : distribHaarChar K (Units.mk0 (ϖ : K) fun h ↦ hϖ.ne_zero (Subtype.ext h)) =
      (Nat.card 𝓀[K] : ℝ≥0)⁻¹ :=
    hchar _ _ (by simpa [Units.smul_def] using measure_smul_integer_of_irreducible μ hϖ)
  simp [hu', hϖ', normalizedValuation_irreducible hϖ, (normalizedValuation_eq_one_iff u).2 hu]

/-- **The Haar character of a local field is the normalized absolute value.** Multiplication
by `x ∈ Kˣ` scales additive Haar measure on `K` by `|x|_K`. -/
@[simp]
theorem distribHaarChar_eq_normalizedAbsoluteValue (x : Kˣ) :
    distribHaarChar K x = normalizedAbsoluteValue K (x : K) := by
  rw [distribHaarChar_eq_zpow, normalizedAbsoluteValue_coe, NNRat.cast_zpow, NNRat.cast_natCast]

/-- A uniformizer scales additive Haar measure by `q⁻¹`, where `q` is the cardinality of the
residue field. -/
theorem distribHaarChar_of_isUniformizer {π : Kˣ} (hπ : IsUniformizer K π) :
    distribHaarChar K π = (Nat.card 𝓀[K] : ℝ≥0)⁻¹ := by
  rw [distribHaarChar_eq_zpow, (isUniformizer_def π).1 hπ]
  simp

/-- The kernel of the Haar character is the unit group of `𝒪[K]`: multiplication by `x ∈ Kˣ`
preserves additive Haar measure exactly when `x` has valuation one. -/
theorem distribHaarChar_eq_one_iff (x : Kˣ) :
    distribHaarChar K x = 1 ↔ valuation K (x : K) = 1 := by
  rw [distribHaarChar_eq_normalizedAbsoluteValue, ← normalizedAbsoluteValue_eq_one_iff]
  exact_mod_cast Iff.rfl

namespace Measure

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- **Scaling of Haar measure on a local field.** For every additive Haar measure `μ` on `K`,
every `a ∈ K` and every set `s`, `μ (a • s) = |a|_K * μ s`. -/
@[simp]
theorem addHaar_smul_eq_normalizedAbsoluteValue_mul (a : K) (s : Set K) :
    μ (a • s) = (normalizedAbsoluteValue K a : ℝ≥0) * μ s := by
  have hunit (b : K) (hb : b ≠ 0) (t : Set K) :
      μ (b • t) = (normalizedAbsoluteValue K b : ℝ≥0) * μ t := by
    have h := distribHaarChar_mul μ (Units.mk0 b hb) t
    rwa [distribHaarChar_eq_normalizedAbsoluteValue, Units.val_mk0, eq_comm] at h
  rcases ne_or_eq a 0 with ha | rfl
  · exact hunit a ha s
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  -- `0 • s = {0}`, a coordinate hyperplane of the integer box of `Unit → K`.
  rw [Set.zero_smul_set hs, AbsoluteValue.map_zero, NNRat.cast_zero, ENNReal.coe_zero, zero_mul]
  have h0 : integerBox K Unit ∩ {a | a () = 0} = Set.univ.pi fun _ ↦ ({0} : Set K) := by
    ext a
    refine ⟨fun h _ _ ↦ h.2, fun h ↦ ⟨mem_integerBox.2 fun i ↦ ?_, h () trivial⟩⟩
    rw [h i trivial]
    exact zero_mem _
  have h := measure_integerBox_inter_coord_eq_zero (Measure.pi fun _ : Unit ↦ μ)
    (by simpa [integerBox_def, pi_pi] using (integerPositiveCompacts K).isCompact.measure_ne_top) ()
  rwa [h0, pi_pi, Fintype.prod_unique] at h

/-- **Pushforward of Haar measure on a local field.** For `a ≠ 0`, multiplication by `a` pushes
every additive Haar measure `μ` on `K` forward to `|a|_K⁻¹ • μ`. -/
theorem map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul {a : K} (ha : a ≠ 0) :
    μ.map (a • ·) = (normalizedAbsoluteValue K a : ℝ≥0)⁻¹ • μ := by
  ext s hs
  rw [map_apply (measurable_const_smul a) hs, Set.preimage_smul₀ ha,
    addHaar_smul_eq_normalizedAbsoluteValue_mul, map_inv₀, smul_apply]
  simp

end Measure

end MeasureTheory
