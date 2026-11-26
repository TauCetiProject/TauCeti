/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
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
* `MeasureTheory.Measure.addHaar_smul_integer_of_irreducible`: the maximal ideal `ϖ • 𝒪[K]`
  has `q⁻¹` times the mass of `𝒪[K]`.
* `MeasureTheory.distribHaarChar_eq_normalizedAbsoluteValue`: the Haar character of `a ∈ Kˣ`
  is `|a|_K`; `MeasureTheory.distribHaarChar_eq_zpow` writes it as `q ^ (-v_K(a))`.
* `MeasureTheory.distribHaarChar_of_isUniformizer`: a uniformizer has character `q⁻¹`.
* `MeasureTheory.distribHaarChar_eq_one_iff`: the kernel of the character is the unit group
  of `𝒪[K]`.
* `Irreducible.distribHaarChar_unitsMk0`, `Units.distribHaarChar_map_subtype_eq_one`,
  `TauCeti.distribHaarChar_eq_one_of_mem_unitFiltration_zero`: character specializations on
  irreducible elements, valuation-ring units, and `unitFiltration K 0`.
* `MeasureTheory.Measure.addHaar_smul_eq_normalizedAbsoluteValue_mul`: `μ (a • s) = |a|_K μ s`
  for every `a ∈ K`, including `a = 0`.
* `MeasureTheory.Measure.map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul`: for `a ≠ 0`,
  multiplication by `a` pushes `μ` forward to `|a|_K⁻¹ • μ`.
* `MeasureTheory.Measure.addHaar_preimage_mul_left`,
  `MeasureTheory.Measure.map_units_mul_left_addHaar`,
  `MeasureTheory.Measure.map_mul_left_addHaar_of_isUniformizer`,
  `MeasureTheory.Measure.map_integerUnits_mul_left_addHaar`,
  `MeasureTheory.Measure.lintegral_mul_left_addHaar`,
  `MeasureTheory.Measure.integral_mul_left_addHaar`: preimage, pushforward, and integral change of
  variables under multiplication on `K`.
* `MeasureTheory.Measure.addHaar_setOf_normalizedAbsoluteValue_le`,
  `MeasureTheory.Measure.addHaar_setOf_normalizedAbsoluteValue_lt` and
  `MeasureTheory.Measure.addHaar_setOf_normalizedAbsoluteValue_eq`: the ball `|x|_K ≤ |a|_K`, the
  ball `|x|_K < |a|_K` and the sphere `|x|_K = |a|_K` have masses `|a|_K`, `q⁻¹ |a|_K` and
  `(1 - q⁻¹) |a|_K` times that of `𝒪[K]`.
* `TauCeti.measurableSet_setOf_normalizedAbsoluteValue_le`,
  `TauCeti.measurableSet_setOf_normalizedAbsoluteValue_lt` and
  `TauCeti.measurableSet_setOf_normalizedAbsoluteValue_eq`: these balls and spheres are
  measurable.
* `MeasureTheory.Measure.addHaar_setOf_valuation_eq_one`: the units of `𝒪[K]`, the elements of
  valuation one, have mass `(1 - q⁻¹) μ 𝒪[K]`.

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
  isCompact' := IsNonarchimedeanLocalField.isCompact_closedBall K 1
  interior_nonempty' := ⟨0, by
    rw [Valuation.isOpen_integer.interior_eq]
    exact zero_mem 𝒪[K]⟩

@[simp]
theorem coe_integerPositiveCompacts : (integerPositiveCompacts K : Set K) = 𝒪[K] :=
  (rfl)

/-- In a ring with a valuative topology, the elements of valuation one form a measurable set: they
are the sphere of radius one, which is closed (`Valuation.isClosed_sphere`). In a local field these
are the units of the ring of integers. -/
theorem measurableSet_setOf_valuation_eq_one {R : Type*} [Ring R] [ValuativeRel R]
    [TopologicalSpace R] [IsValuativeTopology R] [MeasurableSpace R] [OpensMeasurableSpace R] :
    MeasurableSet {x : R | valuation R x = 1} := by
  simpa only [Valuation.restrict_eq_one_iff] using ((valuation R).isClosed_sphere 1).measurableSet

/-- **The normalized Haar measure of a local field.** There is exactly one additive Haar measure
on `K` giving the ring of integers `𝒪[K]` mass one, namely
`MeasureTheory.Measure.addHaarMeasure (integerPositiveCompacts K)`. -/
theorem existsUnique_isAddHaarMeasure_measure_integer_eq_one [MeasurableSpace K]
    [BorelSpace K] : ∃! μ : Measure K, μ.IsAddHaarMeasure ∧ μ 𝒪[K] = 1 :=
  ⟨addHaarMeasure (integerPositiveCompacts K), ⟨inferInstance, addHaarMeasure_self⟩,
    fun μ ⟨_, hμ⟩ ↦ ((addHaarMeasure_eq_iff (integerPositiveCompacts K) μ).2 hμ).symm⟩

variable {K} in
/-- The dilate `a • 𝒪[K]` is the closed ball `|x|_K ≤ |a|_K`; for `a = 0` both are `{0}`. -/
theorem smul_integer_eq_setOf_normalizedAbsoluteValue_le (a : K) :
    a • (𝒪[K] : Set K) = {x | normalizedAbsoluteValue K x ≤ normalizedAbsoluteValue K a} := by
  rcases eq_or_ne a 0 with rfl | ha
  · ext x
    simp [Set.zero_smul_set (⟨0, zero_mem _⟩ : (𝒪[K] : Set K).Nonempty)]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha, SetLike.mem_coe,
    mem_integer_iff_normalizedAbsoluteValue_le_one, smul_eq_mul, map_mul, map_inv₀,
    Set.mem_ofPred_eq, inv_mul_le_one₀ ((normalizedAbsoluteValue K).pos ha)]

section MeasurableSet

variable {K} [MeasurableSpace K] [OpensMeasurableSpace K]

/-- The closed ball `|x|_K ≤ r` is measurable. -/
@[measurability]
theorem measurableSet_setOf_normalizedAbsoluteValue_le (r : ℚ≥0) :
    MeasurableSet {x : K | normalizedAbsoluteValue K x ≤ r} := by
  simp_rw [← NNRat.cast_le (K := ℝ)]
  exact (isClosed_le continuous_normalizedAbsoluteValue continuous_const).measurableSet

/-- The open ball `|x|_K < r` is measurable. -/
@[measurability]
theorem measurableSet_setOf_normalizedAbsoluteValue_lt (r : ℚ≥0) :
    MeasurableSet {x : K | normalizedAbsoluteValue K x < r} := by
  simp_rw [← NNRat.cast_lt (K := ℝ)]
  exact (isOpen_lt continuous_normalizedAbsoluteValue continuous_const).measurableSet

/-- The sphere `|x|_K = r` is measurable. -/
@[measurability]
theorem measurableSet_setOf_normalizedAbsoluteValue_eq (r : ℚ≥0) :
    MeasurableSet {x : K | normalizedAbsoluteValue K x = r} := by
  simp_rw [← NNRat.cast_inj (α := ℝ)]
  exact (isClosed_eq continuous_normalizedAbsoluteValue continuous_const).measurableSet

end MeasurableSet

end TauCeti

namespace MeasureTheory

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For every additive Haar measure on `K` and every uniformizer `ϖ`, the maximal ideal
`ϖ • 𝒪[K]` has `q⁻¹` times the mass of `𝒪[K]`, where `q` is the cardinality of the residue field:
the box formula `MeasureTheory.Measure.measure_univ_pi_image_maximalIdeal_pow` in one
coordinate. -/
theorem Measure.addHaar_smul_integer_of_irreducible [MeasurableSpace K] [BorelSpace K]
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
    hchar _ _ (by simpa [Units.smul_def] using μ.addHaar_smul_integer_of_irreducible hϖ)
  simp [hu', hϖ', normalizedValuation_irreducible hϖ, (normalizedValuation_eq_one_iff u).2 hu]

/-- **The Haar character of a local field is the normalized absolute value.** Multiplication
by `x ∈ Kˣ` scales additive Haar measure on `K` by `|x|_K`. -/
@[simp low]
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

end MeasureTheory

section LocalHaarCharacter

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace Irreducible

open TauCeti

/-- An irreducible element `π` of `𝒪[K]` viewed as a unit of `K` has distributive Haar character
`q⁻¹`. -/
@[grind =]
theorem distribHaarChar_unitsMk0 {π : 𝒪[K]} (hπ : Irreducible π) :
    distribHaarChar K (Units.mk0 (π : K) fun h ↦ hπ.ne_zero (Subtype.ext h)) =
      (Nat.card 𝓀[K] : ℝ≥0)⁻¹ := by
  rw [distribHaarChar_eq_zpow, normalizedValuation_irreducible hπ, toAdd_ofAdd, zpow_neg_one]

end Irreducible

namespace Units

open TauCeti

/-- **Character of a valuation-ring unit.** Every unit `u ∈ 𝒪[K]ˣ` has distributive Haar character
`1` on `K`. -/
@[simp, grind =]
theorem distribHaarChar_map_subtype_eq_one (u : 𝒪[K]ˣ) :
    distribHaarChar K (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) = 1 := by
  rw [distribHaarChar_eq_one_iff]
  exact (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation K))).1 u.isUnit

end Units

namespace TauCeti

/-- Every element of the depth-zero unit filtration `U(K, 0) = 𝒪[K]ˣ` has distributive Haar
character `1`. -/
@[grind =]
theorem distribHaarChar_eq_one_of_mem_unitFiltration_zero {u : Kˣ} (hu : u ∈ unitFiltration K 0) :
    distribHaarChar K u = 1 :=
  (distribHaarChar_eq_one_iff u).2 ((mem_unitFiltration_zero u).1 hu)

end TauCeti

end LocalHaarCharacter

namespace MeasureTheory.Measure

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsAddHaarMeasure]

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

/-- **Haar measure of a closed ball.** For every additive Haar measure `μ` on `K` and every
`a ∈ K`, the ball `|x|_K ≤ |a|_K` has mass `|a|_K μ(𝒪[K])`. -/
theorem addHaar_setOf_normalizedAbsoluteValue_le (a : K) :
    μ {x | normalizedAbsoluteValue K x ≤ normalizedAbsoluteValue K a} =
      (normalizedAbsoluteValue K a : ℝ≥0) * μ 𝒪[K] := by
  rw [← smul_integer_eq_setOf_normalizedAbsoluteValue_le,
    addHaar_smul_eq_normalizedAbsoluteValue_mul]

/-- **Haar measure of an open ball.** For every additive Haar measure `μ` on `K` and every
`a ∈ K`, the ball `|x|_K < |a|_K` has mass `q⁻¹ |a|_K μ(𝒪[K])`, where `q` is the cardinality of
the residue field. -/
theorem addHaar_setOf_normalizedAbsoluteValue_lt (a : K) :
    μ {x | normalizedAbsoluteValue K x < normalizedAbsoluteValue K a} =
      (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹ * (normalizedAbsoluteValue K a : ℝ≥0) * μ 𝒪[K] := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  -- The open ball of radius `|a|_K` is the closed ball of radius `|ϖ a|_K = q⁻¹ |a|_K`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h : {x | normalizedAbsoluteValue K x < normalizedAbsoluteValue K a} =
      {x | normalizedAbsoluteValue K x ≤ normalizedAbsoluteValue K ((ϖ : K) * a)} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, normalizedAbsoluteValue_lt_iff_le_inv_mul ha,
      map_mul, normalizedAbsoluteValue_irreducible hϖ]
  have hq : (Nat.card 𝓀[K] : ℝ≥0) ≠ 0 := natCard_residueField_pos.ne'
  rw [h, addHaar_setOf_normalizedAbsoluteValue_le, map_mul,
    normalizedAbsoluteValue_irreducible hϖ]
  simp [ENNReal.coe_inv hq]

/-- **Haar measure of a sphere.** For every additive Haar measure `μ` on `K` and every `a ∈ K`,
the sphere `|x|_K = |a|_K` has mass `(1 - q⁻¹) |a|_K μ(𝒪[K])`, where `q` is the cardinality of
the residue field. -/
theorem addHaar_setOf_normalizedAbsoluteValue_eq (a : K) :
    μ {x | normalizedAbsoluteValue K x = normalizedAbsoluteValue K a} =
      (1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹) * (normalizedAbsoluteValue K a : ℝ≥0) * μ 𝒪[K] := by
  have h : {x | normalizedAbsoluteValue K x = normalizedAbsoluteValue K a} =
      {x | normalizedAbsoluteValue K x ≤ normalizedAbsoluteValue K a} \
        {x | normalizedAbsoluteValue K x < normalizedAbsoluteValue K a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    exact ⟨fun h ↦ ⟨h.le, not_lt.2 h.ge⟩, fun h ↦ h.1.antisymm (not_lt.1 h.2)⟩
  have hmeas :=
    measurableSet_setOf_normalizedAbsoluteValue_lt (K := K) (normalizedAbsoluteValue K a)
  have hfin : μ 𝒪[K] ≠ ∞ :=
    (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_ne_top
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 natCard_residueField_pos.ne'
  rw [h, measure_sdiff (Set.ofPred_subset_ofPred.2 fun _ hx ↦ hx.le) hmeas.nullMeasurableSet
      (by rw [addHaar_setOf_normalizedAbsoluteValue_lt]; finiteness),
    addHaar_setOf_normalizedAbsoluteValue_le, addHaar_setOf_normalizedAbsoluteValue_lt,
    mul_assoc, mul_assoc, ENNReal.sub_mul (fun _ _ ↦ by finiteness), one_mul]

/-- **The Haar mass of the units.** The units of the ring of integers of a nonarchimedean local
field, the elements of valuation one, have Haar mass `(1 - q⁻¹) μ 𝒪[K]`, where `q` is the
cardinality of the residue field: they are the complement in `𝒪[K]` of the maximal ideal
`ϖ 𝒪[K]`, of mass `q⁻¹ μ 𝒪[K]`. -/
theorem addHaar_setOf_valuation_eq_one :
    μ {x : K | valuation K x = 1} = (1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹) * μ 𝒪[K] := by
  simpa using addHaar_setOf_normalizedAbsoluteValue_eq μ (1 : K)

section Scaling

/-- Preimage under `x ↦ a * x` (`a ≠ 0`) multiplies any additive Haar measure on `K` by
`|a|_K⁻¹`. -/
@[simp, grind =]
theorem addHaar_preimage_mul_left {a : K} (ha : a ≠ 0) (s : Set K) :
    μ ((a * ·) ⁻¹' s) = ((normalizedAbsoluteValue K a : ℝ≥0) : ℝ≥0∞)⁻¹ * μ s := by
  have hpre : (a * ·) ⁻¹' s = a⁻¹ • s := by
    ext x
    simp [Set.mem_smul_set, inv_mul_eq_iff_eq_mul₀ ha]
  rw [hpre, addHaar_smul_eq_normalizedAbsoluteValue_mul, map_inv₀, NNRat.cast_inv,
    ENNReal.coe_inv (coe_normalizedAbsoluteValue_ne_zero ha)]

/-- **Pushforward of additive Haar measure by a unit (valuation form).** For `a ∈ Kˣ` and any
additive Haar measure `μ` on `K`, `Measure.map (a * ·) μ = q ^ (v_K(a)) • μ`, where
`q = Nat.card 𝓀[K]`. -/
theorem map_units_mul_left_addHaar (a : Kˣ) :
    map ((a : K) * ·) μ =
      ((Nat.card 𝓀[K] : ℝ≥0) ^ (normalizedValuation K a).toAdd) • μ := by
  have hfun : ((a : K) * ·) = ((a : K) • ·) := funext fun x ↦ (smul_eq_mul (a : K) x).symm
  rw [hfun, map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul μ a.ne_zero,
    normalizedAbsoluteValue_coe]
  congr 1
  push_cast
  rw [zpow_neg, inv_inv]

/-- Multiplying by a uniformizer `ϖ ∈ Kˣ` pushes any additive Haar measure `μ` on `K` forward to
`q • μ`. -/
theorem map_mul_left_addHaar_of_isUniformizer {ϖ : Kˣ} (hϖ : IsUniformizer K ϖ) :
    map ((ϖ : K) * ·) μ = (Nat.card 𝓀[K] : ℝ≥0) • μ := by
  rw [map_units_mul_left_addHaar μ ϖ, (isUniformizer_def ϖ).1 hϖ, toAdd_ofAdd, zpow_one]

/-- **Valuation-ring units preserve additive Haar measure.** Left multiplication by any `u ∈ 𝒪[K]ˣ`
leaves every additive Haar measure on `K` invariant. -/
@[simp, grind =]
theorem map_integerUnits_mul_left_addHaar (u : 𝒪[K]ˣ) :
    map (((u : 𝒪[K]) : K) * ·) μ = μ := by
  have hfun : (((u : 𝒪[K]) : K) * ·) = (((u : 𝒪[K]) : K) • ·) :=
    funext fun x ↦ (smul_eq_mul _ x).symm
  rw [hfun, map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul μ (by simp)]
  simp

/-- Lower Lebesgue change of variables on `K` under `x ↦ a * x` (`a ≠ 0`). -/
theorem lintegral_mul_left_addHaar {a : K} (ha : a ≠ 0) (f : K → ℝ≥0∞) :
    ∫⁻ x, f (a * x) ∂μ = ((normalizedAbsoluteValue K a : ℝ≥0) : ℝ≥0∞)⁻¹ * ∫⁻ x, f x ∂μ := by
  let e : K ≃ᵐ K := MeasurableEquiv.mulLeft₀ a ha
  have h := lintegral_map_equiv f e (μ := μ)
  simp only [e, MeasurableEquiv.coe_mulLeft₀] at h
  have he : (fun x : K ↦ a * x) = (a • ·) := funext fun x ↦ (smul_eq_mul a x).symm
  rw [he, map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul μ ha, lintegral_smul_measure,
    ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv] at h
  · exact h.symm
  · exact coe_normalizedAbsoluteValue_ne_zero ha

/-- Bochner integral change of variables on `K` under `x ↦ a * x` (`a ≠ 0`). -/
theorem integral_mul_left_addHaar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : K} (ha : a ≠ 0) (f : K → F) :
    ∫ x, f (a * x) ∂μ = ((normalizedAbsoluteValue K a : ℝ)⁻¹) • ∫ x, f x ∂μ := by
  let e : K ≃ᵐ K := MeasurableEquiv.mulLeft₀ a ha
  have h := integral_map_equiv e f (μ := μ)
  simp only [e, MeasurableEquiv.coe_mulLeft₀] at h
  have he : (fun x : K ↦ a * x) = (a • ·) := funext fun x ↦ (smul_eq_mul a x).symm
  rw [he, map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul μ ha, integral_smul_nnreal_measure,
    NNReal.smul_def, NNReal.coe_inv] at h
  exact h.symm

end Scaling

end MeasureTheory.Measure
