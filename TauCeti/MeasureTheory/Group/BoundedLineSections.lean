/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Localization.Integer
import TauCeti.MeasureTheory.Group.Measure

/-!
# Sets with bounded line sections over a local field are null

Let `K` be a nonarchimedean local field and `ι` a finite type. A measurable set `Z ⊆ ι → K`
meeting every line `t ↦ x + t • v` of a fixed direction `v` in at most `D` points is null for
every translation-invariant measure on `ι → K` that is finite on compact sets, in particular for
Haar measure. This applies to the zero locus of a polynomial function whose restrictions to the
lines of some direction are nonzero polynomials of bounded degree in one variable. It is a
nonarchimedean counterpart of Mathlib's
`MeasureTheory.Measure.addHaar_eq_zero_of_disjoint_translates` for real vector spaces.

The argument needs no product structure on the measure, hence no comparison with a product of
Haar measures on `K` and no second countability of `K`. The scaled integer boxes
`{x | ϖ ^ k • x ∈ 𝒪[K] ^ ι}`, for a uniformizer `ϖ`, are compact subgroups exhausting `ι → K`,
and inside each of them the translates of `Z` by the infinitely many vectors `t • v`, `t ∈ 𝒪[K]`
(after rescaling `v` into the box), cover each point at most `D` times. This is
`MeasureTheory.Measure.measure_inter_addSubgroup_eq_zero_of_encard_le`.

## Main results

* `MeasureTheory.Measure.measure_eq_zero_of_encard_setOf_add_smul_mem_le`: a measurable set
  meeting every line of direction `v` in at most `D` points is null.
-/

public section

open Set ValuativeRel
open scoped ENNReal

namespace MeasureTheory.Measure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {ι : Type*} [Finite ι]
  [MeasurableSpace (ι → K)] [BorelSpace (ι → K)]

/-- **Sets with bounded line sections are null.** Let `Z ⊆ ι → K` be measurable, and suppose that
for some direction `v` and bound `D`, every line `t ↦ x + t • v` meets `Z` in at most `D` points.
Then `Z` is null for every translation-invariant measure on `ι → K` that is finite on compact
sets. -/
theorem measure_eq_zero_of_encard_setOf_add_smul_mem_le (μ : Measure (ι → K))
    [μ.IsAddLeftInvariant] [IsFiniteMeasureOnCompacts μ] {Z : Set (ι → K)} (hZ : MeasurableSet Z)
    (v : ι → K) {D : ℕ} (hD : ∀ x, {t : K | x + t • v ∈ Z}.encard ≤ D) : μ Z = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by simpa using hϖ.ne_zero
  -- The scaled integer boxes `{x | ϖ ^ k • x ∈ 𝒪[K] ^ ι}` are compact subgroups of `ι → K`.
  let H (k : ℕ) : AddSubgroup (ι → K) :=
    (AddSubgroup.pi univ fun _ ↦ (𝒪[K]).toAddSubgroup).comap
      (DistribSMul.toAddMonoidHom (ι → K) ((ϖ : K) ^ k))
  have hmemH {k : ℕ} {x : ι → K} : x ∈ H k ↔ ∀ i, (ϖ : K) ^ k * x i ∈ 𝒪[K] := by
    simp [H, AddSubgroup.mem_pi]
  have hcompact (k : ℕ) : IsCompact (H k : Set (ι → K)) := by
    have : (H k : Set (ι → K)) =
        Homeomorph.smulOfNeZero ((ϖ : K) ^ k) (pow_ne_zero k hϖ0) ⁻¹'
          univ.pi fun _ ↦ (𝒪[K] : Set K) := by
      ext x
      simp [hmemH]
    rw [this, Homeomorph.isCompact_preimage]
    exact isCompact_univ_pi fun _ ↦
      isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[K]))
  -- They exhaust `ι → K`: a power of `ϖ` clears the denominators of the coordinates of `x`.
  have hcover (x : ι → K) : ∃ k, x ∈ H k := by
    obtain ⟨⟨b, hb⟩, hbx⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[K]) x
    obtain ⟨k, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
    refine ⟨k, hmemH.mpr fun i ↦ ?_⟩
    obtain ⟨r, hr⟩ := hbx i
    have hu : ((↑u⁻¹ : 𝒪[K]) : K) * (u : 𝒪[K]) = 1 := by
      rw [← Subring.coe_mul, Units.inv_mul, Subring.coe_one]
    convert SetLike.coe_mem (↑u⁻¹ * r : 𝒪[K]) using 1
    simp only [← Algebra.algebraMap_ofSubsemiring_apply, hr, Algebra.smul_def, map_mul, map_pow]
    simp only [Algebra.algebraMap_ofSubsemiring_apply]
    linear_combination (-(ϖ : K) ^ k * x i) * hu
  -- Rescale `v` into the integer box, so that `(ϖ ^ k₀ * t) • v` lies in every `H k`.
  obtain ⟨k₀, hk₀⟩ := hcover v
  have : Infinite 𝒪[K] := by
    by_contra h
    have := not_infinite_iff_finite.mp h
    exact IsDiscreteValuationRing.not_isField 𝒪[K] (Finite.isField_of_domain 𝒪[K])
  rw [← inter_univ Z, ← iUnion_eq_univ_iff.mpr hcover, inter_iUnion]
  refine measure_iUnion_null fun k ↦ μ.measure_inter_addSubgroup_eq_zero_of_encard_le hZ
    (hcompact k).isClosed.measurableSet (hcompact k).measure_lt_top.ne
    (w := fun t : 𝒪[K] ↦ ((ϖ : K) ^ k₀ * t) • v) (fun t ↦ ?_) (D := D) fun x ↦ ?_
  · refine hmemH.mpr fun i ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, show (ϖ : K) ^ k * ((ϖ : K) ^ k₀ * t * v i) =
      (ϖ ^ k * t : 𝒪[K]) * ((ϖ : K) ^ k₀ * v i) by push_cast; ring]
    exact mul_mem (SetLike.coe_mem _) (hmemH.mp hk₀ i)
  · refine le_trans ?_ (hD x)
    rw [← (?_ : InjOn (fun t : 𝒪[K] ↦ (ϖ : K) ^ k₀ * t) _).encard_image]
    · exact encard_le_encard (by rintro _ ⟨t, ht, rfl⟩; exact ht)
    · intro s _ t _ hst
      simpa [pow_ne_zero k₀ hϖ0] using hst

end MeasureTheory.Measure
