/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.DiscreteValuationRing.FractionRing

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

variable {K : Type*} [Field K] [ValuativeRel K] {ι : Type*}

/-- The scaled integer box `{x | ϖ ^ k • x ∈ 𝒪[K] ^ ι}`, an additive subgroup of `ι → K`. -/
private noncomputable def scaledIntegerBox (ϖ : K) (k : ℕ) : AddSubgroup (ι → K) :=
  (AddSubgroup.pi univ fun _ ↦ (𝒪[K]).toAddSubgroup).comap
    (DistribSMul.toAddMonoidHom (ι → K) (ϖ ^ k))

/-- Membership in a scaled integer box, coordinate by coordinate. -/
private theorem mem_scaledIntegerBox {ϖ : K} {k : ℕ} {x : ι → K} :
    x ∈ scaledIntegerBox ϖ k ↔ ∀ i, ϖ ^ k * x i ∈ 𝒪[K] := by
  simp [scaledIntegerBox, AddSubgroup.mem_pi]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- A scaled integer box is compact: it is the preimage of `𝒪[K] ^ ι` under a homeomorphism. -/
private theorem isCompact_scaledIntegerBox {ϖ : K} (hϖ : ϖ ≠ 0) (k : ℕ) :
    IsCompact (scaledIntegerBox (ι := ι) ϖ k : Set (ι → K)) := by
  have : (scaledIntegerBox (ι := ι) ϖ k : Set (ι → K)) =
      Homeomorph.smulOfNeZero (ϖ ^ k) (pow_ne_zero k hϖ) ⁻¹' univ.pi fun _ ↦ (𝒪[K] : Set K) := by
    ext x
    simp [mem_scaledIntegerBox]
  rw [this, Homeomorph.isCompact_preimage]
  exact isCompact_univ_pi fun _ ↦
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[K]))

/-- For a uniformizer `ϖ` and a finite type `ι`, the scaled integer boxes exhaust `ι → K`: a power
of `ϖ` clears the denominators of the coordinates of `x`, since `K` is the localization of `𝒪[K]`
away from `ϖ`. -/
private theorem exists_mem_scaledIntegerBox [Finite ι] {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    (x : ι → K) : ∃ k, x ∈ scaledIntegerBox (ϖ : K) k := by
  have := TauCeti.isLocalizationAway_fractionRing (K := K) hϖ
  have h (i : ι) : ∀ᶠ k in Filter.atTop, (ϖ : K) ^ k * x i ∈ 𝒪[K] := by
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ϖ (x i)
    refine Filter.eventually_atTop.2 ⟨n, fun k hk ↦ ?_⟩
    rw [← Nat.sub_add_cancel hk, pow_add, mul_assoc, mul_comm _ (x i)]
    exact mul_mem (pow_mem ϖ.2 _) (ha ▸ a.2)
  exact (Filter.eventually_all.2 h).exists.imp fun _ ↦ mem_scaledIntegerBox.2

variable [Finite ι] [MeasurableSpace (ι → K)] [BorelSpace (ι → K)]

/-- **Sets with bounded line sections are null.** Let `Z ⊆ ι → K` be measurable, and suppose that
for some direction `v` and bound `D`, every line `t ↦ x + t • v` meets `Z` in at most `D` points.
Then `Z` is null for every translation-invariant measure on `ι → K` that is finite on compact
sets. -/
theorem measure_eq_zero_of_encard_setOf_add_smul_mem_le (μ : Measure (ι → K))
    [μ.IsAddLeftInvariant] [IsFiniteMeasureOnCompacts μ] {Z : Set (ι → K)} (hZ : MeasurableSet Z)
    (v : ι → K) {D : ℕ} (hD : ∀ x, {t : K | x + t • v ∈ Z}.encard ≤ D) : μ Z = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by simpa using hϖ.ne_zero
  -- Rescale `v` into the integer box, so that `(ϖ ^ k₀ * t) • v` lies in every scaled box.
  obtain ⟨k₀, hk₀⟩ := exists_mem_scaledIntegerBox hϖ v
  rw [← inter_univ Z, ← iUnion_eq_univ_iff.mpr (exists_mem_scaledIntegerBox hϖ), inter_iUnion]
  refine measure_iUnion_null fun k ↦ μ.measure_inter_addSubgroup_eq_zero_of_encard_le hZ
    (isCompact_scaledIntegerBox hϖ0 k).isClosed.measurableSet
    (isCompact_scaledIntegerBox hϖ0 k).measure_lt_top.ne
    (w := fun t : 𝒪[K] ↦ ((ϖ : K) ^ k₀ * t) • v) (fun t ↦ ?_) (D := D) fun x ↦ ?_
  · refine mem_scaledIntegerBox.mpr fun i ↦ ?_
    have h : (ϖ : K) ^ k * ((ϖ : K) ^ k₀ * t * v i) =
        (ϖ ^ k * t : 𝒪[K]) * ((ϖ : K) ^ k₀ * v i) := by
      push_cast; ring
    rw [Pi.smul_apply, smul_eq_mul, h]
    exact mul_mem (SetLike.coe_mem _) (mem_scaledIntegerBox.mp hk₀ i)
  · refine le_trans ?_ (hD x)
    rw [← (?_ : InjOn (fun t : 𝒪[K] ↦ (ϖ : K) ^ k₀ * t) _).encard_image]
    · exact encard_le_encard (by rintro _ ⟨t, ht, rfl⟩; exact ht)
    · intro s _ t _ hst
      simpa [pow_ne_zero k₀ hϖ0] using hst

end MeasureTheory.Measure
