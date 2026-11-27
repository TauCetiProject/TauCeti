/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.NumberTheory.HeckeRing.CosetSystem.Basic

/-!
# The volume of a double coset

Let `μ` be a left-invariant measure on a group `G` and `H`, `K` subgroups with `K` measurable. A
finite coset system `HgK = ⊔ᵢ reps i • K` (`Subgroup.IsCosetSystem`) is a finite disjoint union of
left translates of `K`, each of measure `μ K`, so

`μ (HgK) = #ι · μ K`

in `ℝ≥0∞` (`Subgroup.IsCosetSystem.measure_doubleCoset`). Only left invariance is used, so no
Haar or unimodularity hypothesis is needed, and the count is the same for every coset system of
`HgK`. Taking `H = ⊤` and `g = 1` recovers `Subgroup.index_mul_measure`, `K.index * μ K = μ univ`.

When `μ K` is finite and nonzero, as for a Haar measure and a compact open subgroup `K`, the count
is read off from the measures, `#ι = μ (HgK) / μ K`; this is what identifies the number of terms
in the Hecke sum `∑ᵢ ρ(reps i)` with the integral of the characteristic function of `HgK`. For a
Hecke triple the count is the degree of the double coset (`HeckeCoset.measure_toSet`).

## Main results

* `Subgroup.IsCosetSystem.measure_doubleCoset`: `μ (HgK) = #ι · μ K`.
* `Subgroup.IsCosetSystem.natCard_eq_measure_doubleCoset_div`: `#ι = μ (HgK) / μ K`.
* `Subgroup.IsCosetSystem.measure_doubleCoset_lt_top`: a double coset with a finite coset system
  has finite measure when `μ K` is finite.
* `Subgroup.measure_le_measure_doubleCoset` and `Subgroup.measure_doubleCoset_pos`: a double coset
  is at least as large as `K`, so it has positive measure when `K` is open.
* `HeckeCoset.measure_toSet`: for a Hecke triple, `μ (HδK) = deg(HδK) · μ K`.

The proof of `Subgroup.IsCosetSystem.measure_doubleCoset` follows that of Mathlib's
`Subgroup.index_mul_measure`: countable additivity over the disjoint translates, and
`measure_smul` for each of them.
-/

public section

open MeasureTheory Measure

open scoped ENNReal Pointwise

open DoubleCoset

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableConstSMul G G]

namespace Subgroup

variable {H K : Subgroup G} {g : G} {ι : Type*} {reps : ι → G}

/-- For a left-invariant measure, a double coset `HgK` is at least as large as `K`: it contains the
translate `g • K`. -/
theorem measure_le_measure_doubleCoset {μ : Measure G} [μ.IsMulLeftInvariant] (H K : Subgroup G)
    (g : G) : μ K ≤ μ (doubleCoset g H K) := by
  rw [← measure_smul μ g (K : Set G)]
  refine measure_mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact mem_doubleCoset.mpr ⟨1, H.one_mem, k, hk, by simp⟩

/-- A double coset `HgK` of an open subgroup `K` has positive measure for a left-invariant measure
that is positive on open sets. -/
theorem measure_doubleCoset_pos [TopologicalSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    [μ.IsOpenPosMeasure] (H : Subgroup G) (hK : IsOpen (K : Set G)) (g : G) :
    0 < μ (doubleCoset g H K) :=
  (hK.measure_pos μ ⟨1, K.one_mem⟩).trans_le (measure_le_measure_doubleCoset H K g)

namespace IsCosetSystem

/-- **The volume of a double coset.** For a left-invariant measure `μ`, a measurable subgroup `K`
and a finite coset system `HgK = ⊔ᵢ reps i • K`, the double coset has measure `#ι · μ K`. -/
theorem measure_doubleCoset [Finite ι] (h : IsCosetSystem H K g reps)
    (hK : MeasurableSet (K : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    μ (doubleCoset g H K) = Nat.card ι * μ K := by
  have := Fintype.ofFinite ι
  rw [← h.iUnion_smul_eq, measure_iUnion h.pairwise_disjoint fun i ↦ hK.const_smul (reps i),
    tsum_fintype]
  simp [measure_smul, Nat.card_eq_fintype_card]

/-- **The number of members of a coset system as a ratio of volumes**: when `μ K` is finite and
nonzero, `#ι = μ (HgK) / μ K`. -/
theorem natCard_eq_measure_doubleCoset_div [Finite ι] (h : IsCosetSystem H K g reps)
    (hK : MeasurableSet (K : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] (h₀ : μ K ≠ 0)
    (hTop : μ K ≠ ∞) : (Nat.card ι : ℝ≥0∞) = μ (doubleCoset g H K) / μ K := by
  rw [h.measure_doubleCoset hK μ, ENNReal.mul_div_cancel_right h₀ hTop]

/-- A double coset with a finite coset system has finite measure as soon as `K` does. No
measurability is needed: the double coset is covered by finitely many translates of `K`. -/
theorem measure_doubleCoset_lt_top [Finite ι] (h : IsCosetSystem H K g reps) (μ : Measure G)
    [μ.IsMulLeftInvariant] (hK : μ K ≠ ∞) : μ (doubleCoset g H K) < ∞ := by
  have := Fintype.ofFinite ι
  calc μ (doubleCoset g H K) ≤ ∑ i, μ (reps i • (K : Set G)) := by
        rw [← h.iUnion_smul_eq]
        exact measure_iUnion_fintype_le μ _
    _ = Fintype.card ι * μ K := by simp [measure_smul]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hK.lt_top

end IsCosetSystem

end Subgroup

namespace HeckeCoset

open Subgroup

variable {Δ : Submonoid G} {H K : Subgroup G} [IsHeckeTriple Δ H K]

/-- **The volume of a Hecke double coset.** For a Hecke triple `(H, Δ, K)` with `K` measurable and
a left-invariant measure `μ`, the double coset `D = HδK` has measure `D.degree · μ K`. -/
theorem measure_toSet (D : HeckeCoset Δ H K) (hK : MeasurableSet (K : Set G)) (μ : Measure G)
    [μ.IsMulLeftInvariant] : μ D.toSet = D.degree * μ K := by
  obtain ⟨reps, h⟩ := D.exists_isCosetSystem_fin_degree
  rw [toSet_eq_doubleCoset_rep, h.measure_doubleCoset hK μ, Nat.card_fin]

end HeckeCoset
