/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Bases
public import TauCeti.Topology.Algebra.GroupAction.FreeLocus

/-!
# Fundamental domains of properly discontinuous actions

Let a countable group `G` act properly discontinuously on a second countable, locally compact
Hausdorff space `X`. Every point with trivial stabilizer has a neighbourhood disjoint from all
of its nontrivial translates. Enumerating the basic open sets with this property as
`V₀, V₁, …` and keeping, from each `Vₙ`, the points whose orbit misses `V₀, …, Vₙ₋₁`, gives a
Borel set `s` that meets every orbit of a free point exactly once, and meets no orbit twice.

Consequently, for any measure `μ` on `X` for which the non-free points form a null set, `s` is
a measurable fundamental domain for `G` in the sense of `MeasureTheory.IsFundamentalDomain`
(`MeasureTheory.Measure.exists_isFundamentalDomain_of_properlyDiscontinuousSMul`). Its translates
are not merely almost everywhere disjoint but genuinely disjoint. Together with
`MeasureTheory.IsFundamentalDomain.measure_eq` this makes the covolume
`MeasureTheory.covolume G X μ` the measure of any measurable fundamental domain.

A discrete subgroup `Γ` of a second countable, locally compact Hausdorff group acts properly
discontinuously and freely on the right, so this gives a measurable fundamental domain for the
right action of `Γ` (`Subgroup.exists_isFundamentalDomain_op`, `Subgroup.hasFundamentalDomain_op`).

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.1.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §3.1.
-/

public section

open MeasureTheory Set TopologicalSpace

open scoped Pointwise

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]

/-- The measurable set underlying
`MeasureTheory.Measure.exists_isFundamentalDomain_of_properlyDiscontinuousSMul`:
from each set `V n` keep the points whose orbit misses every earlier `V k`. -/
private def firstHitSet (V : ℕ → Set X) : Set X :=
  ⋃ n, V n \ ⋃ k < n, ⋃ g : G, g • V k

variable [SecondCountableTopology X] [T2Space X] [LocallyCompactSpace X]
  [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]

/-- In a second countable space with a properly discontinuous action there is a sequence of
open sets, each disjoint from its nontrivial translates, that covers the free locus. -/
theorem exists_seq_isOpen_disjoint_smul :
    ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧
      (∀ n (g : G), g ≠ 1 → Disjoint (g • V n) (V n)) ∧
      ∀ x ∈ (freeLocus G X : Set X), ∃ n, x ∈ V n := by
  obtain ⟨b, hbc, -, hb⟩ := exists_countable_basis X
  let S : Set (Set X) := insert ∅ {U ∈ b | ∀ g : G, g ≠ 1 → Disjoint (g • U) U}
  have hSc : S.Countable := (hbc.mono (sep_subset _ _)).insert ∅
  obtain ⟨V, hV⟩ := hSc.exists_eq_range (insert_nonempty _ _)
  have hVS : ∀ n, V n ∈ S := fun n ↦ by rw [hV]; exact mem_range_self n
  refine ⟨V, fun n ↦ ?_, fun n g hg ↦ ?_, fun x hx ↦ ?_⟩
  · rcases hVS n with h | h
    · simp [h]
    · exact hb.isOpen h.1
  · rcases hVS n with h | h
    · simp [h]
    · exact h.2 g hg
  · obtain ⟨U, hU, hUx⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image G x
    obtain ⟨W, hWb, hxW, hWU⟩ := hb.mem_nhds_iff.mp hU
    have hWS : W ∈ S := by
      refine mem_insert_of_mem _ ⟨hWb, fun g hg ↦ ?_⟩
      have hgx : g • x ≠ x := fun hgx ↦ hg <| by
        have hmem : g ∈ MulAction.stabilizer G x := hgx
        rwa [(mem_freeLocus G X).mp hx, Subgroup.mem_bot] at hmem
      rw [← image_smul]
      exact (hUx g hgx).mono (image_mono hWU) hWU
    obtain ⟨n, hn⟩ : W ∈ range V := by rwa [← hV]
    exact ⟨n, hn ▸ hxW⟩

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
  [SecondCountableTopology X] [T2Space X] [LocallyCompactSpace X]
  [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
  [Countable G] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **Existence of a measurable fundamental domain.** A countable group acting properly
discontinuously on a second countable, locally compact Hausdorff space has a measurable
fundamental domain with respect to every measure for which the points with nontrivial stabilizer
form a null set. The translates of the domain by distinct elements are disjoint. -/
theorem exists_isFundamentalDomain_of_properlyDiscontinuousSMul (μ : Measure X)
    (hμ : μ (freeLocus G X : Set X)ᶜ = 0) :
    ∃ s : Set X, MeasurableSet s ∧ (Pairwise fun g h : G ↦ Disjoint (g • s) (h • s)) ∧
      IsFundamentalDomain G s μ := by
  obtain ⟨V, hVo, hVd, hVcov⟩ := exists_seq_isOpen_disjoint_smul (G := G) (X := X)
  -- a point of `firstHitSet V` lies in `V n` for an `n` its orbit reaches first
  have hmem : ∀ {y}, y ∈ firstHitSet (G := G) V ↔
      ∃ n, y ∈ V n ∧ ∀ k < n, ∀ g : G, y ∉ g • V k := by
    intro y
    simp [firstHitSet]
  have hdisj : Pairwise fun g h : G ↦
      Disjoint (g • firstHitSet (G := G) V) (h • firstHitSet (G := G) V) := by
    intro g h hgh
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba : h • b = g • a⟩
    obtain ⟨n, han, hn⟩ := hmem.mp ha
    obtain ⟨m, hbm, hm⟩ := hmem.mp hb
    have hb' : b = (h⁻¹ * g) • a := by rw [mul_smul, ← hba, inv_smul_smul]
    have ha' : a = (g⁻¹ * h) • b := by rw [mul_smul, hba, inv_smul_smul]
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · exact hm n hnm _ (hb' ▸ smul_mem_smul_set han)
    · refine Set.disjoint_left.mp (hVd n (h⁻¹ * g) ?_) (hb' ▸ smul_mem_smul_set han) hbm
      rwa [Ne, inv_mul_eq_one, eq_comm]
    · exact hn m hmn _ (ha' ▸ smul_mem_smul_set hbm)
  have hmeas : MeasurableSet (firstHitSet (G := G) V) :=
    MeasurableSet.iUnion fun n ↦ (hVo n).measurableSet.diff <|
      MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦
        MeasurableSet.iUnion fun g ↦ ((hVo k).smul g).measurableSet
  refine ⟨firstHitSet V, hmeas, hdisj,
    ⟨hmeas.nullMeasurableSet, ?_, fun g h hgh ↦ (hdisj hgh).aedisjoint⟩⟩
  · refine measure_mono_null (fun x hx ↦ ?_) hμ
    intro hfree
    classical
    have hex : ∃ n, ∃ g : G, g • x ∈ V n :=
      (hVcov x hfree).imp fun n hn ↦ ⟨1, by rwa [one_smul]⟩
    obtain ⟨g, hg⟩ := Nat.find_spec hex
    refine hx ⟨g, hmem.mpr ⟨Nat.find hex, hg, fun k hk h hmemk ↦ ?_⟩⟩
    refine Nat.find_min hex hk ⟨h⁻¹ * g, ?_⟩
    obtain ⟨y, hy, hyx⟩ := hmemk
    rwa [mul_smul, ← hyx, inv_smul_smul]

end MeasureTheory.Measure

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

/-- A discrete subgroup `Γ` of a second countable, locally compact Hausdorff group `G` has a
measurable fundamental domain for its right action on `G`, for every measure. -/
theorem exists_isFundamentalDomain_op (μ : Measure G) :
    ∃ s : Set G, MeasurableSet s ∧ IsFundamentalDomain Γ.op s μ := by
  have : Countable Γ := countable_of_Lindelof_of_discrete
  have : ProperlyDiscontinuousSMul Γ.op G :=
    Γ.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite
      (Γ.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr ‹_›))
  have hfree : (TauCeti.freeLocus Γ.op G : Set G) = univ :=
    eq_univ_of_forall fun x ↦ by
      simp [TauCeti.mem_freeLocus, Subgroup.eq_bot_iff_forall, MulAction.mem_stabilizer_iff]
  obtain ⟨s, hs, -, h⟩ :=
    μ.exists_isFundamentalDomain_of_properlyDiscontinuousSMul (G := Γ.op) (by simp [hfree])
  exact ⟨s, hs, h⟩

/-- In a second countable, locally compact Hausdorff group, a discrete subgroup has a
fundamental domain for its right action. -/
theorem hasFundamentalDomain_op (μ : Measure G) : HasFundamentalDomain Γ.op G μ :=
  ⟨(Γ.exists_isFundamentalDomain_op μ).imp fun _ ↦ And.right⟩

end Subgroup
