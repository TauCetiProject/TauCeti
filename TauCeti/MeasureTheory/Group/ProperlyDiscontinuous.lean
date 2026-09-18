/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
(`TauCeti.exists_isFundamentalDomain_of_properlyDiscontinuousSMul`). Its translates are not
merely almost everywhere disjoint but genuinely disjoint. Together with
`MeasureTheory.IsFundamentalDomain.measure_eq` this makes the covolume
`MeasureTheory.covolume G X μ` the measure of any measurable fundamental domain.

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

/-- The measurable set underlying `exists_isFundamentalDomain_of_properlyDiscontinuousSMul`:
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
  · obtain ⟨U, hU, hUx⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
    obtain ⟨W, hWb, hxW, hWU⟩ := hb.mem_nhds_iff.mp hU
    have hWS : W ∈ S := by
      refine mem_insert_of_mem _ ⟨hWb, fun g hg ↦ ?_⟩
      rw [Set.disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
      intro hne
      refine hg ?_
      have hgx : g • x = x := hUx g <| hne.mono <| inter_subset_inter
        (by rw [← image_smul]; exact image_mono hWU) hWU
      have hmem : g ∈ MulAction.stabilizer G x := hgx
      rwa [(mem_freeLocus G X).mp hx, Subgroup.mem_bot] at hmem
    obtain ⟨n, hn⟩ : W ∈ range V := by rwa [← hV]
    exact ⟨n, hn ▸ hxW⟩

variable [Countable G] [MeasurableSpace X] [OpensMeasurableSpace X]

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
      MeasurableSet.biUnion (to_countable _) fun k _ ↦
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

end TauCeti
