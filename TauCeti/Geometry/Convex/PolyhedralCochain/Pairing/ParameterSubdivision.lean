/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralCochain.Pairing
import Mathlib.Analysis.Convex.Between

/-!
# Subdivision of one-dimensional intersection tests

Splitting a segment at a point outside a wall preserves its intersection
index and hence its coefficient-valued pairing. The new parameter face must miss the
wall: otherwise the two closed subsegments would count the same intersection twice.
The conclusion allows stationary segments missing the wall, real offsets, unbounded
cells and lineality.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e`,
`Mei/Geometry/Convex/PolyhedralCochain/ParameterSubdivision.lean` (Apache 2.0).
-/

/-
The proof uses cell convexity and Mathlib's betweenness transitivity to keep
intersections on at most one side of the split vertex, `openSegment_subset_union`
to partition the parameter interval, and `Module.Ray.evalSign_smul`
for the orientation under positive parameter rescaling.
-/

public section

open TauCeti (OrientedCell isRationalNormalPolyhedron_iff)

noncomputable section

open Set

namespace TauCeti.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

private theorem segment_inter_carrier_nonempty_iff_subsegments (σ : OrientedCell h 1)
    {x y z : V} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hz : z = AffineMap.lineMap x y t) :
    (segment ℝ x y ∩ σ.carrier).Nonempty ↔
      (segment ℝ x z ∩ σ.carrier).Nonempty ∨ (segment ℝ z y ∩ σ.carrier).Nonempty := by
  have hzseg : z ∈ segment ℝ x y := by
    rw [hz, segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have hleft : segment ℝ x z ⊆ segment ℝ x y :=
    (convex_segment x y).segment_subset (left_mem_segment ℝ x y) hzseg
  have hright : segment ℝ z y ⊆ segment ℝ x y :=
    (convex_segment x y).segment_subset hzseg (right_mem_segment ℝ x y)
  have hcover : segment ℝ x y ⊆ segment ℝ x z ∪ segment ℝ z y := by
    intro p hp
    rw [← insert_endpoints_openSegment] at hp
    rcases hp with rfl | rfl | hp
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (right_mem_segment ℝ _ _)
    · rcases openSegment_subset_union x y ⟨t, hz.symm⟩ hp with rfl | hp | hp
      · exact Or.inl (right_mem_segment ℝ _ _)
      · exact Or.inl (openSegment_subset_segment ℝ _ _ hp)
      · exact Or.inr (openSegment_subset_segment ℝ _ _ hp)
  constructor
  · rintro ⟨p, hp, hpσ⟩
    rcases hcover hp with hp | hp
    · exact Or.inl ⟨p, hp, hpσ⟩
    · exact Or.inr ⟨p, hp, hpσ⟩
  · rintro (⟨p, hp, hpσ⟩ | ⟨p, hp, hpσ⟩)
    · exact ⟨p, hleft hp, hpσ⟩
    · exact ⟨p, hright hp, hpσ⟩

private theorem intersectionIndex_subdivide_of_mem_Ioo (σ : OrientedCell h 1) {x y z : V} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : z = AffineMap.lineMap x y t) (hzσ : z ∉ σ.carrier) :
    σ.intersectionIndex ![x, y] =
      σ.intersectionIndex ![x, z] + σ.intersectionIndex ![z, y] := by
  classical
  have hzseg : z ∈ segment ℝ x y := by
    rw [hz, segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  -- If both sides meet the convex cell, the split vertex lies in the cell too.
  have hexclusive : ¬((segment ℝ x z ∩ σ.carrier).Nonempty ∧
      (segment ℝ z y ∩ σ.carrier).Nonempty) := by
    rintro ⟨⟨p, hp, hpσ⟩, ⟨q, hq, hqσ⟩⟩
    have hzp : Wbtw ℝ p z y :=
      (mem_segment_iff_wbtw.mp hzseg).trans_left_right (mem_segment_iff_wbtw.mp hp)
    have hzpq : z ∈ segment ℝ p q :=
      mem_segment_iff_wbtw.mpr (hzp.trans_right_left (mem_segment_iff_wbtw.mp hq))
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
    have hconv : Convex ℝ σ.carrier := hP ▸ P.convex
    exact hzσ (hconv.segment_subset hpσ hqσ hzpq)
  -- Both parameter changes have positive slope, so their orientation signs agree.
  have hsignleft : σ.orientation.evalSign (fun _ : Fin 1 => z - x) =
      σ.orientation.evalSign (fun _ : Fin 1 => y - x) := by
    rw [hz, AffineMap.lineMap_apply_module', add_sub_cancel_right]
    simp only [Module.Ray.evalSign_smul, Fin.prod_univ_one, sign_pos ht.1, one_mul]
  have hsignright : σ.orientation.evalSign (fun _ : Fin 1 => y - z) =
      σ.orientation.evalSign (fun _ : Fin 1 => y - x) := by
    have hdiff : y - z = (1 - t) • (y - x) := by
      rw [hz, AffineMap.lineMap_apply_module']
      module
    rw [hdiff]
    simpa only [Fin.prod_univ_one, sign_pos (sub_pos.mpr ht.2), one_mul]
      using (Module.Ray.evalSign_smul σ.orientation (fun _ : Fin 1 => y - x)
        (fun _ => 1 - t))
  rw [intersectionIndex_pair, intersectionIndex_pair, intersectionIndex_pair,
    hsignleft, hsignright, σ.segment_inter_carrier_nonempty_iff_subsegments ht hz]
  by_cases hleft : (segment ℝ x z ∩ σ.carrier).Nonempty
  · have hright : ¬(segment ℝ z y ∩ σ.carrier).Nonempty := fun hr => hexclusive ⟨hleft, hr⟩
    simp [hleft, hright]
  · simp [hleft]

/-- Inserting a vertex on a segment outside the cell adds the two subsegment
intersection indices. Endpoints and degenerate segments outside the cell are allowed. -/
theorem intersectionIndex_subdivide (σ : OrientedCell h 1) {x y z : V}
    (hz : z ∈ segment ℝ x y) (hzσ : z ∉ σ.carrier) :
    σ.intersectionIndex ![x, y] =
      σ.intersectionIndex ![x, z] + σ.intersectionIndex ![z, y] := by
  rw [← insert_endpoints_openSegment] at hz
  rcases hz with hzx | hzy | hz
  · subst z
    have hdisj : ¬(segment ℝ x x ∩ σ.carrier).Nonempty := by
      simpa [segment_same] using hzσ
    have hzero : σ.intersectionIndex ![x, x] = 0 := by
      rw [intersectionIndex_pair, ite_eq_right hdisj]
    rw [hzero, zero_add]
  · subst z
    have hdisj : ¬(segment ℝ y y ∩ σ.carrier).Nonempty := by
      simpa [segment_same] using hzσ
    have hzero : σ.intersectionIndex ![y, y] = 0 := by
      rw [intersectionIndex_pair, ite_eq_right hdisj]
    rw [hzero, add_zero]
  · rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact σ.intersectionIndex_subdivide_of_mem_Ioo ht rfl hzσ

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- Subdividing a segment at a point outside every cell with nonzero coefficient
preserves its pairing with a finite presentation. Cells with zero coefficient
impose no avoidance conditions. No transversality condition is needed. -/
theorem intersectionPairing_subdivide (f : OrientedCell h 1 →₀ E) {x y z : V}
    (hz : z ∈ segment ℝ x y)
    (hzf : ∀ σ ∈ f.support, z ∉ σ.carrier) :
    intersectionPairing (R := R) ![x, y] f =
      intersectionPairing (R := R) ![x, z] f + intersectionPairing (R := R) ![z, y] f := by
  simp only [intersectionPairing_apply, Finsupp.sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [σ.intersectionIndex_subdivide hz (hzf σ hσ), add_zsmul]

end TauCeti.OrientedCell
