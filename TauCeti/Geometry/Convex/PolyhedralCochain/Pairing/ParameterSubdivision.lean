/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralCochain.Pairing.Basic
import TauCeti.Analysis.Convex.Between

/-!
# Subdivision of one-dimensional intersection tests

Splitting a segment at a point outside a wall preserves its intersection
index and hence its coefficient-valued pairing. An interior cut on a wall can count a
nonzero intersection twice. Stationary tests have zero index and pairing, and the
subdivision theorem allows real offsets, unbounded cells and lineality.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e`,
`Mei/Geometry/Convex/PolyhedralCochain/ParameterSubdivision.lean` (Apache 2.0).
-/

public section

open TauCeti (OrientedCell)

noncomputable section

open Set

namespace TauCeti.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

private theorem evalSign_fin_one_smul_of_pos
    (o : Module.Ray ℝ (V [⋀^Fin 1]→ₗ[ℝ] ℝ)) (v : Fin 1 → V) {c : ℝ} (hc : 0 < c) :
    o.evalSign (fun j => c • v j) = o.evalSign v := by
  simp only [Module.Ray.evalSign_smul, Fin.prod_univ_one, sign_pos hc, one_mul]

private theorem intersectionIndex_subdivide_lineMap (σ : OrientedCell h 1) {x y : V} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hmiss : AffineMap.lineMap x y t ∉ σ.carrier) :
    σ.intersectionIndex ![x, y] =
      σ.intersectionIndex ![x, AffineMap.lineMap x y t] +
        σ.intersectionIndex ![AffineMap.lineMap x y t, y] := by
  classical
  set z := AffineMap.lineMap x y t with hz
  have hzseg : z ∈ segment ℝ x y := by
    rw [hz]
    exact lineMap_mem_segment ℝ x y (mem_Icc_of_Ioo ht)
  have hpartition : (segment ℝ x y ∩ σ.carrier).Nonempty ↔
      (segment ℝ x z ∩ σ.carrier).Nonempty ∨ (segment ℝ z y ∩ σ.carrier).Nonempty := by
    rw [segment_eq_union_of_mem_segment hzseg, union_inter_distrib_right, union_nonempty]
  -- If both sides meet the convex cell, the split vertex lies in the cell too.
  have hexclusive : ¬((segment ℝ x z ∩ σ.carrier).Nonempty ∧
      (segment ℝ z y ∩ σ.carrier).Nonempty) := by
    rintro ⟨⟨p, hp, hpσ⟩, ⟨q, hq, hqσ⟩⟩
    have hzp : Wbtw ℝ p z y :=
      (mem_segment_iff_wbtw.mp hzseg).trans_left_right (mem_segment_iff_wbtw.mp hp)
    have hzpq : z ∈ segment ℝ p q :=
      mem_segment_iff_wbtw.mpr (hzp.trans_right_left (mem_segment_iff_wbtw.mp hq))
    exact hmiss (σ.rational.convex.segment_subset hpσ hqσ hzpq)
  -- Both parameter changes have positive slope, so their orientation signs agree.
  have hsignleft : σ.orientation.evalSign (fun _ : Fin 1 => z - x) =
      σ.orientation.evalSign (fun _ : Fin 1 => y - x) := by
    have hdiff : z - x = t • (y - x) := by
      rw [hz]
      simpa only [vsub_eq_sub] using AffineMap.lineMap_vsub_left x y t
    rw [hdiff]
    exact evalSign_fin_one_smul_of_pos _ _ ht.1
  have hsignright : σ.orientation.evalSign (fun _ : Fin 1 => y - z) =
      σ.orientation.evalSign (fun _ : Fin 1 => y - x) := by
    have hdiff : y - z = (1 - t) • (y - x) := by
      rw [hz]
      simpa only [vsub_eq_sub] using AffineMap.right_vsub_lineMap x y t
    rw [hdiff]
    exact evalSign_fin_one_smul_of_pos _ _ (sub_pos.mpr ht.2)
  rw [intersectionIndex_pair, intersectionIndex_pair, intersectionIndex_pair,
    hsignleft, hsignright, hpartition]
  by_cases hleft : (segment ℝ x z ∩ σ.carrier).Nonempty
  · have hright : ¬(segment ℝ z y ∩ σ.carrier).Nonempty := fun hr => hexclusive ⟨hleft, hr⟩
    simp [hleft, hright]
  · simp [hleft]

/-- Splitting a segment at a point outside the cell gives the original index as the sum
of the two subsegment indices. The cut may be an endpoint. -/
theorem intersectionIndex_subdivide (σ : OrientedCell h 1) {x y z : V}
    (hz : z ∈ segment ℝ x y) (hzσ : z ∉ σ.carrier) :
    σ.intersectionIndex ![x, y] =
      σ.intersectionIndex ![x, z] + σ.intersectionIndex ![z, y] := by
  rw [← insert_endpoints_openSegment] at hz
  rcases hz with rfl | rfl | hz
  · simp
  · simp
  · rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact σ.intersectionIndex_subdivide_lineMap ht hzσ

variable {R E : Type*} [Semiring R] [AddCommGroup E] [Module R E]

/-- Subdividing a segment at a point outside every cell with nonzero coefficient
preserves its pairing with a finite presentation. Cells with zero coefficient
impose no avoidance conditions. No transversality condition is needed. -/
theorem intersectionPairing_subdivide (f : OrientedCell h 1 →₀ E) {x y z : V}
    (hz : z ∈ segment ℝ x y)
    (hzf : ∀ σ ∈ f.support, z ∉ σ.carrier) :
    intersectionPairing (R := R) ![x, y] f =
      intersectionPairing (R := R) ![x, z] f + intersectionPairing (R := R) ![z, y] f := by
  simp only [intersectionPairing_apply, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro σ hσ
  rw [σ.intersectionIndex_subdivide hz (hzf σ hσ), add_zsmul]

end TauCeti.OrientedCell
