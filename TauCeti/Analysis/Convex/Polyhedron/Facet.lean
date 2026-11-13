/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Direction
public import TauCeti.Analysis.Convex.Exposed
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Minimal
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Facet presentations and relative frontiers

A polyhedron admits a half-space presentation within its affine span
in which every row defines a genuine facet. Its relative frontier is therefore
covered by facets. This identifies the geometric boundary used by signed facet
sums, including for unbounded and lower-dimensional polyhedra with lineality.

Adapted from `Mei/Geometry/Convex/Polyhedron/Face/Facet.lean` at
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).

The construction uses `Convex.exists_mem_zero_iff_forall` to obtain simultaneous
strict inequalities and `TauCeti.vectorSpan_active_eq` to identify each facet direction.
Its relative dimension follows from `Module.Dual.finrank_ker_inf_add_one`.
Only the direction of the polyhedron needs to be finite-dimensional.
-/

public section

open Set Module AffineSubspace

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] {P : Set V} [FiniteDimensional ℝ (vectorSpan ℝ P)]

/-- A polyhedron has a finite half-space presentation within its
affine span in which every row defines a nonempty exposed facet. -/
theorem exists_facet_presentation (hP : TauCeti.IsConvexPolyhedron P) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → (V →ᴬ[ℝ] ℝ)),
      P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0} ∧
      ∀ j, IsExposed ℝ P {x ∈ P | g j x = 0} ∧
        ({x ∈ P | g j x = 0} : Set V).Nonempty ∧
        finrank ℝ (vectorSpan ℝ {x ∈ P | g j x = 0}) + 1 =
          finrank ℝ (vectorSpan ℝ P) := by
  classical
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact ⟨Fin 0, inferInstance, Fin.elim0, by simp, by simp⟩
  -- Remove redundant inequalities relative to the affine span, rather than
  -- requiring an interior point in the ambient vector space.
  obtain ⟨n, f, hf⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  let A := affineSpan ℝ P
  let presents (S : Finset (Fin n)) := P = {x | x ∈ A ∧ ∀ j ∈ S, f j x ≤ 0}
  have hu : presents Finset.univ := by
    ext x
    simp only [Finset.mem_univ, forall_const]
    exact ⟨fun hx => ⟨subset_affineSpan ℝ P hx, by rwa [hf] at hx⟩,
      fun hx => by rw [hf]; exact hx.2⟩
  obtain ⟨S, hS⟩ := exists_minimal_of_wellFoundedLT presents ⟨_, hu⟩
  have hpres : P = {x | x ∈ A ∧ ∀ j ∈ S, f j x ≤ 0} := hS.1
  have hwitness (j : S) : ∃ x ∈ A, (∀ l ∈ S.erase j.val, f l x ≤ 0) ∧ 0 < f j.val x := by
    by_contra! hn
    have herase : presents (S.erase j.val) := by
      apply Set.Subset.antisymm
      · intro x hx
        exact ⟨subset_affineSpan ℝ P hx,
          fun l hl => (hpres ▸ hx).2 l (Finset.mem_of_mem_erase hl)⟩
      · rintro x ⟨hxA, hx⟩
        rw [hpres]
        refine ⟨hxA, fun l hl => ?_⟩
        by_cases he : l = j.val
        · subst l
          exact hn x hxA hx
        · exact hx l (Finset.mem_erase.mpr ⟨he, hl⟩)
    have he := hS.2 herase (Finset.erase_subset _ _)
    exact Finset.notMem_erase j.val S (he j.property)
  -- No retained row vanishes identically: that would also vanish on the
  -- affine span and contradict the witness obtained by deleting that row.
  have hnonzero (j : S) : ∃ p ∈ P, f j.val p < 0 := by
    by_contra! hn
    have hz : ∀ p ∈ P, f j.val p = 0 := fun p hp =>
      le_antisymm ((hpres ▸ hp).2 j.val j.property) (hn p hp)
    have heq : P.EqOn (f j.val).toAffineMap (0 : V →ᵃ[ℝ] ℝ) := hz
    obtain ⟨x, hxA, _, hx⟩ := hwitness j
    have hx0 := AffineMap.eqOn_affineSpan heq hxA
    exact hx.ne' hx0
  obtain ⟨q, hq, hqzero⟩ := hP.convex.exists_mem_zero_iff_forall hne
    (fun j : S => (f j.val).toAffineMap)
    (fun j x hx => (hpres ▸ hx).2 j.val j.property)
  have hqstrict (j : S) : f j.val q < 0 := by
    have hle := (hpres ▸ hq).2 j.val j.property
    apply lt_of_le_of_ne hle
    intro hz
    obtain ⟨p, hp, hpj⟩ := hnonzero j
    exact hpj.ne ((hqzero j).mp hz p hp)
  refine ⟨S, inferInstance, fun j => f j.val, ?_, ?_⟩
  · simpa only [Subtype.forall] using hpres
  · intro j
    -- Join the strictly feasible point to a witness for irredundancy. At the
    -- crossing of this row, every other retained inequality is still strict.
    obtain ⟨x, hxA, hxother, hxj⟩ := hwitness j
    let t := -f j.val q / (f j.val x - f j.val q)
    have hden : 0 < f j.val x - f j.val q := by linarith [hqstrict j]
    have ht0 : 0 < t := div_pos (neg_pos.mpr (hqstrict j)) hden
    have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
    let p := AffineMap.lineMap q x t
    have hpA : p ∈ A := AffineMap.lineMap_mem t (subset_affineSpan ℝ P hq) hxA
    have hpj : f j.val p = 0 := by
      simp only [p, (f j.val).apply_lineMap, AffineMap.lineMap_apply_ring, t]
      field_simp
      ring
    have hpstrict (l : S) (hl : l ≠ j) : f l.val p < 0 := by
      have hlval : l.val ≠ j.val := fun he => hl (Subtype.ext he)
      have hlx := hxother l.val (Finset.mem_erase.mpr ⟨hlval, l.property⟩)
      have hlq := hqstrict l
      have hterm : 0 < (1 - t) * -f l.val q := mul_pos (sub_pos.mpr ht1) (neg_pos.mpr hlq)
      have hterm' : t * f l.val x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0.le hlx
      simp only [p, (f l.val).apply_lineMap, AffineMap.lineMap_apply_ring]
      nlinarith
    have hpP : p ∈ P := by
      rw [hpres]
      refine ⟨hpA, fun l hl => ?_⟩
      by_cases he : l = j.val
      · simpa [he] using hpj.le
      · exact (hpstrict ⟨l, hl⟩ (fun he' => he (congrArg Subtype.val he'))).le
    have hface : IsExposed ℝ P {y ∈ P | f j.val y = 0} := by
      simpa [hf] using (TauCeti.isExposed_setOf_active f {j.val})
    refine ⟨hface, ⟨p, hpP, hpj⟩, ?_⟩
    -- The local active-face direction is a hyperplane in the parent direction.
    -- Restrict the row there before applying rank-nullity.
    have hspan := TauCeti.vectorSpan_active_eq
      (fun l : S => (f l.val).toAffineMap) A j hpA hpj hpstrict
    simp only [ContinuousAffineMap.coe_toAffineMap] at hspan
    have hset : {y | y ∈ A ∧ (∀ l : S, f l.val y ≤ 0) ∧ f j.val y = 0} =
        {y ∈ P | f j.val y = 0} := by
      ext y
      simp only [hpres, Set.mem_ofPred_eq, Subtype.forall, and_assoc]
    rw [hset] at hspan
    let : FiniteDimensional ℝ A.direction := by
      dsimp only [A]
      rw [direction_affineSpan]
      infer_instance
    have hnot : ¬ A.direction ≤ (f j.val).toAffineMap.linear.ker := by
      intro h
      have hv : (f j.val).toAffineMap.linear (x -ᵥ q) = 0 :=
        h (A.vsub_mem_direction hxA (subset_affineSpan ℝ P hq))
      rw [AffineMap.linear_apply_vsub] at hv
      simp only [ContinuousAffineMap.coe_toAffineMap, vsub_eq_sub] at hv
      linarith [hqstrict j]
    rw [hspan, inf_comm]
    rw [← direction_affineSpan ℝ P]
    exact Module.Dual.finrank_ker_inf_add_one hnot

/-- Every relative frontier point of a polyhedron belongs to a nonempty
exposed facet, rather than just to a possibly lower-dimensional active face. -/
theorem exists_facet_of_mem_intrinsicFrontier (hP : TauCeti.IsConvexPolyhedron P)
    {x : V} (hx : x ∈ intrinsicFrontier ℝ P) :
    ∃ F, IsExposed ℝ P F ∧ x ∈ F ∧
      finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  have hxP : x ∈ P := intrinsicFrontier_subset hP.isClosed hx
  obtain ⟨ι, _, g, hpres, hfacets⟩ := hP.exists_facet_presentation
  have hactive : ∃ j, g j x = 0 := by
    by_contra! hn
    let A := affineSpan ℝ P
    let xA : A := ⟨x, subset_affineSpan ℝ P hxP⟩
    let U : Set A := {y | ∀ j, g j (y : V) < 0}
    have hU : IsOpen U := by
      simp only [U, Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt ((g j).continuous.comp continuous_subtype_val) continuous_const
    have hxU : xA ∈ U := fun j => lt_of_le_of_ne ((hpres ▸ hxP).2 j) (hn j)
    have hUP : U ⊆ ((↑) ⁻¹' P : Set A) := by
      intro y hy
      rw [hpres]
      exact ⟨y.property, fun j => (hy j).le⟩
    have hxint : x ∈ intrinsicInterior ℝ P :=
      mem_intrinsicInterior.mpr ⟨xA, interior_mono hUP (by rwa [hU.interior_eq]), rfl⟩
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hx
    exact hx.2 hxint
  obtain ⟨j, hj⟩ := hactive
  exact ⟨{y ∈ P | g j y = 0}, (hfacets j).1, ⟨hxP, hj⟩, (hfacets j).2.2⟩

end TauCeti.IsConvexPolyhedron
