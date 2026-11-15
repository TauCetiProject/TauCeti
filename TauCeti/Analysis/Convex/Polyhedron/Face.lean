/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.ZeroLocus
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Analysis.Convex.Exposed

import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Faces of polyhedra are determined by active inequalities

A *face* of a convex polyhedron `P` is a nonempty exposed subset: the set of maximizers on `P` of
a continuous linear functional which is bounded above on `P` and attains its supremum. A nonempty
convex extreme subset of `P = {x | ∀ j, g j x ≤ 0}` is obtained by turning some of the defining
inequalities into equalities (`IsExtreme.eq_setOf_active`). Consequently the convex extreme
subsets of `P` coincide with its exposed subsets (`IsExtreme.isExposed_of_isConvexPolyhedron`),
they are again convex polyhedra, exposed subsets of exposed subsets are exposed
(`IsExposed.trans_of_isConvexPolyhedron`), and there are only finitely many of them
(`TauCeti.IsConvexPolyhedron.finite_setOf_isExposed`).

The arguments allow unbounded polyhedra, lineality and redundant inequalities. Mathlib's
convention that the empty set is exposed is kept: faces in the sense of the previous paragraph
are the nonempty exposed subsets.

## Main results

* `IsExtreme.eq_setOf_active`: a nonempty convex extreme subset of a polyhedron is cut out by
  making finitely many of the defining inequalities equalities.
* `TauCeti.isExposed_setOf_active`: conversely, every such set is exposed.
* `IsExtreme.isExposed_of_isConvexPolyhedron`: convex extreme subsets of a polyhedron are
  exposed.
* `IsExtreme.isConvexPolyhedron`: convex extreme subsets of a polyhedron are polyhedra.
* `IsExposed.trans_of_isConvexPolyhedron`: faces of faces of a polyhedron are faces.
* `TauCeti.IsConvexPolyhedron.finite_setOf_isExposed`: a polyhedron has finitely many faces.

Adapted from `Mei/Geometry/Convex/Polyhedron/Face.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

open Set Filter Topology

variable {V ι : Type*}

section Algebra

variable [AddCommGroup V] [Module ℝ V]

namespace TauCeti

/-- A direction satisfying the active inequalities of a finite half-space
presentation is realized by a positive step inside the polyhedron. -/
theorem exists_pos_smul_add_forall_le [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ))
    {x v : V} (hx : ∀ j, g j x ≤ 0)
    (hv : ∀ j, g j x = 0 → (g j).linear v ≤ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j, g j (ε • v + x) ≤ 0 := by
  have heach (j : ι) : ∀ᶠ ε : ℝ in 𝓝 0,
      0 ≤ ε → g j (ε • v + x) ≤ 0 := by
    have hval (ε : ℝ) : g j (ε • v + x) = ε * (g j).linear v + g j x := by
      simpa only [vadd_eq_add, map_smul, smul_eq_mul] using (g j).map_vadd x (ε • v)
    by_cases hj : g j x = 0
    · exact Eventually.of_forall fun ε hε => by
        rw [hval, hj, add_zero]
        exact mul_nonpos_of_nonneg_of_nonpos hε (hv j hj)
    · have hc : Continuous (fun ε : ℝ => ε * (g j).linear v + g j x) := by
        fun_prop
      have ht : Tendsto (fun ε : ℝ => ε * (g j).linear v + g j x)
          (𝓝 0) (𝓝 (g j x)) := by simpa using hc.tendsto 0
      have he := ht.eventually (gt_mem_nhds (lt_of_le_of_ne (hx j) hj))
      exact he.mono fun ε hε _ => by rw [hval]; exact hε.le
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (eventually_all.mpr heach)
  refine ⟨δ / 2, by positivity, fun j => hball ?_ j (by positivity)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

/-- Matching the active inequalities at a point permits a small extrapolation
away from the matching point while preserving every defining inequality. -/
theorem exists_pos_lineMap_neg_forall_le [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ))
    {p x : V} (hp : ∀ j, g j p ≤ 0) (hx : ∀ j, g j p = 0 → g j x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j, g j (AffineMap.lineMap p x (-ε)) ≤ 0 := by
  have hv (j : ι) (hj : g j p = 0) : (g j).linear (p - x) ≤ 0 := by
    simpa only [vsub_eq_sub, hj, hx j hj, sub_self] using
      ((g j).linear_apply_vsub p x).le
  obtain ⟨ε, hε, he⟩ := exists_pos_smul_add_forall_le g hp hv
  have heq : AffineMap.lineMap p x (-ε) = ε • (p - x) + p := by
    rw [AffineMap.lineMap_apply_module]
    module
  exact ⟨ε, hε, by simpa only [heq] using he⟩

end TauCeti

/-- A nonempty convex extreme subset of a finite intersection of affine
halfspaces is obtained by imposing equality in some of the defining rows. -/
theorem IsExtreme.eq_setOf_active [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ)) {F : Set V}
    (hF : IsExtreme ℝ {x | ∀ j, g j x ≤ 0} F) (hconv : Convex ℝ F)
    (hne : F.Nonempty) :
    ∃ I : Finset ι, F = {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0} := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨p, hp, hpoint⟩ := hconv.exists_mem_zero_iff_forall hne g
    (fun j x hx => hF.subset hx j)
  let I := Finset.univ.filter (fun j => g j p = 0)
  refine ⟨I, Set.ext fun x => ⟨?_, ?_⟩⟩
  · intro hx
    refine ⟨hF.subset hx, ?_⟩
    intro j hj
    exact (hpoint j).mp (Finset.mem_filter.mp hj).2 x hx
  · rintro ⟨hx, hxI⟩
    obtain ⟨ε, hε, he⟩ := TauCeti.exists_pos_lineMap_neg_forall_le g
      (hF.subset hp) (fun j hj => hxI j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))
    apply hF.left_mem_of_mem_openSegment hx he hp
    have hden : 0 < 1 + ε := by linarith
    refine ⟨ε / (1 + ε), 1 / (1 + ε), div_pos hε hden, div_pos zero_lt_one hden, ?_, ?_⟩
    · field_simp
      ring
    · rw [AffineMap.lineMap_apply_module, smul_add, smul_smul, smul_smul]
      have hpcoef : (1 / (1 + ε)) * (1 - -ε) = 1 := by
        field_simp
        ring
      have hxcoef : ε / (1 + ε) + (1 / (1 + ε)) * -ε = 0 := by ring
      calc
        _ = ((1 / (1 + ε)) * (1 - -ε)) • p +
            (ε / (1 + ε) + (1 / (1 + ε)) * -ε) • x := by module
        _ = p := by rw [hpcoef, hxcoef]; simp

end Algebra

section Topology

variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A nonempty exposed subset of a polyhedron is obtained by imposing equality in some of the
defining rows. -/
theorem IsExposed.eq_setOf_active [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ)) {F : Set V}
    (hF : IsExposed ℝ {x | ∀ j, g j x ≤ 0} F) (hne : F.Nonempty) :
    ∃ I : Finset ι, F = {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0} :=
  hF.isExtreme.eq_setOf_active (fun j => (g j).toAffineMap)
    (hF.convex (TauCeti.isConvexPolyhedron_setOf_forall g).convex) hne

/-- Making a finite set of the defining inequalities equalities cuts out a polyhedron: each
equality is imposed by the original row together with its negative. -/
theorem TauCeti.isConvexPolyhedron_setOf_active [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (I : Finset ι) :
    TauCeti.IsConvexPolyhedron {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0} := by
  have h := (TauCeti.isConvexPolyhedron_setOf_forall g).inter
    (TauCeti.isConvexPolyhedron_setOf_forall (fun j : I => -g j.val))
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx, hxI⟩
    exact ⟨hx, fun j => by simp [hxI j.val j.property]⟩
  · rintro ⟨hx, hxI⟩
    refine ⟨hx, fun j hj => le_antisymm (hx j) ?_⟩
    simpa using hxI ⟨j, hj⟩

/-- Every convex extreme subset of a polyhedron is itself a polyhedron. -/
theorem IsExtreme.isConvexPolyhedron {P F : Set V} (hF : IsExtreme ℝ P F)
    (hP : TauCeti.IsConvexPolyhedron P) (hconv : Convex ℝ F) :
    TauCeti.IsConvexPolyhedron F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact TauCeti.isConvexPolyhedron_iff.mpr
      ⟨1, fun _ => ContinuousAffineMap.const ℝ V 1, by ext; simp⟩
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  obtain ⟨I, rfl⟩ := hF.eq_setOf_active (fun j => (g j).toAffineMap) hconv hne
  exact TauCeti.isConvexPolyhedron_setOf_active g I

/-- A convex polyhedron has finitely many convex extreme subsets, including the empty one. -/
theorem TauCeti.IsConvexPolyhedron.finite_setOf_convex_isExtreme {P : Set V}
    (hP : TauCeti.IsConvexPolyhedron P) :
    {F : Set V | Convex ℝ F ∧ IsExtreme ℝ P F}.Finite := by
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  refine ((Set.finite_range fun I : Finset (Fin m) =>
    {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0}).insert ∅).subset ?_
  rintro F ⟨hconv, hF⟩
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact Set.mem_insert _ _
  · obtain ⟨I, hI⟩ := hF.eq_setOf_active (fun j => (g j).toAffineMap) hconv hne
    exact Set.mem_insert_of_mem _ ⟨I, hI.symm⟩

/-- A convex polyhedron has finitely many exposed subsets, hence finitely many faces. -/
theorem TauCeti.IsConvexPolyhedron.finite_setOf_isExposed {P : Set V}
    (hP : TauCeti.IsConvexPolyhedron P) : {F : Set V | IsExposed ℝ P F}.Finite :=
  hP.finite_setOf_convex_isExtreme.subset fun _ hF => ⟨hF.convex hP.convex, hF.isExtreme⟩

section Group

variable [IsTopologicalAddGroup V]

/-- Making a finite set of the defining inequalities equalities exposes a subset. When the locus
where every selected row vanishes is nonempty, the sum of the selected affine functions is
maximized exactly there; when it is empty, the subset is the empty set, which satisfies
`IsExposed` vacuously. -/
theorem TauCeti.isExposed_setOf_active (g : ι → (V →ᴬ[ℝ] ℝ)) (I : Finset ι) :
    IsExposed ℝ {x | ∀ j, g j x ≤ 0}
      {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0} := by
  intro ⟨p, hp, hpI⟩
  let l : V →L[ℝ] ℝ := ∑ j ∈ I, (g j).contLinear
  have hl (x : V) : l x = (∑ j ∈ I, g j x) - ∑ j ∈ I, g j 0 := by
    simp only [l, sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simpa using (g j).contLinear_apply_vsub x 0
  have hpzero : ∑ j ∈ I, g j p = 0 := Finset.sum_eq_zero hpI
  refine ⟨l, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨hx, hxI⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [hl y, hl x, Finset.sum_eq_zero hxI]
    have hyzero : ∑ j ∈ I, g j y ≤ 0 := Finset.sum_nonpos fun j _ => hy j
    linarith
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, ?_⟩
    have hsum : ∑ j ∈ I, g j x = 0 := by
      have hle : ∑ j ∈ I, g j x ≤ 0 := Finset.sum_nonpos fun j _ => hx j
      have hge := hmax p hp
      rw [hl p, hl x, hpzero] at hge
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hx j)).mp hsum

/-- Every convex extreme subset of a polyhedron is exposed, including the empty subset. -/
theorem IsExtreme.isExposed_of_isConvexPolyhedron {P F : Set V} (hF : IsExtreme ℝ P F)
    (hP : TauCeti.IsConvexPolyhedron P) (hconv : Convex ℝ F) : IsExposed ℝ P F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact isExposed_empty
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  obtain ⟨I, rfl⟩ := hF.eq_setOf_active (fun j => (g j).toAffineMap) hconv hne
  exact TauCeti.isExposed_setOf_active g I

/-- Exposed faces of a polyhedron are closed under taking exposed subfaces.
The polyhedral hypothesis supplies transitivity, which fails for arbitrary convex sets. -/
theorem IsExposed.trans_of_isConvexPolyhedron {P F G : Set V}
    (hF : IsExposed ℝ P F) (hG : IsExposed ℝ F G)
    (hP : TauCeti.IsConvexPolyhedron P) : IsExposed ℝ P G :=
  (hF.isExtreme.trans hG.isExtreme).isExposed_of_isConvexPolyhedron hP
    (hG.convex (hF.convex hP.convex))

end Group

end Topology
