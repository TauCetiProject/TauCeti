/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.EdgeIntersection.Criterion

/-!
# Recovering side intersections from a simple Schwarz--Christoffel boundary

For ordered prevertices, every bounded polygon side is the image of its closed
prevertex interval. The two closing sides are the images of the unbounded real
intervals, together with their common endpoint at infinity. Injectivity of the
compactified boundary therefore forces nonadjacent sides to be disjoint and
adjacent sides to meet only at their shared vertex. This is the converse of the
side-intersection criterion for a simple Schwarz--Christoffel boundary.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- If the Schwarz--Christoffel boundary is injective between the first and last prevertices,
two distinct bounded sides can meet only when consecutive, at their common finite vertex. -/
theorem schwarzChristoffelPolygon_bounded_edges_adjacent_and_eq_vertex_of_injOn
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hinj : InjOn (schwarzChristoffelBoundary a e z₀)
      (Icc (a 0) (a (Fin.last (n + 1)))))
    (i j : Fin (n + 1)) (hij : i < j)
    (z : ℂ) (hzi : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
    (hzj : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc) :
    j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ := by
  let B := schwarzChristoffelBoundary a e z₀
  have hedges (k : Fin (n + 1)) :
      B '' Icc (a k.castSucc) (a k.succ) =
        (schwarzChristoffelPolygon a e z₀).edgeSet ℝ k.castSucc.castSucc := by
    rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc]
    exact schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
      (ha k.castSucc_lt_succ).le
      (fun l _ => TauCeti.not_mem_Ioo_castSucc_succ a ha.monotone k l)
      (hfinite _) (hfinite _)
  rw [← hedges i] at hzi
  rw [← hedges j] at hzj
  obtain ⟨x, hx, rfl⟩ := hzi
  obtain ⟨y, hy, hxy⟩ := hzj
  have hxeq : x = y := hinj
    ⟨(ha.monotone (Fin.zero_le _)).trans hx.1, hx.2.trans (ha.monotone (Fin.le_last _))⟩
    ⟨(ha.monotone (Fin.zero_le _)).trans hy.1, hy.2.trans (ha.monotone (Fin.le_last _))⟩
    hxy.symm
  have hindex : j.val ≤ i.val + 1 := by
    have h : a j.castSucc ≤ a i.succ := by rw [← hxeq] at hy; exact hy.1.trans hx.2
    have h' : j.castSucc ≤ i.succ := (ha.le_iff_le).mp h
    exact Fin.le_def.mp h'
  have hadj : j.val = i.val + 1 := by
    have hlt := Fin.lt_def.mp hij
    omega
  have hparam : x = a i.succ := by
    have h : i.succ = j.castSucc := Fin.ext hadj.symm
    have hlow : a i.succ ≤ x := by rw [h, hxeq]; exact hy.1
    exact le_antisymm hx.2 hlow
  refine ⟨hadj, ?_⟩
  rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ i.succ (hfinite _)]
  exact congrArg B hparam

/-- A bounded Schwarz--Christoffel side can meet the left closing side only
at the first finite vertex when the compactified boundary is injective. -/
theorem schwarzChristoffelPolygon_bounded_edgeSet_last_eq_first_vertex_of_injective
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hinfty : ∑ k, e k < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀))
    (i : Fin (n + 1)) (z : ℂ)
    (hzi : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
    (hzleft : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2))) :
    z = schwarzChristoffelVertex a e z₀ 0 := by
  let B := schwarzChristoffelBoundary a e z₀
  let V := schwarzChristoffelVertexAtInfinity a e z₀
  have hB := (schwarzChristoffelCompactifiedBoundary_injective_iff a e z₀).mp hinj
  have hedge : B '' Icc (a i.castSucc) (a i.succ) =
      (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc := by
    rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc]
    exact schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
      (ha i.castSucc_lt_succ).le
      (fun l _ => TauCeti.not_mem_Ioo_castSucc_succ a ha.monotone i l)
      (hfinite _) (hfinite _)
  rw [← hedge] at hzi
  obtain ⟨x, hx, rfl⟩ := hzi
  have hleftImage : B '' Iic (a 0) =
      segment ℝ (schwarzChristoffelVertex a e z₀ 0) V \ {V} :=
    schwarzChristoffelBoundary_image_Iic_prevertex a e z₀ 0 (hfinite _)
      (fun k _ => ha.monotone k.zero_le) hinfty
  rw [schwarzChristoffelPolygon_edgeSet_last, segment_symm] at hzleft
  have hxinfty : B x ≠ V := hB.2 x
  have hxleft : B x ∈ B '' Iic (a 0) := by
    rw [hleftImage]
    exact ⟨hzleft, hxinfty⟩
  obtain ⟨y, hy, hxy⟩ := hxleft
  have hxeq : x = y := hB.1 hxy.symm
  have hxzero : x = a 0 := le_antisymm (hxeq ▸ hy) (ha.monotone (Fin.zero_le _)|>.trans hx.1)
  rw [hxzero]
  exact schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite _)

/-- A bounded Schwarz--Christoffel side can meet the right closing side only
at the last finite vertex when the compactified boundary is injective. -/
theorem schwarzChristoffelPolygon_bounded_edgeSet_last_prevertex_eq_last_vertex_of_injective
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hinfty : ∑ k, e k < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀))
    (i : Fin (n + 1)) (z : ℂ)
    (hzi : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
    (hzright : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ
      (Fin.last (n + 1)).castSucc) :
    z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1)) := by
  let B := schwarzChristoffelBoundary a e z₀
  let V := schwarzChristoffelVertexAtInfinity a e z₀
  have hB := (schwarzChristoffelCompactifiedBoundary_injective_iff a e z₀).mp hinj
  have hedge : B '' Icc (a i.castSucc) (a i.succ) =
      (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc := by
    rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc]
    exact schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
      (ha i.castSucc_lt_succ).le
      (fun l _ => TauCeti.not_mem_Ioo_castSucc_succ a ha.monotone i l)
      (hfinite _) (hfinite _)
  rw [← hedge] at hzi
  obtain ⟨x, hx, rfl⟩ := hzi
  have hrightImage : B '' Ici (a (Fin.last (n + 1))) =
      segment ℝ (schwarzChristoffelVertex a e z₀ (Fin.last (n + 1))) V \ {V} :=
    schwarzChristoffelBoundary_image_Ici_prevertex a e z₀ (Fin.last (n + 1)) (hfinite _)
      (fun k _ => ha.monotone k.le_last) hinfty
  rw [schwarzChristoffelPolygon_edgeSet_last_prevertex] at hzright
  have hxinfty : B x ≠ V := hB.2 x
  have hxright : B x ∈ B '' Ici (a (Fin.last (n + 1))) := by
    rw [hrightImage]
    exact ⟨hzright, hxinfty⟩
  obtain ⟨y, hy, hxy⟩ := hxright
  have hxeq : x = y := hB.1 hxy.symm
  have hxlast : x = a (Fin.last (n + 1)) :=
    le_antisymm (hx.2.trans (ha.monotone (Fin.le_last _))) (hxeq ▸ hy)
  rw [hxlast]
  exact schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)

/-- The compactified Schwarz--Christoffel boundary is simple exactly when its
bounded sides and closing sides have the indicated finite intersections. -/
theorem schwarzChristoffelCompactifiedBoundary_injective_iff_edge_intersections
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hsum : ∑ k, e k = -2) :
    Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀) ↔
      (∀ (i j : Fin (n + 1)), i < j →
        ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
          z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
            j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ) ∧
      (∀ (i : Fin (n + 1)) (z : ℂ),
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2)) →
          z = schwarzChristoffelVertex a e z₀ 0) ∧
      (∀ (i : Fin (n + 1)) (z : ℂ),
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ
          (Fin.last (n + 1)).castSucc →
          z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1))) := by
  have hinfty : ∑ k, e k < -1 := by rw [hsum]; norm_num
  constructor
  · intro hinj
    have hB := ((schwarzChristoffelCompactifiedBoundary_injective_iff a e z₀).mp hinj).1
    exact ⟨fun i j hij z hzi hzj =>
      schwarzChristoffelPolygon_bounded_edges_adjacent_and_eq_vertex_of_injOn
        a e z₀ ha hfinite hB.injOn
        i j hij z hzi hzj,
      fun i z hzi hzleft =>
        schwarzChristoffelPolygon_bounded_edgeSet_last_eq_first_vertex_of_injective
          a e z₀ ha hfinite
          hinfty hinj i z hzi hzleft,
      fun i z hzi hzright =>
        schwarzChristoffelPolygon_bounded_edgeSet_last_prevertex_eq_last_vertex_of_injective
          a e z₀ ha hfinite
          hinfty hinj i z hzi hzright⟩
  · rintro ⟨hbounded, hleft, hright⟩
    exact schwarzChristoffelCompactifiedBoundary_injective_of_edge_intersections
      a e z₀ ha hfinite hsum hbounded hleft hright

end TauCeti
