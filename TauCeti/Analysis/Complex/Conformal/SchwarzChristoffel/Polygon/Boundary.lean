/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Compactification
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.UnboundedEdge
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# The Schwarz--Christoffel compactified boundary is polygonal

For a nondecreasing finite family of prevertices, the real projective line splits into the
two unbounded intervals and the intervals between consecutive prevertices.  The
Schwarz--Christoffel boundary map carries each finite interval onto its bounded side.  The real
points in the two unbounded intervals trace the two sides incident to the common vertex at infinity
with that vertex omitted; compactification supplies the omitted vertex.

Consequently the range of the compactified boundary map is exactly the boundary of the packaged
polygon.  This identification does not require the polygon to be simple; proving that distinct
nonadjacent sides do not meet is the separate global injectivity problem.

## Main result

* `TauCeti.range_schwarzChristoffelCompactifiedBoundary` -- the compactified boundary map traces
  exactly the boundary of `schwarzChristoffelPolygon`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {n : ℕ}

/-- **The compactified Schwarz--Christoffel boundary traces the polygon boundary.**  For ordered
prevertices, integrability at every finite prevertex and decay at infinity make each
closed finite interval map onto its corresponding bounded side.  Each unbounded interval traces
its side with the common vertex at infinity omitted, and the compactified point supplies that
vertex.  Their union is the complete boundary of `schwarzChristoffelPolygon`.

No simplicity hypothesis is needed: this is an equality of ranges even when nonadjacent polygon
sides intersect. -/
theorem range_schwarzChristoffelCompactifiedBoundary (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    Set.range (schwarzChristoffelCompactifiedBoundary a e z₀) =
      (schwarzChristoffelPolygon a e z₀).boundary ℝ := by
  classical
  let B : ℝ → ℂ := schwarzChristoffelBoundary a e z₀
  let V : ℂ := schwarzChristoffelVertexAtInfinity a e z₀
  have hfree (i : Fin n) :
      ∀ j, e j ≠ 0 → a j ∉ Ioo (a i.castSucc) (a i.succ) := by
    intro j _ hj
    by_cases hji : j ≤ i.castSucc
    · exact (not_lt_of_ge (ha hji)) hj.1
    · have hij : i.succ ≤ j := by
        simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at hji ⊢
        omega
      exact (not_lt_of_ge (ha hij)) hj.2
  have hright : ∀ i, e i ≠ 0 → a i ≤ a (Fin.last n) := by
    intro i _
    exact ha i.le_last
  have hleft : ∀ i, e i ≠ 0 → a 0 ≤ a i := by
    intro i _
    exact ha i.zero_le
  have hbounded (i : Fin n) :
      B '' Icc (a i.castSucc) (a i.succ) =
        segment ℝ (schwarzChristoffelVertex a e z₀ i.castSucc)
          (schwarzChristoffelVertex a e z₀ i.succ) := by
    exact schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
      (ha i.castSucc_le_succ) (hfree i) (hfinite i.castSucc) (hfinite i.succ)
  have hrightImage :
      B '' Ici (a (Fin.last n)) =
        segment ℝ (schwarzChristoffelVertex a e z₀ (Fin.last n)) V \ {V} := by
    exact schwarzChristoffelBoundary_image_Ici_prevertex a e z₀ (Fin.last n)
      (hfinite (Fin.last n)) hright hinfty
  have hleftImage :
      B '' Iic (a 0) =
        segment ℝ (schwarzChristoffelVertex a e z₀ 0) V \ {V} := by
    exact schwarzChristoffelBoundary_image_Iic_prevertex a e z₀ 0
      (hfinite 0) hleft hinfty
  rw [schwarzChristoffelPolygon_boundary]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    induction x using OnePoint.rec with
    | infty =>
        simp only [schwarzChristoffelCompactifiedBoundary_infty]
        exact Or.inr (left_mem_segment ℝ _ _)
    | coe x =>
        simp only [schwarzChristoffelCompactifiedBoundary_coe]
        by_cases hxleft : x ≤ a 0
        · have himage : B x ∈ B '' Iic (a 0) := ⟨x, hxleft, rfl⟩
          rw [hleftImage] at himage
          exact Or.inr
            (segment_symm ℝ (schwarzChristoffelVertex a e z₀ 0) V ▸ himage.1)
        · by_cases hxright : a (Fin.last n) ≤ x
          · have himage : B x ∈ B '' Ici (a (Fin.last n)) := ⟨x, hxright, rfl⟩
            rw [hrightImage] at himage
            exact Or.inl (Or.inr himage.1)
          · -- Mathlib covers `Ioc (a 0) (a (Fin.last n))` by consecutive intervals.
            have hx : x ∈ ⋃ j ∈ Ico 0 (Fin.last n), Ioc (a j) (a (Order.succ j)) := by
              rw [ha.biUnion_Ico_Ioc_map_succ]
              exact ⟨lt_of_not_ge hxleft, (lt_of_not_ge hxright).le⟩
            simp only [mem_iUnion, mem_Ico] at hx
            obtain ⟨j, ⟨-, hj⟩, hxj⟩ := hx
            obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj.ne
            have hi : x ∈ Icc (a i.castSucc) (a i.succ) :=
              Ioc_subset_Icc_self (by simpa only [Fin.orderSucc_castSucc] using hxj)
            have himage : B x ∈ B '' Icc (a i.castSucc) (a i.succ) := ⟨x, hi, rfl⟩
            rw [hbounded i] at himage
            exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i, himage⟩))
  · intro hz
    rcases hz with (hz | hzleft)
    · rcases hz with (hzbounded | hzright)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzbounded
        rw [← hbounded i] at hi
        obtain ⟨x, _, rfl⟩ := hi
        exact ⟨(x : OnePoint ℝ), by simp [B]⟩
      · by_cases hzeq : z = V
        · subst z
          exact ⟨∞, by simp [V]⟩
        · have hi' : z ∈ segment ℝ (schwarzChristoffelVertex a e z₀ (Fin.last n)) V \ {V} :=
            ⟨hzright, by simpa using hzeq⟩
          rw [← hrightImage] at hi'
          obtain ⟨x, _, rfl⟩ := hi'
          exact ⟨(x : OnePoint ℝ), by simp [B]⟩
    · by_cases hzeq : z = V
      · subst z
        exact ⟨∞, by simp [V]⟩
      · have hi' : z ∈ segment ℝ (schwarzChristoffelVertex a e z₀ 0) V \ {V} :=
          ⟨segment_symm ℝ V (schwarzChristoffelVertex a e z₀ 0) ▸ hzleft,
            by simpa using hzeq⟩
        rw [← hleftImage] at hi'
        obtain ⟨x, _, rfl⟩ := hi'
        exact ⟨(x : OnePoint ℝ), by simp [B]⟩

end TauCeti
