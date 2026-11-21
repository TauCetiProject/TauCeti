/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.BoundedArcInjective
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.InfinityIntersection

/-!
# Simplicity from Schwarz--Christoffel side intersections

The compactified boundary of a Schwarz--Christoffel primitive is injective when its bounded
polygon sides intersect only at consecutive vertices and meet each closing side only at that
side's finite endpoint. This criterion applies to nonconvex polygons: it reduces the analytic
injectivity question to intersections of finitely many straight segments. In conjunction with
the polygon mapping theorem, it identifies the image of the upper half-plane with the Jordan
interior bounded by these sides.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- **Injectivity of the finite boundary map from side intersections.** For strictly ordered
prevertices with integrable exponents and total exponent `-2`, the finite boundary map is injective
when the bounded sides meet only at consecutive vertices and each closing side meets the bounded
sides only at its finite endpoint. -/
theorem schwarzChristoffelBoundary_injective_of_polygon_edge_intersections
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hsum : ∑ k, e k = -2)
    (hinter : ∀ (i j : Fin (n + 1)), i < j →
      ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
          j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ)
    (hleft : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2)) →
        z = schwarzChristoffelVertex a e z₀ 0)
    (hright : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1)).castSucc →
        z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1))) :
    Function.Injective (schwarzChristoffelBoundary a e z₀) := by
  let B := schwarzChristoffelBoundary a e z₀
  have hS : ∑ k, e k < -1 := by rw [hsum]; norm_num
  have hbounded : InjOn B (Icc (a 0) (a (Fin.last (n + 1)))) :=
    schwarzChristoffelBoundary_injOn_prevertex_interval_of_edge_intersections
      a e z₀ ha.monotone hfinite hinter
  have hleftInj : InjOn B (Iic (a 0)) :=
    schwarzChristoffelBoundary_injOn_Iic a e z₀ (hfinite 0) fun k _ ↦ ha.monotone k.zero_le
  have hrightInj : InjOn B (Ici (a (Fin.last (n + 1)))) :=
    schwarzChristoffelBoundary_injOn_Ici a e z₀ (hfinite _) fun k _ ↦ ha.monotone k.le_last
  -- The left ray, bounded interval and right ray are separated; equality at their shared
  -- endpoints is excluded by injectivity on the bounded interval.
  suffices h : ∀ x y, x < y → B x ≠ B y by
    intro x y hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact False.elim (h x y hlt hxy)
    · exact heq
    · exact False.elim (h y x hgt hxy.symm)
  intro x y hxy heq
  by_cases hy₀ : y ≤ a 0
  · exact hxy.ne (hleftInj (hxy.le.trans hy₀) hy₀ heq)
  by_cases hxn : a (Fin.last (n + 1)) ≤ x
  · exact hxy.ne (hrightInj hxn (hxn.trans hxy.le) heq)
  by_cases hx₀ : x ≤ a 0
  · by_cases hyn : a (Fin.last (n + 1)) ≤ y
    · have hd := disjoint_schwarzChristoffelBoundary_unbounded_images a e z₀ ha
        (fun k ↦ by simpa [ha.injective.eq_iff, Finset.filter_eq'] using hfinite k) hsum
      exact Set.disjoint_left.mp hd ⟨x, hx₀, rfl⟩ ⟨y, hyn, heq.symm⟩
    · obtain ⟨i, hi⟩ := exists_mem_edgeSet_schwarzChristoffelBoundary_of_mem_Icc a e z₀
        ha.monotone hfinite
        (x := y) ⟨(lt_of_not_ge hy₀).le, (lt_of_not_ge hyn).le⟩
      have hyL := hleft i (B y) hi
        (heq ▸ schwarzChristoffelBoundary_mem_edgeSet_last_of_le a e z₀ ha.monotone (hfinite 0) hS
          hx₀)
      have hya : y = a 0 := hbounded
        ⟨(lt_of_not_ge hy₀).le, (lt_of_not_ge hyn).le⟩
        ⟨le_rfl, ha.monotone (Fin.zero_le _)⟩
        (hyL.trans (schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)).symm)
      exact (lt_of_not_ge hy₀).ne' hya
  · by_cases hyn : a (Fin.last (n + 1)) ≤ y
    · obtain ⟨i, hi⟩ := exists_mem_edgeSet_schwarzChristoffelBoundary_of_mem_Icc a e z₀
        ha.monotone hfinite
        (x := x) ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
      have hxR := hright i (B x) hi
        (heq ▸ schwarzChristoffelBoundary_mem_edgeSet_last_prevertex_of_ge a e z₀ ha.monotone
          (hfinite _) hS hyn)
      have hxa : x = a (Fin.last (n + 1)) := hbounded
        ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
        ⟨ha.monotone (Fin.zero_le _), le_rfl⟩
        (hxR.trans (schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)).symm)
      exact (lt_of_not_ge hxn).ne hxa
    · exact hxy.ne (hbounded
        ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
        ⟨(lt_of_not_ge hy₀).le, (lt_of_not_ge hyn).le⟩ heq)

/-- **The finite boundary avoids the vertex at infinity.** For ordered prevertices with integrable
exponents and total exponent below `-1`, if the left closing side meets each bounded side only at
its finite endpoint, then no finite parameter is sent to the vertex at infinity. -/
theorem schwarzChristoffelBoundary_ne_vertexAtInfinity_of_left_edge_intersection
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hS : ∑ k, e k < -1)
    (hleft : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2)) →
        z = schwarzChristoffelVertex a e z₀ 0)
    (x : ℝ) :
    schwarzChristoffelBoundary a e z₀ x ≠ schwarzChristoffelVertexAtInfinity a e z₀ := by
  -- The left unbounded side omits the vertex at infinity; a bounded parameter attaining it
  -- would put it on a bounded side and the left closing side, contradicting `hleft`.
  have hfirst : ∀ k, e k ≠ 0 → a 0 ≤ a k := fun k _ ↦ ha k.zero_le
  have hlast : ∀ k, e k ≠ 0 → a k ≤ a (Fin.last (n + 1)) :=
    fun k _ ↦ ha k.le_last
  have hleftImage := schwarzChristoffelBoundary_image_Iic_prevertex a e z₀ 0 (hfinite 0) hfirst hS
  have hrightImage := schwarzChristoffelBoundary_image_Ici_prevertex a e z₀ (Fin.last (n + 1))
    (hfinite _) hlast hS
  by_cases hx₀ : x ≤ a 0
  · have hm : schwarzChristoffelBoundary a e z₀ x ∈
        schwarzChristoffelBoundary a e z₀ '' Iic (a 0) := ⟨x, hx₀, rfl⟩
    rw [hleftImage] at hm
    exact hm.2
  by_cases hxn : a (Fin.last (n + 1)) ≤ x
  · have hm : schwarzChristoffelBoundary a e z₀ x ∈
        schwarzChristoffelBoundary a e z₀ '' Ici (a (Fin.last (n + 1))) := ⟨x, hxn, rfl⟩
    rw [hrightImage] at hm
    exact hm.2
  obtain ⟨i, hi⟩ := exists_mem_edgeSet_schwarzChristoffelBoundary_of_mem_Icc a e z₀ ha hfinite
    (x := x) ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
  intro heq
  have hLV : schwarzChristoffelVertex a e z₀ 0 = schwarzChristoffelVertexAtInfinity a e z₀ := by
    have hv : schwarzChristoffelVertexAtInfinity a e z₀ ∈
        (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2)) := by
      rw [schwarzChristoffelPolygon_edgeSet_last]
      exact left_mem_segment ℝ _ _
    exact (hleft i _ hi (heq ▸ hv)).symm.trans heq
  exact (schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_ge
    a e z₀ (hfinite 0) hfirst hS)
    ((schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)).trans hLV)

/-- A side-intersection criterion for simplicity of the compactified
Schwarz--Christoffel boundary. The finite prevertices are strictly ordered, their exponents
are integrable, and the total exponent is `-2`. Bounded sides may make reentrant turns.
The three intersection hypotheses say that nonadjacent bounded sides are disjoint,
adjacent ones meet only at their common vertex, and the bounded arc meets either closing
side only at its finite endpoint. -/
theorem schwarzChristoffelCompactifiedBoundary_injective_of_edge_intersections
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hsum : ∑ k, e k = -2)
    (hinter : ∀ (i j : Fin (n + 1)), i < j →
      ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
          j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ)
    (hleft : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2)) →
        z = schwarzChristoffelVertex a e z₀ 0)
    (hright : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1)).castSucc →
        z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1))) :
    Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀) :=
  (schwarzChristoffelCompactifiedBoundary_injective_iff a e z₀).2
    ⟨schwarzChristoffelBoundary_injective_of_polygon_edge_intersections a e z₀ ha hfinite hsum
      hinter hleft hright,
      schwarzChristoffelBoundary_ne_vertexAtInfinity_of_left_edge_intersection a e z₀ ha.monotone
        hfinite (by rw [hsum]; norm_num) hleft⟩

end TauCeti
