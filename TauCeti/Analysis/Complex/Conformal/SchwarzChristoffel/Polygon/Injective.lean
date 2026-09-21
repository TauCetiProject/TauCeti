/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.LongTurn
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ClosingSide
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Boundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Turning

import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Simplicity of the convex Schwarz--Christoffel boundary

Strictly ordered prevertices and exponents in `(-1, 0)` summing to `-2` give an injective
compactified Schwarz--Christoffel boundary. Nonadjacent bounded sides are disjoint, adjacent
bounded sides meet only at their common corner, and the bounded boundary arc lies strictly above
the horizontal closing side except at its endpoints. The two unbounded arcs occupy opposite sides
of the vertex at infinity. Thus the complete polygon boundary is a Jordan curve.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped ComplexOrder

namespace TauCeti

variable {n : ℕ} {a e : Fin (n + 1) → ℝ} {z₀ : UpperHalfPlane}

private lemma eq_of_boundary_eq_of_mem_bounded_intervals
    (ha : StrictMono a) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2)
    (i j : Fin n) (hij : i ≤ j) {x y : ℝ}
    (hx : x ∈ Icc (a i.castSucc) (a i.succ)) (hy : y ∈ Icc (a j.castSucc) (a j.succ))
    (hxy : schwarzChristoffelBoundary a e z₀ x = schwarzChristoffelBoundary a e z₀ y) :
    x = y := by
  have hfree (i : Fin n) : ∀ k, e k ≠ 0 → a k ∉ Ioo (a i.castSucc) (a i.succ) := by
    intro k _ hk
    have h₁ := ha.lt_iff_lt.mp hk.1
    have h₂ := ha.lt_iff_lt.mp hk.2
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega
  have hfinite (k : Fin (n + 1)) : ∑ l with a l = a k, e l ∈ Ioo (-1 : ℝ) 0 := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using he k
  have hinterval (i : Fin n) := schwarzChristoffelBoundary_injOn_Icc a e z₀
    (hfree i) (hfinite _).1 (hfinite _).1
  have hmem {i : Fin n} {x : ℝ} (hx : x ∈ Icc (a i.castSucc) (a i.succ)) :
      schwarzChristoffelBoundary a e z₀ x ∈
        segment ℝ (schwarzChristoffelVertex a e z₀ i.castSucc)
          (schwarzChristoffelVertex a e z₀ i.succ) := by
    rw [← schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
      (ha.monotone i.castSucc_le_succ) (hfree i) (hfinite _).1 (hfinite _).1]
    exact ⟨x, hx, rfl⟩
  -- On one side, use the analytic boundary parametrization's injectivity.
  rcases hij.eq_or_lt with rfl | hij
  · exact hinterval i hx hy hxy
  have hxmem := hmem hx
  have hymem := hmem hy
  -- Adjacent sides meet only at their common, noncollinear corner.
  by_cases hadj : i.val + 1 = j.val
  · have hmid : i.succ = j.castSucc := Fin.ext hadj
    have haff := affineIndependent_schwarzChristoffelVertex_of_adjacent a e z₀
      i.castSucc i.succ j.succ (ha i.castSucc_lt_succ)
      (by rw [hmid]; exact ha j.castSucc_lt_succ)
      (hfree i) (by rw [hmid]; exact hfree j)
      (hfinite _).1 (hfinite _) (hfinite _).1
    -- Reindex the two displacement vectors based at the middle vertex.
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (1 : Fin 3),
      ← linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))] at haff
    have hlin : LinearIndependent ℝ
        ![schwarzChristoffelVertex a e z₀ i.castSucc - schwarzChristoffelVertex a e z₀ i.succ,
          schwarzChristoffelVertex a e z₀ j.succ - schwarzChristoffelVertex a e z₀ i.succ] := by
      convert! haff using 1
      ext k
      fin_cases k <;> simp [finSuccAboveEquiv_apply]
    have heq : schwarzChristoffelBoundary a e z₀ x =
        schwarzChristoffelVertex a e z₀ i.succ := by
      apply segment_inter_subset_endpoint_of_linearIndependent_sub ℝ hlin
      exact ⟨by rwa [segment_symm], by simpa [hxy, hmid] using hymem⟩
    rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ _
      (hfinite _).1] at heq
    have hx' := hinterval i hx ⟨(ha i.castSucc_lt_succ).le, le_rfl⟩ heq
    have hy' := hinterval j hy ⟨le_rfl, (ha j.castSucc_lt_succ).le⟩
      (by simpa [hmid] using hxy.symm.trans heq)
    exact hx'.trans ((congrArg a hmid).trans hy'.symm)
  · -- The previously established global separation covers all other pairs.
    have hd := disjoint_schwarzChristoffelPolygon_bounded_edgeSet a e z₀ ha he hsum i j
      (by simp only [Fin.lt_def] at hij; omega)
    simp only [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc] at hd
    exact False.elim (Set.disjoint_left.mp hd hxmem (hxy ▸ hymem))

/-- The Schwarz--Christoffel boundary is injective between its first and last finite prevertices
under the classical convex-polygon hypotheses. -/
theorem schwarzChristoffelBoundary_injOn_prevertex_interval
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Icc (a 0) (a (Fin.last n))) := by
  by_cases hn : n = 0
  · subst n
    simp only [Fin.last_zero, Icc_self]
    exact injOn_singleton _ _
  -- Locate each argument on a bounded side using Mathlib's consecutive-interval cover.
  have hcover {x : ℝ} (hx : x ∈ Icc (a 0) (a (Fin.last n))) :
      ∃ i : Fin n, x ∈ Icc (a i.castSucc) (a i.succ) := by
    rcases hx.1.eq_or_lt with h | h
    · refine ⟨⟨0, Nat.pos_of_ne_zero hn⟩, ?_⟩
      rw [← h]
      exact ⟨le_rfl, ha.monotone (Fin.zero_le _)⟩
    · have hx' : x ∈ ⋃ j ∈ Ico 0 (Fin.last n), Ioc (a j) (a (Order.succ j)) := by
        rw [ha.monotone.biUnion_Ico_Ioc_map_succ]
        exact ⟨h, hx.2⟩
      simp only [mem_iUnion, mem_Ico] at hx'
      obtain ⟨j, ⟨-, hj⟩, hxj⟩ := hx'
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj.ne
      exact ⟨i, Ioc_subset_Icc_self (by simpa only [Fin.orderSucc_castSucc] using hxj)⟩
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := hcover hx
  obtain ⟨j, hj⟩ := hcover hy
  rcases le_total i j with hij | hji
  · exact eq_of_boundary_eq_of_mem_bounded_intervals ha he hsum i j hij hi hj hxy
  · exact (eq_of_boundary_eq_of_mem_bounded_intervals ha he hsum j i hji hj hi hxy.symm).symm

/-- Strictly ordered prevertices with exponents in `(-1, 0)` summing to `-2` give an injective
Schwarz--Christoffel boundary on the one-point compactification of the real line. -/
theorem schwarzChristoffelCompactifiedBoundary_injective
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  let B := schwarzChristoffelBoundary a e z₀
  let V := schwarzChristoffelVertexAtInfinity a e z₀
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  have hS : ∑ k, e k < -1 := by rw [hsum]; norm_num
  have hfirst : ∀ k, e k ≠ 0 → a 0 ≤ a k := fun k _ ↦ ha.monotone k.zero_le
  have hlast : ∀ k, e k ≠ 0 → a k ≤ a (Fin.last n) := fun k _ ↦ ha.monotone k.le_last
  have hVfirst : V < B (a 0) :=
    schwarzChristoffelVertexAtInfinity_lt_boundary a e z₀ (hfinite _) hfirst hsum
  have hVlast : B (a (Fin.last n)) < V :=
    schwarzChristoffelBoundary_lt_vertexAtInfinity a e z₀ (hfinite _) hlast hS
  -- The unbounded arcs lie on opposite sides of infinity along the closing line.
  have hleft {x : ℝ} (hx : x ≤ a 0) : V < B x := by
    have hm : B x ∈ B '' Iic (a 0) := ⟨x, hx, rfl⟩
    rw [schwarzChristoffelBoundary_image_Iic a e z₀ (hfinite _) hfirst hS] at hm
    have hseg : B x ∈ segment ℝ V (B (a 0)) := by
      rw [segment_symm]
      exact hm.1
    exact lt_of_le_of_ne (segment_subset_Icc hVfirst.le hseg).1 (Ne.symm hm.2)
  have hright {x : ℝ} (hx : a (Fin.last n) ≤ x) : B x < V := by
    have hm : B x ∈ B '' Ici (a (Fin.last n)) := ⟨x, hx, rfl⟩
    rw [schwarzChristoffelBoundary_image_Ici a e z₀ (hfinite _) hlast hS] at hm
    exact lt_of_le_of_ne (segment_subset_Icc hVlast.le hm.1).2 hm.2
  -- The remaining open arc lies strictly above that line.
  have hmiddle {x : ℝ} (hx : x ∈ Ioo (a 0) (a (Fin.last n))) : V.im < (B x).im := by
    rw [(Complex.lt_def.mp hVfirst).2]
    exact im_schwarzChristoffelBoundary_first_lt a e z₀ ha he hsum hx
  have hne : ∀ x, B x ≠ V := by
    intro x
    by_cases hx₀ : x ≤ a 0
    · exact (hleft hx₀).ne'
    by_cases hxn : a (Fin.last n) ≤ x
    · exact (hright hxn).ne
    · intro h
      have hi := hmiddle ⟨lt_of_not_ge hx₀, lt_of_not_ge hxn⟩
      rw [h] at hi
      exact hi.false
  rw [schwarzChristoffelCompactifiedBoundary_injective_iff]
  refine ⟨?_, hne⟩
  -- Equality on each of the three arcs is already controlled; separate their images.
  have hbounded := schwarzChristoffelBoundary_injOn_prevertex_interval a e z₀ ha he hsum
  have hleftInj := schwarzChristoffelBoundary_injOn_Iic a e z₀ (hfinite _) hfirst
  have hrightInj := schwarzChristoffelBoundary_injOn_Ici a e z₀ (hfinite _) hlast
  suffices h : ∀ x y, x < y → B x ≠ B y by
    intro x y hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact False.elim (h x y hlt hxy)
    · exact heq
    · exact False.elim (h y x hgt hxy.symm)
  intro x y hxy heq
  by_cases hy₀ : y ≤ a 0
  · exact hxy.ne (hleftInj (hxy.le.trans hy₀) hy₀ heq)
  by_cases hxn : a (Fin.last n) ≤ x
  · exact hxy.ne (hrightInj hxn (hxn.trans hxy.le) heq)
  by_cases hx₀ : x ≤ a 0
  · by_cases hyn : a (Fin.last n) ≤ y
    · exact (hleft hx₀).not_ge (heq ▸ (hright hyn).le)
    · have hi := hmiddle ⟨lt_of_not_ge hy₀, lt_of_not_ge hyn⟩
      rw [← heq, ← (Complex.lt_def.mp (hleft hx₀)).2] at hi
      exact hi.false
  · by_cases hyn : a (Fin.last n) ≤ y
    · have hi := hmiddle ⟨lt_of_not_ge hx₀, lt_of_not_ge hxn⟩
      rw [heq, (Complex.lt_def.mp (hright hyn)).2] at hi
      exact hi.false
    · exact hxy.ne (hbounded ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
        ⟨(lt_of_not_ge hy₀).le, (lt_of_not_ge hyn).le⟩ heq)

/-- The polygon traced by a convex Schwarz--Christoffel boundary is a Jordan curve. The vertex
at infinity may subdivide a straight side; it need not be a genuine corner. -/
theorem isJordanCurve_schwarzChristoffelPolygon_boundary
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    IsJordanCurve ((schwarzChristoffelPolygon a e z₀).boundary ℝ) := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  have hS : ∑ k, e k < -1 := by rw [hsum]; norm_num
  rw [← range_schwarzChristoffelCompactifiedBoundary a e z₀ ha.monotone hfinite hS]
  exact isJordanCurve_range_schwarzChristoffelCompactifiedBoundary a e z₀ hfinite hS
    (schwarzChristoffelCompactifiedBoundary_injective a e z₀ ha he hsum)

end TauCeti
