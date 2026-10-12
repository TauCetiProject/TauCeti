/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Ray
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.BoundedArcInjective

/-!
# Simplicity of unbounded Schwarz--Christoffel boundaries

When the total turning exponent is at least `-1`, a Schwarz--Christoffel boundary consists of
finitely many segments and two infinite rays. This file gives a finite geometric criterion for
that boundary to be simple: distinct bounded sides meet only at a shared consecutive vertex,
each outer ray meets the bounded sides only at its endpoint, and the two outer rays are disjoint.

The conclusion is injectivity of the boundary map on the real axis. Together with its properness,
this identifies the boundary as a proper simple polygonal chain and supplies the geometric input
for mapping the upper half-plane onto the region on one side of an unbounded polygon.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- If the bounded sides of an unbounded Schwarz--Christoffel boundary meet only at consecutive
vertices, each outer ray meets the bounded sides only at its finite endpoint, and the two outer
rays are disjoint, then the boundary map is injective. The exponents need only be integrable at
the finite prevertices, with total exponent at least `-1` so that the outer edges are rays. -/
theorem schwarzChristoffelBoundary_injective_of_edge_intersections
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l) (hsum : -1 ≤ ∑ k, e k)
    (hinter : ∀ (i j : Fin (n + 1)), i < j →
      ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
          j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ)
    (hleft : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (fun t : ℝ => schwarzChristoffelVertex a e z₀ 0 -
        (t : ℂ) * exp ((Real.pi * ∑ k, e k) * Complex.I)) '' Ici 0 →
        z = schwarzChristoffelVertex a e z₀ 0)
    (hright : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (fun t : ℝ => schwarzChristoffelVertex a e z₀ (Fin.last (n + 1)) + (t : ℂ)) ''
        Ici 0 → z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1)))
    (houter : Disjoint
      ((fun t : ℝ => schwarzChristoffelVertex a e z₀ 0 -
        (t : ℂ) * exp ((Real.pi * ∑ k, e k) * Complex.I)) '' Ici 0)
      ((fun t : ℝ => schwarzChristoffelVertex a e z₀ (Fin.last (n + 1)) + (t : ℂ)) ''
        Ici 0)) :
    Function.Injective (schwarzChristoffelBoundary a e z₀) := by
  let B := schwarzChristoffelBoundary a e z₀
  let L := schwarzChristoffelVertex a e z₀ 0
  let R := schwarzChristoffelVertex a e z₀ (Fin.last (n + 1))
  let u := exp ((Real.pi * ∑ k, e k) * Complex.I)
  have hfirst : ∀ k, e k ≠ 0 → a 0 ≤ a k := fun k _ => ha k.zero_le
  have hlast : ∀ k, e k ≠ 0 → a k ≤ a (Fin.last (n + 1)) :=
    fun k _ => ha k.le_last
  have hbounded : InjOn B (Icc (a 0) (a (Fin.last (n + 1)))) :=
    schwarzChristoffelBoundary_injOn_prevertex_interval_of_edge_intersections
      a e z₀ ha hfinite hinter
  have hleftInj : InjOn B (Iic (a 0)) :=
    schwarzChristoffelBoundary_injOn_Iic a e z₀ (hfinite 0) hfirst
  have hrightInj : InjOn B (Ici (a (Fin.last (n + 1)))) :=
    schwarzChristoffelBoundary_injOn_Ici a e z₀ (hfinite _) hlast
  have hleftImage : B '' Iic (a 0) = (fun t : ℝ => L - (t : ℂ) * u) '' Ici 0 := by
    simpa only [B, L, u] using
      schwarzChristoffelBoundary_image_Iic_eq_ray_prevertex a e z₀ 0 (hfinite 0) hfirst hsum
  have hrightImage : B '' Ici (a (Fin.last (n + 1))) =
      (fun t : ℝ => R + (t : ℂ)) '' Ici 0 := by
    simpa only [B, R] using
      schwarzChristoffelBoundary_image_Ici_eq_ray_prevertex a e z₀ (Fin.last (n + 1))
        (hfinite _) hlast hsum
  have hmem (x : ℝ) (hx : x ∈ Icc (a 0) (a (Fin.last (n + 1)))) :
      ∃ i : Fin (n + 1),
        B x ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc := by
    obtain ⟨i, hi⟩ := exists_mem_Icc_castSucc_succ a ha (Nat.succ_ne_zero n) hx
    refine ⟨i, ?_⟩
    rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc,
      ← schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
        (ha i.castSucc_le_succ)
        (fun k _ => not_mem_Ioo_castSucc_succ a ha i k) (hfinite _) (hfinite _)]
    exact ⟨x, hi, rfl⟩
  have hleftRay {x : ℝ} (hx : x ≤ a 0) : B x ∈ (fun t : ℝ => L - (t : ℂ) * u) '' Ici 0 := by
    rw [← hleftImage]
    exact ⟨x, hx, rfl⟩
  have hrightRay {x : ℝ} (hx : a (Fin.last (n + 1)) ≤ x) :
      B x ∈ (fun t : ℝ => R + (t : ℂ)) '' Ici 0 := by
    rw [← hrightImage]
    exact ⟨x, hx, rfl⟩
  suffices h : ∀ x y, x < y → B x ≠ B y by
    intro x y hxy
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact False.elim (h x y hlt hxy)
    · rfl
    · exact False.elim (h y x hgt hxy.symm)
  intro x y hxy heq
  by_cases hy₀ : y ≤ a 0
  · exact hxy.ne (hleftInj (hxy.le.trans hy₀) hy₀ heq)
  by_cases hxn : a (Fin.last (n + 1)) ≤ x
  · exact hxy.ne (hrightInj hxn (hxn.trans hxy.le) heq)
  by_cases hx₀ : x ≤ a 0
  · by_cases hyn : a (Fin.last (n + 1)) ≤ y
    · exact Set.disjoint_left.mp houter (hleftRay hx₀) (heq ▸ hrightRay hyn)
    · obtain ⟨i, hi⟩ := hmem y ⟨(lt_of_not_ge hy₀).le, (lt_of_not_ge hyn).le⟩
      have hyL := hleft i (B y) hi (by simpa only [L, u] using heq ▸ hleftRay hx₀)
      have hya : y = a 0 := hbounded
        ⟨(lt_of_not_ge hy₀).le, (lt_of_not_ge hyn).le⟩
        ⟨le_rfl, ha (Fin.zero_le _)⟩
        (hyL.trans (schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)).symm)
      exact (lt_of_not_ge hy₀).ne' hya
  · by_cases hyn : a (Fin.last (n + 1)) ≤ y
    · obtain ⟨i, hi⟩ := hmem x ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
      have hxR := hright i (B x) hi (by simpa only [R] using heq ▸ hrightRay hyn)
      have hxa : x = a (Fin.last (n + 1)) := hbounded
        ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
        ⟨ha (Fin.zero_le _), le_rfl⟩
        (hxR.trans (schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)).symm)
      exact (lt_of_not_ge hxn).ne hxa
    · exact hxy.ne (hbounded
        ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
        ⟨(lt_of_not_ge hy₀).le, (lt_of_not_ge hyn).le⟩ heq)

end TauCeti

end
