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

/-- **Injectivity from three injective pieces.** Let `f` be injective on each of `Iic a`, `Icc a b`
and `Ici b`, with `a ≤ b`. If `f` maps `Iic a` into `S` and `Ici b` into `T` with `S` and `T`
disjoint, and a point of `Icc a b` mapped into `S` (respectively `T`) has the value `f a`
(respectively `f b`), then `f` is injective. -/
theorem injective_of_injOn_Iic_Icc_Ici {ι X : Type*} [LinearOrder ι] {f : ι → X} {a b : ι}
    {S T : Set X} (hab : a ≤ b) (hl : InjOn f (Iic a)) (hm : InjOn f (Icc a b))
    (hr : InjOn f (Ici b)) (hS : ∀ x ≤ a, f x ∈ S) (hT : ∀ x, b ≤ x → f x ∈ T)
    (hST : Disjoint S T) (hSa : ∀ y ∈ Icc a b, f y ∈ S → f y = f a)
    (hTb : ∀ y ∈ Icc a b, f y ∈ T → f y = f b) : Function.Injective f := by
  suffices h : ∀ x y, x < y → f x ≠ f y from fun x y hxy ↦ by
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact (h x y hlt hxy).elim
    · rfl
    · exact (h y x hgt hxy.symm).elim
  intro x y hxy heq
  by_cases hy₀ : y ≤ a
  · exact hxy.ne (hl (hxy.le.trans hy₀) hy₀ heq)
  by_cases hxn : b ≤ x
  · exact hxy.ne (hr hxn (hxn.trans hxy.le) heq)
  have hya := lt_of_not_ge hy₀
  have hxb := lt_of_not_ge hxn
  by_cases hx₀ : x ≤ a
  · by_cases hyn : b ≤ y
    · exact Set.disjoint_left.mp hST (hS x hx₀) (heq ▸ hT y hyn)
    · have hy := hSa y ⟨hya.le, (lt_of_not_ge hyn).le⟩ (heq ▸ hS x hx₀)
      exact hya.ne' (hm ⟨hya.le, (lt_of_not_ge hyn).le⟩ ⟨le_rfl, hab⟩ hy)
  · by_cases hyn : b ≤ y
    · have hx := hTb x ⟨(lt_of_not_ge hx₀).le, hxb.le⟩ (heq ▸ hT y hyn)
      exact hxb.ne (hm ⟨(lt_of_not_ge hx₀).le, hxb.le⟩ ⟨hab, le_rfl⟩ hx)
    · exact hxy.ne (hm ⟨(lt_of_not_ge hx₀).le, hxb.le⟩ ⟨hya.le, (lt_of_not_ge hyn).le⟩ heq)

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
    obtain ⟨i, hi⟩ := exists_mem_Icc_castSucc_succ a (Nat.succ_ne_zero n) hx
    refine ⟨i, ?_⟩
    rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc,
      ← schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
        (ha i.castSucc_le_succ)
        (fun k _ => not_mem_Ioo_castSucc_succ a ha i k) (hfinite _) (hfinite _)]
    exact ⟨x, hi, rfl⟩
  refine injective_of_injOn_Iic_Icc_Ici (ha (Fin.zero_le _)) hleftInj hbounded hrightInj
    (fun x hx ↦ ?_) (fun x hx ↦ ?_) houter (fun y hy hyL ↦ ?_) fun y hy hyR ↦ ?_
  · exact hleftImage ▸ ⟨x, hx, rfl⟩
  · exact hrightImage ▸ ⟨x, hx, rfl⟩
  · obtain ⟨i, hi⟩ := hmem y hy
    exact (hleft i (B y) hi (by simpa only [L, u] using hyL)).trans
      (schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)).symm
  · obtain ⟨i, hi⟩ := hmem y hy
    exact (hright i (B y) hi (by simpa only [R] using hyR)).trans
      (schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)).symm

end TauCeti

end
