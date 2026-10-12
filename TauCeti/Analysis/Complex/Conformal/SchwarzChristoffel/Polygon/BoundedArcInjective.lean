/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Boundary

/-!
# Injectivity of the bounded Schwarz--Christoffel boundary arc

The boundary values between the first and last prevertices trace the finite sides of the
Schwarz--Christoffel polygon. If distinct sides meet only at their common endpoint when they are
consecutive, this parametrization is injective. The hypothesis is phrased entirely in terms of
the polygon's side segments, so it applies equally to convex and reentrant polygons. In the
nonconvex case it is the bridge from side-separation criteria to a simple compactified boundary.

This gives a bounded-arc injectivity criterion in terms of side intersections, including for
polygons with reentrant corners. No condition on the sum of the turning exponents at infinity is
needed for this bounded arc.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- If finite polygon sides meet only at the vertex shared by consecutive sides, the
Schwarz--Christoffel boundary is injective between its first and last finite prevertices.
The exponents need only be integrable at the finite prevertices. -/
theorem schwarzChristoffelBoundary_injOn_prevertex_interval_of_edge_intersections
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (hinter : ∀ (i j : Fin n), i < j →
      ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
          j.val = i.val + 1 ∧
            z = schwarzChristoffelVertex a e z₀ i.succ) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Icc (a 0) (a (Fin.last n))) := by
  let B := schwarzChristoffelBoundary a e z₀
  have hfree (i : Fin n) :
      ∀ k, e k ≠ 0 → a k ∉ Ioo (a i.castSucc) (a i.succ) :=
    fun k _ ↦ not_mem_Ioo_castSucc_succ a ha i k
  have hinterval (i : Fin n) :
      InjOn B (Icc (a i.castSucc) (a i.succ)) :=
    schwarzChristoffelBoundary_injOn_Icc a e z₀ (hfree i) (hfinite _) (hfinite _)
  have hmem {i : Fin n} {x : ℝ} (hx : x ∈ Icc (a i.castSucc) (a i.succ)) :
      B x ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc := by
    rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc,
      ← schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
        (ha i.castSucc_le_succ) (hfree i) (hfinite _) (hfinite _)]
    exact ⟨x, hx, rfl⟩
  have hpair (i j : Fin n) (hij : i ≤ j) {x y : ℝ}
      (hx : x ∈ Icc (a i.castSucc) (a i.succ))
      (hy : y ∈ Icc (a j.castSucc) (a j.succ)) (hxy : B x = B y) : x = y := by
    rcases hij.eq_or_lt with rfl | hij
    · exact hinterval i hx hy hxy
    have ⟨hadj, hvertex⟩ := hinter i j hij (B x) (hmem hx) (hxy ▸ hmem hy)
    have hmid : i.succ = j.castSucc :=
      Fin.ext (by simpa only [Fin.val_succ, Fin.val_castSucc] using hadj.symm)
    have hx' : x = a i.succ := by
      rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)] at hvertex
      exact hinterval i hx ⟨ha i.castSucc_le_succ, le_rfl⟩ hvertex
    have hy' : y = a j.castSucc := by
      have hv : B y = schwarzChristoffelVertex a e z₀ i.succ := hxy.symm.trans hvertex
      rw [hmid] at hv
      rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)] at hv
      exact hinterval j hy ⟨le_rfl, ha j.castSucc_le_succ⟩ hv
    exact hx'.trans ((congrArg a hmid).trans hy'.symm)
  by_cases hn : n = 0
  · subst n
    simpa only [Fin.last_zero, Icc_self] using (injOn_singleton B (a 0))
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := exists_mem_Icc_castSucc_succ a ha hn hx
  obtain ⟨j, hj⟩ := exists_mem_Icc_castSucc_succ a ha hn hy
  rcases le_total i j with hij | hji
  · exact hpair i j hij hi hj hxy
  · exact (hpair j i hji hj hi hxy.symm).symm

end TauCeti
