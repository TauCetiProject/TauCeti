/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Turning

/-!
# Nondegeneracy of the Schwarz--Christoffel polygon

Strictly ordered prevertices with integrable exponents produce distinct consecutive
Schwarz--Christoffel vertices.  The two closing sides are nondegenerate as well: their common
endpoint at infinity differs from the first and last finite vertices.  Consequently every edge of
the packaged Schwarz--Christoffel polygon is nondegenerate.

When there are at least two finite prevertices, the turning-exponent condition `(-1, 0)` also makes
the first and last finite vertices genuine corners.  These are the endpoint counterparts of the
interior-corner theorem in `SchwarzChristoffel.Turning`.  The appended vertex at infinity is not
claimed to be a corner: under the classical exponent sum, it can merely subdivide one straight
closing side.

Together, these results supply the local nondegeneracy needed before separating nonadjacent sides
in the global simplicity argument.

## Main results

* `TauCeti.affineIndependent_schwarzChristoffelPolygon_first` and
  `TauCeti.affineIndependent_schwarzChristoffelPolygon_last` -- the two finite endpoint vertices
  are genuine corners.
* `TauCeti.schwarzChristoffelPolygon_hasNondegenerateEdges` -- every side of the packaged polygon
  has distinct endpoints.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- The first finite vertex of a Schwarz--Christoffel polygon is a genuine corner: it is affinely
independent from the vertex at infinity and the next finite vertex.

The family has `n + 2` finite prevertices so that a next vertex always exists. -/
theorem affineIndependent_schwarzChristoffelPolygon_first (a e : Fin (n + 2) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfirst : ∑ i with a i = a 0, e i ∈ Ioo (-1 : ℝ) 0)
    (hnext : -1 < ∑ i with a i = a 1, e i)
    (hS : ∑ i, e i < -1) :
    AffineIndependent ℝ ![schwarzChristoffelVertexAtInfinity a e z₀,
      schwarzChristoffelVertex a e z₀ 0, schwarzChristoffelVertex a e z₀ 1] := by
  have h01 : a 0 < a 1 := ha (by simp)
  have hleft : ∀ i, e i ≠ 0 → a 0 ≤ a i := by
    intro i _
    exact ha.monotone i.zero_le
  have hfree : ∀ i, e i ≠ 0 → a i ∉ Ioo (a 0) (a 1) := by
    intro i _ hi
    have h0i : (0 : Fin (n + 2)) < i := (ha.lt_iff_lt).mp hi.1
    have hi1 : i < (1 : Fin (n + 2)) := (ha.lt_iff_lt).mp hi.2
    exact (not_lt_of_ge (Fin.one_le_of_ne_zero h0i.ne')) hi1
  simpa only [schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 hfirst.1,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ 1 hnext] using
    affineIndependent_schwarzChristoffelBoundary_left_endpoint a e z₀ h01 hleft hfree hfirst
      hnext hS

/-- The last finite vertex of a Schwarz--Christoffel polygon is a genuine corner: it is affinely
independent from the preceding finite vertex and the vertex at infinity.

The family has `n + 2` finite prevertices so that a preceding vertex always exists. -/
theorem affineIndependent_schwarzChristoffelPolygon_last (a e : Fin (n + 2) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hpreceding : -1 < ∑ i with a i = a (Fin.last n).castSucc, e i)
    (hlast : ∑ i with a i = a (Fin.last (n + 1)), e i ∈ Ioo (-1 : ℝ) 0)
    (hS : ∑ i, e i < -1) :
    AffineIndependent ℝ
      ![schwarzChristoffelVertex a e z₀ (Fin.last n).castSucc,
        schwarzChristoffelVertex a e z₀ (Fin.last (n + 1)),
        schwarzChristoffelVertexAtInfinity a e z₀] := by
  have horder : a (Fin.last n).castSucc < a (Fin.last (n + 1)) := by
    apply ha
    exact (Fin.last n).castSucc_lt_succ
  have hright : ∀ i, e i ≠ 0 → a i ≤ a (Fin.last (n + 1)) := by
    intro i _
    exact ha.monotone i.le_last
  have hfree : ∀ i, e i ≠ 0 →
      a i ∉ Ioo (a (Fin.last n).castSucc) (a (Fin.last (n + 1))) := by
    intro i _ hi
    have hprevi : (Fin.last n).castSucc < i := (ha.lt_iff_lt).mp hi.1
    have hilast : i < Fin.last (n + 1) := (ha.lt_iff_lt).mp hi.2
    have hprevi' := Fin.lt_def.mp hprevi
    have hilast' := Fin.lt_def.mp hilast
    simp only [Fin.val_castSucc, Fin.val_last] at hprevi' hilast'
    omega
  simpa only [schwarzChristoffelBoundary_apply_prevertex a e z₀
      (Fin.last n).castSucc hpreceding,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ (Fin.last (n + 1)) hlast.1] using
    affineIndependent_schwarzChristoffelBoundary_right_endpoint a e z₀ horder hright hfree
      hpreceding hlast hS

/-- Every edge of the Schwarz--Christoffel polygon has distinct endpoints when the finite
prevertices are strictly ordered, all their total exponents are integrable, and the primitive
decays sufficiently to have a finite vertex at infinity. -/
theorem schwarzChristoffelPolygon_hasNondegenerateEdges (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hS : ∑ i, e i < -1) :
    (schwarzChristoffelPolygon a e z₀).HasNondegenerateEdges := by
  intro i
  refine Fin.lastCases (motive := fun i =>
    schwarzChristoffelPolygon a e z₀ i ≠
      schwarzChristoffelPolygon a e z₀ (finRotate (n + 2) i)) ?_ ?_ i
  · rw [finRotate_last, schwarzChristoffelPolygon_apply_last]
    simp only [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl,
      schwarzChristoffelPolygon_apply_castSucc]
    rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)]
    exact (schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_ge a e z₀ (hfinite 0)
      (fun i _ ↦ ha.monotone i.zero_le) hS).symm
  · intro j
    refine Fin.lastCases (motive := fun j =>
      schwarzChristoffelPolygon a e z₀ j.castSucc ≠
        schwarzChristoffelPolygon a e z₀ (finRotate (n + 2) j.castSucc)) ?_ ?_ j
    · have hrotate : finRotate (n + 2) (Fin.last n).castSucc = Fin.last (n + 1) := by
        apply Fin.ext
        simp
      rw [hrotate, schwarzChristoffelPolygon_apply_castSucc,
        schwarzChristoffelPolygon_apply_last]
      rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ (Fin.last n) (hfinite _)]
      exact schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_le a e z₀ (hfinite _)
        (fun i _ ↦ ha.monotone i.le_last) hS
    · intro j
      have hrotate : finRotate (n + 2) j.castSucc.castSucc = j.succ.castSucc := by
        apply Fin.ext
        simp
      rw [hrotate, schwarzChristoffelPolygon_apply_castSucc,
        schwarzChristoffelPolygon_apply_castSucc]
      apply schwarzChristoffelVertex_ne a e z₀ (ha j.castSucc_lt_succ)
      · intro i _ hi
        have hji : j.castSucc < i := (ha.lt_iff_lt).mp hi.1
        have hij : i < j.succ := (ha.lt_iff_lt).mp hi.2
        have hji' := Fin.lt_def.mp hji
        have hij' := Fin.lt_def.mp hij
        simp only [Fin.val_castSucc, Fin.val_succ] at hji' hij'
        omega
      · exact hfinite _
      · exact hfinite _

end TauCeti
