/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Turning

/-!
# Nonconvex corners of a Schwarz--Christoffel polygon

A nonzero turning exponent in `(-1, 1)` gives a genuine corner, including when the exponent is
positive and the polygon turns inward. Consequently the two sides incident to that finite vertex
meet only there. This is the local part of a geometric simplicity test for a nonconvex
Schwarz--Christoffel boundary; separation of nonadjacent sides remains a global condition.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {m : ℕ}

/-- Three vertices at consecutive strictly ordered prevertices form a noncollinear corner
provided the middle turning exponent is nonzero and all three exponent singularities are
integrable. Positive middle exponents, corresponding to reentrant corners, are allowed. -/
theorem affineIndependent_schwarzChristoffelVertex_of_consecutive_of_ne_zero
    (a e : Fin m → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    {j k l : Fin m} (hjk : j.val + 1 = k.val) (hkl : k.val + 1 = l.val)
    (hj : -1 < e j) (hk : e k ∈ Ioo (-1 : ℝ) 1) (hk0 : e k ≠ 0)
    (hl : -1 < e l) :
    AffineIndependent ℝ ![schwarzChristoffelVertex a e z₀ j,
      schwarzChristoffelVertex a e z₀ k,
      schwarzChristoffelVertex a e z₀ l] := by
  have hjk' : a j < a k := ha (Fin.mk_lt_mk.mpr (by omega))
  have hkl' : a k < a l := ha (Fin.mk_lt_mk.mpr (by omega))
  have hfree₁ : ∀ i, e i ≠ 0 → a i ∉ Ioo (a j) (a k) := by
    intro i _ hi
    have hji := Fin.lt_def.mp ((ha.lt_iff_lt).mp hi.1)
    have hik := Fin.lt_def.mp ((ha.lt_iff_lt).mp hi.2)
    omega
  have hfree₂ : ∀ i, e i ≠ 0 → a i ∉ Ioo (a k) (a l) := by
    intro i _ hi
    have hki := Fin.lt_def.mp ((ha.lt_iff_lt).mp hi.1)
    have hil := Fin.lt_def.mp ((ha.lt_iff_lt).mp hi.2)
    omega
  have hsum (i : Fin m) : ∑ t with a t = a i, e t = e i := by
    simp [ha.injective.eq_iff, Finset.filter_eq']
  exact affineIndependent_schwarzChristoffelVertex_of_adjacent
    a e z₀ j k l hjk' hkl' hfree₁ hfree₂
    (by rw [hsum]; exact hj) (by rw [hsum]; exact hk) (by rw [hsum]; exact hk0)
    (by rw [hsum]; exact hl)

/-- The two sides at a nonflat finite corner of a Schwarz--Christoffel polygon intersect only
at their common vertex, even when the corner is reentrant. -/
theorem schwarzChristoffelVertex_adjacent_segments_inter_eq
    (a e : Fin m → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    {j k l : Fin m} (hjk : j.val + 1 = k.val) (hkl : k.val + 1 = l.val)
    (hj : -1 < e j) (hk : e k ∈ Ioo (-1 : ℝ) 1) (hk0 : e k ≠ 0)
    (hl : -1 < e l) :
    segment ℝ (schwarzChristoffelVertex a e z₀ j) (schwarzChristoffelVertex a e z₀ k) ∩
      segment ℝ (schwarzChristoffelVertex a e z₀ k) (schwarzChristoffelVertex a e z₀ l) =
      {schwarzChristoffelVertex a e z₀ k} := by
  have hcorner := affineIndependent_schwarzChristoffelVertex_of_consecutive_of_ne_zero
    a e z₀ ha hjk hkl hj hk hk0 hl
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (1 : Fin 3),
    ← linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))] at hcorner
  have hlin : LinearIndependent ℝ
      ![schwarzChristoffelVertex a e z₀ j - schwarzChristoffelVertex a e z₀ k,
        schwarzChristoffelVertex a e z₀ l - schwarzChristoffelVertex a e z₀ k] := by
    convert! hcorner using 1
    ext i
    fin_cases i <;> simp [finSuccAboveEquiv_apply]
  rw [segment_symm ℝ (schwarzChristoffelVertex a e z₀ j)
    (schwarzChristoffelVertex a e z₀ k)]
  exact segment_inter_eq_endpoint_of_linearIndependent_sub ℝ hlin

end TauCeti
