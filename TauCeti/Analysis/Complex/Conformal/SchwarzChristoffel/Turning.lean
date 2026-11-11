/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.UnboundedEdge
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Between

/-!
# Turning at Schwarz--Christoffel vertices

The direction of a Schwarz--Christoffel boundary edge is
`exp (schwarzChristoffelEdgeAngle a e p * I)`.  When two consecutive edge intervals meet at a
prevertex `q`, their angle difference is `-π` times the total exponent at `q`.  Thus an exponent in
`(-1, 0)` makes the boundary turn strictly through an angle less than `π`. More generally, any
nonzero exponent in `(-1, 1)` gives a noncollinear corner, including an inward turn.

This file combines that angle calculation with the straight-edge description of
`SchwarzChristoffel.ClosedEdge`.  The main result says that the boundary values at three
consecutive prevertices are affinely independent.  In particular, the middle vertex is a genuine
corner rather than a subdivision point of a straight side.  This is the local nondegeneracy input
for proving that a Schwarz--Christoffel boundary chain is a simple polygon.

## Main results

* `TauCeti.schwarzChristoffelEdgeAngle_mem_Ioo_of_adjacent` -- the right-hand edge direction at a
  convex prevertex lies strictly between the left-hand direction and its half-turn.
* `TauCeti.affineIndependent_schwarzChristoffelBoundary_of_adjacent` -- three consecutive boundary
  values around a nonflat convex or reentrant prevertex are affinely independent.
* `TauCeti.affineIndependent_schwarzChristoffelVertex_of_adjacent` -- the corresponding indexed
  prevertex statement.
* `TauCeti.affineIndependent_schwarzChristoffelVertex_of_consecutive_of_ne_zero` -- the
  consecutive-index corner statement.
* `TauCeti.schwarzChristoffelVertex_adjacent_segments_inter_eq` -- adjacent sides meet only at
  their common vertex.
* `TauCeti.affineIndependent_schwarzChristoffelBoundary_left_endpoint` and
  `TauCeti.affineIndependent_schwarzChristoffelBoundary_right_endpoint` -- the first and last
  finite boundary vertices remain genuine corners where the boundary meets its closing sides.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped ComplexConjugate

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- At two adjacent prevertices, a middle exponent in `(-1, 0)` makes the boundary edge angle
increase strictly by less than `π` from the left-hand edge to the right-hand edge.

The exponent is the sum over every index carried by the right endpoint, so the statement also
covers coincident prevertices without selecting a distinguished representative. -/
theorem schwarzChristoffelEdgeAngle_mem_Ioo_of_adjacent (a e : ι → ℝ) {p q : ℝ}
    (hpq : p < q) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hq : ∑ i with a i = q, e i ∈ Ioo (-1 : ℝ) 0) :
    schwarzChristoffelEdgeAngle a e q ∈
      Ioo (schwarzChristoffelEdgeAngle a e p)
        (schwarzChristoffelEdgeAngle a e p + Real.pi) := by
  have hangle :=
    schwarzChristoffelEdgeAngle_sub_eq_pi_mul_exponent_sum_of_adjacent a e hpq ha
  constructor <;> nlinarith [Real.pi_pos, hq.1, hq.2]

/-- Three consecutive Schwarz--Christoffel boundary values around a non-flat prevertex are
affinely independent.

The hypotheses ask that the open intervals `(p, q)` and `(q, r)` contain no prevertex with
nonzero exponent, that the endpoint exponent sums at `p` and `r` exceed `-1`, and that the middle
exponent sum exceeds `-1` with a nonzero sine of its `π` multiple. The three boundary values are
therefore not collinear, so
`schwarzChristoffelBoundary a e z₀ q` is a genuine corner of the boundary chain. -/
theorem affineIndependent_schwarzChristoffelBoundary_of_adjacent (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q r : ℝ} (hpq : p < q) (hqr : q < r)
    (hpqFree : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hqrFree : ∀ i, e i ≠ 0 → a i ∉ Ioo q r)
    (hp : -1 < ∑ i with a i = p, e i)
    (hq : -1 < ∑ i with a i = q, e i)
    (hqSin : Real.sin (Real.pi * ∑ i with a i = q, e i) ≠ 0)
    (hr : -1 < ∑ i with a i = r, e i) :
    AffineIndependent ℝ ![schwarzChristoffelBoundary a e z₀ p,
      schwarzChristoffelBoundary a e z₀ q,
      schwarzChristoffelBoundary a e z₀ r] := by
  let B := schwarzChristoffelBoundary a e z₀
  let up := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  let uq := Complex.exp (schwarzChristoffelEdgeAngle a e q * Complex.I)
  have hangle := schwarzChristoffelEdgeAngle_sub_eq_pi_mul_exponent_sum_of_adjacent
    a e hpq hpqFree
  have hdet : up.re * uq.im - up.im * uq.re ≠ 0 := by
    have h : conj up * uq = Complex.exp
        (↑(schwarzChristoffelEdgeAngle a e q - schwarzChristoffelEdgeAngle a e p) * Complex.I) := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      simp only [map_mul, conj_ofReal, conj_I, ofReal_sub]
      ring_nf
    have him := congrArg Complex.im h
    have hdelta : schwarzChristoffelEdgeAngle a e q - schwarzChristoffelEdgeAngle a e p =
        -(Real.pi * ∑ i with a i = q, e i) := by linarith [hangle]
    rw [Complex.exp_ofReal_mul_I_im, hdelta, Real.sin_neg] at him
    simp only [Complex.mul_im, conj_re, conj_im] at him
    intro h0
    exact hqSin (by linarith)
  have hdir : LinearIndependent ℝ ![up, uq] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s * up.re + t * uq.re = 0 := by simpa using congrArg Complex.re hst
    have h2 : s * up.im + t * uq.im = 0 := by simpa using congrArg Complex.im hst
    exact ⟨(mul_eq_zero.mp (by linear_combination uq.im * h1 - uq.re * h2)).resolve_right hdet,
      (mul_eq_zero.mp (by linear_combination up.re * h2 - up.im * h1)).resolve_right hdet⟩
  have hpqEq : B q - B p = (‖B q - B p‖ : ℂ) * up :=
    schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ hpqFree hp hq
      ⟨hpq.le, le_rfl⟩ ⟨le_rfl, hpq.le⟩ hpq.le
  have hqrEq : B r - B q = (‖B r - B q‖ : ℂ) * uq :=
    schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ hqrFree hq hr
      ⟨hqr.le, le_rfl⟩ ⟨le_rfl, hqr.le⟩ hqr.le
  have hpqne : ‖B q - B p‖ ≠ 0 := norm_ne_zero_iff.mpr <| sub_ne_zero.mpr fun h ↦
    hpq.ne <| schwarzChristoffelBoundary_injOn_Icc a e z₀ hpqFree hp hq
      ⟨le_rfl, hpq.le⟩ ⟨hpq.le, le_rfl⟩ h.symm
  have hqrne : ‖B r - B q‖ ≠ 0 := norm_ne_zero_iff.mpr <| sub_ne_zero.mpr fun h ↦
    hqr.ne <| schwarzChristoffelBoundary_injOn_Icc a e z₀ hqrFree hq hr
      ⟨le_rfl, hqr.le⟩ ⟨hqr.le, le_rfl⟩ h.symm
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (1 : Fin 3),
    ← linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))]
  convert (LinearIndependent.pair_smul_smul_iff (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hpqne))
    (isUnit_iff_ne_zero.mpr hqrne)).2 hdir using 1
  ext i
  fin_cases i
  · simp [finSuccAboveEquiv_apply, Complex.real_smul, ← hpqEq, B]
  · simp [finSuccAboveEquiv_apply, Complex.real_smul, ← hqrEq, B]

/-- Three indexed Schwarz--Christoffel vertices at consecutive ordered prevertices are affinely
independent when the total exponent at the middle prevertex exceeds `-1` and its `π` multiple
has nonzero sine. -/
theorem affineIndependent_schwarzChristoffelVertex_of_adjacent (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j k l : ι) (hjk : a j < a k) (hkl : a k < a l)
    (hjkFree : ∀ i, e i ≠ 0 → a i ∉ Ioo (a j) (a k))
    (hklFree : ∀ i, e i ≠ 0 → a i ∉ Ioo (a k) (a l))
    (hj : -1 < ∑ i with a i = a j, e i)
    (hk : -1 < ∑ i with a i = a k, e i)
    (hkSin : Real.sin (Real.pi * ∑ i with a i = a k, e i) ≠ 0)
    (hl : -1 < ∑ i with a i = a l, e i) :
    AffineIndependent ℝ ![schwarzChristoffelVertex a e z₀ j,
      schwarzChristoffelVertex a e z₀ k, schwarzChristoffelVertex a e z₀ l] := by
  simpa only [schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ k hk,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ l hl] using
    affineIndependent_schwarzChristoffelBoundary_of_adjacent a e z₀ hjk hkl hjkFree hklFree
      hj hk hkSin hl

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
  have hkSin : Real.sin (Real.pi * e k) ≠ 0 :=
    sin_pi_mul_ne_zero_of_mem_Ioo_of_ne_zero hk hk0
  exact affineIndependent_schwarzChristoffelVertex_of_adjacent
    a e z₀ j k l hjk' hkl' hfree₁ hfree₂
    (by rw [hsum]; exact hj) (by rw [hsum]; exact hk.1) (by rw [hsum]; exact hkSin)
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


/-! ### Corners beside the vertex at infinity -/

/-- The first finite Schwarz--Christoffel boundary vertex is a genuine corner.  The left-hand
unbounded edge joins the vertex at infinity to `B p`, while the next finite edge joins `B p` to
`B q`; if the total exponent at `p` lies in `(-1, 0)`, these three points are affinely independent.

The hypothesis `ha` says that `p` is the leftmost prevertex with nonzero exponent. -/
theorem affineIndependent_schwarzChristoffelBoundary_left_endpoint (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (hpq : p < q)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i)
    (hpqFree : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : ∑ i with a i = p, e i ∈ Ioo (-1 : ℝ) 0)
    (hq : -1 < ∑ i with a i = q, e i) (hS : ∑ i, e i < -1) :
    AffineIndependent ℝ ![schwarzChristoffelVertexAtInfinity a e z₀,
      schwarzChristoffelBoundary a e z₀ p, schwarzChristoffelBoundary a e z₀ q] := by
  let x := p - 1
  let B := schwarzChristoffelBoundary a e z₀
  let V := schwarzChristoffelVertexAtInfinity a e z₀
  have hxp : x < p := by simp [x]
  have hxpFree : ∀ i, e i ≠ 0 → a i ∉ Ioo x p := by
    intro i hei hi
    exact (not_lt_of_ge (ha i hei)) hi.2
  have hxsum : ∑ i with a i = x, e i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hei
    have := ha i hei
    rw [hi] at this
    linarith
  have haff : AffineIndependent ℝ ![B x, B p, B q] := by
    apply affineIndependent_schwarzChristoffelBoundary_of_adjacent a e z₀ hxp hpq
      hxpFree hpqFree
    · rw [hxsum]
      norm_num
    · exact hp.1
    · exact sin_pi_mul_ne_zero_of_mem_Ioo_of_ne_zero
        ⟨hp.1, lt_trans hp.2 (by norm_num)⟩ hp.2.ne
    · exact hq
  have hximage : B x ∈ B '' Iic p := ⟨x, hxp.le, rfl⟩
  rw [schwarzChristoffelBoundary_image_Iic a e z₀ hp.1 ha hS] at hximage
  have hxspan : B x ∈ line[ℝ, B p, V] := by
    apply affineSegment_subset_affineSpan ℝ (B p) V
    rw [affineSegment_eq_segment]
    simpa [B, V] using hximage.1
  have hcol : Collinear ℝ ({B p, B x, V} : Set ℂ) := by
    simpa [insert_comm] using
      (collinear_insert_of_mem_affineSpan_pair hxspan)
  have hpV : B p ≠ V :=
    schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_ge a e z₀ hp.1 ha hS
  have hout : AffineIndependent ℝ ![B q, B p, V] :=
    affineIndependent_of_affineIndependent_collinear_ne haff.reverse_of_three hcol hpV
  exact hout.reverse_of_three

/-- The last finite Schwarz--Christoffel boundary vertex is a genuine corner.  The preceding
finite edge joins `B q` to `B p`, while the right-hand unbounded edge joins `B p` to the vertex at
infinity; if the total exponent at `p` lies in `(-1, 0)`, these three points are affinely
independent.

The hypothesis `ha` says that `p` is the rightmost prevertex with nonzero exponent. -/
theorem affineIndependent_schwarzChristoffelBoundary_right_endpoint (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {q p : ℝ} (hqp : q < p)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p)
    (hqpFree : ∀ i, e i ≠ 0 → a i ∉ Ioo q p)
    (hq : -1 < ∑ i with a i = q, e i)
    (hp : ∑ i with a i = p, e i ∈ Ioo (-1 : ℝ) 0) (hS : ∑ i, e i < -1) :
    AffineIndependent ℝ ![schwarzChristoffelBoundary a e z₀ q,
      schwarzChristoffelBoundary a e z₀ p, schwarzChristoffelVertexAtInfinity a e z₀] := by
  let x := p + 1
  let B := schwarzChristoffelBoundary a e z₀
  let V := schwarzChristoffelVertexAtInfinity a e z₀
  have hpx : p < x := by simp [x]
  have hpxFree : ∀ i, e i ≠ 0 → a i ∉ Ioo p x := by
    intro i hei hi
    exact (not_lt_of_ge (ha i hei)) hi.1
  have hxsum : ∑ i with a i = x, e i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hei
    have := ha i hei
    rw [hi] at this
    linarith
  have haff : AffineIndependent ℝ ![B q, B p, B x] := by
    apply affineIndependent_schwarzChristoffelBoundary_of_adjacent a e z₀ hqp hpx
      hqpFree hpxFree
    · exact hq
    · exact hp.1
    · exact sin_pi_mul_ne_zero_of_mem_Ioo_of_ne_zero
        ⟨hp.1, lt_trans hp.2 (by norm_num)⟩ hp.2.ne
    · rw [hxsum]
      norm_num
  have hximage : B x ∈ B '' Ici p := ⟨x, hpx.le, rfl⟩
  rw [schwarzChristoffelBoundary_image_Ici a e z₀ hp.1 ha hS] at hximage
  have hxspan : B x ∈ line[ℝ, B p, V] := by
    apply affineSegment_subset_affineSpan ℝ (B p) V
    rw [affineSegment_eq_segment]
    simpa [B, V] using hximage.1
  have hcol : Collinear ℝ ({B p, B x, V} : Set ℂ) := by
    simpa [insert_comm] using
      (collinear_insert_of_mem_affineSpan_pair hxspan)
  have hpV : B p ≠ V :=
    schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_le a e z₀ hp.1 ha hS
  exact affineIndependent_of_affineIndependent_collinear_ne haff hcol hpV

end TauCeti
