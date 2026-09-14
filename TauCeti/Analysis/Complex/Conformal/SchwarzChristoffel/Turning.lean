/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.ClosedEdge

/-!
# Turning at Schwarz--Christoffel vertices

The direction of a Schwarz--Christoffel boundary edge is
`exp (schwarzChristoffelEdgeAngle a e p * I)`.  When two consecutive edge intervals meet at a
prevertex `q`, their angle difference is `-π` times the total exponent at `q`.  Thus an exponent in
`(-1, 0)` makes the boundary turn strictly through an angle less than `π`.

This file combines that angle calculation with the straight-edge description of
`SchwarzChristoffel.ClosedEdge`.  The main result says that the boundary values at three
consecutive prevertices are affinely independent.  In particular, the middle vertex is a genuine
corner rather than a subdivision point of a straight side.  This is the local nondegeneracy input
for proving that a Schwarz--Christoffel boundary chain is a simple polygon.

## Main results

* `TauCeti.schwarzChristoffelEdgeAngle_mem_Ioo_of_adjacent` -- the right-hand edge direction at a
  convex prevertex lies strictly between the left-hand direction and its half-turn.
* `TauCeti.affineIndependent_schwarzChristoffelBoundary_of_adjacent` -- three consecutive boundary
  values around a convex prevertex are affinely independent.
* `TauCeti.affineIndependent_schwarzChristoffelVertex_of_adjacent` -- the corresponding indexed
  prevertex statement.

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

/-- Three consecutive Schwarz--Christoffel boundary values around a prevertex of total exponent
in `(-1, 0)` are affinely independent.

The two adjacent intervals contain no prevertex with nonzero exponent.  Their boundary images are
therefore nondegenerate straight segments, and the middle exponent turns their directions through
a strictly positive angle less than `π`; consequently the two displacement vectors are linearly
independent over `ℝ`. -/
theorem affineIndependent_schwarzChristoffelBoundary_of_adjacent (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q r : ℝ} (hpq : p < q) (hqr : q < r)
    (hpqFree : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hqrFree : ∀ i, e i ≠ 0 → a i ∉ Ioo q r)
    (hp : -1 < ∑ i with a i = p, e i)
    (hq : ∑ i with a i = q, e i ∈ Ioo (-1 : ℝ) 0)
    (hr : -1 < ∑ i with a i = r, e i) :
    AffineIndependent ℝ ![schwarzChristoffelBoundary a e z₀ p,
      schwarzChristoffelBoundary a e z₀ q,
      schwarzChristoffelBoundary a e z₀ r] := by
  let B := schwarzChristoffelBoundary a e z₀
  let up := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  let uq := Complex.exp (schwarzChristoffelEdgeAngle a e q * Complex.I)
  have hangle := schwarzChristoffelEdgeAngle_mem_Ioo_of_adjacent a e hpq hpqFree hq
  have hdet : 0 < (conj up * uq).im := by
    have hexp :
        conj (schwarzChristoffelEdgeAngle a e p * Complex.I) +
            schwarzChristoffelEdgeAngle a e q * Complex.I =
          (schwarzChristoffelEdgeAngle a e q -
            schwarzChristoffelEdgeAngle a e p) * Complex.I := by
      simp only [map_mul, conj_ofReal, conj_I]
      ring
    dsimp only [up, uq]
    rw [← Complex.exp_conj, ← Complex.exp_add, hexp]
    simpa only [← Complex.ofReal_sub, Complex.exp_ofReal_mul_I_im] using
      Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hangle.1)
        (sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hangle.2))
  have hdir : LinearIndependent ℝ ![up, uq] := by
    rw [linearIndependent_fin2]
    constructor
    · intro huq
      have : uq = 0 := by simpa using huq
      simp [this] at hdet
    · intro t ht
      have ht' : (t : ℂ) * uq = up := by
        simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.real_smul] using ht
      have him : (conj up * uq).im = 0 := by
        rw [← ht']
        simp only [map_mul, conj_ofReal, mul_assoc]
        rw [Complex.conj_mul']
        have hpowim : ((‖uq‖ : ℂ) ^ 2).im = 0 := by
          rw [← Complex.ofReal_pow, Complex.ofReal_im]
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hpowim]
        ring
      linarith
  have hpqEq : B q - B p = (‖B q - B p‖ : ℂ) * up := by
    exact schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ hpqFree hp hq.1
      ⟨hpq.le, le_rfl⟩ ⟨le_rfl, hpq.le⟩ hpq.le
  have hqrEq : B r - B q = (‖B r - B q‖ : ℂ) * uq := by
    exact schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ hqrFree hq.1 hr
      ⟨hqr.le, le_rfl⟩ ⟨le_rfl, hqr.le⟩ hqr.le
  have hpqne : B q - B p ≠ 0 := sub_ne_zero.mpr <|
    fun h => hpq.ne <| schwarzChristoffelBoundary_injOn_Icc a e z₀ hpqFree hp hq.1
      ⟨le_rfl, hpq.le⟩ ⟨hpq.le, le_rfl⟩ h.symm
  have hqrne : B r - B q ≠ 0 := sub_ne_zero.mpr <|
    fun h => hqr.ne <| schwarzChristoffelBoundary_injOn_Icc a e z₀ hqrFree hq.1 hr
      ⟨le_rfl, hqr.le⟩ ⟨hqr.le, le_rfl⟩ h.symm
  have hscaled : LinearIndependent ℝ
      ![-(‖B q - B p‖ • up), ‖B r - B q‖ • uq] := by
    have hs : LinearIndependent ℝ
        ![‖B q - B p‖ • up, ‖B r - B q‖ • uq] :=
      (LinearIndependent.pair_smul_smul_iff
        (isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mpr hpqne))
        (isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mpr hqrne))).2 hdir
    simpa only [_root_.neg_smul] using
      (LinearIndependent.pair_neg_left_iff (R := ℝ)).2 hs
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (1 : Fin 3), ←
    linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))]
  have hfamily :
      ((fun i : {x : Fin 3 // x ≠ 1} =>
          (![B p, B q, B r] i -ᵥ ![B p, B q, B r] 1 : ℂ)) ∘
        (finSuccAboveEquiv (1 : Fin 3))) =
        ![-(‖B q - B p‖ • up), ‖B r - B q‖ • uq] := by
    funext i
    fin_cases i
    · simp only [Function.comp_apply, finSuccAboveEquiv_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      calc
        B p - B q = -(B q - B p) := by ring
        _ = -((‖B q - B p‖ : ℂ) * up) := congrArg Neg.neg hpqEq
        _ = -(‖B q - B p‖ • up) := by rw [Complex.real_smul]
    · simp only [Function.comp_apply, finSuccAboveEquiv_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      calc
        B r - B q = (‖B r - B q‖ : ℂ) * uq := hqrEq
        _ = ‖B r - B q‖ • uq := by rw [Complex.real_smul]
  rw [hfamily]
  exact hscaled

/-- Three indexed Schwarz--Christoffel vertices at consecutive ordered prevertices are affinely
independent when the total exponent at the middle prevertex lies in `(-1, 0)`. -/
theorem affineIndependent_schwarzChristoffelVertex_of_adjacent (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j k l : ι) (hjk : a j < a k) (hkl : a k < a l)
    (hjkFree : ∀ i, e i ≠ 0 → a i ∉ Ioo (a j) (a k))
    (hklFree : ∀ i, e i ≠ 0 → a i ∉ Ioo (a k) (a l))
    (hj : -1 < ∑ i with a i = a j, e i)
    (hk : ∑ i with a i = a k, e i ∈ Ioo (-1 : ℝ) 0)
    (hl : -1 < ∑ i with a i = a l, e i) :
    AffineIndependent ℝ ![schwarzChristoffelVertex a e z₀ j,
      schwarzChristoffelVertex a e z₀ k, schwarzChristoffelVertex a e z₀ l] := by
  simpa only [schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ k hk.1,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ l hl] using
    affineIndependent_schwarzChristoffelBoundary_of_adjacent a e z₀ hjk hkl hjkFree hklFree
      hj hk hl

end TauCeti
