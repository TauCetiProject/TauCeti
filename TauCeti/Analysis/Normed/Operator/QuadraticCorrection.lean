/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Solving a nonlinear equation with a bounded right inverse and a quadratic remainder

Let `D : E → F` have a right inverse `Q`, an additive map with `‖Q y‖ ≤ C ‖y‖`, and consider the
equation

`e + D x + N x = 0`

for an unknown `x : E`, where `e : F` is a small residual and the nonlinear remainder `N`
vanishes at `0` and is quadratic on the ball of radius `δ`:

`‖N x - N y‖ ≤ (L / 2) (‖x‖ + ‖y‖) ‖x - y‖`  for `‖x‖, ‖y‖ ≤ δ`.

This is the form taken by an elliptic equation `S(x) = 0` expanded around an approximate solution,
`S(x) = S(0) + dS(0) x + N x`, once a right inverse `Q` of the linearization `D = dS(0)` with an
operator-norm bound `C` has been constructed. The quadratic estimate holds, for instance, for a
remainder `N x = B x x` built from a bounded bilinear map `B` with `‖B‖ ≤ L / 2`
(`ContinuousLinearMap.norm_apply_apply_sub_apply_apply_le`), such as the quadratic terms of the
Seiberg–Witten and vortex equations. This file gives the quantitative fixed-point argument used in
gluing constructions, with explicit radii.

* The solutions in the range of `Q` are the fixed points of `x ↦ -Q (e + N x)`
  (`TauCeti.mem_range_and_add_add_eq_zero_iff`).
* **A priori estimate.** A solution `x` in the range of `Q` is within `C` times the residual of
  every other point `y` of the range:
  `(1 - C L (‖x‖ + ‖y‖) / 2) ‖x - y‖ ≤ C ‖e + D y + N y‖`
  (`TauCeti.one_sub_mul_norm_sub_le_mul_norm_add_add`). In particular solutions depend
  Lipschitz-continuously on the residual `e` (`TauCeti.one_sub_mul_norm_sub_le_mul_norm_sub`).
* **Uniqueness.** Two solutions in the range of `Q` of norm at most `r ≤ δ` coincide as soon as
  `C L r < 1` (`TauCeti.eq_of_add_add_eq_zero`). The radius `r` may be much larger than the
  radius `2 C ‖e‖` where the solution is constructed.
* **Existence.** If `E` is complete, `2 C ‖e‖ ≤ δ` and `2 C² L ‖e‖ < 1`, then the map
  `x ↦ -Q (e + N x)` contracts the closed ball of radius `2 C ‖e‖`, and its fixed point is a
  solution `x` in the range of `Q` with `‖x‖ ≤ 2 C ‖e‖`
  (`TauCeti.exists_mem_range_norm_le_add_add_eq_zero`).

No linearity of `D`, and no topology or completeness of `F`, is needed. The right inverse `Q` is
only assumed additive, so that it applies to bounded linear maps over any normed field.

Mathlib's `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` gives existence of
some zero in a ball, and `ApproximatesLinearOn.exists_eq_zero_of_two_mul_norm_le` (in
`TauCeti.Analysis.Calculus.ApproximatesLinearOn`) a unique zero when the linearization is an
equivalence. Here the linearization only has a right inverse, and the
solution is singled out by lying in the range of `Q`; for linear `D` this range is a complement of
the kernel of `D`, chosen by the construction. The a priori estimate compares the solution with
arbitrary approximate solutions in that range.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Proposition A.3.4.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open Metric Set
open scoped NNReal

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [SeminormedAddCommGroup F] [FunLike G F E]
  [AddMonoidHomClass G F E] {Q : G} {D N : E → F} {e : F} {C L : ℝ≥0} {δ : ℝ}

/-- A point of the range of a right inverse `Q` of `D` solves `e + D x + N x = 0` exactly when it
is a fixed point of `x ↦ -Q (e + N x)`. -/
theorem mem_range_and_add_add_eq_zero_iff (hDQ : ∀ y, D (Q y) = y) {x : E} :
    (x ∈ range Q ∧ e + D x + N x = 0) ↔ x = -Q (e + N x) := by
  constructor
  · rintro ⟨⟨y, rfl⟩, h⟩
    rw [hDQ] at h
    have hy : y = -(e + N (Q y)) := eq_neg_of_add_eq_zero_left (by rw [← h]; abel)
    calc Q y = Q (-(e + N (Q y))) := by rw [← hy]
      _ = -Q (e + N (Q y)) := map_neg Q _
  · intro hx
    have hDx : D x = -(e + N x) := by
      conv_lhs => rw [hx]
      rw [← map_neg, hDQ]
    refine ⟨⟨-(e + N x), by rw [map_neg, ← hx]⟩, ?_⟩
    rw [hDx]
    abel

variable (hDQ : ∀ y, D (Q y) = y) (hQ : ∀ y, ‖Q y‖ ≤ C * ‖y‖)
  (hN : ∀ x ∈ closedBall (0 : E) δ, ∀ y ∈ closedBall (0 : E) δ,
    ‖N x - N y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
include hDQ hQ hN

/-- **A priori estimate.** A solution `x` of `e + D x + N x = 0` in the range of the right inverse
`Q` is close to every point `y` of the range with small residual: the distance is at most `C`
times the residual of `y`, up to the factor `1 - C L (‖x‖ + ‖y‖) / 2`. -/
theorem one_sub_mul_norm_sub_le_mul_norm_add_add {x y : E} (hx : x ∈ closedBall 0 δ)
    (hy : y ∈ closedBall 0 δ) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) :
    (1 - C * (L / 2 * (‖x‖ + ‖y‖))) * ‖x - y‖ ≤ C * ‖e + D y + N y‖ := by
  have hx' : x = -Q (e + N x) := (mem_range_and_add_add_eq_zero_iff hDQ).1 ⟨hxQ, hxe⟩
  obtain ⟨z, rfl⟩ := hyQ
  -- Writing `x = -Q (e + N x)` and `Q z = Q (D (Q z))`, the difference is `-Q` of the residual
  -- of `Q z` plus the difference of the remainders.
  have hsub : x - Q z = -Q ((e + D (Q z) + N (Q z)) + (N x - N (Q z))) := by
    calc x - Q z = -Q (e + N x) - Q z := by rw [← hx']
      _ = _ := by rw [hDQ]; simp only [map_add, map_sub]; abel
  have h := (hN x hx (Q z) hy)
  have hle : ‖x - Q z‖ ≤ C * ‖e + D (Q z) + N (Q z)‖ +
      C * (L / 2 * (‖x‖ + ‖Q z‖)) * ‖x - Q z‖ := by
    calc ‖x - Q z‖ ≤ C * ‖(e + D (Q z) + N (Q z)) + (N x - N (Q z))‖ := by
          rw [hsub, norm_neg]; exact hQ _
      _ ≤ C * (‖e + D (Q z) + N (Q z)‖ + L / 2 * (‖x‖ + ‖Q z‖) * ‖x - Q z‖) := by
          gcongr; exact (norm_add_le _ _).trans (by gcongr)
      _ = _ := by ring
  linarith

/-- Solutions of `e + D x + N x = 0` and `e' + D y + N y = 0` in the range of `Q` depend
Lipschitz-continuously on the residual. -/
theorem one_sub_mul_norm_sub_le_mul_norm_sub {e' : F} {x y : E} (hx : x ∈ closedBall 0 δ)
    (hy : y ∈ closedBall 0 δ) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) (hye : e' + D y + N y = 0) :
    (1 - C * (L / 2 * (‖x‖ + ‖y‖))) * ‖x - y‖ ≤ C * ‖e - e'‖ := by
  have h : e + D y + N y = e - e' := by
    rw [← sub_eq_zero, ← hye]
    abel
  simpa only [h] using one_sub_mul_norm_sub_le_mul_norm_add_add hDQ hQ hN hx hy hxQ hxe hyQ

/-- **Uniqueness.** Two solutions of `e + D x + N x = 0` in the range of `Q`, both of norm at most
`r ≤ δ`, coincide when `C L r < 1`. -/
theorem eq_of_add_add_eq_zero {r : ℝ} (hrδ : r ≤ δ) (hr : C * L * r < 1) {x y : E}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) (hye : e + D y + N y = 0) : x = y := by
  have h := one_sub_mul_norm_sub_le_mul_norm_add_add hDQ hQ hN
    (mem_closedBall_zero_iff.2 (hx.trans hrδ)) (mem_closedBall_zero_iff.2 (hy.trans hrδ)) hxQ hxe
    hyQ
  rw [hye, norm_zero, mul_zero] at h
  have hk : (L : ℝ) / 2 * (‖x‖ + ‖y‖) ≤ L * r := by
    have := add_le_add hx hy
    have hL : (0 : ℝ) ≤ L := L.2
    nlinarith
  have hpos : 0 < 1 - C * (L / 2 * (‖x‖ + ‖y‖)) := by
    have hC : (0 : ℝ) ≤ C := C.2
    nlinarith [mul_le_mul_of_nonneg_left hk hC]
  have hxy : ‖x - y‖ ≤ 0 := by
    by_contra hxy
    linarith [mul_pos hpos (not_le.1 hxy)]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hxy)

/-- **Existence.** If `E` is complete, `2 C ‖e‖ ≤ δ` and `2 C² L ‖e‖ < 1`, the equation
`e + D x + N x = 0` has a solution `x` in the range of `Q` with `‖x‖ ≤ 2 C ‖e‖`. It is the fixed
point of the contraction `x ↦ -Q (e + N x)` of the closed ball of radius `2 C ‖e‖`, and by
`TauCeti.eq_of_add_add_eq_zero` the only solution in the range of `Q` of norm at most `r`, for every
`r` with `2 C ‖e‖ ≤ r ≤ δ` and `C L r < 1`. -/
theorem exists_mem_range_norm_le_add_add_eq_zero [CompleteSpace E] (hN0 : N 0 = 0)
    (hδ : 2 * C * ‖e‖ ≤ δ) (he : 2 * C ^ 2 * L * ‖e‖ < 1) :
    ∃ x ∈ range Q, ‖x‖ ≤ 2 * C * ‖e‖ ∧ e + D x + N x = 0 := by
  set R : ℝ := 2 * C * ‖e‖ with hR
  have hC : (0 : ℝ) ≤ C := C.2
  have hL : (0 : ℝ) ≤ L := L.2
  have hR0 : 0 ≤ R := by positivity
  have hball : closedBall (0 : E) R ⊆ closedBall 0 δ := closedBall_subset_closedBall hδ
  set T : E → E := fun x ↦ -Q (e + N x) with hT
  -- On the ball of radius `R`, the remainder is bounded by `L ‖x‖² / 2`.
  have hsq (x : E) (hx : ‖x‖ ≤ R) : ‖N x‖ ≤ L / 2 * (‖x‖ * ‖x‖) := by
    have := hN x (hball (mem_closedBall_zero_iff.2 hx)) 0 (hball (mem_closedBall_self hR0))
    simpa [hN0, mul_assoc] using this
  have hmaps : MapsTo T (closedBall 0 R) (closedBall 0 R) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    calc ‖T x‖ ≤ C * ‖e + N x‖ := by rw [hT, norm_neg]; exact hQ _
      _ ≤ C * (‖e‖ + L / 2 * (R * R)) := by
          gcongr
          refine (norm_add_le e (N x)).trans ?_
          gcongr
          exact (hsq x hx).trans (by gcongr)
      _ = C * ‖e‖ * (1 + 2 * C ^ 2 * L * ‖e‖) := by rw [hR]; ring
      _ ≤ C * ‖e‖ * 2 := by gcongr; linarith
      _ = R := by rw [hR]; ring
  have hlip : LipschitzOnWith (Real.toNNReal (C * L * R)) T (closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    have hx' := mem_closedBall_zero_iff.1 hx
    have hy' := mem_closedBall_zero_iff.1 hy
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
    calc ‖T x - T y‖ = ‖Q (N x - N y)‖ := by
          rw [hT, ← norm_neg]; simp only [map_add, map_sub]; congr 1; abel
      _ ≤ C * (L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖) := by
          grw [hQ, hN x (hball hx) y (hball hy)]
      _ ≤ C * (L / 2 * (R + R) * ‖x - y‖) := by gcongr
      _ = C * L * R * ‖x - y‖ := by ring
  have hK : ContractingWith (Real.toNNReal (C * L * R)) (hmaps.restrict T _ _) :=
    ⟨Real.toNNReal_lt_one.2 (by rw [hR]; linarith), hlip.mapsToRestrict hmaps⟩
  obtain ⟨x, hxs, hfix, -⟩ := hK.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    (mem_closedBall_self hR0) (edist_ne_top _ _)
  obtain ⟨hxQ, hxe⟩ := (mem_range_and_add_add_eq_zero_iff hDQ).2 hfix.symm
  exact ⟨x, hxQ, mem_closedBall_zero_iff.1 hxs, hxe⟩

end TauCeti
