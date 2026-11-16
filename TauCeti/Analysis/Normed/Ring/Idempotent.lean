/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Connected.Clopen

/-!
# Idempotents and square roots of unity in normed rings

Every nonzero idempotent `e` in a non-unital normed ring satisfies `1 ≤ ‖e‖`, since
submultiplicativity gives `‖e‖ = ‖e * e‖ ≤ ‖e‖ * ‖e‖`. In particular `0` is isolated among
idempotents, so the zero locus of a continuous idempotent-valued map on a preconnected space is
clopen and any such map that vanishes at one point vanishes identically.

When `2` is a unit in a normed ring `R` and `f : X → R` is a continuous map from a preconnected
space with `f x ^ 2 = 1` everywhere, the elements `2⁻¹ * (1 - f x)` are idempotent, so `f x₀ = 1`
at a single point forces `f x = 1` everywhere.

## Main results

* `IsIdempotentElem.one_le_norm`: every nonzero idempotent in a non-unital normed ring has norm at
  least `1`.
* `TauCeti.eq_zero_of_continuous_isIdempotentElem`: a continuous idempotent-valued map on a
  preconnected space that vanishes at one point is identically `0`.
* `TauCeti.eq_one_of_continuous_sq_eq_one`: a continuous map on a preconnected space into a normed
  ring in which `2` is a unit, taking values of square `1` and equal to `1` at one point, is
  identically `1`.
-/

public section

namespace IsIdempotentElem

/-- Every nonzero idempotent element of a non-unital normed ring has norm at least `1`. -/
theorem one_le_norm {R : Type*} [NonUnitalNormedRing R] {e : R}
    (he : IsIdempotentElem e) (h0 : e ≠ 0) : 1 ≤ ‖e‖ := by
  have hpos : 0 < ‖e‖ := norm_pos_iff.mpr h0
  have hle : ‖e‖ * 1 ≤ ‖e‖ * ‖e‖ := by
    rw [mul_one]
    nth_rewrite 1 [← he.eq]
    exact norm_mul_le e e
  exact le_of_mul_le_mul_left hle hpos

end IsIdempotentElem

namespace TauCeti

/-- A continuous map from a preconnected space into a non-unital normed ring whose values are all
idempotent and which vanishes at one point vanishes identically. -/
theorem eq_zero_of_continuous_isIdempotentElem {X R : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [NonUnitalNormedRing R] {e : X → R} (he : Continuous e)
    (hidem : ∀ x, IsIdempotentElem (e x)) {x₀ : X} (hx₀ : e x₀ = 0) (x : X) : e x = 0 := by
  have hclopen : IsClopen {y : X | e y = 0} := by
    refine ⟨isClosed_singleton.preimage he, ?_⟩
    have hset : {y : X | e y = 0} = e ⁻¹' Metric.ball 0 1 := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
      refine ⟨fun hy ↦ by simp [hy], fun hlt ↦ by_contra fun hne ↦ ?_⟩
      exact not_lt_of_ge ((hidem y).one_le_norm hne) hlt
    rw [hset]
    exact Metric.isOpen_ball.preimage he
  exact Set.eq_univ_iff_forall.mp (hclopen.eq_univ ⟨x₀, hx₀⟩) x

/-- A continuous map from a preconnected space into a normed ring in which `2` is a unit, taking
values of square `1` and equal to `1` at one point, is identically `1`. -/
theorem eq_one_of_continuous_sq_eq_one {X R : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [NormedRing R] (h2 : IsUnit (2 : R)) {f : X → R}
    (hf : Continuous f) {x₀ : X} (hx₀ : f x₀ = 1) (hsq : ∀ y, f y ^ 2 = 1) (x : X) :
    f x = 1 := by
  obtain ⟨u, hu⟩ := h2
  let inv2 : R := ↑u⁻¹
  let e : X → R := fun y ↦ inv2 * (1 - f y)
  have hcomm (r : R) : Commute inv2 r := by
    have hu_comm : Commute (u : R) r := by
      rw [hu]
      exact Commute.ofNat_left 2 r
    exact hu_comm.units_inv_left
  have he_cont : Continuous e := continuous_const.mul (continuous_const.sub hf)
  have he_idem (y : X) : IsIdempotentElem (e y) := by
    rw [IsIdempotentElem]
    have hsq' : (1 - f y) * (1 - f y) = (u : R) * (1 - f y) := by
      rw [hu, two_mul, sub_mul, one_mul, mul_sub, mul_one, ← sq, hsq y]
      abel
    calc
      e y * e y = inv2 * ((1 - f y) * inv2) * (1 - f y) := by simp only [e, mul_assoc]
      _ = inv2 * (inv2 * (1 - f y)) * (1 - f y) := by rw [(hcomm (1 - f y)).symm.eq]
      _ = inv2 * (inv2 * ((1 - f y) * (1 - f y))) := by simp only [mul_assoc]
      _ = inv2 * (inv2 * ((u : R) * (1 - f y))) := by rw [hsq']
      _ = e y := by
          rw [← mul_assoc inv2 (u : R)]
          simp only [inv2, Units.inv_mul, one_mul, e]
  have hx : e x = 0 :=
    eq_zero_of_continuous_isIdempotentElem he_cont he_idem (x₀ := x₀) (by simp [e, hx₀]) x
  have hsub : 1 - f x = 0 := by
    have := congrArg ((u : R) * ·) hx
    simpa [e, inv2, ← mul_assoc] using this
  exact (sub_eq_zero.mp hsub).symm

end TauCeti
