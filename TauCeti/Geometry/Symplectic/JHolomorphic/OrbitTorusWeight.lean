/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.Geometry.Symplectic.JHolomorphic.TorusWeight
public import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo

/-!
# Four-twist weights of orbit tori and the signed iterates of the return map

Let `φ` be an area-preserving diffeomorphism of a closed surface and `Y_φ` its mapping torus. In
the symplectic four-manifold `S¹ × Y_φ` a periodic orbit `γ` of `φ` gives an embedded
square-zero torus `S¹ × γ`, and the normal operator of this torus is governed by the linearized
return map `P` of `γ`, a `2 × 2` matrix of determinant one. Of the four normal operators of the
torus twisted by its real sign characters, the two twisted along the circle factor are expected to
have positive determinant sign, while the untwisted operator and the operator twisted only along
`γ` compare with `det (1 - P)` and `det (1 + P)`. The four-twist label `(σ, i)` of Taubes's
weighted count that these signs prescribe has `σ` the sign of `det (1 - P)`, and `i` equal to `1`
or `0` according as `det (1 + P)` is negative or not. Since `det (1 ∓ P) = 2 ∓ trace P`, a
return map all of whose iterates are nondegenerate falls into one of three classes:

* positive hyperbolic (`2 < trace P`), with label `(-, 0)` and local series `1 - t`;
* negative hyperbolic (`trace P < -2`), with label `(+, 1)` and local series `1 + t`;
* elliptic (`|trace P| < 2`), with label `(+, 0)` and local series `1 / (1 - t)`.

This file proves that in each class the local series `f = f_(σ, i)` of `TauCeti.torusWeightSeries`
satisfies the logarithmic derivative identity

`t f'(t) = f(t) ∑_{k ≥ 1} ε(P ^ k) t ^ k`,    `ε(Q) = sgn det (1 - Q)`,

provided every iterate of `P` is nondegenerate, `det (1 - P ^ k) ≠ 0` for `k ≥ 1`. Here `ε(P ^ k)`
is the Lefschetz index of the fixed point of the `k`-th iterate of the return map. Over `ℚ` the
identity says that `log f = ∑_{k ≥ 1} ε(P ^ k) t ^ k / k`, so that `f` is the factor that the orbit
`γ` contributes to the dynamical zeta function `exp ∑_n L(φ ^ n) t ^ n / n`. Taubes's weights of
the orbit tori thus reproduce the local factors of the Lefschetz zeta function, which is the local
input to the comparison of the curve count of `S¹ × Y_φ` with the zeta function of `φ`.

That the determinant signs of the twisted normal operators of the orbit torus are those of
`det (1 ∓ P)` is a determinant comparison which this file does not prove; the statements here are
about the label that the signs of `det (1 ∓ P)` prescribe.

## Main results

* `TauCeti.X_mul_derivative_torusWeightSeries_false_zero_of_two_lt_trace`: the identity for a
  positive hyperbolic return map and the series `f_(-, 0) = 1 - t`.
* `TauCeti.X_mul_derivative_torusWeightSeries_true_one_of_trace_lt_neg_two`: the identity for a
  negative hyperbolic return map and the series `f_(+, 1) = 1 + t`.
* `TauCeti.X_mul_derivative_torusWeightSeries_true_zero_of_abs_trace_le_two`: the identity for a
  nondegenerate elliptic return map and the series `f_(+, 0) = 1 / (1 - t)`.
* `TauCeti.X_mul_derivative_torusWeightSeries_of_det_eq_one`: the identity for every return map
  all of whose iterates are nondegenerate, with the label read off from the signs of
  `det (1 - P)` and `det (1 + P)`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127--158.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and
  Seiberg–Witten invariants of 3-manifolds*, Topology 38 (1999), 861--888.
-/

public section

open PowerSeries Matrix

namespace TauCeti

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {P : Matrix (Fin 2) (Fin 2) R}

/-- For a positive hyperbolic `2 × 2` matrix `P` of determinant one (`2 < trace P`), the local
series `f_(-, 0) = 1 - t` satisfies `t f' = f ∑_{k ≥ 1} sgn det (1 - P ^ k) t ^ k`: every iterate
of `P` has `det (1 - P ^ k) < 0`, and `1 - t = exp (-∑_{k ≥ 1} t ^ k / k)`. -/
theorem X_mul_derivative_torusWeightSeries_false_zero_of_two_lt_trace (hdet : P.det = 1)
    (htr : 2 < P.trace) :
    X * d⁄dX (torusWeightSeries false 0) = torusWeightSeries false 0 *
      mk fun k ↦ if k = 0 then 0 else (SignType.sign (1 - P ^ k).det : ℤ) := by
  have hS : (mk fun k ↦ if k = 0 then 0 else (SignType.sign (1 - P ^ k).det : ℤ)) =
      mk fun k ↦ if k = 0 then 0 else -1 := by
    congr 1
    funext k
    split_ifs with hk
    · rfl
    · simp [sign_neg (det_one_sub_pow_neg_of_two_lt_trace hdet htr hk)]
  have hX : (mk fun k ↦ if k = 0 then 0 else -1 : ℤ⟦X⟧) = -(X * mk 1) := by
    ext (_ | k) <;> simp [coeff_succ_X_mul]
  -- Both sides are `-X`, as `(1 - X) * mk 1 = 1`.
  rw [hS, hX, torusWeightSeries_false_zero]
  simp only [map_sub, derivative_one, derivative_X]
  linear_combination X * mk_one_mul_one_sub_eq_one (S := ℤ)

/-- For a negative hyperbolic `2 × 2` matrix `P` of determinant one (`trace P < -2`), the local
series `f_(+, 1) = 1 + t` satisfies `t f' = f ∑_{k ≥ 1} sgn det (1 - P ^ k) t ^ k`: the sign of
`det (1 - P ^ k)` is `(-1) ^ (k + 1)`, and `1 + t = exp ∑_{k ≥ 1} (-1) ^ (k + 1) t ^ k / k`. -/
theorem X_mul_derivative_torusWeightSeries_true_one_of_trace_lt_neg_two (hdet : P.det = 1)
    (htr : P.trace < -2) :
    X * d⁄dX (torusWeightSeries true 1) = torusWeightSeries true 1 *
      mk fun k ↦ if k = 0 then 0 else (SignType.sign (1 - P ^ k).det : ℤ) := by
  have hS : (mk fun k ↦ if k = 0 then 0 else (SignType.sign (1 - P ^ k).det : ℤ)) =
      mk fun k ↦ if k = 0 then 0 else (-1) ^ (k + 1) := by
    congr 1
    funext k
    split_ifs with hk
    · rfl
    rcases k.even_or_odd with he | ho
    · simp [sign_neg (det_one_sub_pow_neg_of_trace_lt_neg_two hdet htr he hk),
        he.add_one.neg_one_pow]
    · simp [sign_pos (det_one_sub_pow_pos_of_trace_lt_neg_two hdet htr ho),
        ho.add_one.neg_one_pow]
  have hX : (mk fun k ↦ if k = 0 then 0 else (-1) ^ (k + 1) : ℤ⟦X⟧) =
      X * mk fun k ↦ (-1) ^ k := by
    ext (_ | k) <;> simp [coeff_succ_X_mul, pow_succ]
  -- Both sides are `X`, as `(mk fun k ↦ (-1) ^ k) * (1 + X) = 1`.
  rw [hS, hX, torusWeightSeries_true_one]
  simp only [map_add, derivative_one, derivative_X]
  linear_combination (-X) * mk_neg_one_pow_mul_one_add_eq_one (S := ℤ)

/-- For a `2 × 2` matrix `P` of determinant one with `|trace P| ≤ 2`, all of whose iterates are
nondegenerate (so that `P` is elliptic), the local series `f_(+, 0) = 1 / (1 - t)` satisfies
`t f' = f ∑_{k ≥ 1} sgn det (1 - P ^ k) t ^ k`: every iterate has `0 < det (1 - P ^ k)`, and
`1 / (1 - t) = exp ∑_{k ≥ 1} t ^ k / k`. -/
theorem X_mul_derivative_torusWeightSeries_true_zero_of_abs_trace_le_two (hdet : P.det = 1)
    (htr : |P.trace| ≤ 2) (hP : ∀ k ≠ 0, (1 - P ^ k).det ≠ 0) :
    X * d⁄dX (torusWeightSeries true 0) = torusWeightSeries true 0 *
      mk fun k ↦ if k = 0 then 0 else (SignType.sign (1 - P ^ k).det : ℤ) := by
  have hS : (mk fun k ↦ if k = 0 then 0 else (SignType.sign (1 - P ^ k).det : ℤ)) =
      mk fun k ↦ if k = 0 then 0 else 1 := by
    congr 1
    funext k
    split_ifs with hk
    · rfl
    · simp [sign_pos ((det_one_sub_pow_nonneg_of_abs_trace_le_two hdet htr k).lt_of_ne'
        (hP k hk))]
  have hX : (mk fun k ↦ if k = 0 then 0 else 1 : ℤ⟦X⟧) = X * mk 1 := by
    ext (_ | k) <;> simp [coeff_succ_X_mul]
  -- Both sides are `∑ k X ^ k`, the right side being `X * (mk 1) ^ 2`.
  rw [hS, hX, torusWeightSeries_true_zero, mul_left_comm, ← sq]
  ext (_ | n)
  · simp
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, mk_one_pow_eq_mk_choose_add]
    simp [add_comm]

/-- **Orbit-torus weights are local zeta factors.** Let `P` be a `2 × 2` matrix of determinant
one all of whose iterates are nondegenerate, `det (1 - P ^ k) ≠ 0` for `k ≥ 1`. Read off the label
`σ = (0 < det (1 - P))` and `i = 1` if `det (1 + P) < 0`, `i = 0` otherwise. Then the local series
`f = f_(σ, i)` satisfies `t f' = f ∑_{k ≥ 1} sgn det (1 - P ^ k) t ^ k`; over `ℚ` this says
`log f = ∑_{k ≥ 1} sgn det (1 - P ^ k) t ^ k / k`. -/
theorem X_mul_derivative_torusWeightSeries_of_det_eq_one (hdet : P.det = 1)
    (hP : ∀ k ≠ 0, (1 - P ^ k).det ≠ 0) :
    X * d⁄dX (torusWeightSeries (decide (0 < (1 - P).det)) (if (1 + P).det < 0 then 1 else 0)) =
      torusWeightSeries (decide (0 < (1 - P).det)) (if (1 + P).det < 0 then 1 else 0) *
        mk fun k ↦ if k = 0 then 0 else (SignType.sign (1 - P ^ k).det : ℤ) := by
  have h₁ : (1 - P).det = 2 - P.trace := by
    rw [Matrix.det_one_sub_fin_two, hdet]
    ring
  have h₂ : (1 + P).det = 2 + P.trace := by
    rw [Matrix.det_one_add_fin_two, hdet]
    ring
  rw [h₁, h₂]
  rcases lt_or_ge 2 P.trace with htr | htr
  · rw [decide_eq_false (by linarith), ite_eq_right (by linarith)]
    exact X_mul_derivative_torusWeightSeries_false_zero_of_two_lt_trace hdet htr
  rcases lt_or_ge P.trace (-2) with htr' | htr'
  · rw [decide_eq_true (by linarith), ite_eq_left (by linarith)]
    exact X_mul_derivative_torusWeightSeries_true_one_of_trace_lt_neg_two hdet htr'
  have hne : 2 - P.trace ≠ 0 := by simpa [h₁] using hP 1 one_ne_zero
  rw [decide_eq_true (lt_of_le_of_ne (by linarith) hne.symm), ite_eq_right (by linarith)]
  exact X_mul_derivative_torusWeightSeries_true_zero_of_abs_trace_le_two hdet
    (abs_le.2 ⟨htr', htr⟩) hP

end TauCeti
