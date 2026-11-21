/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Wenzl
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Discrete Wenzl parameters of geometric atomic Markov traces

Let `Q = q ^ 2` and let `c * [r + 1]_Q = 1`, where `[n]_Q = ∑ i < n, Q ^ i`. On the infinite type-A
Hecke algebra with parameter `q`, the Ocneanu trace with Markov parameter `z = c * q ^ (2 * r + 1)`
is realized on each finite stage by the atomic model on `r + 1` positive letters with geometric
weights `c * Q ^ a` (`TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_eq`).

This file identifies its native and Wenzl projection parameters (`TauCeti.wenzlParam`) as
`a_(r + 1)(Q)` and `a_(-(r + 1))(Q) = 1 - a_(r + 1)(Q)`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_eigenprojection_geometric`: appending the
  native eigenprojection `s⁻¹ • (T n + q⁻¹)`, `s = q + q⁻¹`, multiplies the trace by `a_(r + 1)(Q)`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_wenzlProjection_geometric`: appending Wenzl's
  complementary projection `(1 + Q)⁻¹ • (Q - q • T n)` multiplies the trace by `a_(-(r + 1))(Q)`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7, for the atomic geometric models.
-/

public section

open Finset

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {K : Type*} [Field K] {q : Kˣ}

private theorem ocneanuTrace_param_geometric (hQ : 1 + (q : K) ^ 2 ≠ 0) {r : ℕ} {c : K}
    (hc : c * ∑ a ∈ range (r + 1), ((q : K) ^ 2) ^ a = 1) :
    c * (q : K) ^ (2 * r + 1) =
      (q : K) * wenzlParam ((r + 1 : ℕ) : ℤ) ((q : K) ^ 2) -
        ↑q⁻¹ * (1 - wenzlParam ((r + 1 : ℕ) : ℤ) ((q : K) ^ 2)) := by
  have hq : (q : K) ≠ 0 := q.ne_zero
  have hZ : ∑ a ∈ range (r + 1), ((q : K) ^ 2) ^ a ≠ 0 := right_ne_zero_of_mul_eq_one hc
  rw [wenzlParam_natCast, Units.val_inv_eq_inv_val, geom_sum_succ' (n := r + 1)]
  field_simp
  linear_combination ((1 + (q : K) ^ 2) * (q : K) ^ (2 * r + 2)) * hc

/-- **The projection parameter of a geometric atomic model.** Let `Q = q ^ 2` and
`c * [r + 1]_Q = 1`. The Ocneanu trace with parameter `z = c * q ^ (2 * r + 1)`, which the atomic
model on `r + 1` positive letters with weights `c * Q ^ a` realizes
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_eq`), multiplies by `a_(r + 1)(Q)` when the
eigenprojection `s⁻¹ • (T n + q⁻¹)`, `s = q + q⁻¹`, is appended to an element of the stage on
`n + 1` strands. -/
theorem ocneanuTrace_mul_eigenprojection_geometric (s : Kˣ) (hs : (s : K) = q + ↑q⁻¹) {r : ℕ}
    {c : K} (hc : c * ∑ a ∈ range (r + 1), ((q : K) ^ 2) ^ a = 1) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra K q} (hx : x ∈ stage K q (n + 1)) :
    ocneanuTrace K q (c * (q : K) ^ (2 * r + 1))
        (x * (↑s⁻¹ : K) • (T q n + algebraMap K _ (↑q⁻¹ : K))) =
      wenzlParam ((r + 1 : ℕ) : ℤ) ((q : K) ^ 2) *
        ocneanuTrace K q (c * (q : K) ^ (2 * r + 1)) x := by
  -- `1 + q ^ 2 = q * s` is nonzero since `s` is a unit.
  have hqs : 1 + (q : K) ^ 2 = q * s := by
    rw [hs, Units.val_inv_eq_inv_val]
    field_simp [q.ne_zero]
    ring
  have hQ : 1 + (q : K) ^ 2 ≠ 0 := hqs ▸ mul_ne_zero q.ne_zero s.ne_zero
  exact (isMarkovTrace_ocneanuTrace _).map_mul_eigenprojection s hs
    (ocneanuTrace_param_geometric hQ hc) hx

/-- **The Wenzl projection parameter of a geometric atomic model.** Let `Q = q ^ 2`, let
`u = 1 + Q` be a unit, and `c * [r + 1]_Q = 1`. Appending Wenzl's projection
`(1 + Q)⁻¹ • (Q - q • T n)` to an element of the stage on `n + 1` strands multiplies the Ocneanu
trace with parameter `z = c * q ^ (2 * r + 1)` by `a_(-(r + 1))(Q) = 1 - a_(r + 1)(Q)`. -/
theorem ocneanuTrace_mul_wenzlProjection_geometric (u : Kˣ) (hu : (u : K) = 1 + (q : K) ^ 2)
    {r : ℕ} {c : K} (hc : c * ∑ a ∈ range (r + 1), ((q : K) ^ 2) ^ a = 1) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra K q} (hx : x ∈ stage K q (n + 1)) :
    ocneanuTrace K q (c * (q : K) ^ (2 * r + 1))
        (x * (↑u⁻¹ : K) • (algebraMap K _ ((q : K) ^ 2) - (q : K) • T q n)) =
      wenzlParam (-((r + 1 : ℕ) : ℤ)) ((q : K) ^ 2) *
        ocneanuTrace K q (c * (q : K) ^ (2 * r + 1)) x := by
  have hden : (1 + (q : K) ^ 2) * ∑ a ∈ range ((r + 1 : ℕ) : ℤ).natAbs, ((q : K) ^ 2) ^ a ≠ 0 := by
    rw [Int.natAbs_natCast, ← hu]
    exact mul_ne_zero u.ne_zero (right_ne_zero_of_mul_eq_one hc)
  have hcomp : 1 - wenzlParam ((r + 1 : ℕ) : ℤ) ((q : K) ^ 2) =
      wenzlParam (-((r + 1 : ℕ) : ℤ)) ((q : K) ^ 2) := by
    linear_combination -(wenzlParam_add_wenzlParam_neg hden)
  rw [(isMarkovTrace_ocneanuTrace _).map_mul_wenzlProjection u hu
      (ocneanuTrace_param_geometric (hu ▸ u.ne_zero) hc) hx, hcomp]

end InfiniteTypeAHeckeAlgebra

end TauCeti
