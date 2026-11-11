/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import TauCeti.Algebra.Lie.BCH.Dynkin

/-!
# Total numerical sums of the Dynkin series

`TauCeti.BCH.bchSum K x y` is the `tsum` of the homogeneous Dynkin terms in a Lie algebra
over a field `K`, equipped with a topology. Its value is zero when the terms are not summable.
The definition does not assert convergence or identify this total function with
a global logarithm.

For commuting inputs, the series is supported only in degree one. In particular,
the coordinate-axis identities hold for arbitrary inputs, with no size bound.
Continuous Lie homomorphisms preserve the sum when the source series is summable.

## References

* Michael Müger, *Notes on the theorem of Baker--Campbell--Hausdorff--Dynkin*
  (April 22, 2020), Theorem 1.3, formula (1.4), and Remark 1.4.
  <https://www.math.ru.nl/~mueger/PDF/BCHD.pdf>
-/

public section

noncomputable section

namespace TauCeti.BCH

variable (K : Type*) [Field K]
variable {L M : Type*} [LieRing L] [LieAlgebra K L] [TopologicalSpace L]
  [LieRing M] [LieAlgebra K M] [TopologicalSpace M]

/-- The total numerical sum of the degreewise Dynkin terms, zero if they are not summable. -/
def bchSum (x y : L) : L := ∑' n, dynkinTerm K n x y

/-- The total numerical Dynkin sum is the `tsum` of its homogeneous terms. -/
theorem bchSum_def (x y : L) : bchSum K x y = ∑' n, dynkinTerm K n x y := by
  rw [bchSum]

variable {K} in
/-- A summable Dynkin series has its total numerical value as a sum. -/
theorem _root_.Summable.hasSum_bchSum {x y : L}
    (h : Summable (fun n => dynkinTerm K n x y)) :
    HasSum (fun n => dynkinTerm K n x y) (bchSum K x y) := by
  simpa only [bchSum_def] using h.hasSum

/-- A nonsummable Dynkin series has numerical value zero by the `tsum` convention. -/
theorem bchSum_eq_zero_of_not_summable {x y : L}
    (h : ¬Summable (fun n => dynkinTerm K n x y)) : bchSum K x y = 0 := by
  simpa only [bchSum] using tsum_eq_zero_of_not_summable h

/-- The Dynkin terms of commuting inputs sum to their sum, using only the degree-one term. -/
theorem hasSum_dynkinTerm_of_lie_eq_zero (x y : L) (hxy : ⁅x, y⁆ = 0) :
    HasSum (fun n => dynkinTerm K n x y) (x + y) := by
  simp only [dynkinTerm_of_lie_eq_zero K _ x y hxy]
  exact hasSum_ite_eq 1 (x + y)

variable [T2Space L]

variable {K} in
/-- The value of a convergent Dynkin series is its total numerical sum. -/
theorem _root_.HasSum.bchSum_eq {x y a : L}
    (h : HasSum (fun n => dynkinTerm K n x y) a) : bchSum K x y = a := by
  rw [bchSum_def]
  exact h.tsum_eq

/-- For commuting inputs, the total Dynkin sum is their sum without a size restriction. -/
theorem bchSum_of_lie_eq_zero (x y : L) (hxy : ⁅x, y⁆ = 0) : bchSum K x y = x + y := by
  simpa only [bchSum] using (hasSum_dynkinTerm_of_lie_eq_zero K x y hxy).tsum_eq

/-- The left endpoint identity for the total numerical Dynkin sum holds globally. -/
@[simp]
theorem bchSum_zero_left (y : L) : bchSum K 0 y = y := by
  simpa using bchSum_of_lie_eq_zero K 0 y (zero_lie y)

/-- The right endpoint identity for the total numerical Dynkin sum holds globally. -/
@[simp]
theorem bchSum_zero_right (x : L) : bchSum K x 0 = x := by
  simpa using bchSum_of_lie_eq_zero K x 0 (lie_zero x)

variable {K}
omit [T2Space L] in
/-- Continuous Lie homomorphisms preserve the numerical Dynkin sum of a summable series. -/
theorem _root_.LieHom.map_bchSum [T2Space M] (f : L →ₗ⁅K⁆ M) (hf : Continuous f) (x y : L)
    (hxy : Summable (fun n => dynkinTerm K n x y)) :
    f (bchSum K x y) = bchSum K (f x) (f y) := by
  have h := hxy.hasSum.map f.toLinearMap.toAddMonoidHom hf
  simpa only [bchSum, Function.comp_def, LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap,
    LieHom.map_dynkinTerm] using h.tsum_eq.symm

end TauCeti.BCH
