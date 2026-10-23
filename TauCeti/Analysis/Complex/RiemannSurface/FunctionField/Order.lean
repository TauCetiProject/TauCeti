/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField
import Mathlib.Topology.DiscreteSubset

/-!
# Orders and divisors of meromorphic functions on a Riemann surface

Let `X` be a connected Riemann surface and `M(X)` its field of meromorphic functions
(`TauCeti.RiemannSurface.MeromorphicFunction X`). The order `ord_x f` of a meromorphic function `f`
at a point `x` is the order of its finite part read in a chart at `x`, an element of `WithTop ℤ`
which is `⊤` only for `f = 0`. This file shows that `f ↦ ord_x f` is an additive valuation on
`M(X)` (`TauCeti.RiemannSurface.MeromorphicFunction.order`): orders of products add, the order of a
sum is at least the minimum of the orders, and nonzero constants have order `0`. The sign of the
order records the value of `f` at `x`: it is positive exactly at the zeros of `f`, negative exactly
at its poles, and zero elsewhere.

On a compact connected Riemann surface a nonzero meromorphic function has nonzero order at only
finitely many points: its zeros and its poles are isolated, so the points of nonzero order form a
closed discrete set, which is finite by compactness. The orders therefore form an order system on
the multiplicative group of `M(X)` in the sense of `TauCeti.AlgebraicGeometry.WeilDivisor`
(`TauCeti.RiemannSurface.MeromorphicFunction.orderSystem`). Its principal divisor at a nonzero
meromorphic function `f` is the divisor `Σ_x ord_x(f) · [x]` of `f`, whose positive part is
supported on the zeros of `f` and whose negative part is supported on its poles. Through the order
system, the divisor class group and linear equivalence of divisors become available on compact
Riemann surfaces.

## Main definitions

* `TauCeti.RiemannSurface.MeromorphicFunction.order x`: the order at `x`, as an additive valuation
  `M(X) → WithTop ℤ`.
* `TauCeti.RiemannSurface.MeromorphicFunction.orderSystem X`: on a compact connected Riemann
  surface, the order system whose principal divisors are the divisors of meromorphic functions.

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.order_pos_iff`,
  `TauCeti.RiemannSurface.MeromorphicFunction.order_neg_iff` and
  `TauCeti.RiemannSurface.MeromorphicFunction.order_eq_zero_iff`: the order is positive at the
  zeros, negative at the poles, and zero at the other points.
* `TauCeti.RiemannSurface.MeromorphicFunction.order_algebraMap`: nonzero constants have order `0`.
* `TauCeti.RiemannSurface.MeromorphicFunction.setOf_order_eq_zero_mem_codiscrete`: a nonzero
  meromorphic function has order `0` away from a closed discrete set.
* `TauCeti.RiemannSurface.MeromorphicFunction.mem_support_principalDivisor_orderSystem_iff`: the
  support of the divisor of `f` consists of the zeros and the poles of `f`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16 (the order of a meromorphic function and the divisor of a meromorphic function).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §1 (orders of meromorphic functions) and
  Chapter V §1 (principal divisors).
* Mathlib's `MeromorphicOn.divisor` in `Mathlib/Analysis/Meromorphic/Divisor.lean` is the analogous
  construction for meromorphic functions on an open subset of a field.
-/

public noncomputable section

open Filter Function OnePoint Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

open AlgebraicGeometry WeilDivisor

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X] {f : MeromorphicFunction X} {x : X}

/-! ### The order at a point -/

/-- The **order** `ord_x` at a point `x` of a connected Riemann surface, as an additive valuation
on the field of meromorphic functions: `ord_x f` is the order at `x` of the finite part of `f`. It
is `⊤` only for `f = 0`, positive at the zeros of `f` and negative at its poles. -/
def order (x : X) : AddValuation (MeromorphicFunction X) (WithTop ℤ) :=
  AddValuation.of (fun f ↦ meromorphicOrderAt f.finitePart x)
    (by
      rw [finitePart_zero]
      classical exact (meromorphicOrderAt_const (0 : ℂ) x).trans (ite_eq_left rfl))
    (by
      rw [finitePart_one]
      classical exact (meromorphicOrderAt_const (1 : ℂ) x).trans (ite_eq_right one_ne_zero))
    (fun f g ↦ by
      rw [meromorphicOrderAt_congr (finitePart_add_eventuallyEq f g x)]
      exact meromorphicOrderAt_add (f.meromorphicAt_finitePart x) (g.meromorphicAt_finitePart x))
    (fun f g ↦ by
      rw [meromorphicOrderAt_congr (finitePart_mul_eventuallyEq f g x)]
      exact meromorphicOrderAt_mul (f.meromorphicAt_finitePart x) (g.meromorphicAt_finitePart x))

/-- The order of `f` at `x` is the order at `x` of its finite part. -/
theorem order_apply (x : X) (f : MeromorphicFunction X) :
    order x f = meromorphicOrderAt f.finitePart x :=
  AddValuation.of_apply _

/-- The order of a meromorphic function at `x` is negative exactly when `x` is a pole. -/
@[simp]
theorem order_neg_iff : order x f < 0 ↔ f x = ∞ := by
  rw [order_apply, ← sphereMap_eq_infty_iff (f.meromorphicAt_finitePart x), sphereMap_finitePart]

/-- The order of a meromorphic function at `x` is nonnegative exactly when `x` is not a pole. -/
@[simp]
theorem order_nonneg_iff : 0 ≤ order x f ↔ f x ≠ ∞ := by
  rw [← not_lt, order_neg_iff]

/-- The order of a meromorphic function at `x` is positive exactly when `x` is a zero. -/
@[simp]
theorem order_pos_iff : 0 < order x f ↔ f x = ((0 : ℂ) : OnePoint ℂ) := by
  have hf := f.meromorphicAt_finitePart x
  rw [order_apply, ← tendsto_zero_iff_meromorphicOrderAt_pos hf, ← sphereMap_eq_coe_iff hf,
    sphereMap_finitePart]

/-- The order of a meromorphic function at `x` is zero exactly when `x` is neither a zero nor a
pole. -/
theorem order_eq_zero_iff : order x f = 0 ↔ f x ≠ ((0 : ℂ) : OnePoint ℂ) ∧ f x ≠ ∞ := by
  rw [eq_comm, eq_iff_le_not_lt, order_nonneg_iff, order_pos_iff, and_comm]

/-- Nonzero constants have order `0` at every point: the valuation `ord_x` is trivial on `ℂ`. -/
@[simp]
theorem order_algebraMap {c : ℂ} (hc : c ≠ 0) :
    order x (algebraMap ℂ (MeromorphicFunction X) c) = 0 := by
  classical
  simp [order_apply, meromorphicOrderAt_const, hc]

/-! ### The divisor of a meromorphic function on a compact Riemann surface -/

/-- A nonzero meromorphic function has order `0` at every point of a punctured neighbourhood of
any point, since its zeros and its poles are isolated. -/
theorem setOf_order_eq_zero_mem_codiscrete (hf : f ≠ 0) :
    {y | order y f = 0} ∈ codiscrete X :=
  mem_codiscrete_iff_forall_mem_nhdsNE.2 fun x ↦ by
    filter_upwards [f.eventually_ne_infty x, eventually_finitePart_ne_zero hf x] with y hy hy0
    exact order_eq_zero_iff.2 ⟨fun h ↦ hy0 (finitePart_of_eq_coe h), hy⟩

variable (X) [CompactSpace X]

/-- The **order system** of a compact connected Riemann surface `X`: the order at `x` of a nonzero
meromorphic function, as a homomorphism from the multiplicative group of `M(X)` to `ℤ`. A nonzero
meromorphic function has nonzero order at only finitely many points, its zeros and its poles. The
principal divisor of `f` is the divisor `Σ_x ord_x(f) · [x]` of `f`. -/
def orderSystem : OrderSystem X (Additive (MeromorphicFunction X)ˣ) where
  ord x :=
    { toFun u := (order x (u.toMul : MeromorphicFunction X)).untop
        ((order x).ne_top_iff.2 u.toMul.ne_zero)
      map_zero' := by simp
      map_add' u v := by
        refine WithTop.coe_injective ?_
        simp [WithTop.coe_add] }
  finite_support u := by
    refine (mem_cofinite.1 (cofinite_le_codiscrete
      (setOf_order_eq_zero_mem_codiscrete u.toMul.ne_zero))).subset fun y hy ↦ ?_
    simpa [WithTop.untop_eq_iff] using hy

variable {X}

/-- The order map of the order system at `x` is the order `ord_x`, read in `ℤ`. -/
@[simp]
theorem coe_ord_orderSystem (x : X) (u : Additive (MeromorphicFunction X)ˣ) :
    ((orderSystem X).ord x u : WithTop ℤ) = order x (u.toMul : MeromorphicFunction X) :=
  WithTop.coe_untop _ _

/-- The coefficient at `x` of the divisor of a nonzero meromorphic function is its order at `x`. -/
theorem coe_coeff_principalDivisor_orderSystem (u : Additive (MeromorphicFunction X)ˣ) (x : X) :
    (coeff ((orderSystem X).principalDivisor u) x : WithTop ℤ) =
      order x (u.toMul : MeromorphicFunction X) := by
  rw [OrderSystem.coeff_principalDivisor, coe_ord_orderSystem]

/-- The divisor of a nonzero meromorphic function has positive coefficient exactly at its
zeros. -/
theorem coeff_principalDivisor_orderSystem_pos_iff {u : Additive (MeromorphicFunction X)ˣ}
    {x : X} :
    0 < coeff ((orderSystem X).principalDivisor u) x ↔
      (u.toMul : MeromorphicFunction X) x = ((0 : ℂ) : OnePoint ℂ) := by
  rw [← order_pos_iff, ← coe_coeff_principalDivisor_orderSystem, WithTop.coe_pos]

/-- The divisor of a nonzero meromorphic function has negative coefficient exactly at its
poles. -/
theorem coeff_principalDivisor_orderSystem_neg_iff {u : Additive (MeromorphicFunction X)ˣ}
    {x : X} :
    coeff ((orderSystem X).principalDivisor u) x < 0 ↔
      (u.toMul : MeromorphicFunction X) x = ∞ := by
  rw [← order_neg_iff, ← coe_coeff_principalDivisor_orderSystem, WithTop.coe_lt_zero]

/-- The support of the divisor of a nonzero meromorphic function consists of its zeros and its
poles. -/
theorem mem_support_principalDivisor_orderSystem_iff {u : Additive (MeromorphicFunction X)ˣ}
    {x : X} :
    x ∈ ((orderSystem X).principalDivisor u).support ↔
      (u.toMul : MeromorphicFunction X) x = ((0 : ℂ) : OnePoint ℂ) ∨
        (u.toMul : MeromorphicFunction X) x = ∞ := by
  rw [mem_support_iff, ne_eq, ← WithTop.coe_eq_zero, coe_coeff_principalDivisor_orderSystem,
    order_eq_zero_iff, not_and_or, not_not, not_not]

end TauCeti.RiemannSurface.MeromorphicFunction
