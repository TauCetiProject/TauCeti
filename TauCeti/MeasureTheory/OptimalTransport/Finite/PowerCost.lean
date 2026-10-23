/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.FourPoint
public import TauCeti.MeasureTheory.OptimalTransport.Finite.Monotone

/-!
# Finite monotone transport for power-distance costs

For probability weights on two finite linear orders, let `x` and `y` give weakly increasing
real support locations. The monotone transportation matrix minimizes the expected cost
`|x i - y j| ^ p` for every real exponent `1 ≤ p`. Moreover, any matrix reaches that monotone
matrix by finitely many minimum-mass uncrossing steps. The same sequence and endpoint work
for all such exponents, and every uncrossing step weakly decreases each power-distance cost.

The four-point inequality is `TauCeti.abs_sub_rpow_add_abs_sub_rpow_le`; the generic Monge-cost
comparison is reused from the finite uncrossing API. The terminating sequence is supplied
separately by `TauCeti.MeasureTheory.OptimalTransport.Finite.Uncrossing.Termination`.
Rectangular matrices, zero weights, and repeated support locations are allowed.
No uniqueness of power-cost optimizers is asserted: in particular `p = 1` can have other
optimizers even at strictly ordered support locations.

## References

* C. Villani, *Topics in Optimal Transportation*, AMS 2003, §2.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2.
-/

public section

namespace TauCeti.TransportMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
  {μ : PMF ι} {ν : PMF κ} {x : ι → ℝ} {y : κ → ℝ}

/-- A monotone transportation matrix minimizes every power-distance cost with `1 ≤ p` on
weakly increasing real support locations. The support locations need not be distinct. -/
theorem IsMonotone.forall_cost_abs_sub_rpow_le {A : TransportMatrix μ ν} (hA : A.IsMonotone)
    (hx : Monotone x) (hy : Monotone y) {p : ℝ} (hp : 1 ≤ p) :
    ∀ B : TransportMatrix μ ν,
      A.cost (fun q ↦ |x q.1 - y q.2| ^ p) ≤ B.cost (fun q ↦ |x q.1 - y q.2| ^ p) := by
  exact hA.forall_cost_le _ fun {_ _ _ _} hi hj ↦
    abs_sub_rpow_add_abs_sub_rpow_le hp (hx hi.le) (hy hj.le)

/-- Every uncrossing step weakly decreases every power-distance cost with `1 ≤ p` on weakly
increasing real support locations. -/
theorem UncrossStep.cost_abs_sub_rpow_le {A B : TransportMatrix μ ν} (h : A.UncrossStep B)
    (hx : Monotone x) (hy : Monotone y) {p : ℝ} (hp : 1 ≤ p) :
    B.cost (fun q ↦ |x q.1 - y q.2| ^ p) ≤ A.cost (fun q ↦ |x q.1 - y q.2| ^ p) := by
  exact h.cost_le _ fun {_ _ _ _} hi hj ↦
    abs_sub_rpow_add_abs_sub_rpow_le hp (hx hi.le) (hy hj.le)

end TauCeti.TransportMatrix
