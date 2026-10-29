/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import TauCeti.Topology.Algebra.IsUniformGroup.Subring
public import TauCeti.Topology.Algebra.TopologicallyNilpotent.ExpLog

/-!
# Exponential and logarithm of Novikov series

Let `K` be a commutative `ℚ`-algebra, `H` an additive commutative monoid and `N : H →+ ℝ` a
period homomorphism. The nonnegative subring of the Novikov ring `Nov(K, H, N)` is a complete,
separated, linearly topologized `ℚ`-algebra, and the series of its positive ideal are
topologically nilpotent. So the general theory of the exponential and logarithm of topologically
nilpotent elements applies (`TauCeti/Topology/Algebra/TopologicallyNilpotent/ExpLog.lean`): for
`a` in the positive ideal, the series of Mathlib's exponential `NormedSpace.exp` and logarithm
`NormedSpace.log`

`exp a = ∑ aⁿ / n!`,    `log (1 + a) = ∑ (-1)ⁿ⁺¹ aⁿ / n`

converge in the period topology, and the exponential is an isomorphism from the additive group of
the positive ideal onto its principal unit group of units `u` with `u - 1` in the positive ideal,
with inverse the logarithm (`TauCeti.NovikovSeries.expMulEquiv`). The dynamical zeta function of a
closed one-form is defined as the exponential of a rational logarithmic series of periodic orbits
lying in the positive ideal; by this isomorphism it is a principal unit.

## Main definitions

* `TauCeti.NovikovSeries.expMulEquiv`: the exponential, as an isomorphism from the additive group
  of the positive ideal onto its principal unit group, with inverse the logarithm.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovSeries

variable {H K : Type*} [AddCommMonoid H] {N : H →+ ℝ} [CommRing K] [Algebra ℚ K]

variable (K N) in
/-- **Exponential and logarithm** of Novikov series: over a `ℚ`-algebra `K`, the exponential is
an isomorphism from the additive group of the positive ideal onto its principal unit group in the
nonnegative subring, with inverse the logarithm. This is `Ideal.expMulEquiv` for the positive
ideal, whose series are topologically nilpotent. -/
def expMulEquiv : Multiplicative (posIdeal K N) ≃* (posIdeal K N).principalUnitGroup :=
  (posIdeal K N).expMulEquiv fun _ => isTopologicallyNilpotent_of_mem_posIdeal'

/-- `TauCeti.NovikovSeries.expMulEquiv` sends `a` to the unit `exp a`. -/
@[simp]
theorem coe_expMulEquiv_apply (a : posIdeal K N) :
    ((expMulEquiv K N (.ofAdd a) : (nonnegSubring K N)ˣ) : nonnegSubring K N) =
      NormedSpace.exp (a : nonnegSubring K N) :=
  Ideal.coe_expMulEquiv_apply _ _ a

/-- The inverse of `TauCeti.NovikovSeries.expMulEquiv` sends a unit `u` to `log u`. -/
@[simp]
theorem coe_expMulEquiv_symm_apply (u : (posIdeal K N).principalUnitGroup) :
    (((expMulEquiv K N).symm u).toAdd : nonnegSubring K N) =
      NormedSpace.log ((u : (nonnegSubring K N)ˣ) : nonnegSubring K N) :=
  Ideal.coe_expMulEquiv_symm_apply _ _ u

end NovikovSeries

end TauCeti
