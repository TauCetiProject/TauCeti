/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.DividedCommutator

/-!
# Divided commutator on the PBW Rees algebra of an abelian Lie algebra

When `L` is an abelian Lie algebra over a commutative ring `R`, its enveloping algebra
`UniversalEnvelopingAlgebra R L` is commutative (`TauCeti.UniversalEnvelopingAlgebra.instCommRing`),
so `reesAlgebra R L` is commutative and `reesDividedCommutator R L` vanishes identically.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

/-- Over an abelian Lie algebra, `reesAlgebra R L` is commutative (`Abelian.instCommRing`), so its
divided commutator vanishes identically. -/
@[simp]
theorem reesDividedCommutator_eq_zero (R : Type u) (L : Type v) [CommRing R] [LieRing L]
    [LieAlgebra R L] [IsLieAbelian L] (a b : reesAlgebra R L) :
    reesDividedCommutator R L a b = 0 :=
  reesDividedCommutator_of_commute R L (mul_comm a b)

end TauCeti.UniversalEnvelopingAlgebra
