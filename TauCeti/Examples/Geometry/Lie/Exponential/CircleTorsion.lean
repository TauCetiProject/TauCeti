/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Geometry.Lie.Exponential.Circle
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Torsion.Lattice

/-!
# Torsion of the circle through its exponential lattice

For `n = 1` both sides of `TauCeti.lieExpTorsionEquiv` vanish. For the circle, the exponential
lattice contains the period `2π • circleExpGenerator`, and the inverse of
`TauCeti.lieExpTorsionEquiv` sends its class to the primitive `n`-th root of unity
`Circle.exp (2π / n)`.
-/

public section

noncomputable section

namespace TauCeti

open Real
open scoped Manifold

/-- **The circle Check**: the level-`n` torsion isomorphism of the circle sends the class of the
period `2π` to `Circle.exp (2π / n)`, a primitive `n`-th root of unity. -/
theorem toMul_lieExpTorsionEquiv_symm_mk_two_pi_smul_circleExpGenerator (n : ℤ) (hn : n ≠ 0) :
    Additive.toMul ((lieExpTorsionEquiv (𝓡 1) Circle n hn).symm
      (Submodule.Quotient.mk ⟨_, two_pi_smul_circleExpGenerator_mem_lieExpLattice⟩) :
        Additive Circle) = Circle.exp (2 * π / n) := by
  rw [lieExpTorsionEquiv_symm_mk, toMul_ofMul, smul_smul, lieExp_circleExpGenerator, inv_mul_eq_div]

/-- **The case `n = 1`**: only the identity of the circle is killed by `1`, matching `Λ ⧸ 1Λ = 0`
through `TauCeti.lieExpTorsionEquiv`. -/
example : Subsingleton (Submodule.torsionBy ℤ (Additive Circle) 1) := by
  have : Subsingleton (QuotSMulTop (1 : ℤ) (lieExpLattice (I := 𝓡 1) (G := Circle))) := by
    rw [Submodule.Quotient.subsingleton_iff, one_smul]
  exact (lieExpTorsionEquiv (𝓡 1) Circle 1 one_ne_zero).toEquiv.subsingleton

end TauCeti
