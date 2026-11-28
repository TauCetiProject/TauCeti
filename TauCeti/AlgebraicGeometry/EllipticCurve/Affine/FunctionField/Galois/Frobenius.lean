/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Basic
import TauCeti.FieldTheory.Finite.GaloisZHat
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Arithmetic Frobenius on Weierstrass function fields

`WeierstrassCurve.functionFieldGaloisAction_eq_self_of_frobenius_eq_self` uses the open
coefficient stabilizer and
`TauCeti.FiniteField.topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic`
to pass from invariance under Frobenius to invariance under every coefficient automorphism.
-/

public section

open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
  [Algebra.IsAlgebraic F K] (W : WeierstrassCurve F)

/-- A function over an algebraic extension of a finite field fixed by arithmetic Frobenius on
coefficients is fixed by every coefficient automorphism. -/
theorem functionFieldGaloisAction_eq_self_of_frobenius_eq_self
    {z : (W⁄K).toAffine.FunctionField}
    (hz : W.functionFieldGaloisAction (FiniteField.frobeniusAlgEquivOfAlgebraic F K) z = z)
    (σ : K ≃ₐ[F] K) : W.functionFieldGaloisAction σ z = z := by
  have := TauCeti.FiniteField.isGalois_of_isAlgebraic F K
  have hc := (W.functionFieldGaloisStabilizer z).isClosed_of_isOpen
    (W.isOpen_functionFieldGaloisStabilizer z)
  have htop := (TauCeti.closedZpowers_le hc).mpr (W.mem_functionFieldGaloisStabilizer.mpr hz)
  rw [TauCeti.closedZpowers_def,
    TauCeti.FiniteField.topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic] at htop
  exact W.mem_functionFieldGaloisStabilizer.mp (htop (Subgroup.mem_top σ))

end WeierstrassCurve

end
