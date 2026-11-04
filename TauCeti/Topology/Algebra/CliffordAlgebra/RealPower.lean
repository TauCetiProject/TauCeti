/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.RealPower
public import TauCeti.Topology.Algebra.CliffordAlgebra.Complexification

/-!
# Continuity of the real powers of `g† g`

Let `Q` be a real quadratic form with a real orthonormal basis `b`, and `e_s` the ordered-product
basis of the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)` for `1 ⊗ b`. For a unit `g` the matrix
of `g† g` in the basis `e_s` is strictly positive, where `g† = complexConj (reverse g)`, so its real
powers `(g† g) ^ t` are defined through `Algebra.leftMulMatrixRpow`. This file proves that they are
jointly continuous in the unit `g` and the exponent `t`, for the module topology.

## Main results

* `CliffordAlgebra.continuousOn_leftMulMatrixRpow_complexConj_reverse_mul_self`: the real powers
  `(g† g) ^ t` are jointly continuous in the unit `g` and the exponent `t`.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace CliffordAlgebra

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder I] [Fintype I]
  {Q : QuadraticForm ℝ V} {b : Module.Basis I ℝ V}

/-- **The real powers of `g† g` are jointly continuous** in the unit `g` and the exponent `t`, where
`g† = complexConj (reverse g)` and the powers are taken through the matrix of `g† * g` in the
ordered-product basis of a real orthonormal basis. -/
theorem continuousOn_leftMulMatrixRpow_complexConj_reverse_mul_self
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1) :
    ContinuousOn (fun p : CliffordAlgebra (Q.baseChange ℂ) × ℝ ↦
        Algebra.leftMulMatrixRpow (basis (Q.baseChange ℂ) (b.baseChange ℂ))
          (complexConj Q (reverse p.1) * p.1) p.2)
      ({g | IsUnit g} ×ˢ Set.univ) := by
  have : FiniteDimensional ℝ V := b.finiteDimensional_of_finite
  have hf : Continuous fun p : CliffordAlgebra (Q.baseChange ℂ) × ℝ ↦
      (complexConj Q (reverse p.1) * p.1, p.2) := by fun_prop
  exact Algebra.continuousOn_leftMulMatrixRpow.comp hf.continuousOn
    fun p hp ↦ isStrictlyPositive_leftMulMatrix_complexConj_reverse_mul_self hb hQ hp.1

end CliffordAlgebra
