/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic.Basic

/-!
# Base change of split hyperbolic sums

Scalar extension along a commutative algebra homomorphism carries a split hyperbolic sum
`TauCeti.hyperbolicSum R j` to the corresponding split hyperbolic sum `TauCeti.hyperbolicSum A j`.

## Main definitions

* `TauCeti.baseChangeHyperbolicSum`: canonical isometric equivalence identifying
  `(hyperbolicSum R j).baseChange A` with `hyperbolicSum A j`.

## Main results

* `TauCeti.baseChangeHyperbolicSum_tmul`: evaluation of `baseChangeHyperbolicSum` on pure tensors.
-/

public section
noncomputable section

open QuadraticMap QuadraticForm
open scoped TensorProduct

namespace TauCeti

section HyperbolicSum

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Base change carries `hyperbolicSum R j` to `hyperbolicSum A j`. -/
def baseChangeHyperbolicSum (j : ℕ) (A : Type*) [CommRing A] [Algebra R A]
    [Invertible (2 : A)] :
    ((hyperbolicSum R j).baseChange A).IsometryEquiv (hyperbolicSum A j) :=
  ((hyperbolicSumEquivWeightedSumSquares (R := R) j).baseChange A).trans
    ((_root_.QuadraticForm.baseChangeWeightedSumSquares (A := A)
        (fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : R) else -1)).trans
      ((QuadraticMap.IsometryEquiv.ofEq (by
          congr 1
          funext p
          split_ifs <;> simp)).trans
        (hyperbolicSumEquivWeightedSumSquares (R := A) j).symm))

/-- On pure tensors, `baseChangeHyperbolicSum` scales each algebra entry by the corresponding
coordinate of the base vector. -/
@[simp]
theorem baseChangeHyperbolicSum_tmul (j : ℕ) (A : Type*) [CommRing A] [Algebra R A]
    [Invertible (2 : A)] (a : A) (x : Fin j → Fin 2 → R) (i : Fin j) (k : Fin 2) :
    baseChangeHyperbolicSum (R := R) j A (a ⊗ₜ x) i k = x i k • a := by
  dsimp only [baseChangeHyperbolicSum]
  simp [IsometryEquiv.trans_apply, IsometryEquiv.baseChange_tmul,
    _root_.QuadraticForm.baseChangeWeightedSumSquares_apply, TensorProduct.piScalarRightHom_tmul,
    QuadraticMap.IsometryEquiv.ofEq_apply]

end HyperbolicSum

end TauCeti
