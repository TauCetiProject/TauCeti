/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.RingTheory.LambdaRing.Basic

/-!
# Pointwise pre-λ structures on locally constant functions

A pre-λ structure on a commutative ring `R` induces one on the ring of locally constant functions
`X → R` on a topological space `X`, by applying each `λⁿ` pointwise. Applied to the binomial
structure on `ℤ`, this is the pointwise binomial structure on locally constant integer-valued
functions, the target of the rank of a projective module over a ring with disconnected
spectrum.

Evaluation at a point and the inclusion of constant functions are morphisms, and the induced
structure is the only one for which every evaluation is a morphism.

## Main definitions

* `TauCeti.PreLambdaStructure.locallyConstant`: the pointwise pre-λ structure.
* `TauCeti.PreLambdaStructure.locallyConstantEval`: evaluation at a point, as a morphism.
* `TauCeti.PreLambdaStructure.locallyConstantConst`: the constant functions, as a morphism.
-/

public noncomputable section

namespace TauCeti

namespace PreLambdaStructure

variable {R : Type*} [CommRing R] (Λ : PreLambdaStructure R)
variable (X : Type*) [TopologicalSpace X]

/-- The pre-λ structure on locally constant functions obtained by applying each `λⁿ`
pointwise. -/
def locallyConstant : PreLambdaStructure (LocallyConstant X R) where
  lambda n f := f.map (Λ.lambda n)
  lambda_zero f := by
    ext x
    simp
  lambda_one f := by
    ext x
    simp
  lambda_add n f g := by
    ext x
    have h := map_sum (LocallyConstant.evalRingHom (Y := R) x)
      (fun p => f.map (Λ.lambda p.1) * g.map (Λ.lambda p.2)) (Finset.antidiagonal n)
    simp only [LocallyConstant.evalRingHom_apply] at h
    simp [h, Λ.lambda_add]

@[simp]
theorem locallyConstant_lambda_apply (n : ℕ) (f : LocallyConstant X R) (x : X) :
    (Λ.locallyConstant X).lambda n f x = Λ.lambda n (f x) :=
  (rfl)

/-- Evaluation at a point, as a morphism of pre-λ structures. -/
def locallyConstantEval (x : X) : PreLambdaHom (Λ.locallyConstant X) Λ where
  __ := LocallyConstant.evalRingHom x
  map_lambda' _ _ := (rfl)

@[simp]
theorem locallyConstantEval_apply (x : X) (f : LocallyConstant X R) :
    Λ.locallyConstantEval X x f = f x :=
  (rfl)

/-- The inclusion of constant functions, as a morphism of pre-λ structures. -/
def locallyConstantConst : PreLambdaHom Λ (Λ.locallyConstant X) where
  __ := LocallyConstant.constRingHom
  map_lambda' _ _ := (rfl)

@[simp]
theorem locallyConstantConst_apply (r : R) :
    Λ.locallyConstantConst X r = LocallyConstant.const X r :=
  (rfl)

/-- The pointwise structure is the only pre-λ structure on locally constant functions for which
evaluation at every point commutes with every `λⁿ`. -/
theorem eq_locallyConstant {Λ' : PreLambdaStructure (LocallyConstant X R)}
    (h : ∀ n f x, Λ'.lambda n f x = Λ.lambda n (f x)) : Λ' = Λ.locallyConstant X := by
  ext n f x
  rw [h, locallyConstant_lambda_apply]

/-- A locally constant function is a line element exactly when each of its values is. -/
theorem isLine_locallyConstant_iff {f : LocallyConstant X R} :
    (Λ.locallyConstant X).IsLine f ↔ ∀ x, Λ.IsLine (f x) := by
  simp only [isLine_iff, LocallyConstant.ext_iff, locallyConstant_lambda_apply,
    LocallyConstant.coe_zero, Pi.zero_apply]
  exact ⟨fun h x n hn => h n hn x, fun h n hn x => h x n hn⟩

end PreLambdaStructure

end TauCeti
