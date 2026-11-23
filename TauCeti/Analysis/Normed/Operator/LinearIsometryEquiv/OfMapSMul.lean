/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Semilinear isometric equivalences from compatible scalar actions

`LinearIsometryEquiv.toSemilinearIsometryEquivOfMapSMul` upgrades a linear isometric equivalence
over one ring `R` to a `σ`-semilinear isometric equivalence over another ring `S` acting on the same
spaces, given that it is compatible with the `S`-actions. For instance, a real-linear isometric
equivalence of complex normed spaces which commutes with complex scalars is a complex-linear
isometric equivalence, and one which conjugates them is a conjugate-linear isometric equivalence.
This is the isometric analogue of Mathlib's `AddEquiv.toLinearEquiv`.
-/

public section

namespace LinearIsometryEquiv

variable {R S S₂ E F : Type*} [Semiring R] [Semiring S] [Semiring S₂]
  {σ : S →+* S₂} {σ' : S₂ →+* S} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module R E] [Module R F]
  [Module S E] [Module S₂ F]

/-- A linear isometric equivalence over `R` which is `σ`-semilinear for the actions of another
ring `S`, as a `σ`-semilinear isometric equivalence over `S`. -/
def toSemilinearIsometryEquivOfMapSMul (f : E ≃ₗᵢ[R] F)
    (hf : ∀ (c : S) (x : E), f (c • x) = σ c • f x) : E ≃ₛₗᵢ[σ] F where
  toFun := f
  invFun := f.symm
  map_add' := map_add f
  map_smul' := hf
  left_inv := f.symm_apply_apply
  right_inv := f.apply_symm_apply
  norm_map' := f.norm_map

@[simp]
theorem coe_toSemilinearIsometryEquivOfMapSMul (f : E ≃ₗᵢ[R] F)
    (hf : ∀ (c : S) (x : E), f (c • x) = σ c • f x) :
    ⇑(f.toSemilinearIsometryEquivOfMapSMul hf) = f :=
  (rfl)

end LinearIsometryEquiv
