/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Type-tag equivalences of Pi types on one-point families

Mathlib's `MulEquiv.piMultiplicative` and `AddEquiv.piAdditive` commute `Multiplicative` and
`Additive` with dependent products. This file records how these equivalences and their inverses
transport one-point families `Pi.single` and `Pi.mulSingle`.

## Main results

* `MulEquiv.piMultiplicative_ofAdd_single`, `MulEquiv.piMultiplicative_symm_mulSingle`:
  `MulEquiv.piMultiplicative` carries `Pi.single` to `Pi.mulSingle` and its inverse carries
  `Pi.mulSingle` back to `Pi.single`.
* `AddEquiv.piAdditive_ofMul_mulSingle`, `AddEquiv.piAdditive_symm_single`:
  `AddEquiv.piAdditive` carries `Pi.mulSingle` to `Pi.single` and its inverse carries
  `Pi.single` back to `Pi.mulSingle`.
-/

public section

section Multiplicative

variable {ι : Type*} [DecidableEq ι] (K : ι → Type*) [∀ i, Add (K i)] [∀ i, Zero (K i)]

/-- `MulEquiv.piMultiplicative` maps an additive one-point family `Pi.single i x` to the
multiplicative one-point family `Pi.mulSingle i (Multiplicative.ofAdd x)`. -/
@[simp]
theorem MulEquiv.piMultiplicative_ofAdd_single (i : ι) (x : K i) :
    MulEquiv.piMultiplicative K (Multiplicative.ofAdd (Pi.single i x)) =
      Pi.mulSingle (M := fun i => Multiplicative (K i)) i (Multiplicative.ofAdd x) := by
  ext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [h]

/-- The inverse of `MulEquiv.piMultiplicative` maps a multiplicative one-point family
`Pi.mulSingle i x` to `Multiplicative.ofAdd (Pi.single i x.toAdd)`. -/
-- Not `@[simp]` because `MulEquiv.piMultiplicative_symm_apply` already simplifies the LHS.
theorem MulEquiv.piMultiplicative_symm_mulSingle (i : ι) (x : Multiplicative (K i)) :
    (MulEquiv.piMultiplicative K).symm
        (Pi.mulSingle (M := fun i => Multiplicative (K i)) i x) =
      Multiplicative.ofAdd (Pi.single i x.toAdd) := by
  rw [MulEquiv.symm_apply_eq, MulEquiv.piMultiplicative_ofAdd_single, ofAdd_toAdd]

end Multiplicative

section Additive

variable {ι : Type*} [DecidableEq ι] (K : ι → Type*) [∀ i, Mul (K i)] [∀ i, One (K i)]

/-- `AddEquiv.piAdditive` maps a multiplicative one-point family `Pi.mulSingle i x` to the
additive one-point family `Pi.single i (Additive.ofMul x)`. -/
@[simp]
theorem AddEquiv.piAdditive_ofMul_mulSingle (i : ι) (x : K i) :
    AddEquiv.piAdditive K (Additive.ofMul (Pi.mulSingle i x)) =
      Pi.single (M := fun i => Additive (K i)) i (Additive.ofMul x) := by
  ext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [h]

/-- The inverse of `AddEquiv.piAdditive` maps an additive one-point family `Pi.single i x` to
`Additive.ofMul (Pi.mulSingle i x.toMul)`. -/
-- Not `@[simp]` because `AddEquiv.piAdditive_symm_apply` already simplifies the LHS.
theorem AddEquiv.piAdditive_symm_single (i : ι) (x : Additive (K i)) :
    (AddEquiv.piAdditive K).symm
        (Pi.single (M := fun i => Additive (K i)) i x) =
      Additive.ofMul (Pi.mulSingle i x.toMul) := by
  rw [AddEquiv.symm_apply_eq, AddEquiv.piAdditive_ofMul_mulSingle, ofMul_toMul]

end Additive
