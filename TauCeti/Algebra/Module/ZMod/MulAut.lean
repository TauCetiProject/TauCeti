/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.ZMod

/-!
# Automorphisms of a group whose additive copy is a `ℤ/nℤ`-module

Let `Q` be a commutative group whose additive copy `Additive Q` is a `ZMod n`-module, for instance
an elementary abelian `p`-group viewed as an `𝔽_p`-vector space through `AddCommGroup.zmodModule`.
Every additive endomorphism of a `ZMod n`-module is `ZMod n`-linear (`ZMod.map_smul`), so the group
automorphisms of `Q` are exactly the `ZMod n`-linear automorphisms of `Additive Q`. This file
records that identification as an isomorphism of groups; composed with a basis it presents the
automorphism group of a finite elementary abelian `p`-group as a general linear group over `𝔽_p`.

## Main definitions

* `TauCeti.mulAutEquivZModLinearEquiv`: the group isomorphism
  `MulAut Q ≃* (Additive Q ≃ₗ[ZMod n] Additive Q)`.
-/

public section

namespace TauCeti

variable (n : ℕ) (Q : Type*) [CommGroup Q] [Module (ZMod n) (Additive Q)]

/-- **Group automorphisms are linear automorphisms.** For a commutative group `Q` whose additive
copy is a `ZMod n`-module, an automorphism of `Q`, read additively, is a `ZMod n`-linear
automorphism of `Additive Q`, and every linear automorphism arises this way. -/
def mulAutEquivZModLinearEquiv : MulAut Q ≃* (Additive Q ≃ₗ[ZMod n] Additive Q) where
  toFun σ := (MulEquiv.toAdditive σ).toLinearEquiv (ZMod.map_smul (MulEquiv.toAdditive σ))
  invFun e := MulEquiv.toAdditive.symm e.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {n Q}

/-- The linear automorphism attached to `σ` acts on `Additive Q` as `σ` acts on `Q`. -/
@[simp]
theorem mulAutEquivZModLinearEquiv_apply (σ : MulAut Q) (x : Additive Q) :
    mulAutEquivZModLinearEquiv n Q σ x = Additive.ofMul (σ x.toMul) :=
  (rfl)

/-- The group automorphism attached to a linear automorphism `e` acts on `Q` as `e` acts on
`Additive Q`. -/
@[simp]
theorem mulAutEquivZModLinearEquiv_symm_apply (e : Additive Q ≃ₗ[ZMod n] Additive Q) (x : Q) :
    (mulAutEquivZModLinearEquiv n Q).symm e x = (e (Additive.ofMul x)).toMul :=
  (rfl)

end TauCeti
