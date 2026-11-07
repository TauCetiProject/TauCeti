/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The regular module over the double opposite ring

A right `Aᵐᵒᵖ`-module, that is a left `Aᵐᵒᵖᵐᵒᵖ`-module, becomes a left `A`-module by restricting
scalars along the canonical ring isomorphism `RingEquiv.opOp A : A ≃+* Aᵐᵒᵖᵐᵒᵖ`. For the regular
right module `Aᵐᵒᵖ` of `Aᵐᵒᵖ` this gives back the regular module `A`, through `MulOpposite.unop`.

## Main definitions

* `ModuleCat.restrictScalarsOpOpIso`: restricting scalars along `A ≃+* Aᵐᵒᵖᵐᵒᵖ` carries the
  `Aᵐᵒᵖᵐᵒᵖ`-module `Aᵐᵒᵖ` to the regular module `A`.
-/

public section

namespace ModuleCat

universe u

variable (A : Type u) [Ring A]

/-- Restricting scalars along `A ≃+* Aᵐᵒᵖᵐᵒᵖ` carries `Aᵐᵒᵖ`, the regular right module of `Aᵐᵒᵖ`, to
the regular module `A`, through `MulOpposite.unop`. -/
noncomputable def restrictScalarsOpOpIso :
    (restrictScalars.{u} (RingEquiv.opOp A).toRingHom).obj (of Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ) ≅ of A A :=
  let X := (restrictScalars.{u} (RingEquiv.opOp A).toRingHom).obj (of Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ)
  let e : X ≃ₗ[A] A :=
    { (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).symm with
      map_smul' := fun a x ↦ by
        rw [restrictScalars.smul_def]
        -- The element `x` of the restricted module is an element of `Aᵐᵒᵖ`, on which `op (op a)`
        -- acts by right multiplication by `op a`.
        exact (congrArg MulOpposite.unop (op_smul_eq_mul (MulOpposite.op a) (x : Aᵐᵒᵖ))).trans
          (MulOpposite.unop_mul (x : Aᵐᵒᵖ) (MulOpposite.op a)) }
  e.toModuleIso

end ModuleCat
