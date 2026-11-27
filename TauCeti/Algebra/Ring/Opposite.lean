/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.Prod

/-!
# Opposite rings, ring homomorphisms, and products

The canonical equivalence `RingEquiv.opOp A` identifies a semiring with its double opposite.
The inverse-pair instances here allow semilinear maps along this equivalence to invert and compose.
This file also provides `RingHom.op_{id,comp}`, `RingHom.surjective_op_iff`, and
`RingEquiv.prodMulOpposite : (R × S)ᵐᵒᵖ ≃+* Rᵐᵒᵖ × Sᵐᵒᵖ`.
-/

public section

namespace RingHom

@[simp] theorem op_id (R : Type*) [NonAssocSemiring R] :
    RingHom.op (RingHom.id R) = RingHom.id Rᵐᵒᵖ := by ext; rfl

@[simp] theorem op_comp {R S T : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [NonAssocSemiring T] (f : R →+* S) (g : S →+* T) :
    RingHom.op (g.comp f) = (RingHom.op g).comp (RingHom.op f) := by ext; rfl

end RingHom

namespace RingEquiv

/-- Taking the opposite of a ring isomorphism commutes with coercion to a ring homomorphism. -/
theorem toRingHom_op {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (e : R ≃+* S) : (RingEquiv.op e).toRingHom = RingHom.op e.toRingHom := by ext; rfl

section Prod

variable (R S : Type*) [Mul R] [Add R] [Mul S] [Add S]

/-- Opposite of a binary product of rings (binary counterpart of `RingEquiv.piMulOpposite`). -/
def prodMulOpposite : (R × S)ᵐᵒᵖ ≃+* Rᵐᵒᵖ × Sᵐᵒᵖ where
  toFun x := (MulOpposite.op x.unop.1, MulOpposite.op x.unop.2)
  invFun x := MulOpposite.op (x.1.unop, x.2.unop)
  left_inv _ := rfl; right_inv _ := rfl; map_mul' _ _ := rfl; map_add' _ _ := rfl

@[simp] theorem prodMulOpposite_apply (x : (R × S)ᵐᵒᵖ) :
    prodMulOpposite R S x = (MulOpposite.op x.unop.1, MulOpposite.op x.unop.2) := (rfl)

@[simp] theorem prodMulOpposite_symm_apply (x : Rᵐᵒᵖ × Sᵐᵒᵖ) :
    (prodMulOpposite R S).symm x = MulOpposite.op (x.1.unop, x.2.unop) := (rfl)

end Prod

@[simp] theorem fst_comp_prodMulOpposite (R S : Type*) [NonAssocSemiring R] [NonAssocSemiring S] :
    (RingHom.fst Rᵐᵒᵖ Sᵐᵒᵖ).comp (prodMulOpposite R S : (R × S)ᵐᵒᵖ →+* Rᵐᵒᵖ × Sᵐᵒᵖ) =
      RingHom.op (RingHom.fst R S) := by ext; rfl

@[simp] theorem snd_comp_prodMulOpposite (R S : Type*) [NonAssocSemiring R] [NonAssocSemiring S] :
    (RingHom.snd Rᵐᵒᵖ Sᵐᵒᵖ).comp (prodMulOpposite R S : (R × S)ᵐᵒᵖ →+* Rᵐᵒᵖ × Sᵐᵒᵖ) =
      RingHom.op (RingHom.snd R S) := by ext; rfl

end RingEquiv

namespace TauCeti

/-- The canonical double-opposite ring equivalence and its inverse form an inverse pair. -/
instance opOpRingHomInvPair (A : Type*) [Semiring A] :
    RingHomInvPair (RingHomClass.toRingHom (RingEquiv.opOp A))
      (RingHomClass.toRingHom (RingEquiv.opOp A).symm) :=
  RingHomInvPair.of_ringEquiv (RingEquiv.opOp A)

/-- The inverse double-opposite ring equivalence and the forward equivalence form
an inverse pair. -/
instance opOpRingHomInvPairSymm (A : Type*) [Semiring A] :
    RingHomInvPair (RingHomClass.toRingHom (RingEquiv.opOp A).symm)
      (RingHomClass.toRingHom (RingEquiv.opOp A)) :=
  RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp A)

end TauCeti

namespace RingHom

/-- A ring homomorphism is surjective on opposite rings exactly when it is surjective
on the original rings. -/
@[simp]
theorem surjective_op_iff {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) :
    Function.Surjective f.op ↔ Function.Surjective f :=
  ⟨fun h ↦ MulOpposite.unop_surjective.comp (h.comp MulOpposite.op_surjective),
    fun h ↦ MulOpposite.op_surjective.comp (h.comp MulOpposite.unop_surjective)⟩

end RingHom
