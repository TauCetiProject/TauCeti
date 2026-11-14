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
# Opposite ring homomorphisms, products, and double-opposite inverse pairs

This file provides basic functoriality lemmas for `RingHom.op`, the canonical ring isomorphism
`RingEquiv.prodMulOpposite : (R × S)ᵐᵒᵖ ≃+* Rᵐᵒᵖ × Sᵐᵒᵖ` identifying the opposite of a binary
product with the product of the opposites (the binary counterpart of `RingEquiv.piMulOpposite`),
and `RingHomInvPair` instances for `RingEquiv.opOp`.
-/

public section

namespace RingHom

@[simp]
theorem op_id (R : Type*) [NonAssocSemiring R] :
    RingHom.op (RingHom.id R) = RingHom.id Rᵐᵒᵖ := by
  ext x
  rfl

@[simp]
theorem op_comp {R S T : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]
    (f : R →+* S) (g : S →+* T) :
    RingHom.op (g.comp f) = (RingHom.op g).comp (RingHom.op f) := by
  ext x
  rfl

end RingHom

namespace RingEquiv

/-- The opposite of a product of two rings is isomorphic to the product of their opposites.
This is the binary counterpart of `RingEquiv.piMulOpposite`. -/
def prodMulOpposite (R S : Type*) [Mul R] [Add R] [Mul S] [Add S] :
    (R × S)ᵐᵒᵖ ≃+* Rᵐᵒᵖ × Sᵐᵒᵖ where
  toFun x := (MulOpposite.op x.unop.1, MulOpposite.op x.unop.2)
  invFun x := MulOpposite.op (x.1.unop, x.2.unop)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem prodMulOpposite_apply (R S : Type*) [Mul R] [Add R] [Mul S] [Add S] (x : (R × S)ᵐᵒᵖ) :
    prodMulOpposite R S x = (MulOpposite.op x.unop.1, MulOpposite.op x.unop.2) := (rfl)

@[simp]
theorem prodMulOpposite_symm_apply (R S : Type*) [Mul R] [Add R] [Mul S] [Add S]
    (x : Rᵐᵒᵖ × Sᵐᵒᵖ) :
    (prodMulOpposite R S).symm x = MulOpposite.op (x.1.unop, x.2.unop) := (rfl)

@[simp]
theorem fst_comp_prodMulOpposite (R S : Type*) [NonAssocSemiring R] [NonAssocSemiring S] :
    (RingHom.fst Rᵐᵒᵖ Sᵐᵒᵖ).comp (prodMulOpposite R S : (R × S)ᵐᵒᵖ →+* Rᵐᵒᵖ × Sᵐᵒᵖ) =
      RingHom.op (RingHom.fst R S) := by
  ext x
  rfl

@[simp]
theorem snd_comp_prodMulOpposite (R S : Type*) [NonAssocSemiring R] [NonAssocSemiring S] :
    (RingHom.snd Rᵐᵒᵖ Sᵐᵒᵖ).comp (prodMulOpposite R S : (R × S)ᵐᵒᵖ →+* Rᵐᵒᵖ × Sᵐᵒᵖ) =
      RingHom.op (RingHom.snd R S) := by
  ext x
  rfl

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
