/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Opposite
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Opposite nonunital `⋆`-algebra homomorphisms

A nonunital `⋆`-algebra homomorphism `A →⋆ₙₐ[R] B` induces a nonunital `⋆`-algebra homomorphism
`Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ` on multiplicative opposites, inversely to `unop`, mirroring `AlgHom.op`. In
operator algebras this transports homomorphisms of coefficient `⋆`-algebras to the opposite
homomorphisms governing right modules.

## Main declarations

* `NonUnitalStarAlgHom.op`: the equivalence `(A →⋆ₙₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ)`.
* `NonUnitalStarAlgHom.unop`: the inverse equivalence `(Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) ≃ (A →⋆ₙₐ[R] B)`.
-/

public section

namespace NonUnitalStarAlgHom

variable {R A B C : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

/-- A nonunital `⋆`-algebra homomorphism `A →⋆ₙₐ[R] B` can equivalently be viewed as a nonunital
`⋆`-algebra homomorphism `Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ`. -/
protected def op : (A →⋆ₙₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) where
  toFun f :=
    { toFun x := MulOpposite.op (f x.unop)
      map_smul' r x := MulOpposite.unop_injective (map_smul f r x.unop)
      map_zero' := by simp
      map_add' x y := MulOpposite.unop_injective (map_add f x.unop y.unop)
      map_mul' x y := MulOpposite.unop_injective (map_mul f y.unop x.unop)
      map_star' x := MulOpposite.unop_injective (map_star f x.unop) }
  invFun f :=
    { toFun x := (f (MulOpposite.op x)).unop
      map_smul' r x := MulOpposite.op_injective (map_smul f r (MulOpposite.op x))
      map_zero' := by simp
      map_add' x y := MulOpposite.op_injective (map_add f (MulOpposite.op x) (MulOpposite.op y))
      map_mul' x y := MulOpposite.op_injective (map_mul f (MulOpposite.op y) (MulOpposite.op x))
      map_star' x := MulOpposite.op_injective (map_star f (MulOpposite.op x)) }
  left_inv f := by ext x; rfl
  right_inv f := by ext x; exact MulOpposite.op_unop _

/-- The unopposite of a nonunital `⋆`-algebra homomorphism `Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ`, inverse to
`NonUnitalStarAlgHom.op`. -/
abbrev unop : (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) ≃ (A →⋆ₙₐ[R] B) :=
  NonUnitalStarAlgHom.op.symm

@[simp]
theorem op_apply (f : A →⋆ₙₐ[R] B) (x : Aᵐᵒᵖ) :
    f.op x = MulOpposite.op (f x.unop) :=
  (rfl)

@[simp]
theorem unop_apply (f : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) (x : A) :
    unop f x = (f (MulOpposite.op x)).unop :=
  (rfl)

@[simp]
theorem op_id :
    (NonUnitalStarAlgHom.id R A).op = NonUnitalStarAlgHom.id R Aᵐᵒᵖ := by
  ext x
  simp

@[simp]
theorem op_comp (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    (g.comp f).op = g.op.comp f.op := by
  ext x
  simp

@[simp]
theorem unop_id :
    unop (NonUnitalStarAlgHom.id R Aᵐᵒᵖ) = NonUnitalStarAlgHom.id R A := by
  ext x
  simp

@[simp]
theorem unop_comp (g : Bᵐᵒᵖ →⋆ₙₐ[R] Cᵐᵒᵖ) (f : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) :
    unop (g.comp f) = (unop g).comp (unop f) := by
  ext x
  simp

end NonUnitalStarAlgHom
