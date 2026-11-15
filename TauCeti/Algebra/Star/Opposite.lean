/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra

/-!
# Multiplicative opposites of `⋆`-algebra homomorphisms and `⋆`-subalgebras

Applying `MulOpposite.op` on both domain and codomain reverses multiplication twice, so any
(possibly nonunital) `⋆`-algebra homomorphism `f : A →⋆ₙₐ[R] B` induces a `⋆`-algebra homomorphism
`f.op : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ`, and likewise for unital `⋆`-algebra homomorphisms `A →⋆ₐ[R] B` and
nonunital `⋆`-subalgebras `NonUnitalStarSubalgebra R A`. These mirror Mathlib's `AlgHom.op` and
`Subalgebra.op` and translate between left and right coefficient actions on C⋆-modules.

## Main declarations

* `NonUnitalStarAlgHom.op` and `NonUnitalStarAlgHom.unop`: the equivalence
  `(A →⋆ₙₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ)`.
* `StarAlgHom.op` and `StarAlgHom.unop`: the equivalence `(A →⋆ₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ)`.
* `NonUnitalStarSubalgebra.op` and `NonUnitalStarSubalgebra.unop`: the order isomorphism
  `NonUnitalStarSubalgebra R A ≃o NonUnitalStarSubalgebra R Aᵐᵒᵖ`, compatible with `subtype`.
-/

public section

open MulOpposite

namespace NonUnitalStarAlgHom

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- A nonunital `⋆`-algebra homomorphism `A →⋆ₙₐ[R] B` equivalently gives a nonunital `⋆`-algebra
homomorphism `Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ`. -/
protected def op : (A →⋆ₙₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) where
  toFun f :=
    { toFun a := MulOpposite.op (f a.unop)
      map_smul' _ _ := unop_injective <| by simp
      map_zero' := unop_injective <| by simp
      map_add' _ _ := unop_injective <| by simp
      map_mul' _ _ := unop_injective <| by simp
      map_star' _ := unop_injective <| by simp [map_star] }
  invFun f :=
    { toFun a := (f (MulOpposite.op a)).unop
      map_smul' _ _ := op_injective <| by simp
      map_zero' := op_injective <| by simp
      map_add' _ _ := op_injective <| by simp
      map_mul' _ _ := by simp [op_mul]
      map_star' _ := by simp [op_star, map_star] }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- The unopposite of a nonunital `⋆`-algebra homomorphism `Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ`. -/
abbrev unop : (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) ≃ (A →⋆ₙₐ[R] B) := NonUnitalStarAlgHom.op.symm

@[simp] theorem op_apply_apply (f : A →⋆ₙₐ[R] B) (a : Aᵐᵒᵖ) :
    f.op a = MulOpposite.op (f a.unop) := (rfl)

@[simp] theorem unop_apply_apply (f : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) (a : A) :
    NonUnitalStarAlgHom.unop f a = (f (MulOpposite.op a)).unop := (rfl)

@[simp] theorem op_id : (NonUnitalStarAlgHom.id R A).op = NonUnitalStarAlgHom.id R Aᵐᵒᵖ := by
  ext; rfl

@[simp] theorem op_comp {C : Type*} [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
    (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) : (g.comp f).op = g.op.comp f.op := by ext; rfl

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]

/-- A unital `⋆`-algebra homomorphism `A →⋆ₐ[R] B` equivalently gives a unital `⋆`-algebra
homomorphism `Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ`. -/
protected def op : (A →⋆ₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) where
  toFun f := { f.toAlgHom.op with map_star' _ := unop_injective <| by simp [map_star] }
  invFun f := { f.toAlgHom.unop with map_star' _ := by simp [op_star, map_star] }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- The unopposite of a unital `⋆`-algebra homomorphism `Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ`. -/
abbrev unop : (Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) ≃ (A →⋆ₐ[R] B) := StarAlgHom.op.symm

@[simp] theorem op_apply_apply (f : A →⋆ₐ[R] B) (a : Aᵐᵒᵖ) :
    f.op a = MulOpposite.op (f a.unop) := (rfl)

@[simp] theorem unop_apply_apply (f : Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) (a : A) :
    StarAlgHom.unop f a = (f (MulOpposite.op a)).unop := (rfl)

@[simp] theorem toNonUnitalStarAlgHom_op (f : A →⋆ₐ[R] B) :
    f.op.toNonUnitalStarAlgHom = f.toNonUnitalStarAlgHom.op := by ext; rfl

end StarAlgHom

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

/-- A nonunital `⋆`-subalgebra of `A` viewed as a nonunital `⋆`-subalgebra of `Aᵐᵒᵖ`. -/
protected def op : NonUnitalStarSubalgebra R A ≃o NonUnitalStarSubalgebra R Aᵐᵒᵖ where
  toFun S :=
    { carrier := MulOpposite.unop ⁻¹' (S : Set A)
      mul_mem' ha hb := S.mul_mem hb ha
      zero_mem' := S.zero_mem
      add_mem' := S.add_mem
      smul_mem' c _ := S.smul_mem c
      star_mem' := star_mem }
  invFun S :=
    { carrier := MulOpposite.op ⁻¹' (S : Set Aᵐᵒᵖ)
      mul_mem' ha hb := S.mul_mem hb ha
      zero_mem' := S.zero_mem
      add_mem' := S.add_mem
      smul_mem' c _ := S.smul_mem c
      star_mem' := star_mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_rel_iff' := ⟨fun h _ hx ↦ h (x := MulOpposite.op _) hx, fun h _ hx ↦ h hx⟩

/-- The unopposite of a nonunital `⋆`-subalgebra of `Aᵐᵒᵖ`. -/
abbrev unop : NonUnitalStarSubalgebra R Aᵐᵒᵖ ≃o NonUnitalStarSubalgebra R A :=
  NonUnitalStarSubalgebra.op.symm

@[simp] theorem mem_op {S : NonUnitalStarSubalgebra R A} {x : Aᵐᵒᵖ} : x ∈ S.op ↔ x.unop ∈ S :=
  Iff.rfl

theorem op_mem_op {S : NonUnitalStarSubalgebra R A} {x : A} : MulOpposite.op x ∈ S.op ↔ x ∈ S :=
  Iff.rfl

@[simp] theorem coe_op (S : NonUnitalStarSubalgebra R A) :
    (S.op : Set Aᵐᵒᵖ) = MulOpposite.unop ⁻¹' (S : Set A) := (rfl)

end NonUnitalStarSubalgebra
