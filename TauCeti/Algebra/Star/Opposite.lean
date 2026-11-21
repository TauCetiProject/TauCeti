/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Multiplicative opposites of `⋆`-algebra homomorphisms and `⋆`-subalgebras

Applying `MulOpposite.op` on both domain and codomain reverses multiplication twice, inducing
opposite equivalences on nonunital and unital `⋆`-algebra homomorphisms and nonunital
`⋆`-subalgebras, mirroring `AlgHom.op` and `Subalgebra.op`:

* `NonUnitalStarAlgHom.op`, `NonUnitalStarAlgHom.unop`: `(A →⋆ₙₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ)`.
* `StarAlgHom.op`, `StarAlgHom.unop`: `(A →⋆ₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ)`.
* `NonUnitalStarSubalgebra.op`, `NonUnitalStarSubalgebra.unop`, `NonUnitalStarSubalgebra.opEquiv`:
  `NonUnitalStarSubalgebra R A ≃o NonUnitalStarSubalgebra R Aᵐᵒᵖ`.
-/

public section

open MulOpposite

namespace NonUnitalStarAlgHom

variable {R A B : Type*} [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

/-- A nonunital `⋆`-algebra homomorphism `A →⋆ₙₐ[R] B` equivalently gives `Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ`. -/
protected def op : (A →⋆ₙₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) where
  toFun f :=
    { toFun a := op (f a.unop), map_smul' _ _ := unop_injective (by simp),
      map_zero' := unop_injective (by simp), map_add' _ _ := unop_injective (by simp),
      map_mul' _ _ := unop_injective (by simp), map_star' _ := unop_injective (by simp [map_star]) }
  invFun f :=
    { toFun a := (f (op a)).unop, map_smul' _ _ := op_injective (by simp),
      map_zero' := op_injective (by simp), map_add' _ _ := op_injective (by simp),
      map_mul' _ _ := by simp [op_mul], map_star' _ := by simp [op_star, map_star] }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- The unopposite of a nonunital `⋆`-algebra homomorphism `Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ`. -/
abbrev unop : (Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) ≃ (A →⋆ₙₐ[R] B) := NonUnitalStarAlgHom.op.symm

@[simp] theorem op_apply_apply (f : A →⋆ₙₐ[R] B) (a : Aᵐᵒᵖ) : f.op a = op (f a.unop) := (rfl)
@[simp] theorem unop_apply_apply (f : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) (a : A) :
    NonUnitalStarAlgHom.unop f a = (f (op a)).unop := (rfl)
@[simp] theorem op_id : (NonUnitalStarAlgHom.id R A).op = NonUnitalStarAlgHom.id R Aᵐᵒᵖ :=
  DFunLike.ext' rfl
@[simp] theorem unop_id :
    NonUnitalStarAlgHom.unop (NonUnitalStarAlgHom.id R Aᵐᵒᵖ) = NonUnitalStarAlgHom.id R A :=
  DFunLike.ext' rfl
@[simp] theorem op_comp {C : Type*} [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]
    (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) : (g.comp f).op = g.op.comp f.op := DFunLike.ext' rfl
@[simp] theorem unop_comp {C : Type*} [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]
    (g : Bᵐᵒᵖ →⋆ₙₐ[R] Cᵐᵒᵖ) (f : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) :
    NonUnitalStarAlgHom.unop (g.comp f) =
      (NonUnitalStarAlgHom.unop g).comp (NonUnitalStarAlgHom.unop f) := DFunLike.ext' rfl

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]

/-- A unital `⋆`-algebra homomorphism `A →⋆ₐ[R] B` equivalently gives `Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ`. -/
protected def op : (A →⋆ₐ[R] B) ≃ (Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) where
  toFun f := { f.toAlgHom.op with map_star' _ := unop_injective <| by simp [map_star] }
  invFun f := { f.toAlgHom.unop with map_star' _ := by simp [op_star, map_star] }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- The unopposite of a unital `⋆`-algebra homomorphism `Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ`. -/
abbrev unop : (Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) ≃ (A →⋆ₐ[R] B) := StarAlgHom.op.symm

@[simp] theorem op_apply_apply (f : A →⋆ₐ[R] B) (a : Aᵐᵒᵖ) : f.op a = op (f a.unop) := (rfl)
@[simp] theorem unop_apply_apply (f : Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) (a : A) :
    StarAlgHom.unop f a = (f (op a)).unop := (rfl)
@[simp] theorem op_id : (StarAlgHom.id R A).op = StarAlgHom.id R Aᵐᵒᵖ := DFunLike.ext' rfl
@[simp] theorem unop_id : StarAlgHom.unop (StarAlgHom.id R Aᵐᵒᵖ) = StarAlgHom.id R A :=
  DFunLike.ext' rfl
@[simp] theorem op_comp {C : Type*} [Semiring C] [Algebra R C] [Star C]
    (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) : (g.comp f).op = g.op.comp f.op := DFunLike.ext' rfl
@[simp] theorem unop_comp {C : Type*} [Semiring C] [Algebra R C] [Star C]
    (g : Bᵐᵒᵖ →⋆ₐ[R] Cᵐᵒᵖ) (f : Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) :
    StarAlgHom.unop (g.comp f) = (StarAlgHom.unop g).comp (StarAlgHom.unop f) := DFunLike.ext' rfl
@[simp] theorem toAlgHom_op (f : A →⋆ₐ[R] B) : f.op.toAlgHom = f.toAlgHom.op := DFunLike.ext' rfl
@[simp] theorem toAlgHom_unop (f : Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) :
    (StarAlgHom.unop f).toAlgHom = AlgHom.unop f.toAlgHom := DFunLike.ext' rfl
@[simp] theorem toNonUnitalStarAlgHom_op (f : A →⋆ₐ[R] B) :
    f.op.toNonUnitalStarAlgHom = f.toNonUnitalStarAlgHom.op := DFunLike.ext' rfl
@[simp] theorem toNonUnitalStarAlgHom_unop (f : Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) :
    (StarAlgHom.unop f).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.unop f.toNonUnitalStarAlgHom := DFunLike.ext' rfl

end StarAlgHom

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

/-- Pull a nonunital `⋆`-subalgebra of `A` back along `MulOpposite.unop` to `Aᵐᵒᵖ`. -/
protected def op (S : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R Aᵐᵒᵖ :=
  { carrier := MulOpposite.unop ⁻¹' (S : Set A), mul_mem' ha hb := S.mul_mem hb ha,
    zero_mem' := S.zero_mem, add_mem' := S.add_mem, smul_mem' c _ := S.smul_mem c,
    star_mem' := star_mem }

/-- Pull a nonunital `⋆`-subalgebra of `Aᵐᵒᵖ` back along `MulOpposite.op` to `A`. -/
protected def unop (S : NonUnitalStarSubalgebra R Aᵐᵒᵖ) : NonUnitalStarSubalgebra R A :=
  { carrier := MulOpposite.op ⁻¹' (S : Set Aᵐᵒᵖ), mul_mem' ha hb := S.mul_mem hb ha,
    zero_mem' := S.zero_mem, add_mem' := S.add_mem, smul_mem' c _ := S.smul_mem c,
    star_mem' := star_mem }

@[simp] theorem mem_op {S : NonUnitalStarSubalgebra R A} {x : Aᵐᵒᵖ} : x ∈ S.op ↔ x.unop ∈ S := .rfl
theorem op_mem_op {S : NonUnitalStarSubalgebra R A} {x : A} : MulOpposite.op x ∈ S.op ↔ x ∈ S :=
  .rfl
@[simp] theorem mem_unop {S : NonUnitalStarSubalgebra R Aᵐᵒᵖ} {x : A} :
    x ∈ S.unop ↔ MulOpposite.op x ∈ S := .rfl
@[simp, norm_cast] theorem coe_op (S : NonUnitalStarSubalgebra R A) :
    (S.op : Set Aᵐᵒᵖ) = MulOpposite.unop ⁻¹' (S : Set A) := (rfl)
@[simp, norm_cast] theorem coe_unop (S : NonUnitalStarSubalgebra R Aᵐᵒᵖ) :
    (S.unop : Set A) = MulOpposite.op ⁻¹' (S : Set Aᵐᵒᵖ) := (rfl)
@[simp] theorem unop_op (S : NonUnitalStarSubalgebra R A) : S.op.unop = S :=
  SetLike.coe_injective rfl
@[simp] theorem op_unop (S : NonUnitalStarSubalgebra R Aᵐᵒᵖ) : S.unop.op = S :=
  SetLike.coe_injective rfl
@[simp] theorem op_le_op_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall
@[simp] theorem unop_le_unop_iff {S₁ S₂ : NonUnitalStarSubalgebra R Aᵐᵒᵖ} :
    S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ := MulOpposite.unop_surjective.forall

/-- Order isomorphism between nonunital `⋆`-subalgebras of `A` and of `Aᵐᵒᵖ`. -/
def opEquiv : NonUnitalStarSubalgebra R A ≃o NonUnitalStarSubalgebra R Aᵐᵒᵖ :=
  { toFun := NonUnitalStarSubalgebra.op, invFun := NonUnitalStarSubalgebra.unop,
    left_inv := unop_op, right_inv := op_unop, map_rel_iff' := op_le_op_iff }

@[simp] theorem opEquiv_apply (S : NonUnitalStarSubalgebra R A) : opEquiv S = S.op := (rfl)
@[simp] theorem opEquiv_symm_apply (S : NonUnitalStarSubalgebra R Aᵐᵒᵖ) :
    opEquiv.symm S = S.unop := (rfl)

end NonUnitalStarSubalgebra
