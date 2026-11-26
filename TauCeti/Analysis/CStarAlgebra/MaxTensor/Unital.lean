/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Product

/-!
# The maximal tensor product of unital C*-algebras

Let `A` and `B` be unital C*-algebras. The maximal tensor product `A ⊗max B`
(`TauCeti.MaxTensorProduct A B`) is then a unital C*-algebra with unit `1 ⊗ 1`
(`TauCeti.MaxTensorProduct.one_def`). The ring, algebra and normed structures extend the ones
of the nonunital C*-algebra `A ⊗max B`, so the two C*-algebra structures agree.

The unital star homomorphisms `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`
(`TauCeti.MaxTensorProduct.includeLeft`, `TauCeti.MaxTensorProduct.includeRight`) have commuting
ranges, and their products `(a ⊗ 1)(1 ⊗ b) = a ⊗ b` span a dense subalgebra. For unital
commuting star homomorphisms `φ : A → C` and `ψ : B → C` into a unital C*-algebra, the extension
`TauCeti.MaxTensorProduct.lift φ ψ` of the universal property is unital
(`TauCeti.MaxTensorProduct.liftStarAlgHom`), and unital star homomorphisms out of `A ⊗max B` are
determined by their composites with `includeLeft` and `includeRight`
(`TauCeti.MaxTensorProduct.starAlgHom_ext'`).

## Main declarations

* `TauCeti.MaxTensorProduct.instCStarAlgebra`: `A ⊗max B` is a unital C*-algebra, nonzero when
  `A` and `B` are (`TauCeti.MaxTensorProduct.instNontrivial`).
* `TauCeti.MaxTensorProduct.includeLeft`, `TauCeti.MaxTensorProduct.includeRight`: the unital
  star homomorphisms `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`.
* `TauCeti.MaxTensorProduct.liftStarAlgHom`: the unital form of the universal property.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.3 (the maximal tensor product and its universal property).
-/

public section

noncomputable section

open TensorProduct

universe u v

namespace TauCeti

namespace MaxTensorProduct

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- `1 ⊗ 1` is a left unit of `A ⊗max B`. -/
theorem of_one_tmul_one_mul (x : MaxTensorProduct A B) :
    of A B ((1 : A) ⊗ₜ (1 : B)) * x = x :=
  induction_on x (isClosed_eq (by fun_prop) continuous_id) fun y ↦ by
    rw [← map_mul]
    exact congrArg (of A B) (one_mul y)

/-- `1 ⊗ 1` is a right unit of `A ⊗max B`. -/
theorem mul_of_one_tmul_one (x : MaxTensorProduct A B) :
    x * of A B ((1 : A) ⊗ₜ (1 : B)) = x :=
  induction_on x (isClosed_eq (by fun_prop) continuous_id) fun y ↦ by
    rw [← map_mul]
    exact congrArg (of A B) (mul_one y)

/-- The maximal tensor product of unital C*-algebras is a unital ring with unit `1 ⊗ 1`. It
extends the nonunital ring structure. -/
instance instRing : Ring (MaxTensorProduct A B) where
  __ : NonUnitalRing (MaxTensorProduct A B) := inferInstance
  one := of A B ((1 : A) ⊗ₜ (1 : B))
  one_mul := of_one_tmul_one_mul
  mul_one := mul_of_one_tmul_one

/-- The unit of `A ⊗max B` is `1 ⊗ 1`. -/
theorem one_def : (1 : MaxTensorProduct A B) = of A B ((1 : A) ⊗ₜ (1 : B)) :=
  (rfl)

/-- The maximal tensor product of unital C*-algebras is a complex algebra, with the scalar
multiplication of the nonunital C*-algebra. -/
instance instAlgebra : Algebra ℂ (MaxTensorProduct A B) :=
  Algebra.ofModule (fun r x y ↦ smul_mul_assoc r x y) (fun r x y ↦ mul_smul_comm r x y)

/-- The maximal tensor product of unital C*-algebras is a normed ring. -/
instance instNormedRing : NormedRing (MaxTensorProduct A B) where
  __ : NonUnitalNormedRing (MaxTensorProduct A B) := inferInstance
  __ : Ring (MaxTensorProduct A B) := inferInstance

/-- The maximal tensor product of unital C*-algebras is a normed algebra. -/
instance instNormedAlgebra : NormedAlgebra ℂ (MaxTensorProduct A B) where
  norm_smul_le := norm_smul_le

/-- **Units.** The maximal tensor product of unital C*-algebras is a unital C*-algebra, with unit
`1 ⊗ 1`. -/
instance instCStarAlgebra : CStarAlgebra (MaxTensorProduct A B) where
  __ : NonUnitalCStarAlgebra (MaxTensorProduct A B) := inferInstance
  __ : NormedRing (MaxTensorProduct A B) := inferInstance
  __ : NormedAlgebra ℂ (MaxTensorProduct A B) := inferInstance

/-- For nonzero unital `A` and `B`, the maximal tensor product is nonzero:
`‖1 ⊗ 1‖ = ‖1‖ ‖1‖ = 1`. -/
instance instNontrivial [Nontrivial A] [Nontrivial B] : Nontrivial (MaxTensorProduct A B) :=
  ⟨⟨1, 0, fun h ↦ by simpa [one_def, norm_of_tmul] using congrArg norm h⟩⟩

variable (A B)

/-- The unital star homomorphism `A → A ⊗max B`, `a ↦ a ⊗ 1`. -/
def includeLeft : A →⋆ₐ[ℂ] MaxTensorProduct A B where
  toFun a := of A B (a ⊗ₜ 1)
  map_one' := (rfl)
  map_mul' a a' := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by rw [TensorProduct.zero_tmul, map_zero]
  map_add' a a' := by rw [TensorProduct.add_tmul, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, one_def,
      ← TensorProduct.smul_tmul', map_smul]
  map_star' a := by rw [← map_star, TensorProduct.star_tmul, star_one]

/-- The unital star homomorphism `B → A ⊗max B`, `b ↦ 1 ⊗ b`. -/
def includeRight : B →⋆ₐ[ℂ] MaxTensorProduct A B where
  toFun b := of A B (1 ⊗ₜ b)
  map_one' := (rfl)
  map_mul' b b' := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by rw [TensorProduct.tmul_zero, map_zero]
  map_add' b b' := by rw [TensorProduct.tmul_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, one_def,
      TensorProduct.tmul_smul, map_smul]
  map_star' b := by rw [← map_star, TensorProduct.star_tmul, star_one]

variable {A B}

@[simp]
theorem includeLeft_apply (a : A) : includeLeft A B a = of A B (a ⊗ₜ 1) :=
  (rfl)

@[simp]
theorem includeRight_apply (b : B) : includeRight A B b = of A B (1 ⊗ₜ b) :=
  (rfl)

/-- `(a ⊗ 1)(1 ⊗ b) = a ⊗ b`. -/
theorem includeLeft_mul_includeRight (a : A) (b : B) :
    includeLeft A B a * includeRight A B b = of A B (a ⊗ₜ b) := by
  rw [includeLeft_apply, includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- `(1 ⊗ b)(a ⊗ 1) = a ⊗ b`. -/
theorem includeRight_mul_includeLeft (a : A) (b : B) :
    includeRight A B b * includeLeft A B a = of A B (a ⊗ₜ b) := by
  rw [includeLeft_apply, includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- The ranges of `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` commute. -/
theorem commute_includeLeft_includeRight (a : A) (b : B) :
    Commute (includeLeft A B a) (includeRight A B b) := by
  rw [Commute, SemiconjBy, includeLeft_mul_includeRight, includeRight_mul_includeLeft]

/-- **Uniqueness for unital star homomorphisms.** Two unital star homomorphisms out of `A ⊗max B`
into a C*-algebra agree if they agree on `a ⊗ 1` and on `1 ⊗ b`. -/
@[ext]
theorem starAlgHom_ext' {C : Type*} [CStarAlgebra C] {φ ψ : MaxTensorProduct A B →⋆ₐ[ℂ] C}
    (hA : φ.comp (includeLeft A B) = ψ.comp (includeLeft A B))
    (hB : φ.comp (includeRight A B) = ψ.comp (includeRight A B)) : φ = ψ := by
  have h := starAlgHom_ext (φ := φ.toNonUnitalStarAlgHom) (ψ := ψ.toNonUnitalStarAlgHom)
    fun a b ↦ by
      rw [← includeLeft_mul_includeRight]
      simp only [StarAlgHom.coe_toNonUnitalStarAlgHom, map_mul]
      rw [← StarAlgHom.comp_apply, hA, ← StarAlgHom.comp_apply φ, hB, StarAlgHom.comp_apply,
        StarAlgHom.comp_apply]
  exact StarAlgHom.ext fun x ↦ congrArg (· x) h

variable {C : Type (max u v)} [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
  (h : ∀ a b, Commute (φ a) (ψ b))

/-- **The universal property for unital algebras.** Commuting unital star homomorphisms
`φ : A → C` and `ψ : B → C` into a unital C*-algebra `C` in the universe `max u v` extend to the
unital star homomorphism `A ⊗max B → C` sending `a ⊗ b` to `φ a * ψ b`. -/
def liftStarAlgHom : MaxTensorProduct A B →⋆ₐ[ℂ] C where
  __ := lift φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h
  map_one' := by
    change lift _ _ h (of A B (1 ⊗ₜ 1)) = 1
    refine (lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h 1 1).trans ?_
    simp
  commutes' r := by
    change lift _ _ h (algebraMap ℂ (MaxTensorProduct A B) r) = _
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, one_def,
      lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h 1 1]
    simp

@[simp]
theorem liftStarAlgHom_of_tmul (a : A) (b : B) :
    liftStarAlgHom φ ψ h (of A B (a ⊗ₜ b)) = φ a * ψ b :=
  lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h a b

/-- The unital extension restricts to `φ` along `a ↦ a ⊗ 1`. -/
@[simp]
theorem liftStarAlgHom_comp_includeLeft :
    (liftStarAlgHom φ ψ h).comp (includeLeft A B) = φ :=
  StarAlgHom.ext fun a ↦ by simp

/-- The unital extension restricts to `ψ` along `b ↦ 1 ⊗ b`. -/
@[simp]
theorem liftStarAlgHom_comp_includeRight :
    (liftStarAlgHom φ ψ h).comp (includeRight A B) = ψ :=
  StarAlgHom.ext fun b ↦ by simp

end MaxTensorProduct

end TauCeti
