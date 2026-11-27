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
(`TauCeti.MaxTensorProduct.one_def`): the algebraic tensor product with the maximal norm,
`TauCeti.CStarTensorAlgebra (TauCeti.maxCStarTensorNorm A B)`, is then a unital normed algebra, and
its completion carries Mathlib's unital ring, algebra and normed structures, which extend the ones
of the nonunital C*-algebra `A ⊗max B`. The canonical map
`TauCeti.CStarTensorProduct.of (TauCeti.maxCStarTensorNorm A B)` is unital
(`TauCeti.MaxTensorProduct.ofStarAlgHom`).

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
* `TauCeti.MaxTensorProduct.ofStarAlgHom`: the unital star homomorphism `A ⊗[ℂ] B → A ⊗max B`.
* `TauCeti.MaxTensorProduct.includeLeft`, `TauCeti.MaxTensorProduct.includeRight`: the unital
  star homomorphisms `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`.
* `TauCeti.MaxTensorProduct.liftStarAlgHom`: the unital form of the universal property.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.3 (the maximal tensor product and its universal property).
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

namespace CStarTensorAlgebra

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with the maximal norm is the unital ring `A ⊗[ℂ] B`. -/
instance : Ring (CStarTensorAlgebra (maxCStarTensorNorm A B)) :=
  inferInstanceAs (Ring (A ⊗[ℂ] B))

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with the maximal norm is the complex algebra `A ⊗[ℂ] B`. -/
instance : Algebra ℂ (CStarTensorAlgebra (maxCStarTensorNorm A B)) :=
  inferInstanceAs (Algebra ℂ (A ⊗[ℂ] B))

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with the maximal norm is a unital normed ring. -/
instance : NormedRing (CStarTensorAlgebra (maxCStarTensorNorm A B)) where
  __ : NonUnitalNormedRing (CStarTensorAlgebra (maxCStarTensorNorm A B)) := inferInstance
  __ : Ring (CStarTensorAlgebra (maxCStarTensorNorm A B)) := inferInstance

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with the maximal norm is a normed algebra. -/
instance : NormedAlgebra ℂ (CStarTensorAlgebra (maxCStarTensorNorm A B)) where
  __ : Algebra ℂ (CStarTensorAlgebra (maxCStarTensorNorm A B)) := inferInstance
  norm_smul_le := norm_smul_le

end CStarTensorAlgebra

namespace MaxTensorProduct

open CStarTensorProduct

/-- **Units.** The maximal tensor product of unital C*-algebras is a unital C*-algebra, the
completion of the unital normed algebra `A ⊗[ℂ] B` with the maximal norm, with unit `1 ⊗ 1`. -/
instance instCStarAlgebra : CStarAlgebra (MaxTensorProduct A B) :=
  letI : CStarAlgebra (Completion (CStarTensorAlgebra (maxCStarTensorNorm A B))) :=
    { toCStarRing := Completion.cstarRing fun x ↦ (CStarRing.norm_star_mul_self (x := x)).ge
      norm_smul_le := norm_smul_le }
  inferInstanceAs (CStarAlgebra (Completion (CStarTensorAlgebra (maxCStarTensorNorm A B))))

/-- The canonical map `A ⊗[ℂ] B → A ⊗max B` is unital. -/
@[simp]
theorem of_one : of (maxCStarTensorNorm A B) 1 = 1 := by
  rw [← coe_equiv_eq_of, map_one]
  -- the unit of `MaxTensorProduct A B` is the unit of the completion, reached through the
  -- `CStarAlgebra` instance rather than syntactically as `Completion`'s `One`
  exact Completion.coe_one (CStarTensorAlgebra (maxCStarTensorNorm A B))

/-- The unit of `A ⊗max B` is `1 ⊗ 1`. -/
@[simp]
theorem of_one_tmul_one : of (maxCStarTensorNorm A B) ((1 : A) ⊗ₜ (1 : B)) = 1 := by
  rw [← Algebra.TensorProduct.one_def, of_one]

/-- The unit of `A ⊗max B` is `1 ⊗ 1`. -/
theorem one_def :
    (1 : MaxTensorProduct A B) = of (maxCStarTensorNorm A B) ((1 : A) ⊗ₜ (1 : B)) :=
  of_one_tmul_one.symm

/-- For nonzero unital `A` and `B`, the maximal tensor product is nonzero:
`‖1 ⊗ 1‖ = ‖1‖ ‖1‖ = 1`. -/
instance instNontrivial [Nontrivial A] [Nontrivial B] : Nontrivial (MaxTensorProduct A B) :=
  ⟨⟨1, 0, fun h ↦ by
    simpa [norm_of_tmul, -of_one_tmul_one] using congrArg norm (of_one_tmul_one.trans h)⟩⟩

variable (A B)

/-- The canonical map `A ⊗[ℂ] B → A ⊗max B` as a unital star homomorphism. -/
def ofStarAlgHom : A ⊗[ℂ] B →⋆ₐ[ℂ] MaxTensorProduct A B where
  __ := of (maxCStarTensorNorm A B)
  map_one' := of_one
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

variable {A B} in
@[simp]
theorem ofStarAlgHom_apply (x : A ⊗[ℂ] B) :
    ofStarAlgHom A B x = of (maxCStarTensorNorm A B) x :=
  (rfl)

/-- The unital star homomorphism `A → A ⊗max B`, `a ↦ a ⊗ 1`. -/
def includeLeft : A →⋆ₐ[ℂ] MaxTensorProduct A B where
  __ := (ofStarAlgHom A B).toAlgHom.comp Algebra.TensorProduct.includeLeft
  map_star' a := by
    simpa [TensorProduct.star_tmul] using map_star (of (maxCStarTensorNorm A B)) (a ⊗ₜ (1 : B))

/-- The unital star homomorphism `B → A ⊗max B`, `b ↦ 1 ⊗ b`. -/
def includeRight : B →⋆ₐ[ℂ] MaxTensorProduct A B where
  __ := (ofStarAlgHom A B).toAlgHom.comp Algebra.TensorProduct.includeRight
  map_star' b := by
    simpa [TensorProduct.star_tmul] using map_star (of (maxCStarTensorNorm A B)) ((1 : A) ⊗ₜ b)

variable {A B}

@[simp]
theorem includeLeft_apply (a : A) : includeLeft A B a = of (maxCStarTensorNorm A B) (a ⊗ₜ 1) :=
  (rfl)

@[simp]
theorem includeRight_apply (b : B) :
    includeRight A B b = of (maxCStarTensorNorm A B) (1 ⊗ₜ b) :=
  (rfl)

/-- `(a ⊗ 1)(1 ⊗ b) = a ⊗ b`. -/
theorem includeLeft_mul_includeRight (a : A) (b : B) :
    includeLeft A B a * includeRight A B b = of (maxCStarTensorNorm A B) (a ⊗ₜ b) := by
  rw [includeLeft_apply, includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- `(1 ⊗ b)(a ⊗ 1) = a ⊗ b`. -/
theorem includeRight_mul_includeLeft (a : A) (b : B) :
    includeRight A B b * includeLeft A B a = of (maxCStarTensorNorm A B) (a ⊗ₜ b) := by
  rw [includeLeft_apply, includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- The ranges of `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` commute. -/
theorem commute_includeLeft_includeRight (a : A) (b : B) :
    Commute (includeLeft A B a) (includeRight A B b) := by
  rw [Commute, SemiconjBy, includeLeft_mul_includeRight, includeRight_mul_includeLeft]

/-- **Uniqueness for unital star homomorphisms.** Two unital star homomorphisms out of `A ⊗max B`
into a C*-algebra agree if they agree on `a ⊗ 1` and on `1 ⊗ b`. -/
@[ext high]
theorem starAlgHom_ext' {C : Type*} [CStarAlgebra C] {φ ψ : MaxTensorProduct A B →⋆ₐ[ℂ] C}
    (hA : φ.comp (includeLeft A B) = ψ.comp (includeLeft A B))
    (hB : φ.comp (includeRight A B) = ψ.comp (includeRight A B)) : φ = ψ := by
  have h := starAlgHom_ext (φ := φ.toNonUnitalStarAlgHom) (ψ := ψ.toNonUnitalStarAlgHom)
    fun a b ↦ by
      rw [← includeLeft_mul_includeRight]
      simpa using congr($hA a * $hB b)
  exact StarAlgHom.ext fun x ↦ congrArg (· x) h

variable {C : Type (max u v)} [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
  (h : ∀ a b, Commute (φ a) (ψ b))

/-- **The universal property for unital algebras.** Commuting unital star homomorphisms
`φ : A → C` and `ψ : B → C` into a unital C*-algebra `C` in the universe `max u v` extend to the
unital star homomorphism `A ⊗max B → C` sending `a ⊗ b` to `φ a * ψ b`. -/
def liftStarAlgHom : MaxTensorProduct A B →⋆ₐ[ℂ] C where
  __ := lift φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h
  map_one' := by simpa using lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h 1 1
  commutes' r := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      congrArg (r • ·) (lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h 1 1)

/-- On `A ⊗[ℂ] B`, the unital extension is the integrated form `a ⊗ b ↦ φ a * ψ b`, Mathlib's
`Algebra.TensorProduct.lift`. -/
@[simp]
theorem liftStarAlgHom_of (x : A ⊗[ℂ] B) :
    liftStarAlgHom φ ψ h (of (maxCStarTensorNorm A B) x) =
      Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact lift_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom h a b
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The unital extension sends `a ⊗ b` to `φ a * ψ b`. -/
theorem liftStarAlgHom_of_tmul (a : A) (b : B) :
    liftStarAlgHom φ ψ h (of (maxCStarTensorNorm A B) (a ⊗ₜ b)) = φ a * ψ b :=
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
