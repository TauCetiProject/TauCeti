/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TensorProduct
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The C*-tensor product of unital C*-algebras

Let `A` and `B` be unital C*-algebras and `N` a C*-norm on `A ⊗[ℂ] B`. The C*-tensor product
`TauCeti.CStarTensorProduct N` is then a unital C*-algebra with unit `1 ⊗ 1`
(`TauCeti.CStarTensorProduct.one_def`): the algebraic tensor product with the norm `N`,
`TauCeti.CStarTensorAlgebra N`, is a unital normed algebra, and its completion carries Mathlib's
unital ring, algebra and normed structures, which extend the ones of the nonunital C*-algebra
`TauCeti.CStarTensorProduct N`. The canonical map `TauCeti.CStarTensorProduct.of N` is unital
(`TauCeti.CStarTensorProduct.ofStarAlgHom`).

The unital star homomorphisms `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`
(`TauCeti.CStarTensorProduct.includeLeft`, `TauCeti.CStarTensorProduct.includeRight`) are
injective, hence isometric, when the other factor is nonzero. They have commuting
ranges, and their products `(a ⊗ 1)(1 ⊗ b) = a ⊗ b` span a dense subalgebra, so unital
star homomorphisms out of `TauCeti.CStarTensorProduct N` are determined by their composites with
`includeLeft` and `includeRight` (`TauCeti.CStarTensorProduct.starAlgHom_ext'`).

The maximal and minimal tensor products `TauCeti.MaxTensorProduct A B` and
`TauCeti.MinTensorProduct A B` inherit all of this as the cases of the maximal and minimal norms.

## Main declarations

* `TauCeti.CStarTensorProduct.instCStarAlgebra`: `TauCeti.CStarTensorProduct N` is a unital
  C*-algebra, nonzero when `A` and `B` are (`TauCeti.CStarTensorProduct.instNontrivial`).
* `TauCeti.CStarTensorProduct.ofStarAlgHom`: the unital star homomorphism
  `A ⊗[ℂ] B → TauCeti.CStarTensorProduct N`.
* `TauCeti.CStarTensorProduct.includeLeft`, `TauCeti.CStarTensorProduct.includeRight`: the unital
  star homomorphisms `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`, isometric for nonzero factors
  (`TauCeti.CStarTensorProduct.norm_includeLeft`, `TauCeti.CStarTensorProduct.norm_includeRight`;
  in simp normal form `TauCeti.CStarTensorNorm.map_tmul_one`,
  `TauCeti.CStarTensorNorm.map_one_tmul`).

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.1–II.9.2.
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

namespace CStarTensorAlgebra

variable (N : CStarTensorNorm A B)

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with a C*-norm is the unital ring `A ⊗[ℂ] B`. -/
instance : Ring (CStarTensorAlgebra N) :=
  inferInstanceAs (Ring (A ⊗[ℂ] B))

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with a C*-norm is the complex algebra `A ⊗[ℂ] B`. -/
instance : Algebra ℂ (CStarTensorAlgebra N) :=
  inferInstanceAs (Algebra ℂ (A ⊗[ℂ] B))

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with a C*-norm is a unital normed ring. -/
instance : NormedRing (CStarTensorAlgebra N) where
  __ : NonUnitalNormedRing (CStarTensorAlgebra N) := inferInstance
  __ : Ring (CStarTensorAlgebra N) := inferInstance

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with a C*-norm is a normed algebra. -/
instance : NormedAlgebra ℂ (CStarTensorAlgebra N) where
  __ : Algebra ℂ (CStarTensorAlgebra N) := inferInstance
  norm_smul_le := norm_smul_le

end CStarTensorAlgebra

namespace CStarTensorProduct

variable {N : CStarTensorNorm A B}

/-- **Units.** The C*-tensor product of unital C*-algebras is a unital C*-algebra, the completion
of the unital normed algebra `A ⊗[ℂ] B` with the norm `N`, with unit `1 ⊗ 1`. -/
instance instCStarAlgebra : CStarAlgebra (CStarTensorProduct N) :=
  letI : CStarAlgebra (Completion (CStarTensorAlgebra N)) :=
    { toCStarRing := Completion.cstarRing fun x ↦ (CStarRing.norm_star_mul_self (x := x)).ge
      norm_smul_le := norm_smul_le }
  inferInstanceAs (CStarAlgebra (Completion (CStarTensorAlgebra N)))

/-- The canonical map `A ⊗[ℂ] B → CStarTensorProduct N` is unital. -/
@[simp]
theorem of_one : of N 1 = 1 := by
  rw [← coe_equiv_eq_of, map_one]
  -- the unit of `CStarTensorProduct N` is the unit of the completion, reached through the
  -- `CStarAlgebra` instance rather than syntactically as `Completion`'s `One`
  exact Completion.coe_one (CStarTensorAlgebra N)

/-- The unit of `CStarTensorProduct N` is `1 ⊗ 1`. -/
@[simp]
theorem of_one_tmul_one : of N ((1 : A) ⊗ₜ (1 : B)) = 1 := by
  rw [← Algebra.TensorProduct.one_def, of_one]

/-- The unit of `CStarTensorProduct N` is `1 ⊗ 1`. -/
theorem one_def : (1 : CStarTensorProduct N) = of N ((1 : A) ⊗ₜ (1 : B)) :=
  of_one_tmul_one.symm

/-- For nonzero unital `A` and `B`, the C*-tensor product is nonzero, since `A ⊗[ℂ] B` is
nonzero and embeds in it. -/
instance instNontrivial [Nontrivial A] [Nontrivial B] : Nontrivial (CStarTensorProduct N) :=
  haveI := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left ℂ A B
    (algebraMap ℂ B).injective
  (of_injective (N := N)).nontrivial

variable (N)

/-- The canonical map `A ⊗[ℂ] B → CStarTensorProduct N` as a unital star homomorphism. -/
def ofStarAlgHom : A ⊗[ℂ] B →⋆ₐ[ℂ] CStarTensorProduct N where
  __ := of N
  map_one' := of_one
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

variable {N} in
@[simp]
theorem ofStarAlgHom_apply (x : A ⊗[ℂ] B) : ofStarAlgHom N x = of N x :=
  (rfl)

/-- The unital star homomorphism `A → CStarTensorProduct N`, `a ↦ a ⊗ 1`. -/
def includeLeft : A →⋆ₐ[ℂ] CStarTensorProduct N where
  __ := (ofStarAlgHom N).toAlgHom.comp Algebra.TensorProduct.includeLeft
  map_star' a := by
    simpa [TensorProduct.star_tmul] using map_star (of N) (a ⊗ₜ (1 : B))

/-- The unital star homomorphism `B → CStarTensorProduct N`, `b ↦ 1 ⊗ b`. -/
def includeRight : B →⋆ₐ[ℂ] CStarTensorProduct N where
  __ := (ofStarAlgHom N).toAlgHom.comp Algebra.TensorProduct.includeRight
  map_star' b := by
    simpa [TensorProduct.star_tmul] using map_star (of N) ((1 : A) ⊗ₜ b)

variable {N}

@[simp]
theorem includeLeft_apply (a : A) : includeLeft N a = of N (a ⊗ₜ 1) :=
  (rfl)

@[simp]
theorem includeRight_apply (b : B) : includeRight N b = of N (1 ⊗ₜ b) :=
  (rfl)

/-- For nonzero `B`, `a ↦ a ⊗ 1` is injective. -/
theorem includeLeft_injective [Nontrivial B] : Function.Injective (includeLeft N) :=
  of_injective.comp (Algebra.TensorProduct.includeLeft_injective (S := ℂ)
    (algebraMap ℂ B).injective)

/-- For nonzero `A`, `b ↦ 1 ⊗ b` is injective. -/
theorem includeRight_injective [Nontrivial A] : Function.Injective (includeRight N) :=
  of_injective.comp (Algebra.TensorProduct.includeRight_injective (algebraMap ℂ A).injective)

/-- For nonzero `B`, `a ↦ a ⊗ 1` is isometric: `‖a ⊗ 1‖ = ‖a‖`. -/
theorem norm_includeLeft [Nontrivial B] (a : A) : ‖includeLeft N a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ includeLeft_injective a

/-- For nonzero `A`, `b ↦ 1 ⊗ b` is isometric: `‖1 ⊗ b‖ = ‖b‖`. -/
theorem norm_includeRight [Nontrivial A] (b : B) : ‖includeRight N b‖ = ‖b‖ :=
  NonUnitalStarAlgHom.norm_map _ includeRight_injective b

variable (N) in
/-- For nonzero `B`, every C*-norm satisfies `N (a ⊗ 1) = ‖a‖`. This is the simp normal form of
`TauCeti.CStarTensorProduct.norm_includeLeft`, as `simp` rewrites `‖includeLeft N a‖` to
`N (a ⊗ₜ 1)`. -/
@[simp]
theorem _root_.TauCeti.CStarTensorNorm.map_tmul_one [Nontrivial B] (a : A) :
    N (a ⊗ₜ (1 : B)) = ‖a‖ := by
  rw [← norm_of, ← includeLeft_apply, norm_includeLeft]

variable (N) in
/-- For nonzero `A`, every C*-norm satisfies `N (1 ⊗ b) = ‖b‖`. This is the simp normal form of
`TauCeti.CStarTensorProduct.norm_includeRight`, as `simp` rewrites `‖includeRight N b‖` to
`N (1 ⊗ₜ b)`. -/
@[simp]
theorem _root_.TauCeti.CStarTensorNorm.map_one_tmul [Nontrivial A] (b : B) :
    N ((1 : A) ⊗ₜ b) = ‖b‖ := by
  rw [← norm_of, ← includeRight_apply, norm_includeRight]

/-- `(a ⊗ 1)(1 ⊗ b) = a ⊗ b`. -/
theorem includeLeft_mul_includeRight (a : A) (b : B) :
    includeLeft N a * includeRight N b = of N (a ⊗ₜ b) := by
  rw [includeLeft_apply, includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- `(1 ⊗ b)(a ⊗ 1) = a ⊗ b`. -/
theorem includeRight_mul_includeLeft (a : A) (b : B) :
    includeRight N b * includeLeft N a = of N (a ⊗ₜ b) := by
  rw [includeLeft_apply, includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- The ranges of `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` commute. -/
theorem commute_includeLeft_includeRight (a : A) (b : B) :
    Commute (includeLeft N a) (includeRight N b) := by
  rw [Commute, SemiconjBy, includeLeft_mul_includeRight, includeRight_mul_includeLeft]

/-- **Uniqueness for unital star homomorphisms.** Two unital star homomorphisms out of
`CStarTensorProduct N` into a C*-algebra agree if they agree on `a ⊗ 1` and on `1 ⊗ b`. -/
@[ext high]
theorem starAlgHom_ext' {C : Type*} [CStarAlgebra C] {φ ψ : CStarTensorProduct N →⋆ₐ[ℂ] C}
    (hA : φ.comp (includeLeft N) = ψ.comp (includeLeft N))
    (hB : φ.comp (includeRight N) = ψ.comp (includeRight N)) : φ = ψ := by
  have h := starAlgHom_ext (φ := φ.toNonUnitalStarAlgHom) (ψ := ψ.toNonUnitalStarAlgHom)
    fun a b ↦ by
      rw [← includeLeft_mul_includeRight]
      simpa using congr($hA a * $hB b)
  exact StarAlgHom.ext fun x ↦ congrArg (· x) h

end CStarTensorProduct

end TauCeti
