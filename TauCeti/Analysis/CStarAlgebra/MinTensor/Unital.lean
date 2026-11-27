/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Product
public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Unital

/-!
# The minimal tensor product of unital C*-algebras

Let `A` and `B` be unital C*-algebras. The minimal tensor product `A ⊗min B`
(`TauCeti.MinTensorProduct A B`) is then a unital C*-algebra with unit `1 ⊗ 1`
(`TauCeti.MinTensorProduct.one_def`): the algebraic tensor product with the minimal norm,
`TauCeti.CStarTensorAlgebra (TauCeti.minCStarTensorNorm A B)`, is then a unital normed algebra, and
its completion carries Mathlib's unital ring, algebra and normed structures, which extend the ones
of the nonunital C*-algebra `A ⊗min B`. The canonical map
`TauCeti.CStarTensorProduct.of (TauCeti.minCStarTensorNorm A B)` is unital
(`TauCeti.MinTensorProduct.ofStarAlgHom`).

The unital star homomorphisms `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`
(`TauCeti.MinTensorProduct.includeLeft`, `TauCeti.MinTensorProduct.includeRight`) have commuting
ranges, and their products `(a ⊗ 1)(1 ⊗ b) = a ⊗ b` span a dense subalgebra, so unital star
homomorphisms out of `A ⊗min B` are determined by their composites with `includeLeft` and
`includeRight` (`TauCeti.MinTensorProduct.starAlgHom_ext'`). For nonzero `B`, `a ↦ a ⊗ 1` is
isometric (`TauCeti.MinTensorProduct.norm_includeLeft`), and similarly on the right.

Functoriality is unital: unital star homomorphisms `φ : A → A'` and `ψ : B → B'` give the unital
star homomorphism `TauCeti.MinTensorProduct.mapStarAlgHom φ ψ` extending `φ ⊗ ψ`, and the
canonical surjection `A ⊗max B → A ⊗min B` is unital
(`TauCeti.MaxTensorProduct.toMinStarAlgHom`).

## Main declarations

* `TauCeti.MinTensorProduct.instCStarAlgebra`: `A ⊗min B` is a unital C*-algebra, nonzero when
  `A` and `B` are (`TauCeti.MinTensorProduct.instNontrivial`).
* `TauCeti.MinTensorProduct.ofStarAlgHom`: the unital star homomorphism `A ⊗[ℂ] B → A ⊗min B`.
* `TauCeti.MinTensorProduct.includeLeft`, `TauCeti.MinTensorProduct.includeRight`: the unital
  star homomorphisms `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`.
* `TauCeti.MinTensorProduct.mapStarAlgHom`: unital functoriality.
* `TauCeti.MaxTensorProduct.toMinStarAlgHom`: the canonical surjection `A ⊗max B → A ⊗min B` as
  a unital star homomorphism.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.6.
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

namespace CStarTensorAlgebra

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with the minimal norm is the unital ring `A ⊗[ℂ] B`. -/
instance instRingMin : Ring (CStarTensorAlgebra (minCStarTensorNorm A B)) :=
  inferInstanceAs (Ring (A ⊗[ℂ] B))

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with the minimal norm is the complex algebra `A ⊗[ℂ] B`. -/
instance instAlgebraMin : Algebra ℂ (CStarTensorAlgebra (minCStarTensorNorm A B)) :=
  inferInstanceAs (Algebra ℂ (A ⊗[ℂ] B))

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with the minimal norm is a unital normed ring. -/
instance instNormedRingMin : NormedRing (CStarTensorAlgebra (minCStarTensorNorm A B)) where
  __ : NonUnitalNormedRing (CStarTensorAlgebra (minCStarTensorNorm A B)) := inferInstance
  __ : Ring (CStarTensorAlgebra (minCStarTensorNorm A B)) := inferInstance

/-- For unital `A` and `B`, `A ⊗[ℂ] B` with the minimal norm is a normed algebra. -/
instance instNormedAlgebraMin : NormedAlgebra ℂ (CStarTensorAlgebra (minCStarTensorNorm A B)) where
  __ : Algebra ℂ (CStarTensorAlgebra (minCStarTensorNorm A B)) := inferInstance
  norm_smul_le := norm_smul_le

end CStarTensorAlgebra

namespace MinTensorProduct

open CStarTensorProduct

/-- **Units.** The minimal tensor product of unital C*-algebras is a unital C*-algebra, the
completion of the unital normed algebra `A ⊗[ℂ] B` with the minimal norm, with unit `1 ⊗ 1`. -/
instance instCStarAlgebra : CStarAlgebra (MinTensorProduct A B) :=
  letI : CStarAlgebra (Completion (CStarTensorAlgebra (minCStarTensorNorm A B))) :=
    { toCStarRing := Completion.cstarRing fun x ↦ (CStarRing.norm_star_mul_self (x := x)).ge
      norm_smul_le := norm_smul_le }
  inferInstanceAs (CStarAlgebra (Completion (CStarTensorAlgebra (minCStarTensorNorm A B))))

/-- The canonical map `A ⊗[ℂ] B → A ⊗min B` is unital. -/
@[simp]
theorem of_one : of (minCStarTensorNorm A B) 1 = 1 := by
  rw [← coe_equiv_eq_of, map_one]
  -- the unit of `MinTensorProduct A B` is the unit of the completion, reached through the
  -- `CStarAlgebra` instance rather than syntactically as `Completion`'s `One`
  exact Completion.coe_one (CStarTensorAlgebra (minCStarTensorNorm A B))

/-- The unit of `A ⊗min B` is `1 ⊗ 1`. -/
@[simp]
theorem of_one_tmul_one : of (minCStarTensorNorm A B) ((1 : A) ⊗ₜ (1 : B)) = 1 := by
  rw [← Algebra.TensorProduct.one_def, of_one]

/-- The unit of `A ⊗min B` is `1 ⊗ 1`. -/
theorem one_def :
    (1 : MinTensorProduct A B) = of (minCStarTensorNorm A B) ((1 : A) ⊗ₜ (1 : B)) :=
  of_one_tmul_one.symm

/-- For nonzero unital `A` and `B`, the minimal tensor product is nonzero:
`‖1 ⊗ 1‖ = ‖1‖ ‖1‖ = 1`. -/
instance instNontrivial [Nontrivial A] [Nontrivial B] : Nontrivial (MinTensorProduct A B) :=
  ⟨⟨1, 0, fun h ↦ by
    simpa [norm_of_tmul, -of_one_tmul_one] using congrArg norm (of_one_tmul_one.trans h)⟩⟩

variable (A B)

/-- The canonical map `A ⊗[ℂ] B → A ⊗min B` as a unital star homomorphism. -/
def ofStarAlgHom : A ⊗[ℂ] B →⋆ₐ[ℂ] MinTensorProduct A B where
  __ := of (minCStarTensorNorm A B)
  map_one' := of_one
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

variable {A B} in
@[simp]
theorem ofStarAlgHom_apply (x : A ⊗[ℂ] B) :
    ofStarAlgHom A B x = of (minCStarTensorNorm A B) x :=
  (rfl)

/-- The unital star homomorphism `A → A ⊗min B`, `a ↦ a ⊗ 1`. -/
def includeLeft : A →⋆ₐ[ℂ] MinTensorProduct A B where
  __ := (ofStarAlgHom A B).toAlgHom.comp Algebra.TensorProduct.includeLeft
  map_star' a := by
    simpa [TensorProduct.star_tmul] using map_star (of (minCStarTensorNorm A B)) (a ⊗ₜ (1 : B))

/-- The unital star homomorphism `B → A ⊗min B`, `b ↦ 1 ⊗ b`. -/
def includeRight : B →⋆ₐ[ℂ] MinTensorProduct A B where
  __ := (ofStarAlgHom A B).toAlgHom.comp Algebra.TensorProduct.includeRight
  map_star' b := by
    simpa [TensorProduct.star_tmul] using map_star (of (minCStarTensorNorm A B)) ((1 : A) ⊗ₜ b)

variable {A B}

@[simp]
theorem includeLeft_apply (a : A) : includeLeft A B a = of (minCStarTensorNorm A B) (a ⊗ₜ 1) :=
  (rfl)

@[simp]
theorem includeRight_apply (b : B) :
    includeRight A B b = of (minCStarTensorNorm A B) (1 ⊗ₜ b) :=
  (rfl)

/-- `(a ⊗ 1)(1 ⊗ b) = a ⊗ b`. -/
theorem includeLeft_mul_includeRight (a : A) (b : B) :
    includeLeft A B a * includeRight A B b = of (minCStarTensorNorm A B) (a ⊗ₜ b) := by
  rw [includeLeft_apply, includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- `(1 ⊗ b)(a ⊗ 1) = a ⊗ b`. -/
theorem includeRight_mul_includeLeft (a : A) (b : B) :
    includeRight A B b * includeLeft A B a = of (minCStarTensorNorm A B) (a ⊗ₜ b) := by
  rw [includeLeft_apply, includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- The ranges of `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` commute. -/
theorem commute_includeLeft_includeRight (a : A) (b : B) :
    Commute (includeLeft A B a) (includeRight A B b) := by
  rw [Commute, SemiconjBy, includeLeft_mul_includeRight, includeRight_mul_includeLeft]

/-- **Uniqueness for unital star homomorphisms.** Two unital star homomorphisms out of `A ⊗min B`
into a C*-algebra agree if they agree on `a ⊗ 1` and on `1 ⊗ b`. -/
@[ext high]
theorem starAlgHom_ext' {C : Type*} [CStarAlgebra C] {φ ψ : MinTensorProduct A B →⋆ₐ[ℂ] C}
    (hA : φ.comp (includeLeft A B) = ψ.comp (includeLeft A B))
    (hB : φ.comp (includeRight A B) = ψ.comp (includeRight A B)) : φ = ψ := by
  have h := starAlgHom_ext (φ := φ.toNonUnitalStarAlgHom) (ψ := ψ.toNonUnitalStarAlgHom)
    fun a b ↦ by
      rw [← includeLeft_mul_includeRight]
      simpa using congr($hA a * $hB b)
  exact StarAlgHom.ext fun x ↦ congrArg (· x) h

/-- For nonzero `B`, `a ↦ a ⊗ 1` is isometric: `‖a ⊗ 1‖ = ‖a‖`. -/
theorem norm_includeLeft [Nontrivial B] (a : A) : ‖includeLeft A B a‖ = ‖a‖ := by
  rw [includeLeft_apply, norm_of_tmul, norm_one, mul_one]

/-- For nonzero `A`, `b ↦ 1 ⊗ b` is isometric: `‖1 ⊗ b‖ = ‖b‖`. -/
theorem norm_includeRight [Nontrivial A] (b : B) : ‖includeRight A B b‖ = ‖b‖ := by
  rw [includeRight_apply, norm_of_tmul, norm_one, one_mul]

/-- For nonzero `B`, `a ↦ a ⊗ 1` is injective. -/
theorem includeLeft_injective [Nontrivial B] : Function.Injective (includeLeft A B) :=
  (AddMonoidHomClass.isometry_of_norm _ norm_includeLeft).injective

/-- For nonzero `A`, `b ↦ 1 ⊗ b` is injective. -/
theorem includeRight_injective [Nontrivial A] : Function.Injective (includeRight A B) :=
  (AddMonoidHomClass.isometry_of_norm _ norm_includeRight).injective

section Map

variable {A' : Type*} {B' : Type*} [CStarAlgebra A'] [CStarAlgebra B']

/-- `φ ⊗ ψ` is unital for unital `φ` and `ψ`. -/
theorem map_one (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') :
    map φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom 1 = 1 := by
  rw [one_def, map_of_tmul, StarAlgHom.coe_toNonUnitalStarAlgHom,
    StarAlgHom.coe_toNonUnitalStarAlgHom, _root_.map_one, _root_.map_one, of_one_tmul_one]

/-- **Unital functoriality**: unital star homomorphisms `φ : A → A'` and `ψ : B → B'` give the
unital star homomorphism `A ⊗min B → A' ⊗min B'` extending `φ ⊗ ψ`, the unital form of
`TauCeti.MinTensorProduct.map`. -/
def mapStarAlgHom (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') :
    MinTensorProduct A B →⋆ₐ[ℂ] MinTensorProduct A' B' where
  __ := map φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom
  map_one' := map_one φ ψ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (map_smul _ r 1).trans (congrArg (r • ·) (map_one φ ψ))

/-- The unital functoriality map is `TauCeti.MinTensorProduct.map`. -/
@[simp]
theorem mapStarAlgHom_apply (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') (x : MinTensorProduct A B) :
    mapStarAlgHom φ ψ x = map φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom x :=
  (rfl)

/-- `(φ ⊗ ψ)(a ⊗ 1) = φ a ⊗ 1`. -/
@[simp]
theorem mapStarAlgHom_comp_includeLeft (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') :
    (mapStarAlgHom φ ψ).comp (includeLeft A B) = (includeLeft A' B').comp φ :=
  StarAlgHom.ext fun a ↦ by simp

/-- `(φ ⊗ ψ)(1 ⊗ b) = 1 ⊗ ψ b`. -/
@[simp]
theorem mapStarAlgHom_comp_includeRight (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') :
    (mapStarAlgHom φ ψ).comp (includeRight A B) = (includeRight A' B').comp ψ :=
  StarAlgHom.ext fun b ↦ by simp

end Map

end MinTensorProduct

namespace MaxTensorProduct

open CStarTensorProduct

variable (A B) in
/-- The canonical surjection `A ⊗max B → A ⊗min B` of unital C*-algebras is unital. -/
def toMinStarAlgHom : MaxTensorProduct A B →⋆ₐ[ℂ] MinTensorProduct A B where
  __ := toMin
  map_one' := by
    change toMin 1 = 1
    rw [one_def, toMin_of, MinTensorProduct.of_one_tmul_one]
  commutes' r := by
    change toMin (algebraMap ℂ _ r) = algebraMap ℂ _ r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, one_def,
      toMin_of, MinTensorProduct.of_one_tmul_one]

/-- The unital canonical surjection is `TauCeti.MaxTensorProduct.toMin`. -/
@[simp]
theorem toMinStarAlgHom_apply (x : MaxTensorProduct A B) : toMinStarAlgHom A B x = toMin x :=
  (rfl)

/-- The canonical surjection sends `a ⊗ 1` to `a ⊗ 1`. -/
@[simp]
theorem toMinStarAlgHom_comp_includeLeft :
    (toMinStarAlgHom A B).comp (includeLeft A B) = MinTensorProduct.includeLeft A B :=
  StarAlgHom.ext fun a ↦ by simp

/-- The canonical surjection sends `1 ⊗ b` to `1 ⊗ b`. -/
@[simp]
theorem toMinStarAlgHom_comp_includeRight :
    (toMinStarAlgHom A B).comp (includeRight A B) = MinTensorProduct.includeRight A B :=
  StarAlgHom.ext fun b ↦ by simp

end MaxTensorProduct

end TauCeti
