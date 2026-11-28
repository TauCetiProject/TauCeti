/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Product
public import TauCeti.Analysis.CStarAlgebra.TensorProduct.Unital

/-!
# The minimal tensor product of unital C*-algebras

Let `A` and `B` be unital C*-algebras. Like every C*-tensor product of unital C*-algebras, the
minimal tensor product `A ⊗min B` (`TauCeti.MinTensorProduct A B`) is a unital C*-algebra with unit
`1 ⊗ 1` (`TauCeti.CStarTensorProduct.instCStarAlgebra`), with the unital star homomorphisms
`a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` (`TauCeti.CStarTensorProduct.includeLeft`,
`TauCeti.CStarTensorProduct.includeRight`), which are isometric for nonzero factors
(`TauCeti.CStarTensorProduct.norm_includeLeft`, `TauCeti.CStarTensorProduct.norm_includeRight`).

Functoriality is unital: unital star homomorphisms `φ : A → A'` and `ψ : B → B'` give the unital
star homomorphism `TauCeti.MinTensorProduct.mapStarAlgHom φ ψ` extending `φ ⊗ ψ`, and the
canonical surjection `A ⊗max B → A ⊗min B` is unital
(`TauCeti.MaxTensorProduct.toMinStarAlgHom`).

## Main declarations

* `TauCeti.MinTensorProduct.mapStarAlgHom`: unital functoriality.
* `TauCeti.MaxTensorProduct.toMinStarAlgHom`: the canonical surjection `A ⊗max B → A ⊗min B` as
  a unital star homomorphism.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.6.
-/

public section

noncomputable section

open TensorProduct

universe u v

namespace TauCeti

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

namespace MinTensorProduct

open CStarTensorProduct

section Map

variable {A' B' A'' B'' : Type*} [CStarAlgebra A'] [CStarAlgebra B'] [CStarAlgebra A'']
  [CStarAlgebra B'']

/-- `φ ⊗ ψ` is unital for unital `φ` and `ψ`. -/
@[simp]
theorem map_toNonUnitalStarAlgHom_one (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') :
    map φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom 1 = 1 := by
  simpa using map_of_tmul φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom 1 1

/-- **Unital functoriality**: unital star homomorphisms `φ : A → A'` and `ψ : B → B'` give the
unital star homomorphism `A ⊗min B → A' ⊗min B'` extending `φ ⊗ ψ`, the unital form of
`TauCeti.MinTensorProduct.map`. -/
def mapStarAlgHom (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') :
    MinTensorProduct A B →⋆ₐ[ℂ] MinTensorProduct A' B' where
  __ := map φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom
  map_one' := map_toNonUnitalStarAlgHom_one φ ψ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (map_smul _ r 1).trans (congrArg (r • ·) (map_toNonUnitalStarAlgHom_one φ ψ))

/-- The unital functoriality map is `TauCeti.MinTensorProduct.map`. -/
@[simp]
theorem mapStarAlgHom_apply (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') (x : MinTensorProduct A B) :
    mapStarAlgHom φ ψ x = map φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom x :=
  (rfl)

/-- `(φ ⊗ ψ)(a ⊗ 1) = φ a ⊗ 1`. -/
@[simp]
theorem mapStarAlgHom_comp_includeLeft (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') :
    (mapStarAlgHom φ ψ).comp (includeLeft (minCStarTensorNorm A B)) =
      (includeLeft (minCStarTensorNorm A' B')).comp φ :=
  StarAlgHom.ext fun a ↦ by simp

/-- `(φ ⊗ ψ)(1 ⊗ b) = 1 ⊗ ψ b`. -/
@[simp]
theorem mapStarAlgHom_comp_includeRight (φ : A →⋆ₐ[ℂ] A') (ψ : B →⋆ₐ[ℂ] B') :
    (mapStarAlgHom φ ψ).comp (includeRight (minCStarTensorNorm A B)) =
      (includeRight (minCStarTensorNorm A' B')).comp ψ :=
  StarAlgHom.ext fun b ↦ by simp

/-- Unital functoriality preserves identities. -/
@[simp]
theorem mapStarAlgHom_id :
    mapStarAlgHom (StarAlgHom.id ℂ A) (StarAlgHom.id ℂ B) =
      StarAlgHom.id ℂ (MinTensorProduct A B) :=
  starAlgHom_ext' (by ext; simp) (by ext; simp)

/-- Unital functoriality preserves composition. -/
theorem mapStarAlgHom_comp (φ' : A' →⋆ₐ[ℂ] A'') (ψ' : B' →⋆ₐ[ℂ] B'') (φ : A →⋆ₐ[ℂ] A')
    (ψ : B →⋆ₐ[ℂ] B') :
    mapStarAlgHom (φ'.comp φ) (ψ'.comp ψ) = (mapStarAlgHom φ' ψ').comp (mapStarAlgHom φ ψ) :=
  starAlgHom_ext' (by ext; simp) (by ext; simp)

end Map

end MinTensorProduct

namespace MaxTensorProduct

open CStarTensorProduct

/-- The canonical surjection `A ⊗max B → A ⊗min B` sends `1` to `1`. -/
@[simp]
theorem toMin_one : toMin (1 : MaxTensorProduct A B) = 1 := by
  rw [one_def, toMin_of, of_one_tmul_one]

variable (A B) in
/-- The canonical surjection `A ⊗max B → A ⊗min B` of unital C*-algebras is unital. -/
def toMinStarAlgHom : MaxTensorProduct A B →⋆ₐ[ℂ] MinTensorProduct A B where
  __ := toMin
  map_one' := toMin_one
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (map_smul _ r 1).trans (congrArg (r • ·) toMin_one)

/-- The unital canonical surjection is `TauCeti.MaxTensorProduct.toMin`. -/
@[simp]
theorem toMinStarAlgHom_apply (x : MaxTensorProduct A B) : toMinStarAlgHom A B x = toMin x :=
  (rfl)

/-- The canonical surjection sends `a ⊗ 1` to `a ⊗ 1`. -/
@[simp]
theorem toMinStarAlgHom_comp_includeLeft :
    (toMinStarAlgHom A B).comp (includeLeft (maxCStarTensorNorm A B)) =
      includeLeft (minCStarTensorNorm A B) :=
  StarAlgHom.ext fun a ↦ by simp

/-- The canonical surjection sends `1 ⊗ b` to `1 ⊗ b`. -/
@[simp]
theorem toMinStarAlgHom_comp_includeRight :
    (toMinStarAlgHom A B).comp (includeRight (maxCStarTensorNorm A B)) =
      includeRight (minCStarTensorNorm A B) :=
  StarAlgHom.ext fun b ↦ by simp

end MaxTensorProduct

end TauCeti
