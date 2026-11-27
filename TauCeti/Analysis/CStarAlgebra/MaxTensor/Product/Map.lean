/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Map
public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Product

/-!
# Functoriality and the flip of the maximal C*-tensor product

Let `A`, `A'` and `B`, `B'` be C*-algebras. Star homomorphisms `φ : A → A'` and `ψ : B → B'`
give the star homomorphism `φ ⊗ ψ : A ⊗[ℂ] B → A' ⊗[ℂ] B'`, which is contractive for the maximal
norms (`TauCeti.maxTensorNorm_mapNonUnitalStarAlgHom_le`). It therefore extends to the maximal
tensor products, `TauCeti.MaxTensorProduct.map φ ψ : A ⊗max B → A' ⊗max B'`, sending `a ⊗ b` to
`φ a ⊗ ψ b` (`TauCeti.MaxTensorProduct.map_of_tmul`). The construction is functorial
(`TauCeti.MaxTensorProduct.map_id`, `TauCeti.MaxTensorProduct.map_comp`), turns star isomorphisms
into star isomorphisms (`TauCeti.MaxTensorProduct.congr`), and is compatible with the universal
property (`TauCeti.MaxTensorProduct.lift_comp_map`).

Since the maximal norm is invariant under the flip (`TauCeti.maxTensorNorm_comm`), the flip
`a ⊗ b ↦ b ⊗ a` extends to a star isomorphism `A ⊗max B ≃ B ⊗max A`
(`TauCeti.MaxTensorProduct.comm`), natural with respect to `TauCeti.MaxTensorProduct.map`
(`TauCeti.MaxTensorProduct.commHom_comp_map`).

The Hilbert spaces of the commuting pairs defining the maximal norm range over the universe
`max u v` for `A : Type u` and `B : Type v`, so the functoriality is stated for `A, A' : Type u`
and `B, B' : Type v`.

## Main declarations

* `TauCeti.MaxTensorProduct.map`: the star homomorphism `A ⊗max B → A' ⊗max B'` induced by
  `φ : A → A'` and `ψ : B → B'`.
* `TauCeti.MaxTensorProduct.congr`: the star isomorphism induced by star isomorphisms.
* `TauCeti.MaxTensorProduct.comm`: the flip `A ⊗max B ≃ B ⊗max A`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.5–II.9.2.6 (functoriality of C*-tensor products).
-/

public section

noncomputable section

open TensorProduct

universe u v

namespace TauCeti

namespace MaxTensorProduct

open CStarTensorProduct

section Map

variable {A A' A'' : Type u} {B B' B'' : Type v} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra B'] [NonUnitalCStarAlgebra B'']

/-- **Functoriality of the maximal tensor product.** Star homomorphisms `φ : A → A'` and
`ψ : B → B'` induce the star homomorphism `A ⊗max B → A' ⊗max B'` sending `a ⊗ b` to
`φ a ⊗ ψ b` (`TauCeti.MaxTensorProduct.map_of_tmul`): the extension of `φ ⊗ ψ`, which is
contractive for the maximal norms. -/
def map (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    MaxTensorProduct A B →⋆ₙₐ[ℂ] MaxTensorProduct A' B' :=
  extend ((of (maxCStarTensorNorm A' B')).comp
    (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ)) fun x ↦ by
    simpa using maxTensorNorm_mapNonUnitalStarAlgHom_le φ ψ x

variable (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B')

/-- On `A ⊗[ℂ] B`, the induced map is `φ ⊗ ψ`. -/
@[simp]
theorem map_of (x : A ⊗[ℂ] B) :
    map φ ψ (of (maxCStarTensorNorm A B) x) =
      of (maxCStarTensorNorm A' B') (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ x) :=
  extend_of _ _ x

/-- The induced map sends `a ⊗ b` to `φ a ⊗ ψ b`. -/
theorem map_of_tmul (a : A) (b : B) :
    map φ ψ (of (maxCStarTensorNorm A B) (a ⊗ₜ b)) =
      of (maxCStarTensorNorm A' B') (φ a ⊗ₜ ψ b) := by
  rw [map_of, Algebra.TensorProduct.mapNonUnitalStarAlgHom_tmul]

/-- Composing the induced map with the canonical map of `A ⊗[ℂ] B` gives `φ ⊗ ψ` followed by the
canonical map of `A' ⊗[ℂ] B'`. -/
@[simp]
theorem map_comp_of :
    (map φ ψ).comp (of (maxCStarTensorNorm A B)) =
      (of (maxCStarTensorNorm A' B')).comp (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ) :=
  NonUnitalStarAlgHom.ext (map_of φ ψ)

/-- The tensor product of the identities induces the identity. -/
@[simp]
theorem map_id :
    map (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ B) =
      NonUnitalStarAlgHom.id ℂ (MaxTensorProduct A B) :=
  starAlgHom_ext fun a b ↦ by simp

/-- The map induced by composites is the composite of the induced maps. -/
theorem map_comp (φ' : A' →⋆ₙₐ[ℂ] A'') (ψ' : B' →⋆ₙₐ[ℂ] B'') :
    map (φ'.comp φ) (ψ'.comp ψ) = (map φ' ψ').comp (map φ ψ) :=
  starAlgHom_ext fun a b ↦ by simp

/-- The induced map applied twice is the map induced by the composites. -/
theorem map_map (φ' : A' →⋆ₙₐ[ℂ] A'') (ψ' : B' →⋆ₙₐ[ℂ] B'') (x : MaxTensorProduct A B) :
    map φ' ψ' (map φ ψ x) = map (φ'.comp φ) (ψ'.comp ψ) x := by
  rw [map_comp, NonUnitalStarAlgHom.comp_apply]

/-- **Compatibility with the universal property.** If `φ' : A' → C` and `ψ' : B' → C` commute,
then so do `φ' ∘ φ` and `ψ' ∘ ψ`, and the extension of the latter pair is the extension of the
former composed with `map φ ψ`. -/
theorem lift_comp_map {C : Type (max u v)} [NonUnitalCStarAlgebra C] (φ' : A' →⋆ₙₐ[ℂ] C)
    (ψ' : B' →⋆ₙₐ[ℂ] C) (h : ∀ a b, Commute (φ' a) (ψ' b)) :
    (lift φ' ψ' h).comp (map φ ψ) =
      lift (φ'.comp φ) (ψ'.comp ψ) (fun a b ↦ h (φ a) (ψ b) :
        ∀ a b, Commute ((φ'.comp φ) a) ((ψ'.comp ψ) b)) :=
  starAlgHom_ext fun a b ↦ by
    rw [NonUnitalStarAlgHom.comp_apply, map_of_tmul, lift_of_tmul]
    exact (lift_of_tmul (φ'.comp φ) (ψ'.comp ψ) _ a b).symm

/-- Star isomorphisms `e : A ≃ A'` and `f : B ≃ B'` induce a star isomorphism
`A ⊗max B ≃ A' ⊗max B'`, sending `a ⊗ b` to `e a ⊗ f b`. -/
def congr (e : A ≃⋆ₐ[ℂ] A') (f : B ≃⋆ₐ[ℂ] B') :
    MaxTensorProduct A B ≃⋆ₐ[ℂ] MaxTensorProduct A' B' :=
  .ofNonUnitalStarAlgHom (map e.toNonUnitalStarAlgHom f.toNonUnitalStarAlgHom)
    (map e.symm.toNonUnitalStarAlgHom f.symm.toNonUnitalStarAlgHom)
    (starAlgHom_ext fun a b ↦ by simp) (starAlgHom_ext fun a b ↦ by simp)

/-- The induced isomorphism is the map induced by the underlying star homomorphisms. -/
@[simp]
theorem congr_apply (e : A ≃⋆ₐ[ℂ] A') (f : B ≃⋆ₐ[ℂ] B') (x : MaxTensorProduct A B) :
    congr e f x = map e.toNonUnitalStarAlgHom f.toNonUnitalStarAlgHom x :=
  (rfl)

/-- The identities induce the identity. -/
@[simp]
theorem congr_refl :
    congr (.refl ℂ A) (.refl ℂ B) = StarAlgEquiv.refl ℂ (MaxTensorProduct A B) :=
  StarAlgEquiv.ext fun x ↦ by simp [congr_apply]

/-- The inverse of the induced isomorphism is induced by the inverses. -/
@[simp]
theorem congr_symm (e : A ≃⋆ₐ[ℂ] A') (f : B ≃⋆ₐ[ℂ] B') :
    (congr e f).symm = congr e.symm f.symm :=
  StarAlgEquiv.symm_ofNonUnitalStarAlgHom _ _ _ _

/-- The isomorphism induced by composites is the composite of the induced isomorphisms. -/
theorem congr_trans (e : A ≃⋆ₐ[ℂ] A') (f : B ≃⋆ₐ[ℂ] B') (e' : A' ≃⋆ₐ[ℂ] A'')
    (f' : B' ≃⋆ₐ[ℂ] B'') : (congr e f).trans (congr e' f') = congr (e.trans e') (f.trans f') :=
  StarAlgEquiv.ext fun x ↦ by simp [congr_apply, map_map]

end Map

section Comm

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The flip `A ⊗max B → B ⊗max A`, `a ⊗ b ↦ b ⊗ a`, as a star homomorphism: the extension of
the flip of `A ⊗[ℂ] B`, which is isometric for the maximal norms. -/
def commHom : MaxTensorProduct A B →⋆ₙₐ[ℂ] MaxTensorProduct B A :=
  extend ((of (maxCStarTensorNorm B A)).comp
    (Algebra.TensorProduct.commNonUnitalStarAlgHom ℂ A B)) fun x ↦ by
    simp [Algebra.TensorProduct.coe_commNonUnitalStarAlgHom]

variable {A B}

/-- On `A ⊗[ℂ] B`, the flip of the maximal tensor product is the algebraic flip. -/
@[simp]
theorem commHom_of (x : A ⊗[ℂ] B) :
    commHom A B (of (maxCStarTensorNorm A B) x) =
      of (maxCStarTensorNorm B A) (TensorProduct.comm ℂ A B x) :=
  (extend_of _ _ x).trans (by simp [Algebra.TensorProduct.coe_commNonUnitalStarAlgHom])

/-- Flipping twice is the identity, as a composite of star homomorphisms. -/
@[simp]
theorem commHom_comp_commHom : (commHom B A).comp (commHom A B) = NonUnitalStarAlgHom.id ℂ _ :=
  starAlgHom_ext fun a b ↦ by simp

/-- Flipping twice is the identity. -/
@[simp]
theorem commHom_commHom (x : MaxTensorProduct A B) : commHom B A (commHom A B x) = x :=
  DFunLike.congr_fun commHom_comp_commHom x

variable (A B)

/-- **The flip of the maximal tensor product**: the star isomorphism `A ⊗max B ≃ B ⊗max A`
sending `a ⊗ b` to `b ⊗ a` (`TauCeti.MaxTensorProduct.comm_of_tmul`). -/
def comm : MaxTensorProduct A B ≃⋆ₐ[ℂ] MaxTensorProduct B A :=
  .ofNonUnitalStarAlgHom (commHom A B) (commHom B A) commHom_comp_commHom commHom_comp_commHom

variable {A B}

/-- The flip is the star homomorphism `TauCeti.MaxTensorProduct.commHom`. -/
@[simp]
theorem comm_apply (x : MaxTensorProduct A B) : comm A B x = commHom A B x :=
  (rfl)

/-- The inverse of the flip is the flip. -/
@[simp]
theorem comm_symm : (comm A B).symm = comm B A :=
  StarAlgEquiv.symm_ofNonUnitalStarAlgHom _ _ _ _

/-- The flip sends `a ⊗ b` to `b ⊗ a`. -/
theorem comm_of_tmul (a : A) (b : B) :
    comm A B (of (maxCStarTensorNorm A B) (a ⊗ₜ b)) = of (maxCStarTensorNorm B A) (b ⊗ₜ a) := by
  simp [comm_apply]

end Comm

section CommMap

variable {A A' : Type u} {B B' : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra B'] (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B')

/-- **Naturality of the flip.** Flipping after `map φ ψ` is `map ψ φ` after flipping. -/
theorem commHom_comp_map : (commHom A' B').comp (map φ ψ) = (map ψ φ).comp (commHom A B) :=
  starAlgHom_ext fun a b ↦ by simp

/-- **Naturality of the flip**, pointwise. -/
theorem commHom_map (x : MaxTensorProduct A B) :
    commHom A' B' (map φ ψ x) = map ψ φ (commHom A B x) :=
  DFunLike.congr_fun (commHom_comp_map φ ψ) x

end CommMap

end MaxTensorProduct

end TauCeti
