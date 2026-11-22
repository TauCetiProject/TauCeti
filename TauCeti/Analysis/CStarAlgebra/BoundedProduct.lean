/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The bounded product of C⋆-algebras

For a family of nonzero unital C⋆-algebras `A i`, the bounded product `lp A ∞` is a unital
C⋆-algebra, `lp.inftyCStarAlgebra`. Mathlib provides the nonunital instance and the unital
commutative one; nontriviality of the factors makes the unit `(1)ᵢ` have norm one.

With the closed `c₀` ideal `lp.c0Ideal` of `TauCeti.Analysis.Normed.Lp.C0Ideal`, the quotient
`lp A ∞ ⧸ lp.c0Ideal A` is then a unital C⋆-algebra by `TwoSidedIdeal.Quotient.cstarAlgebra`.

For a family of possibly nonunital C⋆-algebras, `lp A ∞` is the product in the category of
C⋆-algebras: the coordinate projections `lp.evalNonUnitalStarAlgHom` are star homomorphisms, and
`lp.liftNonUnitalStarAlgHom` identifies star homomorphisms into `lp A ∞` with families of star
homomorphisms into the factors. A family of star homomorphisms out of a C⋆-algebra is uniformly
bounded because each of them is contractive.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
-/

public section

open scoped ENNReal

namespace lp

section Product

section Eval

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalNormedRing (A i)] [∀ i, StarRing (A i)]
  [∀ i, NormedStarGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, IsBoundedSMul ℂ (A i)]

variable (A) in
/-- The coordinate projection of the bounded product `lp A ∞` onto its factor `A i`, as a star
homomorphism. -/
def evalNonUnitalStarAlgHom (i : ι) : lp A ∞ →⋆ₙₐ[ℂ] A i where
  toFun a := a i
  map_smul' c a := by simp [lp.coeFn_smul]
  map_zero' := by simp
  map_add' a b := by simp
  map_mul' a b := by simp [infty_coeFn_mul]
  map_star' a := lp.star_apply a i

/-- The coordinate projection evaluates a bounded family at an index. -/
@[simp]
theorem evalNonUnitalStarAlgHom_apply (i : ι) (a : lp A ∞) :
    evalNonUnitalStarAlgHom A i a = a i :=
  (rfl)

/-- Two star homomorphisms into a bounded product agree when all their coordinates agree. -/
@[ext]
theorem nonUnitalStarAlgHom_ext {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction ℂ B]
    [Star B] {φ ψ : B →⋆ₙₐ[ℂ] lp A ∞}
    (h : ∀ i, (evalNonUnitalStarAlgHom A i).comp φ = (evalNonUnitalStarAlgHom A i).comp ψ) :
    φ = ψ :=
  NonUnitalStarAlgHom.ext fun b ↦ lp.ext <| funext fun i ↦ by
    simpa using congr($(h i) b)

end Eval

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]
variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- **The universal property of the bounded product**: star homomorphisms from a C⋆-algebra `B`
into `lp A ∞` are the families of star homomorphisms `B → A i`. The family `φ` is sent to
`b ↦ (φ i b)ᵢ`, which is bounded by `‖b‖` since star homomorphisms between C⋆-algebras are
contractive. -/
noncomputable def liftNonUnitalStarAlgHom : (∀ i, B →⋆ₙₐ[ℂ] A i) ≃ (B →⋆ₙₐ[ℂ] lp A ∞) where
  toFun φ :=
    { toFun b := ⟨fun i ↦ φ i b, memℓp_infty ⟨‖b‖, by
        rintro _ ⟨i, rfl⟩
        exact NonUnitalStarAlgHom.norm_apply_le (φ i) b⟩⟩
      map_smul' c b := lp.ext <| funext fun i ↦ map_smul (φ i) c b
      map_zero' := lp.ext <| funext fun i ↦ map_zero (φ i)
      map_add' b b' := lp.ext <| funext fun i ↦ map_add (φ i) b b'
      map_mul' b b' := lp.ext <| funext fun i ↦ map_mul (φ i) b b'
      map_star' b := lp.ext <| funext fun i ↦ map_star (φ i) b }
  invFun ψ i := (evalNonUnitalStarAlgHom A i).comp ψ
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

/-- The `i`-th coordinate of `lp.liftNonUnitalStarAlgHom φ b` is `φ i b`. -/
@[simp]
theorem liftNonUnitalStarAlgHom_apply_apply (φ : ∀ i, B →⋆ₙₐ[ℂ] A i) (b : B) (i : ι) :
    liftNonUnitalStarAlgHom φ b i = φ i b :=
  (rfl)

/-- The coordinates of `lp.liftNonUnitalStarAlgHom φ` are the members of the family `φ`. -/
@[simp]
theorem evalNonUnitalStarAlgHom_comp_liftNonUnitalStarAlgHom (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (i : ι) : (evalNonUnitalStarAlgHom A i).comp (liftNonUnitalStarAlgHom φ) = φ i := by
  ext b
  simp

/-- The inverse of `lp.liftNonUnitalStarAlgHom` takes the coordinates of a star homomorphism. -/
@[simp]
theorem liftNonUnitalStarAlgHom_symm_apply (ψ : B →⋆ₙₐ[ℂ] lp A ∞) (i : ι) :
    liftNonUnitalStarAlgHom.symm ψ i = (evalNonUnitalStarAlgHom A i).comp ψ :=
  (rfl)

end Product

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- The bounded product `lp A ∞` of nonzero unital C⋆-algebras is a unital C⋆-algebra. -/
noncomputable instance inftyCStarAlgebra : CStarAlgebra (lp A ∞) where

end lp
