/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

/-!
# The projection `K₀`-group of a nonunital star algebra

For a nonunital star algebra `A` over a commutative star ring `R`, let `A⁺ = Unitization R A` be
its forced unitization and `ε : A⁺ → R` the augmentation `(r, a) ↦ r`
(`Unitization.fstStarAlgHom`). The `K₀`-group of `A` is the kernel of the homomorphism
`K₀(ε) : K₀(A⁺) → K₀(R)` induced on projection `K₀`-groups
(`TauCeti.UnitizationKZero R A`). For a C⋆-algebra `A` and `R = ℂ` this is the operator
`K₀`-group of `A`; matrix projections over `A` alone need not generate it.

The scalar inclusion `R → A⁺` splits `K₀(ε)`, so `K₀(A⁺) ≃ K₀(A) × K₀(R)`
(`TauCeti.UnitizationKZero.prodEquiv`). A star homomorphism `φ : A → B`, unital or not, induces a
homomorphism `K₀(A) → K₀(B)` through the unitization `Unitization.starMap φ`
(`TauCeti.UnitizationKZero.map`), functorially.

## Main definitions

* `TauCeti.UnitizationKZero R A`: `K₀(A) = ker (K₀(A⁺) → K₀(R))`.
* `TauCeti.UnitizationKZero.map φ`: the homomorphism `K₀(A) →+ K₀(B)` induced by a star
  homomorphism `φ : A →⋆ₙₐ[R] B`.
* `TauCeti.UnitizationKZero.prodEquiv`: the split decomposition `K₀(A⁺) ≃+ K₀(A) × K₀(R)`.

## Main statements

* `TauCeti.UnitizationKZero.map_id` and `TauCeti.UnitizationKZero.map_comp`: functoriality.
* `TauCeti.UnitizationKZero.map_zero`: the zero homomorphism induces zero on `K₀`.
* `TauCeti.UnitizationKZero.augmentation_comp_inl`: the scalar inclusion splits `K₀(ε)`.
* `TauCeti.UnitizationKZero.augmentation_comp_map_starMap`: `K₀(ε)` is natural for unitized star
  homomorphisms.
* `TauCeti.UnitizationKZero.inl_comp_map_starMap`: so is the scalar inclusion `K₀(ι)`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definition 5.5.1 and Proposition 5.4.1.
-/

public section

open Algebra

namespace TauCeti

variable (R A : Type*) [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

namespace UnitizationKZero

/-- The homomorphism `K₀(ε) : K₀(A⁺) →+ K₀(R)` induced by the augmentation
`ε : Unitization R A → R`. -/
noncomputable def augmentation : ProjectionKZero (Unitization R A) →+ ProjectionKZero R :=
  ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.fstStarAlgHom R A))

/-- The homomorphism `K₀(R) →+ K₀(A⁺)` induced by the scalar inclusion `R → Unitization R A`. -/
noncomputable def inl : ProjectionKZero R →+ ProjectionKZero (Unitization R A) :=
  ProjectionKZero.map (NonUnitalStarRingHom.ofClass (StarAlgHom.ofId R (Unitization R A)))

/-- `K₀(ε)` is the homomorphism `ProjectionKZero.map` induces from the augmentation. -/
theorem augmentation_def :
    augmentation R A =
      ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.fstStarAlgHom R A)) :=
  (rfl)

/-- `K₀(ι)` is the homomorphism `ProjectionKZero.map` induces from the scalar inclusion. -/
theorem inl_def :
    inl R A =
      ProjectionKZero.map (NonUnitalStarRingHom.ofClass (StarAlgHom.ofId R (Unitization R A))) :=
  (rfl)

/-- The scalar inclusion splits the augmentation: `K₀(ε) ∘ K₀(ι) = id`. -/
theorem augmentation_comp_inl :
    (augmentation R A).comp (inl R A) = AddMonoidHom.id (ProjectionKZero R) := by
  rw [augmentation, inl, ← ProjectionKZero.map_comp]
  convert ProjectionKZero.map_id (R := R)
  ext r
  simp [Algebra.algebraMap_self]

/-- The scalar inclusion splits the augmentation: `K₀(ε) (K₀(ι) x) = x`. -/
@[simp]
theorem augmentation_inl (x : ProjectionKZero R) : augmentation R A (inl R A x) = x :=
  DFunLike.congr_fun (augmentation_comp_inl R A) x

end UnitizationKZero

/-- The **`K₀`-group of a nonunital star algebra** `A`: the kernel of the homomorphism
`K₀(A⁺) →+ K₀(R)` induced by the augmentation of the forced unitization `A⁺ = Unitization R A`.
For a C⋆-algebra `A` and `R = ℂ` this is the operator `K₀`-group of `A`. -/
noncomputable def UnitizationKZero : AddSubgroup (ProjectionKZero (Unitization R A)) :=
  (UnitizationKZero.augmentation R A).ker

namespace UnitizationKZero

variable {R A}

/-- An element of `K₀(A⁺)` lies in `K₀(A)` exactly when the augmentation kills it. -/
@[simp]
theorem mem_iff (x : ProjectionKZero (Unitization R A)) :
    x ∈ UnitizationKZero R A ↔ augmentation R A x = 0 :=
  Iff.rfl

variable (R A) in
/-- **Split decomposition.** `K₀(A⁺) ≃+ K₀(A) × K₀(R)`: an element `x` is sent to
`(x - K₀(ι) (K₀(ε) x), K₀(ε) x)`, with inverse `(y, z) ↦ y + K₀(ι) z`. -/
noncomputable def prodEquiv :
    ProjectionKZero (Unitization R A) ≃+ UnitizationKZero R A × ProjectionKZero R where
  toFun x := (⟨x - inl R A (augmentation R A x), by
    rw [mem_iff, map_sub, augmentation_inl, sub_self]⟩, augmentation R A x)
  invFun y := y.1 + inl R A y.2
  left_inv x := by simp
  right_inv y := by
    obtain ⟨⟨y, hy⟩, z⟩ := y
    rw [mem_iff] at hy
    ext <;> simp [hy]
  map_add' x y := by
    ext <;> simp only [map_add, Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add]; abel

/-- The second component of the split decomposition is the augmentation. -/
@[simp]
theorem prodEquiv_apply_snd (x : ProjectionKZero (Unitization R A)) :
    (prodEquiv R A x).2 = augmentation R A x :=
  (rfl)

/-- The first component of the split decomposition is `x - K₀(ι) (K₀(ε) x)`. -/
@[simp]
theorem coe_prodEquiv_apply_fst (x : ProjectionKZero (Unitization R A)) :
    ((prodEquiv R A x).1 : ProjectionKZero (Unitization R A)) = x - inl R A (augmentation R A x) :=
  (rfl)

/-- The inverse of the split decomposition is `(y, z) ↦ y + K₀(ι) z`. -/
@[simp]
theorem prodEquiv_symm_apply (y : UnitizationKZero R A × ProjectionKZero R) :
    (prodEquiv R A).symm y = y.1 + inl R A y.2 :=
  (rfl)

/-- The split decomposition sends an element `y` of `K₀(A)` to `(y, 0)`. -/
@[simp]
theorem prodEquiv_apply_coe (y : UnitizationKZero R A) : prodEquiv R A y = (y, 0) := by
  have hy : augmentation R A y = 0 := y.property
  ext <;> simp [hy]

/-- The split decomposition sends the scalar class `K₀(ι) z` to `(0, z)`. -/
@[simp]
theorem prodEquiv_inl (z : ProjectionKZero R) : prodEquiv R A (inl R A z) = (0, z) := by
  ext <;> simp

section map

variable {B C : Type*} [NonUnitalSemiring B] [StarRing B] [Module R B] [IsScalarTower R B B]
  [SMulCommClass R B B] [StarModule R B] [NonUnitalSemiring C] [StarRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] [StarModule R C]

/-- **Naturality of the augmentation.** The homomorphism induced by the unitization of a star
homomorphism commutes with the augmentations. -/
theorem augmentation_comp_map_starMap (φ : A →⋆ₙₐ[R] B) :
    (augmentation R B).comp
        (ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.starMap φ))) =
      augmentation R A := by
  rw [augmentation, augmentation, ← ProjectionKZero.map_comp]
  congr 1
  ext x
  simp

/-- **Naturality of the augmentation**, pointwise. -/
@[simp]
theorem augmentation_map_starMap (φ : A →⋆ₙₐ[R] B) (x : ProjectionKZero (Unitization R A)) :
    augmentation R B
        (ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.starMap φ)) x) =
      augmentation R A x :=
  DFunLike.congr_fun (augmentation_comp_map_starMap φ) x

/-- **Naturality of the scalar inclusion.** The homomorphism induced by the unitization of a star
homomorphism commutes with the scalar inclusions. -/
theorem inl_comp_map_starMap (φ : A →⋆ₙₐ[R] B) :
    (ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.starMap φ))).comp
        (inl R A) =
      inl R B := by
  rw [inl, inl, ← ProjectionKZero.map_comp]
  congr 1
  exact NonUnitalStarRingHom.ext fun r ↦ AlgHomClass.commutes (Unitization.starMap φ) r

/-- **Naturality of the scalar inclusion**, pointwise. -/
@[simp]
theorem map_starMap_inl (φ : A →⋆ₙₐ[R] B) (x : ProjectionKZero R) :
    ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.starMap φ)) (inl R A x) =
      inl R B x :=
  DFunLike.congr_fun (inl_comp_map_starMap φ) x

/-- **Functoriality.** A star homomorphism `φ : A →⋆ₙₐ[R] B`, unital or not, induces a
homomorphism `K₀(A) →+ K₀(B)` through its unitization `Unitization.starMap φ`. -/
noncomputable def map (φ : A →⋆ₙₐ[R] B) : UnitizationKZero R A →+ UnitizationKZero R B :=
  ((ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.starMap φ))).comp
      (UnitizationKZero R A).subtype).codRestrict _ fun x ↦ by
    rw [AddMonoidHom.comp_apply, mem_iff, augmentation_map_starMap]
    exact x.property

/-- On the underlying elements of `K₀(A⁺)`, `TauCeti.UnitizationKZero.map φ` is the homomorphism
induced by `Unitization.starMap φ`. -/
@[simp]
theorem coe_map (φ : A →⋆ₙₐ[R] B) (x : UnitizationKZero R A) :
    (map φ x : ProjectionKZero (Unitization R B)) =
      ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.starMap φ)) x :=
  (rfl)

/-- The identity homomorphism induces the identity of `K₀(A)`. -/
@[simp]
theorem map_id : map (NonUnitalStarAlgHom.id R A) = AddMonoidHom.id (UnitizationKZero R A) := by
  ext x
  have h : NonUnitalStarRingHom.ofClass (StarAlgHom.id R (Unitization R A)) =
      NonUnitalStarRingHom.id _ :=
    NonUnitalStarRingHom.ext fun _ ↦ rfl
  rw [coe_map, AddMonoidHom.id_apply, Unitization.starMap_id, h, ProjectionKZero.map_id,
    AddMonoidHom.id_apply]

/-- The homomorphism induced by a composite is the composite of the induced homomorphisms. -/
theorem map_comp (ψ : B →⋆ₙₐ[R] C) (φ : A →⋆ₙₐ[R] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext x
  have h : NonUnitalStarRingHom.ofClass ((Unitization.starMap ψ).comp (Unitization.starMap φ)) =
      (NonUnitalStarRingHom.ofClass (Unitization.starMap ψ)).comp
        (NonUnitalStarRingHom.ofClass (Unitization.starMap φ)) :=
    NonUnitalStarRingHom.ext fun _ ↦ rfl
  rw [coe_map, AddMonoidHom.comp_apply, coe_map, coe_map, Unitization.starMap_comp, h,
    ProjectionKZero.map_comp, AddMonoidHom.comp_apply]

/-- **Zero maps.** The zero homomorphism `A → B` induces the zero homomorphism on `K₀`: its
unitization is the augmentation `A⁺ → R` followed by the scalar inclusion `R → B⁺`. -/
@[simp]
theorem map_zero : map (0 : A →⋆ₙₐ[R] B) = 0 := by
  have h : NonUnitalStarRingHom.ofClass (Unitization.starMap (0 : A →⋆ₙₐ[R] B)) =
      (NonUnitalStarRingHom.ofClass (StarAlgHom.ofId R (Unitization R B))).comp
        (NonUnitalStarRingHom.ofClass (Unitization.fstStarAlgHom R A)) :=
    NonUnitalStarRingHom.ext fun u ↦ by ext <;> simp
  ext v
  rw [coe_map, h, ProjectionKZero.map_comp, ← augmentation_def, ← inl_def]
  simp [(mem_iff _).1 v.property]

end map

end UnitizationKZero

end TauCeti
