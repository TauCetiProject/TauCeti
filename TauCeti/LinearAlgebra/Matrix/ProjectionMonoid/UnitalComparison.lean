/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Prod
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization.Basic

/-!
# `K₀` through the unitization agrees with `K₀` of a unital algebra

Let `A` be a unital star algebra over a commutative star ring `R`. Following
`TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization`, `K₀(A)` denotes the `K₀`-group of `A`
defined through the forced unitization `A⁺`, the kernel `TauCeti.UnitizationKZero R A` of
`K₀(ε) : K₀(A⁺) → K₀(R)`, where `K₀(A⁺)` and `K₀(R)` are projection `K₀`-groups. Write `K₀ᵖ(A)`
for the projection `K₀`-group `TauCeti.ProjectionKZero A` of `A` itself; this file shows that the
two agree.

The forced unitization splits as `A⁺ ≃⋆ₐ[R] A × R`, `(r, a) ↦ (r • 1 + a, r)`
(`Unitization.prodStarAlgEquiv`), and the augmentation `ε : A⁺ → R` becomes the second projection.
Combined with `K₀` of a product (`TauCeti.ProjectionKZero.prodEquiv`) this gives
`K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)` (`TauCeti.UnitizationKZero.unitalProdEquiv`), under which `K₀(ε)` is the
second projection (`TauCeti.UnitizationKZero.unitalProdEquiv_apply_snd`). So its kernel `K₀(A)` is
`K₀ᵖ(A)` (`TauCeti.UnitizationKZero.unitalEquiv`). This differs from the split decomposition
`TauCeti.UnitizationKZero.prodEquiv : K₀(A⁺) ≃+ K₀(A) × K₀(R)`, which exists for every `A` and
whose first factor is the kernel `K₀(A)` itself rather than `K₀ᵖ(A)`.

## Main definitions

* `TauCeti.UnitizationKZero.unitalProdEquiv`: `K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)` for unital `A`.
* `TauCeti.UnitizationKZero.unitalEquiv`: `K₀(A) ≃+ K₀ᵖ(A)` for unital `A`, induced by
  `A⁺ → A`, `(r, a) ↦ r • 1 + a` (`TauCeti.UnitizationKZero.unitalEquiv_apply_eq_map`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definition 5.5.1 and Proposition 5.4.1.
-/

public section

namespace TauCeti

namespace UnitizationKZero

open ProjectionMonoid

variable (R A : Type*) [CommSemiring R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  [StarModule R A]

/-- For a unital star algebra `A`, `K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)`, where `K₀ᵖ(A)` is the projection
`K₀`-group `TauCeti.ProjectionKZero A`, induced by the splitting `A⁺ ≃⋆ₐ[R] A × R` and `K₀` of a
product. Unlike `TauCeti.UnitizationKZero.prodEquiv`, the first factor is the projection
`K₀`-group of `A`, not the kernel of `K₀(ε)`. -/
noncomputable def unitalProdEquiv :
    ProjectionKZero (Unitization R A) ≃+ ProjectionKZero A × ProjectionKZero R :=
  (ProjectionKZero.mapEquiv (Unitization.prodStarAlgEquiv R A).toStarRingEquiv).trans
    (ProjectionKZero.prodEquiv A R)

/-- `K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)` is `K₀` of the splitting followed by `K₀` of the product. -/
theorem unitalProdEquiv_apply (x : ProjectionKZero (Unitization R A)) :
    unitalProdEquiv R A x = ProjectionKZero.prodEquiv A R
      (ProjectionKZero.map (Unitization.prodStarAlgEquiv R A).toStarRingEquiv x) := by
  rw [unitalProdEquiv, AddEquiv.trans_apply, ProjectionKZero.mapEquiv_apply]

/-- The inverse of `K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)` is the inverse of `K₀` of the product followed by
`K₀` of the inverse splitting. -/
theorem unitalProdEquiv_symm_apply (y : ProjectionKZero A × ProjectionKZero R) :
    (unitalProdEquiv R A).symm y =
      ProjectionKZero.map (Unitization.prodStarAlgEquiv R A).toStarRingEquiv.symm
        ((ProjectionKZero.prodEquiv A R).symm y) := by
  rw [unitalProdEquiv, AddEquiv.symm_trans_apply, ProjectionKZero.mapEquiv_symm_apply]

/-- Under `K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)`, the homomorphism `K₀(ε)` induced by the augmentation is the
second projection. -/
@[simp]
theorem unitalProdEquiv_apply_snd (x : ProjectionKZero (Unitization R A)) :
    (unitalProdEquiv R A x).2 = augmentation R A x := by
  have h : (NonUnitalStarRingHom.snd A R).comp
      (Unitization.prodStarAlgEquiv R A).toStarRingEquiv =
      NonUnitalStarRingHom.ofClass (Unitization.fstStarAlgHom R A) :=
    NonUnitalStarRingHom.ext fun y ↦ (NonUnitalStarRingHom.snd_apply _).trans <|
      (congrArg Prod.snd (Unitization.prodStarAlgEquiv_apply R A y)).trans
        (Unitization.fstStarAlgHom_apply R A y).symm
  rw [augmentation_def, ← h, ProjectionKZero.map_comp, unitalProdEquiv_apply,
    ProjectionKZero.prodEquiv_apply, AddMonoidHom.comp_apply]

/-- **The `K₀`-group of a unital algebra through the unitization**: for unital `A`, the kernel
`K₀(A)` of `K₀(ε) : K₀(A⁺) → K₀(R)` is isomorphic to the projection `K₀`-group `K₀ᵖ(A)`, by the
first component of `K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)`. -/
noncomputable def unitalEquiv : UnitizationKZero R A ≃+ ProjectionKZero A where
  toFun x := (unitalProdEquiv R A x).1
  invFun a := ⟨(unitalProdEquiv R A).symm (a, 0), by
    rw [mem_iff, ← unitalProdEquiv_apply_snd, AddEquiv.apply_symm_apply]⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    rw [mem_iff, ← unitalProdEquiv_apply_snd] at hx
    exact Subtype.ext ((unitalProdEquiv R A).symm_apply_eq.2 (Prod.ext rfl hx.symm))
  right_inv a := by simp
  map_add' x y := by simp

/-- The isomorphism `K₀(A) ≃+ K₀ᵖ(A)` is the first component of `K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)`. -/
@[simp]
theorem unitalEquiv_apply (x : UnitizationKZero R A) :
    unitalEquiv R A x = (unitalProdEquiv R A x).1 :=
  (rfl)

/-- The isomorphism `K₀(A) ≃+ K₀ᵖ(A)` is induced by the star homomorphism `A⁺ → A`,
`(r, a) ↦ r • 1 + a`, the unital lift `Unitization.starLift` of the identity of `A`. -/
theorem unitalEquiv_apply_eq_map (x : UnitizationKZero R A) :
    unitalEquiv R A x = ProjectionKZero.map
      (NonUnitalStarRingHom.ofClass (Unitization.starLift (NonUnitalStarAlgHom.id R A))) x := by
  have h : (NonUnitalStarRingHom.fst A R).comp
      (Unitization.prodStarAlgEquiv R A).toStarRingEquiv =
      NonUnitalStarRingHom.ofClass (Unitization.starLift (NonUnitalStarAlgHom.id R A)) :=
    NonUnitalStarRingHom.ext fun y ↦ (NonUnitalStarRingHom.fst_apply _).trans <|
      (congrArg Prod.fst (Unitization.prodStarAlgEquiv_apply R A y)).trans (by simp)
  rw [← h, ProjectionKZero.map_comp, unitalEquiv_apply, unitalProdEquiv_apply,
    ProjectionKZero.prodEquiv_apply, AddMonoidHom.comp_apply]

/-- The inverse of `K₀(A) ≃+ K₀ᵖ(A)` sends `a` to the preimage of `(a, 0)` under
`K₀(A⁺) ≃+ K₀ᵖ(A) × K₀(R)`. -/
@[simp]
theorem coe_unitalEquiv_symm_apply (a : ProjectionKZero A) :
    ((unitalEquiv R A).symm a : ProjectionKZero (Unitization R A)) =
      (unitalProdEquiv R A).symm (a, 0) :=
  (rfl)

end UnitizationKZero

end TauCeti
