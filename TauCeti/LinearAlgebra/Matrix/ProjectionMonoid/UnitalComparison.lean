/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Prod
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization

/-!
# `K₀` through the unitization agrees with `K₀` of a unital algebra

For a unital star algebra `A` over a commutative star ring `R`, the forced unitization splits as
`A⁺ ≃⋆ₐ[R] A × R`, `(r, a) ↦ (r • 1 + a, r)` (`Unitization.prodStarAlgEquiv`), and the
augmentation `ε : A⁺ → R` becomes the second projection. Combined with `K₀` of a product
(`TauCeti.ProjectionKZero.prodEquiv`) this gives `K₀(A⁺) ≃+ K₀(A) × K₀(R)`
(`TauCeti.UnitizationKZero.unitalProdEquiv`), under which `K₀(ε)` is the second projection
(`TauCeti.UnitizationKZero.unitalProdEquiv_apply_snd`). So its kernel, the `K₀`-group of `A`
defined through the unitization, is the projection `K₀`-group of `A`
(`TauCeti.UnitizationKZero.unitalEquiv`).

## Main definitions

* `TauCeti.UnitizationKZero.unitalProdEquiv`: `K₀(A⁺) ≃+ K₀(A) × K₀(R)` for unital `A`.
* `TauCeti.UnitizationKZero.unitalEquiv`: `ker K₀(ε) ≃+ K₀(A)` for unital `A`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definition 5.5.1 and Proposition 5.4.1.
-/

public section

namespace TauCeti

namespace UnitizationKZero

open ProjectionMonoid

variable (R A : Type*) [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  [StarModule R A]

/-- For a unital star algebra `A`, `K₀(A⁺) ≃+ K₀(A) × K₀(R)`, induced by the splitting
`A⁺ ≃⋆ₐ[R] A × R` and `K₀` of a product. -/
noncomputable def unitalProdEquiv :
    ProjectionKZero (Unitization R A) ≃+ ProjectionKZero A × ProjectionKZero R :=
  (AddMonoidHom.toAddEquiv
    (ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.prodStarAlgEquiv R A)))
    (ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.prodStarAlgEquiv R A).symm))
    (by
      rw [← ProjectionKZero.map_comp]
      convert ProjectionKZero.map_id (R := Unitization R A)
      exact NonUnitalStarRingHom.ext (Unitization.prodStarAlgEquiv R A).symm_apply_apply)
    (by
      rw [← ProjectionKZero.map_comp]
      convert ProjectionKZero.map_id (R := A × R)
      exact NonUnitalStarRingHom.ext (Unitization.prodStarAlgEquiv R A).apply_symm_apply)).trans
    (ProjectionKZero.prodEquiv A R)

/-- `K₀(A⁺) ≃+ K₀(A) × K₀(R)` is `K₀` of the splitting followed by `K₀` of the product. -/
theorem unitalProdEquiv_apply (x : ProjectionKZero (Unitization R A)) :
    unitalProdEquiv R A x = ProjectionKZero.prodEquiv A R
      (ProjectionKZero.map (NonUnitalStarRingHom.ofClass (Unitization.prodStarAlgEquiv R A)) x) :=
  (rfl)

/-- Under `K₀(A⁺) ≃+ K₀(A) × K₀(R)`, the homomorphism `K₀(ε)` induced by the augmentation is the
second projection. -/
theorem unitalProdEquiv_apply_snd (x : ProjectionKZero (Unitization R A)) :
    (unitalProdEquiv R A x).2 = augmentation R A x := by
  have h : (sndHom A R).comp (NonUnitalStarRingHom.ofClass (Unitization.prodStarAlgEquiv R A)) =
      NonUnitalStarRingHom.ofClass (Unitization.fstStarAlgHom R A) :=
    NonUnitalStarRingHom.ext fun y ↦ by simp
  rw [augmentation_def, ← h, ProjectionKZero.map_comp, unitalProdEquiv_apply,
    ProjectionKZero.prodEquiv_apply, AddMonoidHom.comp_apply]

/-- **The `K₀`-group of a unital algebra through the unitization**: for unital `A`, the kernel of
`K₀(ε) : K₀(A⁺) → K₀(R)` is isomorphic to the projection `K₀`-group of `A`, by the first
component of `K₀(A⁺) ≃+ K₀(A) × K₀(R)`. -/
noncomputable def unitalEquiv : UnitizationKZero R A ≃+ ProjectionKZero A where
  toFun x := (unitalProdEquiv R A x).1
  invFun a := ⟨(unitalProdEquiv R A).symm (a, 0), by
    rw [mem_iff, ← unitalProdEquiv_apply_snd, AddEquiv.apply_symm_apply]⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    refine Subtype.ext ?_
    rw [mem_iff, ← unitalProdEquiv_apply_snd] at hx
    simp only
    rw [← hx, Prod.mk.eta, AddEquiv.symm_apply_apply]
  right_inv a := by simp
  map_add' x y := by simp

/-- The isomorphism `ker K₀(ε) ≃+ K₀(A)` is the first component of
`K₀(A⁺) ≃+ K₀(A) × K₀(R)`. -/
theorem unitalEquiv_apply (x : UnitizationKZero R A) :
    unitalEquiv R A x = (unitalProdEquiv R A x).1 :=
  (rfl)

end UnitizationKZero

end TauCeti
