/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Unitization.Basic
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent.Prod

/-!
# `K₁` through the unitization agrees with `K₁` of a unital algebra

Let `A` be a regular unital normed algebra over a nontrivially normed field `𝕜`
(`RegularNormedAlgebra 𝕜 A`, which holds for instance when `‖1‖ = 1`, as in a unital
C⋆-algebra). Its `K₁`-group defined through the forced unitization `A⁺ = Unitization 𝕜 A` is
the kernel `TauCeti.UnitizationKOne 𝕜 A` of the homomorphism `π₀GL_∞(A⁺) → π₀GL_∞(𝕜)` induced
by the scalar part; its `K₁`-group as a unital algebra is the stable component group `π₀GL_∞(A)`
itself (`TauCeti.StableComponentGroup A`). This file shows that the two agree.

The forced unitization splits as `A⁺ ≃ₐ[𝕜] A × 𝕜`, `(r, a) ↦ (r • 1 + a, r)`
(`Unitization.prodAlgEquiv`), which is a homeomorphism, and the scalar part becomes the second
projection. Combined with the stable component group of a product
(`TauCeti.StableComponentGroup.prodEquiv`) this gives `π₀GL_∞(A⁺) ≃* π₀GL_∞(A) × π₀GL_∞(𝕜)`
(`TauCeti.UnitizationKOne.unitalProdEquiv`), under which the scalar part is the second projection
(`TauCeti.UnitizationKOne.unitalProdEquiv_apply_snd`). So its kernel `K₁(A)` is `π₀GL_∞(A)`
(`TauCeti.UnitizationKOne.unitalEquiv`), by the homomorphism induced by `A⁺ → A`,
`(r, a) ↦ r • 1 + a` (`TauCeti.UnitizationKOne.unitalEquiv_apply`). This is the `K₁` counterpart
of `TauCeti.UnitizationKZero.unitalEquiv`.

## Main definitions

* `TauCeti.UnitizationKOne.unitalProdEquiv`: `π₀GL_∞(A⁺) ≃* π₀GL_∞(A) × π₀GL_∞(𝕜)` for unital
  `A`.
* `TauCeti.UnitizationKOne.unitalEquiv`: `K₁(A) ≃* π₀GL_∞(A)` for unital `A`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definition 8.1.1 and 8.1.5.
-/

public section

noncomputable section

namespace TauCeti

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

variable [RegularNormedAlgebra 𝕜 A]

namespace UnitizationKOne

/-- For a regular unital normed algebra `A` (for instance one with `‖1‖ = 1`),
`π₀GL_∞(A⁺) ≃* π₀GL_∞(A) × π₀GL_∞(𝕜)`, induced by the splitting `A⁺ ≃ₐ[𝕜] A × 𝕜` and the
stable component group of a product. -/
def unitalProdEquiv :
    StableComponentGroup (Unitization 𝕜 A) ≃* StableComponentGroup A × StableComponentGroup 𝕜 :=
  (StableComponentGroup.mapEquiv (Unitization.prodAlgEquiv 𝕜 A).toRingEquiv
    (Unitization.continuous_prodAlgEquiv 𝕜 A) (Unitization.continuous_prodAlgEquiv_symm 𝕜 A)).trans
    (StableComponentGroup.prodEquiv A 𝕜)

variable {𝕜 A}

/-- Under `π₀GL_∞(A⁺) ≃* π₀GL_∞(A) × π₀GL_∞(𝕜)`, the first component is induced by the map
`A⁺ → A`, `(r, a) ↦ r • 1 + a`. -/
@[simp]
theorem unitalProdEquiv_apply_fst (x : StableComponentGroup (Unitization 𝕜 A)) :
    (unitalProdEquiv 𝕜 A x).1 =
      StableComponentGroup.map (Unitization.lift (NonUnitalAlgHom.id 𝕜 A))
        (Unitization.continuous_lift_id 𝕜 A) x := by
  simp only [unitalProdEquiv, MulEquiv.trans_apply, StableComponentGroup.mapEquiv_apply,
    StableComponentGroup.prodEquiv_apply, StableComponentGroup.map_map,
    AlgEquiv.toRingEquiv_toRingHom, ← Unitization.fst_comp_prodAlgEquiv]

/-- Under `π₀GL_∞(A⁺) ≃* π₀GL_∞(A) × π₀GL_∞(𝕜)`, the second component is induced by the scalar
part `A⁺ → 𝕜`. -/
@[simp]
theorem unitalProdEquiv_apply_snd (x : StableComponentGroup (Unitization 𝕜 A)) :
    (unitalProdEquiv 𝕜 A x).2 =
      StableComponentGroup.map (Unitization.fstHom 𝕜 A : Unitization 𝕜 A →+* 𝕜)
        (Unitization.continuous_fstHom 𝕜 A) x := by
  simp only [unitalProdEquiv, MulEquiv.trans_apply, StableComponentGroup.mapEquiv_apply,
    StableComponentGroup.prodEquiv_apply, StableComponentGroup.map_map,
    AlgEquiv.toRingEquiv_toRingHom, ← Unitization.snd_comp_prodAlgEquiv]

/-- The inverse of `π₀GL_∞(A⁺) ≃* π₀GL_∞(A) × π₀GL_∞(𝕜)` is the inverse of the stable component
group of a product followed by the map induced by the inverse splitting. -/
theorem unitalProdEquiv_symm_apply (y : StableComponentGroup A × StableComponentGroup 𝕜) :
    (unitalProdEquiv 𝕜 A).symm y =
      StableComponentGroup.map (Unitization.prodAlgEquiv 𝕜 A).toRingEquiv.symm
        (Unitization.continuous_prodAlgEquiv_symm 𝕜 A)
        ((StableComponentGroup.prodEquiv A 𝕜).symm y) := by
  rw [unitalProdEquiv, MulEquiv.symm_trans_apply, StableComponentGroup.mapEquiv_symm_apply]

variable (𝕜 A) in
/-- **`K₁` of a unital algebra through the unitization**: for a regular unital normed algebra `A`
(for instance one with `‖1‖ = 1`, such as a unital C⋆-algebra), the kernel `K₁(A)` of
`π₀GL_∞(A⁺) → π₀GL_∞(𝕜)` is isomorphic to the stable component group `π₀GL_∞(A)`, by the first
component of `π₀GL_∞(A⁺) ≃* π₀GL_∞(A) × π₀GL_∞(𝕜)`. -/
def unitalEquiv : UnitizationKOne 𝕜 A ≃* StableComponentGroup A where
  toFun x := (unitalProdEquiv 𝕜 A x).1
  invFun a := ⟨(unitalProdEquiv 𝕜 A).symm (a, 1), by
    rw [mem_iff, ← unitalProdEquiv_apply_snd, MulEquiv.apply_symm_apply]⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    rw [mem_iff, ← unitalProdEquiv_apply_snd] at hx
    exact Subtype.ext ((unitalProdEquiv 𝕜 A).symm_apply_eq.2 (Prod.ext rfl hx.symm))
  right_inv a := by simp only [MulEquiv.apply_symm_apply]
  map_mul' x y := by simp only [Subgroup.coe_mul, map_mul, Prod.fst_mul]

/-- The isomorphism `K₁(A) ≃* π₀GL_∞(A)` is induced by the map `A⁺ → A`, `(r, a) ↦ r • 1 + a`, the
lift of the identity of `A`. -/
@[simp]
theorem unitalEquiv_apply (x : UnitizationKOne 𝕜 A) :
    unitalEquiv 𝕜 A x =
      StableComponentGroup.map (Unitization.lift (NonUnitalAlgHom.id 𝕜 A))
        (Unitization.continuous_lift_id 𝕜 A) (x : StableComponentGroup (Unitization 𝕜 A)) :=
  unitalProdEquiv_apply_fst _

/-- The inverse of `K₁(A) ≃* π₀GL_∞(A)` sends `a` to the preimage of `(a, 1)` under
`π₀GL_∞(A⁺) ≃* π₀GL_∞(A) × π₀GL_∞(𝕜)`. -/
@[simp]
theorem coe_unitalEquiv_symm_apply (a : StableComponentGroup A) :
    ((unitalEquiv 𝕜 A).symm a : StableComponentGroup (Unitization 𝕜 A)) =
      (unitalProdEquiv 𝕜 A).symm (a, 1) :=
  (rfl)

end UnitizationKOne

end TauCeti
