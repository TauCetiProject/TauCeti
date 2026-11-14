/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal

/-!
# Topological properties of C⋆-algebra homomorphisms and equivalences

A `⋆`-algebra homomorphism between complex C⋆-algebras is automatically continuous, so its
two-sided ideal kernel is closed (`NonUnitalStarAlgHom.isClosed_ker`, stated for any morphism
class, so it covers unital `⋆`-homomorphisms and `⋆`-equivalences as well).
A `⋆`-algebra equivalence of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it
bundles as a continuous linear equivalence `StarAlgEquiv.toContinuousLinearEquiv` and as a linear
isometric equivalence `StarAlgEquiv.toLinearIsometryEquiv`, whose restriction to self-adjoint
elements is the real-linear isometric equivalence `StarAlgEquiv.selfAdjointLinearIsometryEquiv`.
-/

public section

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] (φ : F)

open scoped CStarAlgebra in
/-- The two-sided ideal kernel of any `⋆`-homomorphism between C⋆-algebras (unital or not, and
in any morphism class) is closed. -/
instance isClosed_ker : IsClosed (TwoSidedIdeal.ker φ : Set A) :=
  TwoSidedIdeal.isClosed_ker (map_continuous φ)

end NonUnitalStarAlgHom

namespace StarAlgEquiv

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A star-algebra equivalence of C⋆-algebras as a continuous linear equivalence. Both directions
are continuous because star-algebra equivalences of C⋆-algebras are isometric. -/
def toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : A ≃L[ℂ] B where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := map_add e
  map_smul' := map_smul e
  continuous_toFun := (StarAlgEquiv.isometry e).continuous
  continuous_invFun := (StarAlgEquiv.isometry e.symm).continuous

/-- `StarAlgEquiv.toContinuousLinearEquiv` acts by the underlying star-algebra equivalence. -/
@[simp]
theorem coe_toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑e.toContinuousLinearEquiv = e :=
  (rfl)

/-- Taking the inverse commutes with `StarAlgEquiv.toContinuousLinearEquiv`. -/
@[simp]
theorem toContinuousLinearEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.toContinuousLinearEquiv.symm = e.symm.toContinuousLinearEquiv :=
  (rfl)

/-- A star-algebra equivalence of complex C⋆-algebras as a `ℂ`-linear isometric equivalence. -/
noncomputable def toLinearIsometryEquiv (e : A ≃⋆ₐ[ℂ] B) : A ≃ₗᵢ[ℂ] B where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := map_add e
  map_smul' := map_smul e
  norm_map' := StarAlgEquiv.norm_map e

/-- `StarAlgEquiv.toLinearIsometryEquiv` acts by the underlying star-algebra equivalence. -/
@[simp]
theorem coe_toLinearIsometryEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑e.toLinearIsometryEquiv = e :=
  (rfl)

/-- Evaluating `StarAlgEquiv.toLinearIsometryEquiv` applies the star-algebra equivalence. -/
theorem toLinearIsometryEquiv_apply (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    e.toLinearIsometryEquiv a = e a :=
  (rfl)

/-- Taking the inverse commutes with `StarAlgEquiv.toLinearIsometryEquiv`. -/
@[simp]
theorem toLinearIsometryEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.toLinearIsometryEquiv.symm = e.symm.toLinearIsometryEquiv :=
  (rfl)

/-- Restricting a star-algebra equivalence of complex C⋆-algebras to the self-adjoint elements gives
an `ℝ`-linear isometric equivalence `selfAdjoint A ≃ₗᵢ[ℝ] selfAdjoint B`. -/
noncomputable def selfAdjointLinearIsometryEquiv (e : A ≃⋆ₐ[ℂ] B) :
    selfAdjoint A ≃ₗᵢ[ℝ] selfAdjoint B where
  toFun a := ⟨e a.1, a.2.map e⟩
  invFun b := ⟨e.symm b.1, b.2.map e.symm⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.1)
  right_inv b := Subtype.ext (e.apply_symm_apply b.1)
  map_add' a₁ a₂ := Subtype.ext (map_add e a₁.1 a₂.1)
  map_smul' r a := Subtype.ext <| by
    simp only [RingHom.id_apply, selfAdjoint.val_smul, ← Complex.coe_smul, map_smul]
  norm_map' a := StarAlgEquiv.norm_map e a.1

/-- The underlying element of `e.selfAdjointLinearIsometryEquiv a` is `e a`. -/
@[simp]
theorem coe_selfAdjointLinearIsometryEquiv_apply (e : A ≃⋆ₐ[ℂ] B) (a : selfAdjoint A) :
    (e.selfAdjointLinearIsometryEquiv a : B) = e a.1 :=
  (rfl)

/-- Taking the inverse commutes with `StarAlgEquiv.selfAdjointLinearIsometryEquiv`. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.selfAdjointLinearIsometryEquiv.symm = e.symm.selfAdjointLinearIsometryEquiv :=
  (rfl)

/-- On unital commutative C⋆-algebras, `selfAdjointLinearIsometryEquiv` preserves `1`. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_one {A B : Type*} [CommCStarAlgebra A] [CommCStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) : e.selfAdjointLinearIsometryEquiv 1 = 1 :=
  Subtype.ext (map_one e)

/-- On commutative C⋆-algebras, `selfAdjointLinearIsometryEquiv` preserves multiplication. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_mul {A B : Type*} [NonUnitalCommCStarAlgebra A]
    [NonUnitalCommCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B) (a₁ a₂ : selfAdjoint A) :
    e.selfAdjointLinearIsometryEquiv (a₁ * a₂) =
      e.selfAdjointLinearIsometryEquiv a₁ * e.selfAdjointLinearIsometryEquiv a₂ :=
  Subtype.ext (map_mul e a₁.1 a₂.1)

end StarAlgEquiv
