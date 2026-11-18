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
A `⋆`-homomorphism between complex C⋆-algebras is contractive, so it bundles as a continuous
linear map `NonUnitalStarAlgHom.toContinuousLinearMap` of norm at most `1`.
A `⋆`-algebra equivalence of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it
bundles as a continuous linear equivalence `StarAlgEquiv.toContinuousLinearEquiv`.
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

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A `⋆`-homomorphism between C⋆-algebras as a continuous linear map. It has norm at most `1`
because `⋆`-homomorphisms between C⋆-algebras are contractive. -/
def toContinuousLinearMap (φ : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous (φ : A →ₗ[ℂ] B) 1 fun a => by
    simpa using NonUnitalStarAlgHom.norm_apply_le φ a

@[simp]
theorem coe_toContinuousLinearMap (φ : A →⋆ₙₐ[ℂ] B) : ⇑φ.toContinuousLinearMap = φ :=
  (rfl)

/-- A `⋆`-homomorphism between C⋆-algebras has norm at most `1` as a continuous linear map. -/
theorem norm_toContinuousLinearMap_le (φ : A →⋆ₙₐ[ℂ] B) : ‖φ.toContinuousLinearMap‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

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

@[simp]
theorem coe_toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑e.toContinuousLinearEquiv = e :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.toContinuousLinearEquiv.symm = e.symm.toContinuousLinearEquiv :=
  (rfl)

end StarAlgEquiv
