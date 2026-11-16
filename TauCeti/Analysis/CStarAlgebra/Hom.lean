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

A `⋆`-algebra homomorphism between complex C⋆-algebras is automatically continuous and contractive,
so it bundles as a continuous linear map (`NonUnitalStarAlgHom.toContinuousLinearMap`, with operator
norm at most one) and its two-sided ideal kernel is closed (`NonUnitalStarAlgHom.isClosed_ker`),
stated for any morphism class so both cover unital `⋆`-homomorphisms and `⋆`-equivalences as well.
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

open scoped CStarAlgebra in
/-- Any `⋆`-homomorphism between complex C⋆-algebras (unital or not, and in any morphism class)
bundled as a continuous complex linear map. -/
def toContinuousLinearMap : A →L[ℂ] B where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_smul φ
  cont := map_continuous φ

/-- The underlying function of `toContinuousLinearMap φ` is `φ`. -/
@[simp]
theorem coe_toContinuousLinearMap : ⇑(toContinuousLinearMap φ) = φ :=
  (rfl)

/-- Applying `toContinuousLinearMap φ` evaluates `φ`. -/
theorem toContinuousLinearMap_apply (a : A) : toContinuousLinearMap φ a = φ a :=
  (rfl)

open scoped CStarAlgebra in
/-- Any `⋆`-homomorphism between complex C⋆-algebras is a contraction as a continuous linear
map. -/
theorem norm_toContinuousLinearMap_le : ‖toContinuousLinearMap φ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    simpa only [toContinuousLinearMap_apply, one_mul] using norm_apply_le φ a

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
