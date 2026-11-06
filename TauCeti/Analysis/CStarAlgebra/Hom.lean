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
two-sided ideal kernel is closed (`NonUnitalStarAlgHom.isClosed_ker`, `StarAlgHom.isClosed_ker`).
A `⋆`-algebra equivalence of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it
bundles as a continuous linear equivalence `StarAlgEquiv.toContinuousLinearEquiv`.
-/

public section

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (φ : A →⋆ₙₐ[ℂ] B)

open scoped CStarAlgebra in
/-- The two-sided ideal kernel of any `⋆`-homomorphism between C⋆-algebras is closed. -/
instance isClosed_ker : IsClosed (TwoSidedIdeal.ker φ : Set A) :=
  TwoSidedIdeal.isClosed_ker (map_continuous φ)

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] (φ : A →⋆ₐ[ℂ] B)

open scoped CStarAlgebra in
/-- The two-sided ideal kernel of any unital `⋆`-homomorphism between C⋆-algebras is closed. -/
instance isClosed_ker : IsClosed (TwoSidedIdeal.ker φ : Set A) :=
  TwoSidedIdeal.isClosed_ker (map_continuous φ)

end StarAlgHom

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
