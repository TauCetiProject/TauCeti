/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.GeneratorAutomorphisms.Basic

/-!
# Vector-preserving automorphisms for the zero form

The vector stabilizer `CliffordAlgebra.vectorStabilizer Q` is the group of algebra automorphisms of
`CliffordAlgebra Q` that map the vectors onto themselves. When the generator map and the scalar map
of `CliffordAlgebra Q` are injective, for instance when `2` is invertible in `R`, it is the image
of the orthogonal group of `Q` (`CliffordAlgebra.orthogonalGroupEquivVectorStabilizer`), with no
nondegeneracy hypothesis on `Q`. This file works out the degenerate extreme, the zero form, where
the Clifford algebra is the exterior algebra and both maps are injective over every commutative
ring.

Every linear automorphism of `M` is an isometry of the zero form, so the vector stabilizer of
`ExteriorAlgebra R M` is a copy of the group of linear automorphisms of `M`, acting through the
exterior algebra functor `ExteriorAlgebra.map`
(`TauCeti.ExteriorAlgebra.linearEquivEquivVectorStabilizer`).

In higher rank the vector stabilizer of the exterior algebra is in general a proper subgroup of
all automorphisms: for instance, on `⋀(R²)` the assignment `e₁ ↦ e₁ + e₁ ∧ e₂`, `e₂ ↦ e₂`
extends to an automorphism that moves the vector `e₁` out of `R²`.

## Main definitions

* `TauCeti.ExteriorAlgebra.linearEquivEquivVectorStabilizer`: the group isomorphism from the
  linear automorphisms of `M` onto the vector stabilizer of `ExteriorAlgebra R M`.

## Main results

* `TauCeti.ExteriorAlgebra.toAlgHom_linearEquivEquivVectorStabilizer_apply`: the automorphism
  attached to `f` is `ExteriorAlgebra.map f`.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.3 and Theorem 1.4.
-/

public section

universe u v

namespace TauCeti.ExteriorAlgebra

open _root_.ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

variable (R M) in
/-- **The vector stabilizer of the exterior algebra.** Every linear automorphism `f` of `M` is an
isometry of the zero form, so it induces an automorphism of `ExteriorAlgebra R M` that maps the
vectors onto themselves, namely `ExteriorAlgebra.map f`
(`TauCeti.ExteriorAlgebra.toAlgHom_linearEquivEquivVectorStabilizer_apply`). Every automorphism of
the exterior algebra that maps the vectors onto themselves arises from exactly one `f`, and
composition of automorphisms corresponds to composition of linear maps. This holds over every
commutative ring, with no invertibility assumption on `2`: it is
`CliffordAlgebra.orthogonalGroupEquivVectorStabilizer` for the zero form, whose generator map
`ExteriorAlgebra.ι` and scalar map are injective over every commutative ring. -/
noncomputable def linearEquivEquivVectorStabilizer :
    (M ≃ₗ[R] M) ≃* CliffordAlgebra.vectorStabilizer (0 : QuadraticForm R M) :=
  -- Every linear automorphism of `M` preserves the zero form.
  (Subgroup.topEquiv.symm.trans <| MulEquiv.subgroupCongr <| Eq.symm <| eq_top_iff.mpr fun _ _ ↦
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun _ ↦ zero_apply _).trans
    (CliffordAlgebra.orthogonalGroupEquivVectorStabilizer _ ι_leftInverse.injective
      (algebraMap_leftInverse M).injective)

/-- On generators, the automorphism attached to `f` applies `f`. -/
@[simp]
theorem linearEquivEquivVectorStabilizer_apply_ι (f : M ≃ₗ[R] M) (m : M) :
    (linearEquivEquivVectorStabilizer R M f :
      ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) (ι R m) = ι R (f m) := by
  rw [linearEquivEquivVectorStabilizer, MulEquiv.trans_apply,
    CliffordAlgebra.orthogonalGroupEquivVectorStabilizer_apply_ι]
  simp

/-- **The vector stabilizer acts through the exterior algebra functor**: the automorphism attached
to a linear automorphism `f` of `M` is `ExteriorAlgebra.map f`. -/
@[simp]
theorem toAlgHom_linearEquivEquivVectorStabilizer_apply (f : M ≃ₗ[R] M) :
    ((linearEquivEquivVectorStabilizer R M f : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) :
      ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M) = map (f : M →ₗ[R] M) :=
  hom_ext <| LinearMap.ext fun m ↦ by simp

/-- The linear automorphism underlying `φ` in the vector stabilizer of the exterior algebra is
characterized by its action on generators. -/
@[simp]
theorem ι_linearEquivEquivVectorStabilizer_symm_apply
    (φ : CliffordAlgebra.vectorStabilizer (0 : QuadraticForm R M)) (m : M) :
    ι R ((linearEquivEquivVectorStabilizer R M).symm φ m) =
      (φ : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R M) (ι R m) := by
  rw [linearEquivEquivVectorStabilizer, MulEquiv.symm_trans_apply]
  simp

end TauCeti.ExteriorAlgebra
