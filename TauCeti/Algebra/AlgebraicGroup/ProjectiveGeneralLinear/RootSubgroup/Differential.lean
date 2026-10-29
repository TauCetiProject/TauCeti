/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.RootSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Tangent.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential

/-!
# Differentials of projective elementary root subgroups

The differential of `xᵢⱼ : 𝔾ₐ → PGLₙ` sends a tangent parameter `c` to the inner
derivation `X ↦ (c Eᵢⱼ) X - X (c Eᵢⱼ)` of the matrix algebra. This identifies the
normalized vector supplied by the root parametrization in the faithful tangent
representation of `PGLₙ`, as needed to compare root vectors with a pinning.
The image of the differential is characterized by these commutator endomorphisms.

The calculation combines `tangentEnd_derivationComp_conjugationMap` with
`GeneralLinear.tangentMatrix_derivationComp_rootSubgroup`. It works over arbitrary
commutative base rings and coefficient algebras, including in characteristics
dividing `n`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10 and §21.
-/

public section

namespace TauCeti.ProjectiveGeneralLinear

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable {n : ℕ} {i j : Fin n}

/-- The ambient tangent matrix of a projective root map is the matrix of the
commutator with its single-entry tangent matrix. -/
@[simp]
theorem tangentMatrix_quotientLieHom_derivationComp_rootSubgroup (hij : i ≠ j)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix (n * n)
        (HopfIdeal.quotientLieHom (definingHopfIdeal n R)
          (derivationComp (B := B) (rootSubgroupCoordinateMap hij).hom d)) =
      conjugationMatrix (Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d)) 1 -
        conjugationMatrix 1 (Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d)) := by
  rw [rootSubgroupCoordinateMap_def, CommHopfAlgCat.hom_comp, derivationComp_comp,
    LinearMap.comp_apply, tangentMatrix_quotientLieHom_derivationComp_conjugationMap,
    GeneralLinear.tangentMatrix_derivationComp_rootSubgroup]

/-- The differential of an elementary root map into `PGLₙ` acts on the matrix algebra
by commutator with `c Eᵢⱼ`, where `c` is the additive tangent parameter. -/
@[simp]
theorem tangentEnd_derivationComp_rootSubgroup (hij : i ≠ j)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    tangentEnd n (derivationComp (B := B) (rootSubgroupCoordinateMap hij).hom d) =
      LinearMap.mulLeft B (Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d)) -
        LinearMap.mulRight B (Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d)) := by
  rw [tangentEnd_apply, tangentMatrix_quotientLieHom_derivationComp_rootSubgroup]
  simp only [map_sub, toLinAlgEquiv_conjugationMatrix,
    LinearMap.mulLeft_one, LinearMap.mulRight_one, LinearMap.comp_id, LinearMap.id_comp]

/-- A tangent vector lies in the differential image of `xᵢⱼ` exactly when its
action on the matrix algebra is commutator with a scalar multiple of `Eᵢⱼ`. -/
theorem mem_range_derivationCompLieHom_rootSubgroup_iff (hij : i ≠ j)
    (d : Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B)) :
    d ∈ (derivationCompLieHom (B := B) (rootSubgroupCoordinateMap hij).hom).range ↔
      ∃ c : B, tangentEnd n d =
        LinearMap.mulLeft B (Matrix.single i j c) -
          LinearMap.mulRight B (Matrix.single i j c) := by
  rw [LieHom.mem_range]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨AdditiveGroup.gaTangentLinearEquiv e, by
      rw [derivationCompLieHom_apply, tangentEnd_derivationComp_rootSubgroup]⟩
  · rintro ⟨c, hc⟩
    refine ⟨(AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm c, ?_⟩
    apply tangentEnd_injective n
    rw [derivationCompLieHom_apply, tangentEnd_derivationComp_rootSubgroup hij,
      LinearEquiv.apply_symm_apply]
    exact hc.symm

end TauCeti.ProjectiveGeneralLinear
