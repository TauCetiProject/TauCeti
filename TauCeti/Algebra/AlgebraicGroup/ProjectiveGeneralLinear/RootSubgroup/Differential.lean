/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.RootSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent

/-!
# Differentials of projective elementary root subgroups

The differential of `xᵢⱼ : 𝔾ₐ → PGLₙ` sends a tangent parameter `c` to the inner
derivation `X ↦ (c Eᵢⱼ) X - X (c Eᵢⱼ)` of the matrix algebra. This identifies the
normalized vector supplied by the root parametrization in the faithful tangent
representation of `PGLₙ`, as needed to compare root vectors with a pinning.
The image of the differential is characterized by these commutator endomorphisms.

The calculation uses `map_genericMatrix_rootSubgroupCoordinateMap` and the
matrix-unit realization `tangentEnd`. It works over arbitrary commutative base
rings and coefficient algebras, including in characteristics dividing `n`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10 and §21.
-/

public section

namespace TauCeti.ProjectiveGeneralLinear

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable {n : ℕ} {i j : Fin n}

private theorem rootSubgroup_tangentMatrix (hij : i ≠ j)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix (n * n)
        (HopfIdeal.quotientLieHom (definingHopfIdeal n R)
          (derivationComp (B := B) (rootSubgroupCoordinateMap hij).hom d)) =
      conjugationMatrix (Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d)) 1 -
        conjugationMatrix 1 (Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d)) := by
  classical
  ext a b
  rw [HopfIdeal.quotientLieHom_apply, ← LinearMap.comp_apply, ← derivationComp_comp,
    GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply,
    ← GeneralLinear.genericMatrix_apply]
  have hentry := congrFun (congrFun
    (map_genericMatrix_rootSubgroupCoordinateMap (R := R) hij) a) b
  simp only [Matrix.map_apply, CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_mkQuotient] at hentry
  -- The coordinate identity uses the bialgebra-hom coercion rather than its algebra hom.
  erw [hentry]
  clear hentry
  rw [conjugationMatrix_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply_mul]
  simp only [conjugationMatrix_apply, Matrix.transvection, Matrix.add_apply,
    Matrix.single_apply, Matrix.one_apply, Matrix.sub_apply,
    AdditiveGroup.gaTangentLinearEquiv_apply]
  split_ifs <;>
    simp_all [map_neg, SymmetricAlgebra.counit_ι,
      -Bialgebra.CounitAlgebra.algEquivSelf_apply]

/-- The differential of an elementary root map into `PGLₙ` acts on the matrix algebra
by commutator with `c Eᵢⱼ`, where `c` is the additive tangent parameter.
Use `rw` with this formula; matching the bundled coordinate maps may require explicit arguments. -/
theorem tangentEnd_derivationComp_rootSubgroup (hij : i ≠ j)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    tangentEnd n (derivationComp (B := B) (rootSubgroupCoordinateMap hij).hom d) =
      LinearMap.mulLeft B (Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d)) -
        LinearMap.mulRight B (Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d)) := by
  rw [tangentEnd_apply, rootSubgroup_tangentMatrix hij]
  simp only [map_sub, ← toMatrix_mulLeft_comp_mulRight,
    LinearMap.mulLeft_one, LinearMap.mulRight_one, LinearMap.comp_id, LinearMap.id_comp]
  exact congrArg₂ (· - ·)
    ((Matrix.toLinAlgEquiv (matrixUnitBasis n B)).apply_symm_apply _)
    ((Matrix.toLinAlgEquiv (matrixUnitBasis n B)).apply_symm_apply _)

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
