/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.RootSubgroup.Basic

/-!
# The diagonal torus action on projective root subgroups

The diagonal torus of `PGL_{r+1}` conjugates the elementary root subgroup `xᵢⱼ`
by rescaling its additive parameter with the character `εᵢ - εⱼ`, where the last
coordinate character is zero. This relates the closed root maps to the specified
torus, including the roots involving the normalized last diagonal entry.

The equation holds on points over every commutative value algebra over every
commutative base ring. In particular it retains the scheme-theoretic information
over nonreduced rings and in characteristics dividing `r + 1`. It supplies the
root-character conjugation equation used in a pinning; no identification of the
full adjoint root spaces is asserted here.

The proof transports `TauCeti.diagGL_mul_transvectionUnit_mul_inv` through the
projective points equivalence, using the torus and root point formulas in the
two imported modules.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u v

variable {R : Type u} [CommRing R] {r : ℕ} {i j : Fin (r + 1)}

/-- Conjugation by the projective diagonal torus rescales the parameter of the
elementary root subgroup by its root character. This is an equality of points
over an arbitrary commutative value algebra, with no field or reducedness hypothesis. -/
theorem diagonalTorus_mul_rootSubgroupPoints_mul_inv
    (A : CommAlgCat.{v} R) (hij : i ≠ j)
    (t : HopfAlgebra.points (R := R)
      (H := MonoidAlgebra R (SplitTorus.characterGroup (ULift.{u} (Fin r)))) A)
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    BialgHom.mapDomain (diagonalTorusCoordinateMap r R).hom t *
        rootSubgroupPoints A hij c *
        (BialgHom.mapDomain (diagonalTorusCoordinateMap r R).hom t)⁻¹ =
      rootSubgroupPoints A hij
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm
          (Multiplicative.ofAdd
            ((torusCharacter (SplitTorus.pointsMulEquiv t)
                (diagonalTorusWeight r (finProdFinEquiv (i, j))) : Aˣ) •
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c)))) := by
  apply (pointsMulEquiv (r + 1) R A).injective
  have ht := pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap r R A t
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, ← BialgHom.mapDomain_apply] at ht
  rw [map_mul, map_mul, map_inv, ht,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd,
    torusCharacter_diagonalTorusWeight, Equiv.symm_apply_apply, Units.smul_def, div_eq_mul_inv,
    Units.val_mul, smul_eq_mul]
  rw [← map_inv, ← map_mul, ← map_mul, diagGL_mul_transvectionUnit_mul_inv]
  congr 2
  ring

end TauCeti.ProjectiveGeneralLinear
