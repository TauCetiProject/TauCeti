/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential

/-!
# Integral root-space trivializations for the general linear group

Each adjoint root space of the diagonal torus of `GL_n` is a free rank-one module over
any commutative base ring, including rings with zero divisors. The normalized matrix unit
`E_ij` trivializes the space of the root `e_i - e_j`; the inverse trivialization reads its
`(i, j)` matrix entry. These trivializations supply the generators required in a pinning.

The differential of the represented root subgroup `x_ij : 𝔾_a → GL_n` sends an additive
tangent vector to its scalar under this trivialization. Thus the generator is normalized
by the root subgroup, rather than just chosen up to a unit.

The construction uses the matrix-unit classification in
`GeneralLinear.Adjoint.Classification` and the root-subgroup differential in
`GeneralLinear.Root.Differential`. Its organization follows the special-linear
`rootSpaceEquiv` in `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Adjoint.Comodule`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
-/

public section

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Each adjoint root space of `GL_n` is trivialized by its normalized matrix unit.
The inverse reads the matrix entry indexed by the root. -/
def rootSpaceEquiv (p : DiagonalRootIndex n) :
    R ≃ₗ[R] Derivation.adjointWeightSpace (diagonalTorusCoordinateMap (R := R) (N := n)).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} n).root p)) where
  toFun c := ⟨c • matrixUnitTangent p.1.1.down p.1.2.down, by
    rw [diagonalRootDatum_root, ofAdd_diagonalRoot]
    exact Submodule.smul_mem _ c (matrixUnitTangent_mem_adjointWeightSpace _ _)⟩
  invFun x := cotangentDualMatrixEquiv x.val p.1.1.down p.1.2.down
  left_inv c := by simp
  right_inv x := by
    apply Subtype.ext
    dsimp only
    have hx := x.property
    simp only [diagonalRootDatum_root, ofAdd_diagonalRoot,
      adjointWeightSpace_matrixUnitWeight_eq_span_singleton
        (fun h ↦ p.2 (ULift.down_injective h)), Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    have hentry : cotangentDualMatrixEquiv x.val p.1.1.down p.1.2.down = c := by
      simpa using congrArg
        (fun y ↦ cotangentDualMatrixEquiv y p.1.1.down p.1.2.down) hc.symm
    rw [hentry]
    exact hc
  map_add' a b := Subtype.ext (add_smul _ _ _)
  map_smul' a b := Subtype.ext (mul_smul _ _ _)

/-- The root-space trivialization sends a scalar to that multiple of the matrix unit. -/
@[simp]
theorem rootSpaceEquiv_apply_coe (p : DiagonalRootIndex n) (c : R) :
    (rootSpaceEquiv (R := R) p c :
      Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R n))) =
      c • matrixUnitTangent p.1.1.down p.1.2.down := (rfl)

/-- The inverse root-space trivialization is the distinguished matrix entry. -/
@[simp]
theorem rootSpaceEquiv_symm_apply (p : DiagonalRootIndex n)
    (x : Derivation.adjointWeightSpace (diagonalTorusCoordinateMap (R := R) (N := n)).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} n).root p))) :
    (rootSpaceEquiv (R := R) p).symm x =
      cotangentDualMatrixEquiv x.val p.1.1.down p.1.2.down := (rfl)

/-- The represented root-subgroup differential is the normalized root-space trivialization,
with the additive tangent space identified with the base ring. -/
theorem cotangentLinearEquiv_rootSpaceEquiv (p : DiagonalRootIndex n)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) R)) :
    Derivation.cotangentLinearEquiv (B := R)
        (rootSpaceEquiv (R := R) p (AdditiveGroup.gaTangentLinearEquiv d)) =
      derivationComp (B := R)
        (rootSubgroupCoordinateMap (R := R) (N := n)
          (fun h ↦ p.2 (ULift.down_injective h))).hom d := by
  apply (tangentLinearEquivMatrix n).injective
  simp only [tangentLinearEquivMatrix_apply]
  rw [tangentMatrix_derivationComp_rootSubgroup, ← cotangentDualMatrixEquiv_apply]
  rw [rootSpaceEquiv_apply_coe, map_smul, cotangentDualMatrixEquiv_matrixUnitTangent]
  simp only [Matrix.smul_single, smul_eq_mul, mul_one]

end

end TauCeti.GeneralLinear
