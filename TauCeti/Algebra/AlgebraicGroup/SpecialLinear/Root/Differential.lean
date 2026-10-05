/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential

/-!
# Differential of a special-linear root subgroup

The differential at the identity of the represented morphism `xᵢⱼ : 𝔾ₐ → SLₙ` is
the map `c ↦ c Eᵢⱼ` into the trace-zero matrices. In particular, the unit tangent
vector gives the normalized root vector used in the standard type-A pinning.

The calculation uses the coordinate factorization through `SLₙ → GLₙ` and
`GeneralLinear.tangentMatrix_derivationComp_rootSubgroup`. It holds over every commutative base ring
and every commutative coefficient algebra, without smoothness or characteristic
assumptions.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
-/

public section

namespace TauCeti.SpecialLinear

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable {n : ℕ} {i j : Fin n}

/-- In the special linear Lie algebra, the differential of `xᵢⱼ : 𝔾ₐ → SLₙ` is
Mathlib's linear map `c ↦ c Eᵢⱼ` of off-diagonal single-entry matrices. -/
@[simp]
theorem tangentMatrix_derivationComp_rootSubgroup (hij : i ≠ j)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    tangentMatrix n
        (derivationComp (B := B)
          (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom d) =
      LieAlgebra.SpecialLinear.single i j hij (AdditiveGroup.gaTangentLinearEquiv d) := by
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.val_single, tangentMatrix_apply_coe,
    HopfIdeal.quotientLieHom_apply]
  have hcomp := congrArg CommHopfAlgCat.Hom.hom
    (coordinateMap_comp_rootSubgroupCoordinateMap (R := R) hij)
  simp only [CommHopfAlgCat.hom_comp, coordinateMap,
    CommHopfAlgCat.hom_mkQuotient] at hcomp
  rw [← LinearMap.comp_apply, ← derivationComp_comp, hcomp]
  exact GeneralLinear.tangentMatrix_derivationComp_rootSubgroup hij d

/-- The root-subgroup differential is injective, even over nonreduced coefficient rings. -/
theorem derivationComp_rootSubgroup_injective (hij : i ≠ j) :
    Function.Injective
      (derivationComp (B := B) (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom) := by
  intro d e hde
  apply (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).injective
  have hentry := congrArg (fun x ↦
    (tangentMatrix (R := R) (B := B) n x : Matrix (Fin n) (Fin n) B) i j) hde
  simpa only [tangentMatrix_derivationComp_rootSubgroup (R := R) (B := B) hij,
    LieAlgebra.SpecialLinear.val_single, Matrix.single_apply_same] using hentry

/-- A tangent vector belongs to the image of the root-subgroup differential exactly when
its trace-zero matrix is a scalar multiple of the corresponding matrix unit. -/
theorem mem_range_derivationCompLieHom_rootSubgroup_iff (hij : i ≠ j)
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    d ∈ (derivationCompLieHom (B := B)
        (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom).range ↔
      ∃ c : B, tangentMatrix n d = LieAlgebra.SpecialLinear.single i j hij c := by
  rw [LieHom.mem_range]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨AdditiveGroup.gaTangentLinearEquiv e, by
      rw [derivationCompLieHom_apply, tangentMatrix_derivationComp_rootSubgroup]⟩
  · rintro ⟨c, hc⟩
    refine ⟨(AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm c, ?_⟩
    apply (tangentLieEquivSl (R := R) (B := B) n).injective
    simpa only [LieEquiv.coe_toLieHom, tangentLieEquivSl_apply (R := R) (B := B),
      derivationCompLieHom_apply, tangentMatrix_derivationComp_rootSubgroup (R := R) (B := B),
      LinearEquiv.apply_symm_apply] using hc.symm

private theorem tangentMatrix_smul_derivationComp_rootSubgroup_unit (hij : i ≠ j) (c : B) :
    tangentMatrix n
        (c • derivationComp (B := B)
          (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom
          ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)) =
      LieAlgebra.SpecialLinear.single i j hij c := by
  simp only [map_smul, tangentMatrix_derivationComp_rootSubgroup (R := R) (B := B),
    LinearEquiv.apply_symm_apply]
  simpa using ((LieAlgebra.SpecialLinear.single i j hij (R := B)).map_smul c 1).symm

/-- The image of the root-subgroup differential is the line spanned by the image of the
unit tangent vector. This characterizes the normalized root vector inside `Lie(SLₙ)`. -/
theorem range_derivationCompLieHom_rootSubgroup_eq_span (hij : i ≠ j) :
    (derivationCompLieHom (B := B)
        (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom).range.toSubmodule =
      Submodule.span B
        {derivationComp (B := B) (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom
          ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)} := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, Submodule.mem_span_singleton,
    mem_range_derivationCompLieHom_rootSubgroup_iff hij]
  apply exists_congr
  intro c
  constructor
  · intro hc
    apply (tangentLieEquivSl (R := R) (B := B) n).injective
    simpa only [LieEquiv.coe_toLieHom, tangentLieEquivSl_apply (R := R) (B := B),
      tangentMatrix_smul_derivationComp_rootSubgroup_unit (R := R) (B := B)] using hc.symm
  · intro hc
    rw [← hc, tangentMatrix_smul_derivationComp_rootSubgroup_unit]

/-- The normalized root vector is nonzero over any nontrivial coefficient algebra. -/
theorem derivationComp_rootSubgroup_unit_ne_zero [Nontrivial B] (hij : i ≠ j) :
    derivationComp (B := B) (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1) ≠ 0 := by
  intro hzero
  have hentry := congrArg (fun d ↦
    (tangentMatrix (R := R) (B := B) n d : Matrix (Fin n) (Fin n) B) i j) hzero
  simp only [tangentMatrix_derivationComp_rootSubgroup (R := R) (B := B) hij,
    LieAlgebra.SpecialLinear.val_single, LinearEquiv.apply_symm_apply, Matrix.single_apply_same,
    map_zero, ZeroMemClass.coe_zero, Matrix.zero_apply, one_ne_zero] at hentry

end TauCeti.SpecialLinear
