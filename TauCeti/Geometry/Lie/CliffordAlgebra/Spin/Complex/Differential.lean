/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.SpecialFunctions.Exponential
import TauCeti.Geometry.Lie.Adjoint.Units.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Projection
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Representation
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Realization

/-!
# Differentiating the complex Spin-to-SO projection and comparing Spin differentials

For a nondegenerate quadratic form `Q` on `Fin n → ℂ`, the real differential of the smooth complex
`Spin(Q) → SO(Q)` range-carrier projection acts on embedded vectors by the Clifford commutator:

`ι Q (d(spinToSpecialOrthogonal)(x) v) = ⁅(x : CliffordAlgebra Q), ι Q v⁆`,

with positive sign and no extra factor of `2`. Differentiating along real one-parameter Lie
exponential curves compares `exp (t • A) *ᵥ v` on the matrix side with Clifford conjugation
`exp (t • x) * ι Q v * exp (t • (-x))` on the Spin side.

Because `ι Q` is injective and `ℂ`-linear, this commutator formula identifies the coordinate
differentials with the inverses of `CliffordAlgebra.soEquivQuadratic` and
`CliffordAlgebra.skewAdjointMatricesEquivQuadratic`. In particular, although the Lie-group
differential is taken over `ℝ`, it commutes with complex scalar multiplication and is bijective, so
it upgrades to `ℂ`-linear Lie algebra equivalences
`complexSpinToSpecialOrthogonalPolarComplexLieEquiv` and
`complexSpinToSpecialOrthogonalComplexLieEquiv`. For a spin polarization `P`, the real differential
of `P.complexSpinSmoothMatrixHom b` likewise upgrades to a `ℂ`-linear Lie homomorphism
`P.complexSpinSmoothMatrixComplexLieHom b` that intertwines the Spin and `SO(Q)` differentials on
Clifford vector operators.

## Main definitions and results

* `TauCeti.CliffordAlgebra.complexSpinToSpecialOrthogonalCoordinateLieHom_lie_ι` and
  `TauCeti.CliffordAlgebra.complexSpinToSpecialOrthogonalPolarCoordinateLieHom_lie_ι`: the real
  coordinate differentials act on Clifford generators by the Clifford commutator.
* `TauCeti.CliffordAlgebra.complexSpinToSpecialOrthogonalPolarComplexLieEquiv` and
  `TauCeti.CliffordAlgebra.complexSpinToSpecialOrthogonalComplexLieEquiv`: the complex Spin-to-SO
  differential packaged as `ℂ`-linear Lie algebra equivalences onto `skewAdjointLieSubalgebra` and
  `skewAdjointMatricesLieSubalgebra`.
* `complexSpinToSpecialOrthogonalPolarComplexLieEquiv_eq_soEquivQuadratic_symm` and
  `complexSpinToSpecialOrthogonalComplexLieEquiv_eq_skewAdjointMatricesEquivQuadratic_symm` (in
  `TauCeti.CliffordAlgebra`): exact agreement with the algebraic quadratic realizations.
* `TauCeti.CliffordAlgebra.complexSpinToSpecialOrthogonalRangeLieMap_bijective`: the abstract real
  Lie map of the complex `Spin(Q) → SO(Q)` carrier projection is bijective.
* `TauCeti.SpinPolarizationData.complexSpinSmoothMatrixComplexLieHom` and
  `TauCeti.SpinPolarizationData.lie_complexSpinSmoothMatrixComplexLieHom_ι_eq`: the `ℂ`-linear
  differential of the Fock representation and its intertwining identity with the `SO(Q)`
  differential.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 2 and 5.
* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras* (2008), Chapter 3.
-/

public section

open Manifold
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] NormedAlgebra.toNormedSpace
attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] CliffordAlgebra.starModule_of_trivialStar
attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)} [Fact Q.Nondegenerate]

local notation "SpinUnitsRange" => MonoidHom.range (spinGroup.toUnits (Q := Q))

local notation "SpecialOrthogonalUnitsRange" =>
  MonoidHom.range Q.specialOrthogonalToGeneralLinear

local notation "SpinLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange)

local notation "SpecialOrthogonalLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) SpecialOrthogonalUnitsRange)

private theorem coe_smoothRange_lieExp_smul_eq_exp
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) (t : ℝ) :
    let X := (complexSpinLieEquivQuadratic (Q := Q)).symm x
    let A := ((RestrictScalars.addEquiv ℝ ℂ
      (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
      (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x)) : Matrix (Fin n) (Fin n) ℂ)
    (((complexSpinToSpecialOrthogonalSmoothRange (Q := Q) (lieExp (t • X))).1 :
        (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      NormedSpace.exp (t • A) := by
  intro X A
  let Y := lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q)) X
  have hY : Y = complexSpinToSpecialOrthogonalRangeLieMap (Q := Q) X :=
    DFunLike.congr_fun (complexSpinToSpecialOrthogonalRangeLieMap_eq_lieMap (Q := Q)).symm X
  have hmap : complexSpinToSpecialOrthogonalSmoothRange (Q := Q) (lieExp (t • X)) =
      lieExp (t • Y) := by
    rw [map_lieExp, map_smul]
  calc
    _ = (((complexSpecialOrthogonalEmbeddedLieSubgroupData Q).subtypeVal
        (lieExp (t • Y)) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      simpa only [TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply] using congrArg
        (fun z : SpecialOrthogonalUnitsRange ↦
          ((z.1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) hmap
    _ = NormedSpace.exp (t • unitsLieAlgebraEquiv
        ((complexSpecialOrthogonalEmbeddedLieSubgroupData Q).lieMapSubtypeVal Y)) :=
      (complexSpecialOrthogonalEmbeddedLieSubgroupData Q).coe_lieExp_smul Y t
    _ = NormedSpace.exp (t • A) := by
      congr 2
      rw [← TauCeti.Lie.unitsLieAlgebraLieEquiv_apply,
        unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpecialOrthogonalLieEquivMatrices,
        hY, ← complexSpinToSpecialOrthogonalCoordinateLieHom_apply]

private theorem coe_symm_lieExp_smul_eq_exp
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) (t : ℝ) :
    let X := (complexSpinLieEquivQuadratic (Q := Q)).symm x
    let s := (spinGroupContinuousMulEquivUnitsRange Q).symm (lieExp (t • X))
    let x₀ := RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x
    (s : CliffordAlgebra Q) = NormedSpace.exp (t • (x₀ : CliffordAlgebra Q)) := by
  intro X s x₀
  let D := complexSpinEmbeddedLieSubgroupData (Fact.out : Q.Nondegenerate)
  calc
    (s : CliffordAlgebra Q) =
        (((lieExp (t • X) : SpinUnitsRange).1 : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
      coe_spinGroupContinuousMulEquivUnitsRange_symm_apply Q (lieExp (t • X))
    _ = NormedSpace.exp (t • unitsLieAlgebraEquiv (D.lieMapSubtypeVal X)) := by
      simpa only [TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply] using D.coe_lieExp_smul X t
    _ = NormedSpace.exp (t • (x₀ : CliffordAlgebra Q)) := by
      congr 2
      rw [← TauCeti.Lie.unitsLieAlgebraLieEquiv_apply,
        unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpinLieEquivQuadratic,
        LieEquiv.apply_symm_apply]

private theorem coordinate_exp_mulVec_eq_conjugation
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) (v : Fin n → ℂ) (t : ℝ) :
    let A := ((RestrictScalars.addEquiv ℝ ℂ
      (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
      (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x)) : Matrix (Fin n) (Fin n) ℂ)
    let x₀ := RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x
    ι Q (NormedSpace.exp (t • A) *ᵥ v) =
      NormedSpace.exp (t • (x₀ : CliffordAlgebra Q)) * ι Q v *
        NormedSpace.exp (t • (-(x₀ : CliffordAlgebra Q))) := by
  intro A x₀
  let X := (complexSpinLieEquivQuadratic (Q := Q)).symm x
  let s := (spinGroupContinuousMulEquivUnitsRange Q).symm (lieExp (t • X))
  have htarget := coe_smoothRange_lieExp_smul_eq_exp (Q := Q) x t
  have hsource := coe_symm_lieExp_smul_eq_exp (Q := Q) x t
  have hmatrix : NormedSpace.exp (t • A) *ᵥ v = spinVectorAction Q s v := by
    rw [← htarget, complexSpinToSpecialOrthogonalSmoothRange_apply,
      spinToSpecialOrthogonalUnitsRange_apply, Q.specialOrthogonalContinuousMulEquivRange_apply]
    change (((Q.specialOrthogonalToGeneralLinear (spinToSpecialOrthogonal Q s) :
      Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) = _
    rw [Q.specialOrthogonalToGeneralLinear_mulVec, coe_spinToSpecialOrthogonal_apply]
  have hstar : star (x₀ : CliffordAlgebra Q) = -(x₀ : CliffordAlgebra Q) := by
    have hrev := reverse_eq_neg_of_mem_quadraticLieSubalgebra Q x₀.property
    rwa [reverse_eq_star_of_mem_even
      ⟨(x₀ : CliffordAlgebra Q), quadraticLieSubalgebra_le_even Q x₀.property⟩] at hrev
  rw [hmatrix, ι_spinVectorAction_apply, hsource, NormedSpace.star_exp, StarModule.star_smul,
    star_trivial]
  change NormedSpace.exp (t • (x₀ : CliffordAlgebra Q)) * ι Q v *
      NormedSpace.exp (t • star (x₀ : CliffordAlgebra Q)) = _
  rw [hstar]

omit [Fact Q.Nondegenerate] in
private theorem hasDerivAt_ι_exp_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    HasDerivAt
      (fun t : ℝ ↦ ι Q (NormedSpace.exp (t • A) *ᵥ v))
      (ι Q (A *ᵥ v)) 0 := by
  let fLin : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] CliffordAlgebra Q :=
    ((ι Q).restrictScalars ℝ).comp (((Matrix.mulVecBilin ℂ ℂ).flip v).restrictScalars ℝ)
  let fCLM : Matrix (Fin n) (Fin n) ℂ →L[ℝ] CliffordAlgebra Q :=
    ContinuousLinearMap.mk fLin fLin.continuous_of_finiteDimensional
  have h := fCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_exp_smul_const A (0 : ℝ))
  change HasDerivAt (fCLM ∘ fun t : ℝ ↦ NormedSpace.exp (t • A)) (fCLM A) 0
  simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using h

/-- The real matrix coordinate differential of the complex `Spin(Q) → SO(Q)` projection acts on an
embedded vector `v` by the Clifford Lie bracket with its quadratic source coordinate. -/
theorem complexSpinToSpecialOrthogonalCoordinateLieHom_lie_ι
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) (v : Fin n → ℂ) :
    ι Q (((RestrictScalars.addEquiv ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
        (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x)) :
          Matrix (Fin n) (Fin n) ℂ) *ᵥ v) =
      ⁅((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x) : CliffordAlgebra Q),
        ι Q v⁆ := by
  let A := ((RestrictScalars.addEquiv ℝ ℂ
    (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
    (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x)) : Matrix (Fin n) (Fin n) ℂ)
  let x₀ := RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x
  have hleft := hasDerivAt_ι_exp_mulVec (Q := Q) A v
  have hright := (TauCeti.hasDerivAt_exp_mul_const_mul_exp_neg
    (x₀ : CliffordAlgebra Q) (ι Q v)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t ↦ coordinate_exp_mulVec_eq_conjugation (Q := Q) x v t)
  rw [Ring.lie_def]
  exact hleft.unique hright

/-- The basis-free polar endomorphism differential of the complex `Spin(Q) → SO(Q)` projection acts
on an embedded vector `v` by the Clifford Lie bracket with its quadratic source coordinate. -/
theorem complexSpinToSpecialOrthogonalPolarCoordinateLieHom_lie_ι
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) (v : Fin n → ℂ) :
    ι Q (((RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)
        (complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q) x)) :
          Module.End ℂ (Fin n → ℂ)) v) =
      ⁅((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x) : CliffordAlgebra Q),
        ι Q v⁆ := by
  rw [coe_complexSpinToSpecialOrthogonalPolarCoordinateLieHom_apply_apply,
    complexSpinToSpecialOrthogonalCoordinateLieHom_lie_ι]

/-- On every quadratic element, the polar coordinate differential of the complex `Spin(Q) → SO(Q)`
projection equals `(CliffordAlgebra.soEquivQuadratic Q hQ).symm`. -/
theorem complexSpinToSpecialOrthogonalPolarCoordinateLieHom_eq_soEquivQuadratic_symm
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) :
    RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)
        (complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q) x) =
      (soEquivQuadratic Q (Fact.out : Q.Nondegenerate)).symm
        (RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x) := by
  let hQ := (Fact.out : Q.Nondegenerate)
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  apply ι_injective Q
  rw [complexSpinToSpecialOrthogonalPolarCoordinateLieHom_lie_ι, ← soEquivQuadratic_lie_ι Q hQ,
    LieEquiv.apply_symm_apply]

/-- On every quadratic element, the matrix coordinate differential of the complex `Spin(Q) → SO(Q)`
projection equals `(CliffordAlgebra.skewAdjointMatricesEquivQuadratic Q hQ ...).symm` in the
standard basis `Pi.basisFun ℂ (Fin n)`. -/
theorem complexSpinToSpecialOrthogonalCoordinateLieHom_eq_skewAdjointMatricesEquivQuadratic_symm
    (x : RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q)) :
    RestrictScalars.addEquiv ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
        (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x) =
      (skewAdjointMatricesEquivQuadratic Q (Fact.out : Q.Nondegenerate) (Pi.basisFun ℂ (Fin n))
        (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)).symm
        (RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x) := by
  let hQ := (Fact.out : Q.Nondegenerate)
  let hJ := DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin
  let e := skewAdjointMatricesEquivQuadratic Q hQ (Pi.basisFun ℂ (Fin n)) hJ
  let x₀ := RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  apply ι_injective Q
  rw [complexSpinToSpecialOrthogonalCoordinateLieHom_lie_ι]
  have hrhs := skewAdjointMatricesEquivQuadratic_lie_ι Q hQ (Pi.basisFun ℂ (Fin n)) hJ
    (e.symm x₀) v
  rw [e.apply_symm_apply] at hrhs
  rw [hrhs]
  congr 1

/-- The complex `Spin(Q) → SO(Q)` differential in polar skew-adjoint endomorphism coordinates,
packaged as a `ℂ`-linear Lie algebra equivalence. Its forward map is the manifold differential
`complexSpinToSpecialOrthogonalPolarCoordinateLieHom`. -/
def complexSpinToSpecialOrthogonalPolarComplexLieEquiv :
    quadraticLieSubalgebra Q ≃ₗ⁅ℂ⁆ skewAdjointLieSubalgebra Q.polarBilin where
  toFun x := RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)
    (complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q)
      ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x))
  invFun := soEquivQuadratic Q (Fact.out : Q.Nondegenerate)
  left_inv x := by
    dsimp only
    rw [complexSpinToSpecialOrthogonalPolarCoordinateLieHom_eq_soEquivQuadratic_symm,
      AddEquiv.apply_symm_apply, LieEquiv.apply_symm_apply]
  right_inv y := by
    dsimp only
    rw [complexSpinToSpecialOrthogonalPolarCoordinateLieHom_eq_soEquivQuadratic_symm,
      AddEquiv.apply_symm_apply, LieEquiv.symm_apply_apply]
  map_add' x y := by simp
  map_smul' c x := by
    rw [complexSpinToSpecialOrthogonalPolarCoordinateLieHom_eq_soEquivQuadratic_symm,
      complexSpinToSpecialOrthogonalPolarCoordinateLieHom_eq_soEquivQuadratic_symm,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingHom.id_apply, map_smul]
  map_lie' {x y} :=
    (complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q)).map_lie
      ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x)
      ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm y)

/-- Evaluating `complexSpinToSpecialOrthogonalPolarComplexLieEquiv` applies the real polar
coordinate differential `complexSpinToSpecialOrthogonalPolarCoordinateLieHom`. -/
@[simp]
theorem complexSpinToSpecialOrthogonalPolarComplexLieEquiv_apply
    (x : quadraticLieSubalgebra Q) :
    complexSpinToSpecialOrthogonalPolarComplexLieEquiv (Q := Q) x =
      RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)
        (complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q)
          ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x)) := by
  rfl

/-- `complexSpinToSpecialOrthogonalPolarComplexLieEquiv` acts on Clifford generators by the
Clifford commutator. -/
theorem complexSpinToSpecialOrthogonalPolarComplexLieEquiv_lie_ι
    (x : quadraticLieSubalgebra Q) (v : Fin n → ℂ) :
    ι Q (((complexSpinToSpecialOrthogonalPolarComplexLieEquiv (Q := Q) x :
        skewAdjointLieSubalgebra Q.polarBilin) : Module.End ℂ (Fin n → ℂ)) v) =
      ⁅(x : CliffordAlgebra Q), ι Q v⁆ := by
  rw [complexSpinToSpecialOrthogonalPolarComplexLieEquiv_apply,
    complexSpinToSpecialOrthogonalPolarCoordinateLieHom_lie_ι, AddEquiv.apply_symm_apply]

/-- As a `ℂ`-linear Lie algebra equivalence, the polar coordinate differential of the complex
`Spin(Q) → SO(Q)` projection equals `(CliffordAlgebra.soEquivQuadratic Q hQ).symm`. -/
theorem complexSpinToSpecialOrthogonalPolarComplexLieEquiv_eq_soEquivQuadratic_symm :
    complexSpinToSpecialOrthogonalPolarComplexLieEquiv (Q := Q) =
      (soEquivQuadratic Q (Fact.out : Q.Nondegenerate)).symm := by
  ext x : 1
  rw [complexSpinToSpecialOrthogonalPolarComplexLieEquiv_apply,
    complexSpinToSpecialOrthogonalPolarCoordinateLieHom_eq_soEquivQuadratic_symm,
    AddEquiv.apply_symm_apply]

/-- The complex `Spin(Q) → SO(Q)` differential in polar skew-adjoint matrix coordinates, packaged
as a `ℂ`-linear Lie algebra equivalence. Its forward map is the manifold differential
`complexSpinToSpecialOrthogonalCoordinateLieHom`. -/
def complexSpinToSpecialOrthogonalComplexLieEquiv :
    quadraticLieSubalgebra Q ≃ₗ⁅ℂ⁆
      skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin) where
  toFun x := RestrictScalars.addEquiv ℝ ℂ
    (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
    (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q)
      ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x))
  invFun := skewAdjointMatricesEquivQuadratic Q (Fact.out : Q.Nondegenerate) (Pi.basisFun ℂ (Fin n))
    (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)
  left_inv x := by
    dsimp only
    rw [complexSpinToSpecialOrthogonalCoordinateLieHom_eq_skewAdjointMatricesEquivQuadratic_symm,
      AddEquiv.apply_symm_apply, LieEquiv.apply_symm_apply]
  right_inv A := by
    dsimp only
    rw [complexSpinToSpecialOrthogonalCoordinateLieHom_eq_skewAdjointMatricesEquivQuadratic_symm,
      AddEquiv.apply_symm_apply, LieEquiv.symm_apply_apply]
  map_add' x y := by simp
  map_smul' c x := by
    rw [complexSpinToSpecialOrthogonalCoordinateLieHom_eq_skewAdjointMatricesEquivQuadratic_symm,
      complexSpinToSpecialOrthogonalCoordinateLieHom_eq_skewAdjointMatricesEquivQuadratic_symm,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingHom.id_apply, map_smul]
  map_lie' {x y} :=
    (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q)).map_lie
      ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x)
      ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm y)

/-- Evaluating `complexSpinToSpecialOrthogonalComplexLieEquiv` applies the real matrix coordinate
differential `complexSpinToSpecialOrthogonalCoordinateLieHom`. -/
@[simp]
theorem complexSpinToSpecialOrthogonalComplexLieEquiv_apply
    (x : quadraticLieSubalgebra Q) :
    complexSpinToSpecialOrthogonalComplexLieEquiv (Q := Q) x =
      RestrictScalars.addEquiv ℝ ℂ
        (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
        (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q)
          ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x)) := by
  rfl

/-- `complexSpinToSpecialOrthogonalComplexLieEquiv` acts on embedded vectors through `*ᵥ` by the
Clifford commutator. -/
theorem complexSpinToSpecialOrthogonalComplexLieEquiv_lie_ι
    (x : quadraticLieSubalgebra Q) (v : Fin n → ℂ) :
    ι Q (((complexSpinToSpecialOrthogonalComplexLieEquiv (Q := Q) x :
        skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) :
          Matrix (Fin n) (Fin n) ℂ) *ᵥ v) =
      ⁅(x : CliffordAlgebra Q), ι Q v⁆ := by
  rw [complexSpinToSpecialOrthogonalComplexLieEquiv_apply,
    complexSpinToSpecialOrthogonalCoordinateLieHom_lie_ι, AddEquiv.apply_symm_apply]

/-- As a `ℂ`-linear Lie algebra equivalence, the matrix coordinate differential of the complex
`Spin(Q) → SO(Q)` projection equals `(CliffordAlgebra.skewAdjointMatricesEquivQuadratic ...).symm`
in the standard basis `Pi.basisFun ℂ (Fin n)`. -/
theorem complexSpinToSpecialOrthogonalComplexLieEquiv_eq_skewAdjointMatricesEquivQuadratic_symm :
    complexSpinToSpecialOrthogonalComplexLieEquiv (Q := Q) =
      (skewAdjointMatricesEquivQuadratic Q (Fact.out : Q.Nondegenerate) (Pi.basisFun ℂ (Fin n))
        (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)).symm := by
  ext x : 1
  rw [complexSpinToSpecialOrthogonalComplexLieEquiv_apply,
    complexSpinToSpecialOrthogonalCoordinateLieHom_eq_skewAdjointMatricesEquivQuadratic_symm,
    AddEquiv.apply_symm_apply]

/-- The abstract real Lie map of the complex `Spin(Q) → SO(Q)` range-carrier projection is
bijective. -/
theorem complexSpinToSpecialOrthogonalRangeLieMap_bijective :
    Function.Bijective (complexSpinToSpecialOrthogonalRangeLieMap (Q := Q)) := by
  have hbij :
      Function.Bijective (complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q)) := by
    have heq : ⇑(complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q)) =
        ⇑(RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)).symm ∘
          ⇑(soEquivQuadratic Q (Fact.out : Q.Nondegenerate)).symm ∘
            ⇑(RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)) := by
      funext x
      apply (RestrictScalars.addEquiv ℝ ℂ (skewAdjointLieSubalgebra Q.polarBilin)).injective
      simpa using complexSpinToSpecialOrthogonalPolarCoordinateLieHom_eq_soEquivQuadratic_symm
        (Q := Q) x
    rw [heq]
    exact (RestrictScalars.addEquiv ℝ ℂ _).symm.bijective.comp
      ((soEquivQuadratic Q (Fact.out : Q.Nondegenerate)).symm.bijective.comp
        (RestrictScalars.addEquiv ℝ ℂ _).bijective)
  have hcomp : ⇑(complexSpinToSpecialOrthogonalRangeLieMap (Q := Q)) =
      ⇑(complexSpecialOrthogonalLieEquivSkewAdjoint (Q := Q)).symm ∘
        ⇑(complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q)) ∘
          ⇑(complexSpinLieEquivQuadratic (Q := Q)) := by
    funext X
    simp [complexSpinToSpecialOrthogonalPolarCoordinateLieHom_apply]
  rw [hcomp]
  exact (complexSpecialOrthogonalLieEquivSkewAdjoint (Q := Q)).symm.bijective.comp
    (hbij.comp (complexSpinLieEquivQuadratic (Q := Q)).bijective)

end TauCeti.CliffordAlgebra

namespace TauCeti.SpinPolarizationData

open TauCeti.CliffordAlgebra _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] NormedAlgebra.toNormedSpace
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)} (P : SpinPolarizationData Q)
  {κ : Type*} [Fintype κ] [DecidableEq κ]
  (b : Module.Basis κ ℂ (ExteriorAlgebra ℂ P.W)) [Fact Q.Nondegenerate]

private theorem unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothMatrixHom_symm
    (x : quadraticLieSubalgebra Q) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv
        (lieMap (P.complexSpinSmoothMatrixHom b)
          ((complexSpinLieEquivQuadratic (Q := Q)).symm
            ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x))) =
      ((LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (spinAction Q P)) x := by
  ext i j
  simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

/-- The real differential of the smooth Fock representation `P.complexSpinSmoothMatrixHom b`,
upgraded to a `ℂ`-linear Lie algebra homomorphism on `quadraticLieSubalgebra Q`. -/
def complexSpinSmoothMatrixComplexLieHom :
    quadraticLieSubalgebra Q →ₗ⁅ℂ⁆ Matrix κ κ ℂ where
  toFun x := TauCeti.Lie.unitsLieAlgebraLieEquiv
    (lieMap (P.complexSpinSmoothMatrixHom b)
      ((complexSpinLieEquivQuadratic (Q := Q)).symm
        ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)).symm x)))
  map_add' x y := by
    simp only [unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothMatrixHom_symm, map_add]
  map_smul' c x := by
    simp only [unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothMatrixHom_symm,
      SetLike.val_smul, map_smul, RingHom.id_apply]
  map_lie' {x y} := by
    simp only [unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothMatrixHom_symm,
      LieSubalgebra.coe_bracket]
    exact (((LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (spinAction Q P)).toLieHom).map_lie
      (x : CliffordAlgebra Q) (y : CliffordAlgebra Q)

/-- In the chosen spinor basis `b`, the `ℂ`-linear differentiated Fock representation acts by the
matrix of `spinAction Q P x`. -/
@[simp]
theorem complexSpinSmoothMatrixComplexLieHom_apply (x : quadraticLieSubalgebra Q) :
    P.complexSpinSmoothMatrixComplexLieHom b x = LinearMap.toMatrix b b (spinAction Q P x) := by
  change TauCeti.Lie.unitsLieAlgebraLieEquiv _ = _
  rw [unitsLieAlgebraLieEquiv_lieMap_complexSpinSmoothMatrixHom_symm]
  ext i j
  simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

/-- `P.complexSpinSmoothMatrixComplexLieHom b` equals the `ℂ`-linear matrix Fock algebra
homomorphism restricted to `quadraticLieSubalgebra Q`. -/
theorem complexSpinSmoothMatrixComplexLieHom_eq :
    P.complexSpinSmoothMatrixComplexLieHom b =
      (((LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (spinAction Q P)).toLieHom).comp
        (quadraticLieSubalgebra Q).incl := by
  ext x i j
  simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

/-- **Spin–SO differential intertwining on Clifford generators.** Bracketing the differentiated Fock
representation `d(spinRep)(x)` with the Fock operator of a vector `v` produces the Fock operator of
`d(spinToSpecialOrthogonal)(x) v`, where both differentials are computed from the smooth complex
group homomorphisms. -/
theorem lie_complexSpinSmoothMatrixComplexLieHom_ι_eq
    (x : quadraticLieSubalgebra Q) (v : Fin n → ℂ) :
    ⁅P.complexSpinSmoothMatrixComplexLieHom b x,
        LinearMap.toMatrix b b (spinAction Q P (ι Q v))⁆ =
      LinearMap.toMatrix b b
        (spinAction Q P
          (ι Q (((complexSpinToSpecialOrthogonalPolarComplexLieEquiv (Q := Q) x :
            skewAdjointLieSubalgebra Q.polarBilin) : Module.End ℂ (Fin n → ℂ)) v))) := by
  let φ : CliffordAlgebra Q →ₐ[ℂ] Matrix κ κ ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (spinAction Q P)
  have hφ (z : CliffordAlgebra Q) : LinearMap.toMatrix b b (spinAction Q P z) = φ z := by
    ext i j
    simp [φ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hlie : ⁅φ x, φ (ι Q v)⁆ = φ ⁅(x : CliffordAlgebra Q), ι Q v⁆ :=
    (φ.toLieHom.map_lie (x : CliffordAlgebra Q) (ι Q v)).symm
  rw [complexSpinSmoothMatrixComplexLieHom_apply, hφ, hφ, hφ, hlie,
    complexSpinToSpecialOrthogonalPolarComplexLieEquiv_lie_ι]

/-- Matrix-coordinate form of `lie_complexSpinSmoothMatrixComplexLieHom_ι_eq`. -/
theorem lie_complexSpinSmoothMatrixComplexLieHom_ι_eq_mulVec
    (x : quadraticLieSubalgebra Q) (v : Fin n → ℂ) :
    ⁅P.complexSpinSmoothMatrixComplexLieHom b x,
        LinearMap.toMatrix b b (spinAction Q P (ι Q v))⁆ =
      LinearMap.toMatrix b b
        (spinAction Q P
          (ι Q (((complexSpinToSpecialOrthogonalComplexLieEquiv (Q := Q) x :
            skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin)) :
              Matrix (Fin n) (Fin n) ℂ) *ᵥ v))) := by
  rw [lie_complexSpinSmoothMatrixComplexLieHom_ι_eq,
    complexSpinToSpecialOrthogonalPolarComplexLieEquiv_apply,
    complexSpinToSpecialOrthogonalComplexLieEquiv_apply,
    coe_complexSpinToSpecialOrthogonalPolarCoordinateLieHom_apply_apply]

end TauCeti.SpinPolarizationData
