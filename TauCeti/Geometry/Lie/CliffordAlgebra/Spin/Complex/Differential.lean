/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.UnitsDifferential
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
`complexSpinToSpecialOrthogonalComplexLieEquiv`. For a spin polarization `P`, the `ℂ`-linear Fock
differential `P.complexSpinSmoothMatrixComplexLieHom b` (constructed in
`TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Complex.Representation`) intertwines with the `SO(Q)`
differential on Clifford vector operators.

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
* `TauCeti.CliffordAlgebra.lieMap_complexSpinToSpecialOrthogonalSmoothRange_bijective`: the
  abstract real Lie map of the complex `Spin(Q) → SO(Q)` carrier projection is bijective.
* `TauCeti.SpinPolarizationData.lie_complexSpinSmoothMatrixComplexLieHom_ι_eq` and
  `TauCeti.SpinPolarizationData.lie_complexSpinSmoothMatrixComplexLieHom_ι_eq_mulVec`: the
  intertwining identities between the `ℂ`-linear differential of the Fock representation and the
  `SO(Q)` differential in endomorphism and matrix coordinates.

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

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)} [Fact Q.Nondegenerate]

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
  let D := complexSpinEmbeddedLieSubgroupData (Fact.out : Q.Nondegenerate)
  let X := (complexSpinLieEquivQuadratic (Q := Q)).symm x
  let A := ((RestrictScalars.addEquiv ℝ ℂ
    (skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin))
    (complexSpinToSpecialOrthogonalCoordinateLieHom (Q := Q) x)) : Matrix (Fin n) (Fin n) ℂ)
  let x₀ := RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q) x
  refine ι_mulVec_eq_lie_of_spinToSpecialOrthogonal_exp_curve (Q := Q)
    (AlgEquiv.refl : CliffordAlgebra Q ≃ₐ[ℝ] CliffordAlgebra Q) (x₀ : CliffordAlgebra Q) A
    (fun t : ℝ ↦ lieExp (t • X)) ?_ ?_ v
  · intro t
    rw [← TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply (d := D),
      D.coe_lieExp_smul X t, ← TauCeti.Lie.unitsLieAlgebraLieEquiv_apply,
      unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpinLieEquivQuadratic]
    simp only [X, LieEquiv.apply_symm_apply, x₀, AlgEquiv.coe_refl, id_eq]
  · intro t
    rw [← complexSpinToSpecialOrthogonalSmoothRange_apply,
      ← TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply
        (d := complexSpecialOrthogonalEmbeddedLieSubgroupData Q),
      D.coe_map_lieExp_smul (complexSpecialOrthogonalEmbeddedLieSubgroupData Q)
        (complexSpinToSpecialOrthogonalSmoothRange (Q := Q)) X t,
      ← TauCeti.Lie.unitsLieAlgebraLieEquiv_apply]
    rw [
unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpecialOrthogonalLieEquivSkewAdjointMatrices
    ]
    rw [← complexSpinToSpecialOrthogonalCoordinateLieHom_apply]

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
  let eB := TauCeti.skewAdjointLieEquivOfBasis (Pi.basisFun ℂ (Fin n)) Q.polarBilin hJ
  apply eB.injective
  dsimp only [LieEquiv.coe_toLieHom]
  rw [← coe_complexSpinToSpecialOrthogonalPolarCoordinateLieHom (Q := Q) x,
    complexSpinToSpecialOrthogonalPolarCoordinateLieHom_eq_soEquivQuadratic_symm]
  apply (soEquivQuadratic Q hQ).injective
  dsimp only [LieEquiv.coe_toLieHom]
  rw [LieEquiv.apply_symm_apply]
  refine quadraticLieSubalgebra_ext Q hQ fun v ↦ ?_
  rw [soEquivQuadratic_lie_ι, TauCeti.coe_skewAdjointLieEquivOfBasis_apply,
    ← skewAdjointMatricesEquivQuadratic_lie_ι Q hQ (Pi.basisFun ℂ (Fin n)) hJ,
    LieEquiv.apply_symm_apply]

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
  map_lie' {x y} := by
    rw [RestrictScalars.addEquiv_symm_lie, LieHom.map_lie, RestrictScalars.addEquiv_lie]

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
      skewAdjointMatricesLieSubalgebra (LinearMap.BilinForm.toMatrix' Q.polarBilin) :=
  (complexSpinToSpecialOrthogonalPolarComplexLieEquiv (Q := Q)).trans
    (TauCeti.skewAdjointLieEquivOfBasis (Pi.basisFun ℂ (Fin n)) Q.polarBilin
      (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)).symm

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
  let eB := TauCeti.skewAdjointLieEquivOfBasis (Pi.basisFun ℂ (Fin n)) Q.polarBilin
    (DFunLike.congr_fun LinearMap.BilinForm.toMatrix_basisFun Q.polarBilin)
  apply eB.injective
  dsimp only [LieEquiv.coe_toLieHom]
  rw [complexSpinToSpecialOrthogonalComplexLieEquiv, LieEquiv.trans_apply,
    LieEquiv.apply_symm_apply, complexSpinToSpecialOrthogonalPolarComplexLieEquiv_apply,
    coe_complexSpinToSpecialOrthogonalPolarCoordinateLieHom]

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
theorem lieMap_complexSpinToSpecialOrthogonalSmoothRange_bijective :
    Function.Bijective (lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))) := by
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
  have hcomp : ⇑(lieMap (complexSpinToSpecialOrthogonalSmoothRange (Q := Q))) =
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

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)} (P : SpinPolarizationData Q)
  {κ : Type*} [Fintype κ] [DecidableEq κ]
  (b : Module.Basis κ ℂ (ExteriorAlgebra ℂ P.W)) [Fact Q.Nondegenerate]

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
    simp [φ, LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply]
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
