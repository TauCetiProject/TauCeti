/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Naturality
public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Determinant

/-!
# The Lie-algebra projection splitting of compact `Spinᶜ`

The compact group `Spinᶜ(n)` sits in two smooth central double covers: the defining quotient
`Spin(n) × U(1) → Spinᶜ(n)` by `{1, (-1, -1)}` and the frame-and-determinant homomorphism
`Spinᶜ(n) → SO(n) × U(1)` sending `[s, z]` to `(π(s), z²)`.

Because `Spin(n) → SO(n)` has invertible differential and the determinant character has weight two
on the central circle, the paired smooth homomorphism `Spinᶜ(n) → SO(n) × U(1)` has bijective Lie
map and is therefore a smooth local diffeomorphism in every dimension. Its Lie-algebra equivalence
identifies `𝔰𝔭𝔦𝔫ᶜ(n)` with `𝔰𝔬(n) × ℝ`, where the inverse lifts an infinitesimal orthogonal
transformation `Ω` through `𝔰𝔭𝔦𝔫(n)` into the kernel of the determinant differential and lifts a
determinant parameter `a` by the half-speed central generator `realDetLieLift n hQ a`.

Naturality of the group adjoint along the smooth rotation homomorphism and `Ad`-invariance of the
determinant weight imply that the lifted orthogonal Lie homomorphism `realSpinOrthogonalLieLift`
intertwines the `Spinᶜ(n)` adjoint action with the `SO(n)` adjoint action through the descended
rotation map `Spinᶜ(n) → SO(n)`. Consequently, in any associated `Spinᶜ` bundle, the spin-Lie
action of an `𝔰𝔬(n)`-valued curvature form descends directly through `Spinᶜ(n)` without choosing a
separate global `Spin(n)` lift.

## Main definitions

* `CliffordAlgebra.spinCGroup.realMkSmoothHom`, `realOfSpinSmoothHom`, `realOfCircleSmoothHom`,
  `realDetSmoothHom`: the smooth homomorphisms of the defining cover and determinant character.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalSmoothRange` and
  `realToSpecialOrthogonalProdDetSmoothHom`: the smooth rotation and frame-and-determinant
  homomorphisms into the embedded `SO(n)` carrier and its product with `Circle`.
* `CliffordAlgebra.spinCGroup.realSpinOrthogonalLieLift` and `realSoLieLift`: the canonical
  Lie-algebra lift of `𝔰𝔬(n)` into `𝔰𝔭𝔦𝔫ᶜ(n)` via `𝔰𝔭𝔦𝔫(n)`.
* `CliffordAlgebra.spinCGroup.realOfSpinLieEquivDetKer`: the Lie-algebra equivalence between
  `𝔰𝔭𝔦𝔫(n)` and the kernel ideal of the determinant differential.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalProdDetLieEquiv`,
  `realToSpecialOrthogonalProdDetLinearEquiv`, and `realLinearEquivSoProdReal`: the Lie and
  weight-normalized splittings of `𝔰𝔭𝔦𝔫ᶜ(n)` into orthogonal and determinant components.

## Main results

* `CliffordAlgebra.spinCGroup.isLocalDiffeomorph_realToSpecialOrthogonalProdDet`: the smooth
  frame-and-determinant homomorphism `Spinᶜ(n) → SO(n) × U(1)` is a local diffeomorphism.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right`: shifting
  the determinant parameter by `b` shifts the lifted `𝔰𝔭𝔦𝔫ᶜ(n)` element by `realDetLieLift n hQ b`.
* `CliffordAlgebra.spinCGroup.Ad_realSpinOrthogonalLieLift` and
  `Ad_realToSpecialOrthogonalProdDetLinearEquiv_symm`: `Spinᶜ(n)`-equivariance of the orthogonal
  lift and full connection/curvature splitting.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Manifold TauCeti TauCeti.CliffordAlgebra
open scoped Manifold ContDiff Matrix.Norms.Operator

namespace CliffordAlgebra.spinCGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace

variable (n : ℕ) (hQ : realCliffordForm n 0 ≠ 0)

local notation "IS" => 𝓘(ℝ, realSpinLieModel n)
local notation "ISO" => 𝓘(ℝ, realSpecialOrthogonalLieModel n)
local notation "IC" => ModelWithCorners.prod IS (𝓡 1)
local notation "ISOProd" => ModelWithCorners.prod ISO (𝓡 1)
local notation "Spin" => spinGroup (realCliffordForm n 0)
local notation "SORange" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))
local notation "SpinC" => spinCGroup (realCliffordForm n 0) hQ
local notation "𝔤" => LeftInvariantDerivation IC SpinC
local notation "d" => ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ)

/-! ### Smooth homomorphisms on compact `Spinᶜ` -/

/-- The defining central quotient map `Spin(n) × U(1) → Spinᶜ(n)` as a smooth homomorphism. -/
def realMkSmoothHom : ContMDiffMonoidMorphism IC IC ∞ (Spin × Circle) SpinC where
  toMonoidHom := mk (realCliffordForm n 0) hQ
  contMDiff_toFun := (isLocalDiffeomorph_realMk n hQ).contMDiff

@[simp]
theorem realMkSmoothHom_apply (p : Spin × Circle) :
    realMkSmoothHom n hQ p = mk (realCliffordForm n 0) hQ p :=
  (rfl)

/-- The canonical inclusion `Spin(n) → Spinᶜ(n)` as a smooth homomorphism. -/
def realOfSpinSmoothHom : ContMDiffMonoidMorphism IS IC ∞ Spin SpinC :=
  (realMkSmoothHom n hQ).comp ContMDiffMonoidMorphism.inl

@[simp]
theorem realOfSpinSmoothHom_apply (s : Spin) :
    realOfSpinSmoothHom n hQ s = ofSpin (realCliffordForm n 0) hQ s := by
  simp only [realOfSpinSmoothHom, ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    ContMDiffMonoidMorphism.inl_apply, realMkSmoothHom_apply, ofSpin_apply]

/-- The central weight-one inclusion `U(1) → Spinᶜ(n)` as a smooth homomorphism. -/
def realOfCircleSmoothHom : ContMDiffMonoidMorphism (𝓡 1) IC ∞ Circle SpinC :=
  (realMkSmoothHom n hQ).comp ContMDiffMonoidMorphism.inr

@[simp]
theorem realOfCircleSmoothHom_apply (z : Circle) :
    realOfCircleSmoothHom n hQ z = ofCircle (realCliffordForm n 0) hQ z := by
  simp only [realOfCircleSmoothHom, ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    ContMDiffMonoidMorphism.inr_apply, realMkSmoothHom_apply, ofCircle_apply]

/-- The Lie map of `realOfCircleSmoothHom` agrees with the continuous Lie map of
`ofCircleContinuousMonoidHom`. -/
theorem lieMap_realOfCircleSmoothHom :
    lieMap (realOfCircleSmoothHom n hQ) =
      ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
        (ofCircleContinuousMonoidHom (realCliffordForm n 0) hQ) := by
  refine (congrArg _root_.lieMap ?_).trans
    (ContinuousMonoidHom.lieMap_def (I := 𝓡 1) (I' := IC)
      (ofCircleContinuousMonoidHom (realCliffordForm n 0) hQ)).symm
  apply DFunLike.coe_injective
  funext z
  rw [realOfCircleSmoothHom_apply, ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
    ofCircleContinuousMonoidHom_apply]

/-- The weight-two determinant character `Spinᶜ(n) → U(1)` as a smooth homomorphism. -/
def realDetSmoothHom : ContMDiffMonoidMorphism IC (𝓡 1) ∞ SpinC Circle where
  toMonoidHom := det (realCliffordForm n 0) hQ
  contMDiff_toFun := contMDiff_realDet n hQ

@[simp]
theorem realDetSmoothHom_apply (x : SpinC) :
    realDetSmoothHom n hQ x = det (realCliffordForm n 0) hQ x :=
  (rfl)

/-- The Lie map of `realDetSmoothHom` agrees with the continuous Lie map of
`detContinuousMonoidHom`. -/
theorem lieMap_realDetSmoothHom :
    lieMap (realDetSmoothHom n hQ) =
      ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1)
        (detContinuousMonoidHom (realCliffordForm n 0) hQ) := by
  refine (congrArg _root_.lieMap ?_).trans
    (ContinuousMonoidHom.lieMap_def (I := IC) (I' := 𝓡 1)
      (detContinuousMonoidHom (realCliffordForm n 0) hQ)).symm
  apply DFunLike.coe_injective
  funext x
  rw [realDetSmoothHom_apply, ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
    detContinuousMonoidHom_apply]

/-- The descended rotation homomorphism `Spinᶜ(n) → SO(n)` into the embedded special-orthogonal
matrix-units carrier, as a smooth homomorphism. -/
def realToSpecialOrthogonalSmoothRange : ContMDiffMonoidMorphism IC ISO ∞ SpinC SORange where
  toMonoidHom :=
    (realCliffordSpecialOrthogonalContinuousMulEquivRange n).toMulEquiv.toMonoidHom.comp
      (toSpecialOrthogonal (realCliffordForm n 0) hQ)
  contMDiff_toFun := by
    apply (contMDiff_iff_contMDiff_comp_mk n hQ _).mpr
    refine (((realSpinToSpecialOrthogonalSmoothRange n).contMDiff_toFun.comp
      contMDiff_fst).congr fun p ↦ ?_)
    exact (congrArg (realCliffordSpecialOrthogonalContinuousMulEquivRange n)
      (toSpecialOrthogonal_mk (realCliffordForm n 0) hQ p)).trans
      (realSpinToSpecialOrthogonalSmoothRange_apply n p.1).symm

@[simp]
theorem realToSpecialOrthogonalSmoothRange_apply (x : SpinC) :
    realToSpecialOrthogonalSmoothRange n hQ x =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (toSpecialOrthogonal (realCliffordForm n 0) hQ x) :=
  (rfl)

@[simp]
theorem realToSpecialOrthogonalSmoothRange_comp_ofSpin :
    (realToSpecialOrthogonalSmoothRange n hQ).comp (realOfSpinSmoothHom n hQ) =
      realSpinToSpecialOrthogonalSmoothRange n :=
  DFunLike.coe_injective <| funext fun s ↦ by simp [toSpecialOrthogonal_ofSpin]

@[simp]
theorem realToSpecialOrthogonalSmoothRange_comp_ofCircle :
    (realToSpecialOrthogonalSmoothRange n hQ).comp (realOfCircleSmoothHom n hQ) = 1 :=
  DFunLike.coe_injective <| funext fun z ↦ by simp [toSpecialOrthogonal_ofCircle]; rfl

@[simp]
theorem realDetSmoothHom_comp_ofSpin :
    (realDetSmoothHom n hQ).comp (realOfSpinSmoothHom n hQ) = 1 :=
  DFunLike.coe_injective <| funext fun s ↦ by simp [det_ofSpin]; rfl

/-- The paired frame-and-determinant smooth homomorphism `Spinᶜ(n) → SO(n) × U(1)`. -/
def realToSpecialOrthogonalProdDetSmoothHom :
    ContMDiffMonoidMorphism IC ISOProd ∞ SpinC (SORange × Circle) :=
  (realToSpecialOrthogonalSmoothRange n hQ).prod (realDetSmoothHom n hQ)

@[simp]
theorem realToSpecialOrthogonalProdDetSmoothHom_apply (x : SpinC) :
    realToSpecialOrthogonalProdDetSmoothHom n hQ x =
      (realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (toSpecialOrthogonal (realCliffordForm n 0) hQ x),
        det (realCliffordForm n 0) hQ x) :=
  ContMDiffMonoidMorphism.prod_apply (realToSpecialOrthogonalSmoothRange n hQ)
    (realDetSmoothHom n hQ) x

/-! ### The defining cover and the Spin lift of `𝔰𝔬(n)` -/

/-- The Lie-algebra equivalence `(𝔰𝔭𝔦𝔫(n) × Lie(U(1))) ≃ₗ⁅ℝ⁆ 𝔰𝔭𝔦𝔫ᶜ(n)` induced by the defining
central double cover. -/
def realMkLieEquiv :
    (LeftInvariantDerivation IS Spin × LeftInvariantDerivation (𝓡 1) Circle) ≃ₗ⁅ℝ⁆ 𝔤 :=
  (TauCeti.Lie.prodLieEquiv (I := IS) (I' := 𝓡 1)).symm.trans
    (TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt (realMkSmoothHom n hQ)
      (isLocalDiffeomorph_realMk n hQ 1))

/-- The defining-cover Lie equivalence sums the differentials of `ofSpin` and `ofCircle`. -/
@[simp]
theorem realMkLieEquiv_apply
    (p : LeftInvariantDerivation IS Spin × LeftInvariantDerivation (𝓡 1) Circle) :
    realMkLieEquiv n hQ p =
      lieMap (realOfSpinSmoothHom n hQ) p.1 + lieMap (realOfCircleSmoothHom n hQ) p.2 := by
  have h1 := (DFunLike.congr_fun
    (lieMap_comp (ContMDiffMonoidMorphism.inl (I := IS) (I' := 𝓡 1) (G := Spin) (G' := Circle))
      (realMkSmoothHom n hQ)) p.1).symm
  have h2 := (DFunLike.congr_fun
    (lieMap_comp (ContMDiffMonoidMorphism.inr (I := IS) (I' := 𝓡 1) (G := Spin) (G' := Circle))
      (realMkSmoothHom n hQ)) p.2).symm
  exact (TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply _ _ _).trans <|
    (congrArg (lieMap (realMkSmoothHom n hQ)) (TauCeti.Lie.prodLieEquiv_symm_eq_add p)).trans <|
      ((lieMap (realMkSmoothHom n hQ)).map_add _ _).trans (congrArg₂ HAdd.hAdd h1 h2)

/-- The differential of `ofSpin : Spin(n) → Spinᶜ(n)` is injective. -/
theorem lieMap_realOfSpinSmoothHom_injective :
    Function.Injective (lieMap (realOfSpinSmoothHom n hQ)) := fun X Y hXY ↦ by
  have h (Z) : realMkLieEquiv n hQ (Z, 0) = lieMap (realOfSpinSmoothHom n hQ) Z :=
    (realMkLieEquiv_apply n hQ (Z, 0)).trans <|
      (congrArg _ (lieMap (realOfCircleSmoothHom n hQ)).map_zero).trans (add_zero _)
  exact congrArg Prod.fst <| (realMkLieEquiv n hQ).injective <| (h X).trans (hXY.trans (h Y).symm)

/-- The differential of `det` vanishes on the image of `𝔰𝔭𝔦𝔫(n)`. -/
@[simp]
theorem lieMap_realDetSmoothHom_lieMap_realOfSpinSmoothHom
    (X : LeftInvariantDerivation IS Spin) :
    lieMap (realDetSmoothHom n hQ) (lieMap (realOfSpinSmoothHom n hQ) X) = 0 :=
  (DFunLike.congr_fun
    (lieMap_comp (realOfSpinSmoothHom n hQ) (realDetSmoothHom n hQ)) X).symm.trans
    ((DFunLike.congr_fun
      (congrArg _root_.lieMap (realDetSmoothHom_comp_ofSpin n hQ)) X).trans
      ((DFunLike.congr_fun lieMap_one X).trans (zero_apply X)))

/-- The determinant differential vanishes on the image of `𝔰𝔭𝔦𝔫(n)` in `𝔰𝔭𝔦𝔫ᶜ(n)`. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_lieMap_realOfSpinSmoothHom
    (X : LeftInvariantDerivation IS Spin) :
    d (lieMap (realOfSpinSmoothHom n hQ) X) = 0 :=
  (ContinuousMonoidHom.lieWeight_apply (I := IC) (detContinuousMonoidHom _ hQ) _).trans <|
    (congrArg circleLieAlgebraEquiv <| DFunLike.congr_fun (lieMap_realDetSmoothHom n hQ).symm
      (lieMap (realOfSpinSmoothHom n hQ) X)).trans <|
      (congrArg circleLieAlgebraEquiv
        (lieMap_realDetSmoothHom_lieMap_realOfSpinSmoothHom n hQ X)).trans
        circleLieAlgebraEquiv.map_zero

/-- On the central circle Lie algebra, the differential of `det` acts by multiplication by `2`. -/
@[simp]
theorem lieMap_realDetSmoothHom_lieMap_realOfCircleSmoothHom
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    lieMap (realDetSmoothHom n hQ) (lieMap (realOfCircleSmoothHom n hQ) Z) = (2 : ℝ) • Z := by
  apply circleLieAlgebraEquiv.injective
  have hsmul : 2 * circleLieAlgebraEquiv Z = circleLieAlgebraEquiv ((2 : ℝ) • Z) := by
    rw [map_smul, smul_eq_mul]
  exact ((congrArg circleLieAlgebraEquiv <| DFunLike.congr_fun (lieMap_realDetSmoothHom n hQ)
      (lieMap (realOfCircleSmoothHom n hQ) Z)).trans <|
    (ContinuousMonoidHom.lieWeight_apply (I := IC) (detContinuousMonoidHom _ hQ) _).symm.trans <|
      congrArg d (DFunLike.congr_fun (lieMap_realOfCircleSmoothHom n hQ) Z)).trans
    ((lieWeight_detContinuousMonoidHom_lieMap_ofCircleContinuousMonoidHom n hQ Z).trans hsmul)

/-- On `𝔰𝔭𝔦𝔫(n)`, the differential of the descended rotation homomorphism recovers the differential
of the Spin projection. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom
    (X : LeftInvariantDerivation IS Spin) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (lieMap (realOfSpinSmoothHom n hQ) X) =
      realSpinToSpecialOrthogonalRangeLieEquiv n X :=
  (DFunLike.congr_fun (lieMap_comp (realOfSpinSmoothHom n hQ)
    (realToSpecialOrthogonalSmoothRange n hQ)) X).symm.trans <|
    (DFunLike.congr_fun
      (congrArg _root_.lieMap (realToSpecialOrthogonalSmoothRange_comp_ofSpin n hQ)) X).trans
      (realSpinToSpecialOrthogonalRangeLieEquiv_apply n X).symm

/-- The differential of the descended rotation homomorphism vanishes on the central circle. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (lieMap (realOfCircleSmoothHom n hQ) Z) =
      0 :=
  (DFunLike.congr_fun (lieMap_comp (realOfCircleSmoothHom n hQ)
    (realToSpecialOrthogonalSmoothRange n hQ)) Z).symm.trans
    ((DFunLike.congr_fun
      (congrArg _root_.lieMap (realToSpecialOrthogonalSmoothRange_comp_ofCircle n hQ)) Z).trans
      ((DFunLike.congr_fun lieMap_one Z).trans (zero_apply Z)))

/-- The differential of the descended rotation homomorphism vanishes on `realDetLieLift`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_realDetLieLift (a : ℝ) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realDetLieLift n hQ a) = 0 :=
  (congrArg (lieMap (realToSpecialOrthogonalSmoothRange n hQ)) <|
    (realDetLieLift_apply n hQ a).trans <|
      DFunLike.congr_fun (lieMap_realOfCircleSmoothHom n hQ).symm _).trans
    (lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom n hQ _)

/-- The canonical Lie-algebra lift `𝔰𝔬(n) →ₗ⁅ℝ⁆ 𝔰𝔭𝔦𝔫ᶜ(n)`, obtained by inverting the differential
of `Spin(n) → SO(n)` and pushing forward along `ofSpin : Spin(n) → Spinᶜ(n)`. Unlike the
group-level maps, this infinitesimal lift exists canonically with no choice of sign. -/
def realSpinOrthogonalLieLift : LeftInvariantDerivation ISO SORange →ₗ⁅ℝ⁆ 𝔤 :=
  (lieMap (realOfSpinSmoothHom n hQ)).comp
    (realSpinToSpecialOrthogonalRangeLieEquiv n).symm.toLieHom

theorem realSpinOrthogonalLieLift_apply (Ω : LeftInvariantDerivation ISO SORange) :
    realSpinOrthogonalLieLift n hQ Ω =
      lieMap (realOfSpinSmoothHom n hQ) ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω) :=
  (rfl)

/-- The orthogonal Lie lift is a right inverse of the differential of `Spinᶜ(n) → SO(n)`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_realSpinOrthogonalLieLift
    (Ω : LeftInvariantDerivation ISO SORange) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realSpinOrthogonalLieLift n hQ Ω) = Ω :=
  (congrArg (lieMap (realToSpecialOrthogonalSmoothRange n hQ))
    (realSpinOrthogonalLieLift_apply n hQ Ω)).trans
    ((lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom n hQ _).trans
      ((realSpinToSpecialOrthogonalRangeLieEquiv n).apply_symm_apply Ω))

/-- The orthogonal Lie lift lands in the kernel of the determinant differential. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realSpinOrthogonalLieLift
    (Ω : LeftInvariantDerivation ISO SORange) :
    d (realSpinOrthogonalLieLift n hQ Ω) = 0 :=
  lieWeight_detContinuousMonoidHom_lieMap_realOfSpinSmoothHom n hQ _

/-- The orthogonal Lie lift lands in the kernel of `lieMap (realDetSmoothHom n hQ)`. -/
@[simp]
theorem lieMap_realDetSmoothHom_realSpinOrthogonalLieLift
    (Ω : LeftInvariantDerivation ISO SORange) :
    lieMap (realDetSmoothHom n hQ) (realSpinOrthogonalLieLift n hQ Ω) = 0 :=
  lieMap_realDetSmoothHom_lieMap_realOfSpinSmoothHom n hQ _

/-- The canonical Lie-algebra lift `so(n, ℝ) →ₗ⁅ℝ⁆ 𝔰𝔭𝔦𝔫ᶜ(n)` in skew-symmetric matrix
coordinates. -/
def realSoLieLift : LieAlgebra.Orthogonal.so (Fin n) ℝ →ₗ⁅ℝ⁆ 𝔤 :=
  (realSpinOrthogonalLieLift n hQ).comp (realCliffordSpecialOrthogonalLieEquivSo n).symm.toLieHom

theorem realSoLieLift_apply (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    realSoLieLift n hQ A =
      realSpinOrthogonalLieLift n hQ ((realCliffordSpecialOrthogonalLieEquivSo n).symm A) :=
  (rfl)

/-! ### Bijectivity and local diffeomorphism of `Spinᶜ(n) → SO(n) × U(1)` -/

private theorem prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_apply (Y : 𝔤) :
    TauCeti.Lie.prodLieEquiv (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ) Y) =
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y, lieMap (realDetSmoothHom n hQ) Y) :=
  TauCeti.Lie.prodLieEquiv_lieMap_prod (realToSpecialOrthogonalSmoothRange n hQ)
    (realDetSmoothHom n hQ) Y

private theorem prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_lift
    (p : LeftInvariantDerivation ISO SORange × LeftInvariantDerivation (𝓡 1) Circle) :
    TauCeti.Lie.prodLieEquiv (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ)
      (realSpinOrthogonalLieLift n hQ p.1 +
        lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2))) = p := by
  have hhalf : (2 : ℝ) • ((1 / 2 : ℝ) • p.2) = p.2 := by rw [smul_smul]; norm_num
  refine (prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_apply n hQ _).trans (Prod.ext ?_ ?_)
  · exact (map_add (lieMap (realToSpecialOrthogonalSmoothRange n hQ)) _ _).trans <|
      (congrArg₂ HAdd.hAdd
        (lieMap_realToSpecialOrthogonalSmoothRange_realSpinOrthogonalLieLift n hQ p.1)
        (lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom n hQ _)).trans
        (add_zero p.1)
  · exact (map_add (lieMap (realDetSmoothHom n hQ)) _ _).trans <|
      (congrArg₂ HAdd.hAdd (lieMap_realDetSmoothHom_realSpinOrthogonalLieLift n hQ p.1)
        ((lieMap_realDetSmoothHom_lieMap_realOfCircleSmoothHom n hQ _).trans hhalf)).trans
        (zero_add p.2)

/-- Reconstructing an element of `𝔰𝔭𝔦𝔫ᶜ(n)` from its orthogonal projection and determinant weight
recovers the element. -/
theorem realSpinOrthogonalLieLift_add_realDetLieLift (Y : 𝔤) :
    realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y) +
        realDetLieLift n hQ (d Y) =
      Y := by
  let p := (realMkLieEquiv n hQ).symm Y
  have hYZ : lieMap (realOfSpinSmoothHom n hQ) p.1 + lieMap (realOfCircleSmoothHom n hQ) p.2 = Y :=
    (realMkLieEquiv_apply n hQ (p.1, p.2)).symm.trans ((realMkLieEquiv n hQ).apply_symm_apply Y)
  have hSO : lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y =
      realSpinToSpecialOrthogonalRangeLieEquiv n p.1 :=
    (congrArg _ hYZ.symm).trans <| (map_add _ _ _).trans <| (congrArg₂ HAdd.hAdd
      (lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom n hQ p.1)
      (lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom n hQ p.2)).trans
      (add_zero _)
  have hdY : d Y = 2 * circleLieAlgebraEquiv p.2 :=
    (congrArg d hYZ.symm).trans <| (map_add d _ _).trans <| (congrArg₂ HAdd.hAdd
      (lieWeight_detContinuousMonoidHom_lieMap_realOfSpinSmoothHom n hQ p.1)
      (congrArg d (DFunLike.congr_fun (lieMap_realOfCircleSmoothHom n hQ) p.2))).trans <|
      (zero_add _).trans
        (lieWeight_detContinuousMonoidHom_lieMap_ofCircleContinuousMonoidHom n hQ p.2)
  have h1 : realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y) =
      lieMap (realOfSpinSmoothHom n hQ) p.1 :=
    (congrArg (realSpinOrthogonalLieLift n hQ) hSO).trans <|
      (realSpinOrthogonalLieLift_apply n hQ _).trans <|
        congrArg (lieMap (realOfSpinSmoothHom n hQ))
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm_apply_apply p.1)
  have harg : circleLieAlgebraEquiv.symm (2 * circleLieAlgebraEquiv p.2 / 2) = p.2 := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, LinearEquiv.symm_apply_apply]
  have h2 : realDetLieLift n hQ (d Y) = lieMap (realOfCircleSmoothHom n hQ) p.2 :=
    (congrArg (realDetLieLift n hQ) hdY).trans <| (realDetLieLift_apply n hQ _).trans <|
      (congrArg _ harg).trans (DFunLike.congr_fun (lieMap_realOfCircleSmoothHom n hQ).symm p.2)
  exact (congrArg₂ HAdd.hAdd h1 h2).trans hYZ

/-- The Lie map of the paired smooth homomorphism `Spinᶜ(n) → SO(n) × U(1)` is bijective in every
dimension. -/
theorem lieMap_realToSpecialOrthogonalProdDet_bijective :
    Function.Bijective (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ)) :=
  ⟨fun Y₁ Y₂ h ↦ by
    have hprod := (prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_apply n hQ Y₁).symm.trans <|
      (congrArg (TauCeti.Lie.prodLieEquiv (I := ISO) (I' := 𝓡 1)) h).trans
        (prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_apply n hQ Y₂)
    have hd : d Y₁ = d Y₂ :=
      ((ContinuousMonoidHom.lieWeight_apply (I := IC) (detContinuousMonoidHom _ hQ) Y₁).trans
        (congrArg circleLieAlgebraEquiv
          (DFunLike.congr_fun (lieMap_realDetSmoothHom n hQ).symm Y₁))).trans
        ((congrArg circleLieAlgebraEquiv (congrArg Prod.snd hprod)).trans <|
          (congrArg circleLieAlgebraEquiv
            (DFunLike.congr_fun (lieMap_realDetSmoothHom n hQ) Y₂)).trans
            (ContinuousMonoidHom.lieWeight_apply (I := IC) (detContinuousMonoidHom _ hQ) Y₂).symm)
    exact (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y₁).symm.trans <|
      (congrArg₂ HAdd.hAdd (congrArg (realSpinOrthogonalLieLift n hQ) (congrArg Prod.fst hprod))
        (congrArg (realDetLieLift n hQ) hd)).trans
        (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y₂),
  fun P ↦ ⟨_, (TauCeti.Lie.prodLieEquiv (I := ISO) (I' := 𝓡 1)).injective <|
    prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_lift n hQ
      (TauCeti.Lie.prodLieEquiv (I := ISO) (I' := 𝓡 1) P)⟩⟩

/-- **The frame-and-determinant map `Spinᶜ(n) → SO(n) × U(1)` is a smooth local diffeomorphism.** -/
theorem isLocalDiffeomorph_realToSpecialOrthogonalProdDet :
    IsLocalDiffeomorph IC ISOProd ∞ (realToSpecialOrthogonalProdDetSmoothHom n hQ) :=
  (realToSpecialOrthogonalProdDetSmoothHom n hQ).isLocalDiffeomorph_of_lieMap_bijective
    (lieMap_realToSpecialOrthogonalProdDet_bijective n hQ)

/-- The Lie-algebra equivalence `𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ⁅ℝ⁆ (𝔰𝔬(n) × Lie(U(1)))` induced by the smooth
frame-and-determinant homomorphism. -/
def realToSpecialOrthogonalProdDetLieEquiv :
    𝔤 ≃ₗ⁅ℝ⁆ (LeftInvariantDerivation ISO SORange × LeftInvariantDerivation (𝓡 1) Circle) :=
  (TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt (realToSpecialOrthogonalProdDetSmoothHom n hQ)
    (isLocalDiffeomorph_realToSpecialOrthogonalProdDet n hQ 1)).trans
      (TauCeti.Lie.prodLieEquiv (I := ISO) (I' := 𝓡 1))

@[simp]
theorem realToSpecialOrthogonalProdDetLieEquiv_apply (Y : 𝔤) :
    realToSpecialOrthogonalProdDetLieEquiv n hQ Y =
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y, lieMap (realDetSmoothHom n hQ) Y) :=
  (congrArg TauCeti.Lie.prodLieEquiv
    (TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply _ _ Y)).trans
    (prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_apply n hQ Y)

@[simp]
theorem realToSpecialOrthogonalProdDetLieEquiv_symm_apply
    (p : LeftInvariantDerivation ISO SORange × LeftInvariantDerivation (𝓡 1) Circle) :
    (realToSpecialOrthogonalProdDetLieEquiv n hQ).symm p =
      realSpinOrthogonalLieLift n hQ p.1 +
        lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2) :=
  (realToSpecialOrthogonalProdDetLieEquiv n hQ).injective <|
    ((realToSpecialOrthogonalProdDetLieEquiv n hQ).apply_symm_apply p).trans <|
      ((realToSpecialOrthogonalProdDetLieEquiv_apply n hQ _).trans <|
        (prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_apply n hQ _).symm.trans
          (prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_lift n hQ p)).symm

/-! ### Identification of the determinant kernel with `𝔰𝔭𝔦𝔫(n)` -/

/-- Membership in the kernel ideal of `det`'s Lie map is vanishing of the determinant weight. -/
theorem mem_ker_lieMap_detContinuousMonoidHom_iff (Y : 𝔤) :
    Y ∈ (ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1) (detContinuousMonoidHom _ hQ)).ker ↔
      d Y = 0 := by
  have hw := ContinuousMonoidHom.lieWeight_apply (I := IC) (detContinuousMonoidHom _ hQ) Y
  exact LieHom.mem_ker.trans
    ⟨fun h ↦ hw.trans ((congrArg circleLieAlgebraEquiv h).trans circleLieAlgebraEquiv.map_zero),
      fun h ↦ circleLieAlgebraEquiv.injective
        ((hw.symm.trans h).trans circleLieAlgebraEquiv.map_zero.symm)⟩

/-- The Lie-algebra equivalence `𝔰𝔭𝔦𝔫(n) ≃ₗ⁅ℝ⁆ ker(d det)` induced by `ofSpin`. -/
def realOfSpinLieEquivDetKer :
    LeftInvariantDerivation IS Spin ≃ₗ⁅ℝ⁆
      (ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1) (detContinuousMonoidHom _ hQ)).ker :=
  LieEquiv.ofBijective
    { toLinearMap := (lieMap (realOfSpinSmoothHom n hQ)).toLinearMap.codRestrict
        (ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1)
          (detContinuousMonoidHom _ hQ)).ker.toSubmodule
        fun X ↦ (mem_ker_lieMap_detContinuousMonoidHom_iff n hQ _).mpr
          (lieWeight_detContinuousMonoidHom_lieMap_realOfSpinSmoothHom n hQ X)
      map_lie' := by
        intro X Y; apply Subtype.ext; exact (lieMap (realOfSpinSmoothHom n hQ)).map_lie X Y }
    ⟨fun X Y h ↦ lieMap_realOfSpinSmoothHom_injective n hQ (congrArg Subtype.val h),
      fun Y ↦ by
        have hdv : d Y.1 = 0 := (mem_ker_lieMap_detContinuousMonoidHom_iff n hQ Y.1).mp Y.2
        refine ⟨(realSpinToSpecialOrthogonalRangeLieEquiv n).symm
          (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1), Subtype.ext ?_⟩
        exact ((add_zero _).symm.trans <| congrArg
          (realSpinOrthogonalLieLift n hQ
              (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1) + ·)
          ((realDetLieLift n hQ).map_zero.symm.trans
            (congrArg (realDetLieLift n hQ) hdv.symm))).trans
          (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y.1)⟩

@[simp]
theorem coe_realOfSpinLieEquivDetKer_apply (X : LeftInvariantDerivation IS Spin) :
    (realOfSpinLieEquivDetKer n hQ X : 𝔤) = lieMap (realOfSpinSmoothHom n hQ) X :=
  (rfl)

/-! ### Weight-normalized connection and curvature splitting -/

/-- The weight-normalized linear equivalence `𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ[ℝ] (𝔰𝔬(n) × ℝ)` pairing the differential
of the rotation map `Spinᶜ(n) → SO(n)` with the determinant weight `d`. Its inverse lifts `(Ω, a)`
to `realSpinOrthogonalLieLift n hQ Ω + realDetLieLift n hQ a`, encoding the unique compatible
`Spinᶜ` connection and curvature decomposition from an orthogonal part `Ω` and unitary determinant
part `a`. -/
def realToSpecialOrthogonalProdDetLinearEquiv :
    𝔤 ≃ₗ[ℝ] (LeftInvariantDerivation ISO SORange × ℝ) :=
  (realToSpecialOrthogonalProdDetLieEquiv n hQ).toLinearEquiv.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ _) circleLieAlgebraEquiv)

@[simp]
theorem realToSpecialOrthogonalProdDetLinearEquiv_apply (Y : 𝔤) :
    realToSpecialOrthogonalProdDetLinearEquiv n hQ Y =
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y, d Y) :=
  (LinearEquiv.trans_apply Y).trans <|
    (congrArg ((LinearEquiv.refl ℝ _).prodCongr circleLieAlgebraEquiv)
      (realToSpecialOrthogonalProdDetLieEquiv_apply n hQ Y)).trans <|
      (LinearEquiv.prodCongr_apply _ _ _).trans <| Prod.ext rfl <|
        (congrArg circleLieAlgebraEquiv
          (DFunLike.congr_fun (lieMap_realDetSmoothHom n hQ) Y)).trans
          (ContinuousMonoidHom.lieWeight_apply (I := IC) _ Y).symm

@[simp]
theorem realToSpecialOrthogonalProdDetLinearEquiv_symm_apply
    (p : LeftInvariantDerivation ISO SORange × ℝ) :
    (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm p =
      realSpinOrthogonalLieLift n hQ p.1 + realDetLieLift n hQ p.2 :=
  (realToSpecialOrthogonalProdDetLinearEquiv n hQ).injective <|
    ((realToSpecialOrthogonalProdDetLinearEquiv n hQ).apply_symm_apply p).trans <|
      ((realToSpecialOrthogonalProdDetLinearEquiv_apply n hQ _).trans <| Prod.ext
        ((map_add (lieMap (realToSpecialOrthogonalSmoothRange n hQ)) _ _).trans <|
          (congrArg₂ HAdd.hAdd
            (lieMap_realToSpecialOrthogonalSmoothRange_realSpinOrthogonalLieLift n hQ p.1)
            (lieMap_realToSpecialOrthogonalSmoothRange_realDetLieLift n hQ p.2)).trans
            (add_zero p.1))
        ((map_add d _ _).trans <|
          (congrArg₂ HAdd.hAdd
            (lieWeight_detContinuousMonoidHom_realSpinOrthogonalLieLift n hQ p.1)
            (lieWeight_detContinuousMonoidHom_realDetLieLift n hQ p.2)).trans
            (zero_add p.2))).symm

/-- In skew-symmetric matrix coordinates, `𝔰𝔭𝔦𝔫ᶜ(n)` splits linearly as `so(n, ℝ) × ℝ`. -/
def realLinearEquivSoProdReal : 𝔤 ≃ₗ[ℝ] (LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :=
  (realToSpecialOrthogonalProdDetLinearEquiv n hQ).trans
    (LinearEquiv.prodCongr (realCliffordSpecialOrthogonalLieEquivSo n).toLinearEquiv
      (LinearEquiv.refl ℝ ℝ))

@[simp]
theorem realLinearEquivSoProdReal_apply (Y : 𝔤) :
    realLinearEquivSoProdReal n hQ Y =
      (realCliffordSpecialOrthogonalLieEquivSo n
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y), d Y) :=
  (LinearEquiv.trans_apply Y).trans
    ((congrArg _ (realToSpecialOrthogonalProdDetLinearEquiv_apply n hQ Y)).trans
      (LinearEquiv.prodCongr_apply _ _ _))

@[simp]
theorem realLinearEquivSoProdReal_symm_apply
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    (realLinearEquivSoProdReal n hQ).symm p =
      realSoLieLift n hQ p.1 + realDetLieLift n hQ p.2 :=
  realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ
    ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1, p.2)

/-- **Affine shift in the determinant component.** Shifting the determinant parameter by `b` adds
the half-speed central lift `realDetLieLift n hQ b` while leaving the orthogonal part unchanged. -/
theorem realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right
    (Ω : LeftInvariantDerivation ISO SORange) (a b : ℝ) :
    (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a + b) =
      (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a) + realDetLieLift n hQ b :=
  (realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (Ω, a + b)).trans <|
    (congrArg (realSpinOrthogonalLieLift n hQ Ω + ·) ((realDetLieLift n hQ).map_add a b)).trans <|
      (add_assoc _ _ _).symm.trans <| congrArg (· + realDetLieLift n hQ b)
        (realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (Ω, a)).symm

/-- The Lie bracket of two lifted pairs `(Ω₁, a₁)` and `(Ω₂, a₂)` depends only on the orthogonal
bracket `⁅Ω₁, Ω₂⁆`, because the central determinant lift brackets trivially. -/
theorem lie_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (Ω₁ Ω₂ : LeftInvariantDerivation ISO SORange) (a₁ a₂ : ℝ) :
    ⁅(realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω₁, a₁),
        (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω₂, a₂)⁆ =
      realSpinOrthogonalLieLift n hQ ⁅Ω₁, Ω₂⁆ := by
  let U₁ := realSpinOrthogonalLieLift n hQ Ω₁
  let U₂ := realSpinOrthogonalLieLift n hQ Ω₂
  let Z₁ := realDetLieLift n hQ a₁
  let Z₂ := realDetLieLift n hQ a₂
  refine (congrArg₂ Bracket.bracket
      (realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (Ω₁, a₁))
      (realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (Ω₂, a₂))).trans <|
    ((add_lie U₁ Z₁ (U₂ + Z₂)).trans
      (congrArg₂ HAdd.hAdd (lie_add U₁ U₂ Z₂) (lie_add Z₁ U₂ Z₂))).trans ?_
  exact (congrArg₂ HAdd.hAdd (congrArg (⁅U₁, U₂⁆ + ·) (lie_realDetLieLift n hQ U₁ a₂))
      (congrArg₂ HAdd.hAdd (realDetLieLift_lie n hQ a₁ U₂)
        (lie_realDetLieLift n hQ Z₁ a₂))).trans <|
    (congrArg₂ HAdd.hAdd (add_zero _) (add_zero _)).trans <|
      (add_zero _).trans ((realSpinOrthogonalLieLift n hQ).map_lie Ω₁ Ω₂).symm

/-- Exponentiating a lifted pair `(Ω, a)` multiplies the `Spin` lift of `exp Ω` by the half-speed
central phase `ofCircle _ hQ (Circle.exp (a / 2))`. -/
theorem lieExp_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (Ω : LeftInvariantDerivation ISO SORange) (a : ℝ) :
    lieExp ((realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) =
      ofSpin _ hQ (lieExp ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)) *
        ofCircle _ hQ (Circle.exp (a / 2)) :=
  (congrArg (fun X : 𝔤 ↦ lieExp X)
    (realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (Ω, a))).trans <|
    (lieExp_add_realDetLieLift n hQ _ a).trans <|
      congrArg (· * ofCircle _ hQ (Circle.exp (a / 2))) <|
        (map_lieExp (realOfSpinSmoothHom n hQ)
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)).symm.trans
          (realOfSpinSmoothHom_apply n hQ _)

/-! ### `Spinᶜ` adjoint equivariance of the orthogonal lift -/

/-- Under the connection-splitting equivalence, the `Spinᶜ(n)` adjoint action acts on the
orthogonal component through the descended rotation map `Spinᶜ(n) → SO(n)` and fixes the
determinant weight. -/
theorem realToSpecialOrthogonalProdDetLinearEquiv_Ad (g : SpinC) (Y : 𝔤) :
    realToSpecialOrthogonalProdDetLinearEquiv n hQ (TauCeti.Lie.Ad (I := IC) g Y) =
      (TauCeti.Lie.Ad (I := ISO) (realToSpecialOrthogonalSmoothRange n hQ g)
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y), d Y) :=
  (realToSpecialOrthogonalProdDetLinearEquiv_apply n hQ (TauCeti.Lie.Ad (I := IC) g Y)).trans
    (Prod.ext (lieMap_Ad (realToSpecialOrthogonalSmoothRange n hQ) g Y)
      (ContinuousMonoidHom.lieWeight_Ad (detContinuousMonoidHom _ hQ) g Y))

/-- **Adjoint equivariance of the connection/curvature lift.** Conjugating a lifted pair `(Ω, a)`
by `g ∈ Spinᶜ(n)` acts on `Ω` by the `SO(n)` adjoint of the descended rotation of `g` and fixes
`a`. -/
theorem Ad_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (g : SpinC) (Ω : LeftInvariantDerivation ISO SORange) (a : ℝ) :
    TauCeti.Lie.Ad (I := IC) g ((realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) =
      (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm
        (TauCeti.Lie.Ad (I := ISO) (realToSpecialOrthogonalSmoothRange n hQ g) Ω, a) := by
  let L := realToSpecialOrthogonalProdDetLinearEquiv n hQ
  have hp := (realToSpecialOrthogonalProdDetLinearEquiv_apply n hQ (L.symm (Ω, a))).symm.trans
    (L.apply_symm_apply (Ω, a))
  have hSO : lieMap (realToSpecialOrthogonalSmoothRange n hQ) (L.symm (Ω, a)) = Ω :=
    congrArg Prod.fst hp
  have hd : d (L.symm (Ω, a)) = a := congrArg Prod.snd hp
  exact L.injective <| (realToSpecialOrthogonalProdDetLinearEquiv_Ad n hQ g (L.symm (Ω, a))).trans
    ((Prod.ext (congrArg (TauCeti.Lie.Ad (I := ISO) (realToSpecialOrthogonalSmoothRange n hQ g))
      hSO) hd).trans (L.apply_symm_apply _).symm)

/-- **`Spinᶜ` equivariance of the lifted orthogonal Lie homomorphism.** For every `g ∈ Spinᶜ(n)`
and `Ω ∈ 𝔰𝔬(n)`, `Ad_g` transports the lifted orthogonal element through the descended rotation of
`g` in `SO(n)`, with no global `Spin(n)` lift required. -/
@[simp]
theorem Ad_realSpinOrthogonalLieLift
    (g : SpinC) (Ω : LeftInvariantDerivation ISO SORange) :
    TauCeti.Lie.Ad (I := IC) g (realSpinOrthogonalLieLift n hQ Ω) =
      realSpinOrthogonalLieLift n hQ
        (TauCeti.Lie.Ad (I := ISO) (realToSpecialOrthogonalSmoothRange n hQ g) Ω) := by
  have hz (X : LeftInvariantDerivation ISO SORange) :
      (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (X, 0) =
        realSpinOrthogonalLieLift n hQ X :=
    (realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (X, 0)).trans
      ((congrArg (realSpinOrthogonalLieLift n hQ X + ·) (realDetLieLift n hQ).map_zero).trans
        (add_zero _))
  exact (congrArg (TauCeti.Lie.Ad (I := IC) g) (hz Ω).symm).trans
    ((Ad_realToSpecialOrthogonalProdDetLinearEquiv_symm n hQ g Ω 0).trans (hz _))

end CliffordAlgebra.spinCGroup
