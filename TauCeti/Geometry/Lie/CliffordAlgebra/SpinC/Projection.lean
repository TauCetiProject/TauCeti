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
on the central circle, in every positive dimension (where `realCliffordForm n 0 ≠ 0`) the paired
smooth homomorphism `Spinᶜ(n) → SO(n) × U(1)` has bijective Lie map and is therefore a smooth local
diffeomorphism. It induces a Lie-algebra equivalence
`realToSpecialOrthogonalProdDetLieEquiv : 𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ⁅ℝ⁆ 𝔰𝔬(n) × Lie(U(1))` and, after normalizing
`Lie(U(1))` by `circleLieAlgebraEquiv`, a linear equivalence
`realToSpecialOrthogonalProdDetLinearEquiv : 𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ[ℝ] 𝔰𝔬(n) × ℝ`, whose inverse lifts an
infinitesimal orthogonal transformation `Ω` through `𝔰𝔭𝔦𝔫(n)` into the kernel of the determinant
differential and lifts a determinant parameter `a` by the half-speed central generator
`realDetLieLift n hQ a`.

Naturality of the group adjoint along the smooth rotation homomorphism and `Ad`-invariance of the
determinant weight imply that the lifted orthogonal Lie homomorphism `realSpinOrthogonalLieLift`
intertwines the `Spinᶜ(n)` adjoint action with the `SO(n)` adjoint action through the descended
rotation map `Spinᶜ(n) → SO(n)`. Consequently, in any associated `Spinᶜ` bundle, the spin-Lie
action of an `𝔰𝔬(n)`-valued curvature form descends directly through `Spinᶜ(n)` without choosing a
separate global `Spin(n)` lift.

## Main definitions

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

/-! ### Smooth rotation and frame-and-determinant homomorphisms -/

/-- The descended rotation homomorphism `Spinᶜ(n) → SO(n)` into the embedded special-orthogonal
matrix-units carrier, as a smooth homomorphism. -/
def realToSpecialOrthogonalSmoothRange : ContMDiffMonoidMorphism IC ISO ∞ SpinC SORange where
  toMonoidHom :=
    (realCliffordSpecialOrthogonalContinuousMulEquivRange n).toMulEquiv.toMonoidHom.comp
      (toSpecialOrthogonal (realCliffordForm n 0) hQ)
  contMDiff_toFun := by
    apply (contMDiff_iff_contMDiff_comp_mk n hQ _).mpr
    exact ((realSpinToSpecialOrthogonalSmoothRange n).contMDiff_toFun.comp
      contMDiff_fst).congr fun p ↦
        (congrArg (realCliffordSpecialOrthogonalContinuousMulEquivRange n)
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
  DFunLike.coe_injective <| funext fun z ↦ by simp [toSpecialOrthogonal_ofCircle]

/-- The paired frame-and-determinant smooth homomorphism `Spinᶜ(n) → SO(n) × U(1)`. -/
def realToSpecialOrthogonalProdDetSmoothHom :
    ContMDiffMonoidMorphism IC ISOProd ∞ SpinC (SORange × Circle) :=
  (realToSpecialOrthogonalSmoothRange n hQ).prod (realDetSmoothHom n hQ)

@[simp]
theorem realToSpecialOrthogonalProdDetSmoothHom_apply (x : SpinC) :
    realToSpecialOrthogonalProdDetSmoothHom n hQ x =
      (realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (toSpecialOrthogonal (realCliffordForm n 0) hQ x),
        det (realCliffordForm n 0) hQ x) := by
  simp only [realToSpecialOrthogonalProdDetSmoothHom, ContMDiffMonoidMorphism.prod_apply,
    realToSpecialOrthogonalSmoothRange_apply, realDetSmoothHom_apply]

/-! ### The defining cover and the Spin lift of `𝔰𝔬(n)` -/

/-- The Lie-algebra equivalence `(𝔰𝔭𝔦𝔫(n) × Lie(U(1))) ≃ₗ⁅ℝ⁆ 𝔰𝔭𝔦𝔫ᶜ(n)` induced by the defining
central double cover. -/
def realMkLieEquiv :
    (LeftInvariantDerivation IS Spin × LeftInvariantDerivation (𝓡 1) Circle) ≃ₗ⁅ℝ⁆ 𝔤 :=
  (TauCeti.Lie.prodLieEquiv (I := IS) (I' := 𝓡 1)).symm.trans
    (TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt (realMkSmoothHom n hQ)
      (isLocalDiffeomorph_realMkSmoothHom n hQ 1))

/-- The defining-cover Lie equivalence sums the differentials of `ofSpin` and `ofCircle`. -/
@[simp]
theorem realMkLieEquiv_apply
    (p : LeftInvariantDerivation IS Spin × LeftInvariantDerivation (𝓡 1) Circle) :
    realMkLieEquiv n hQ p =
      lieMap (realOfSpinSmoothHom n hQ) p.1 + lieMap (realOfCircleSmoothHom n hQ) p.2 := by
  -- Congruence avoids costly `isDefEq` unfolding across the Spin and Spinᶜ Lie-algebra models.
  have hinl : (lieMap (realMkSmoothHom n hQ)).comp (lieMap ContMDiffMonoidMorphism.inl) =
      lieMap (realOfSpinSmoothHom n hQ) :=
    (lieMap_comp _ _).symm.trans (congrArg _root_.lieMap (realMkSmoothHom_comp_inl n hQ))
  have hinr : (lieMap (realMkSmoothHom n hQ)).comp (lieMap ContMDiffMonoidMorphism.inr) =
      lieMap (realOfCircleSmoothHom n hQ) :=
    (lieMap_comp _ _).symm.trans (congrArg _root_.lieMap (realMkSmoothHom_comp_inr n hQ))
  calc
    realMkLieEquiv n hQ p
      = lieMap (realMkSmoothHom n hQ)
          ((TauCeti.Lie.prodLieEquiv (I := IS) (I' := 𝓡 1)).symm p) := by
      simp only [realMkLieEquiv, LieEquiv.trans_apply,
        TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply]
    _ = lieMap (realMkSmoothHom n hQ)
          (lieMap ContMDiffMonoidMorphism.inl p.1 + lieMap ContMDiffMonoidMorphism.inr p.2) :=
      congrArg (lieMap (realMkSmoothHom n hQ)) (TauCeti.Lie.prodLieEquiv_symm_eq_add p)
    _ = lieMap (realMkSmoothHom n hQ) (lieMap ContMDiffMonoidMorphism.inl p.1) +
          lieMap (realMkSmoothHom n hQ) (lieMap ContMDiffMonoidMorphism.inr p.2) :=
      map_add (lieMap (realMkSmoothHom n hQ)) _ _
    _ = lieMap (realOfSpinSmoothHom n hQ) p.1 + lieMap (realOfCircleSmoothHom n hQ) p.2 :=
      congrArg₂ (· + ·) (DFunLike.congr_fun hinl p.1) (DFunLike.congr_fun hinr p.2)

/-- The differential of `ofSpin : Spin(n) → Spinᶜ(n)` is injective. -/
theorem lieMap_realOfSpinSmoothHom_injective :
    Function.Injective (lieMap (realOfSpinSmoothHom n hQ)) := fun X Y hXY ↦ by
  have h : realMkLieEquiv n hQ (X, 0) = realMkLieEquiv n hQ (Y, 0) :=
    calc
      realMkLieEquiv n hQ (X, 0)
        = lieMap (realOfSpinSmoothHom n hQ) X + lieMap (realOfCircleSmoothHom n hQ) 0 :=
        realMkLieEquiv_apply n hQ (X, 0)
      _ = lieMap (realOfSpinSmoothHom n hQ) Y + lieMap (realOfCircleSmoothHom n hQ) 0 :=
        congrArg (· + _) hXY
      _ = realMkLieEquiv n hQ (Y, 0) := (realMkLieEquiv_apply n hQ (Y, 0)).symm
  exact congrArg Prod.fst ((realMkLieEquiv n hQ).injective h)

/-- On `𝔰𝔭𝔦𝔫(n)`, the differential of the descended rotation homomorphism recovers the differential
of the Spin projection. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom
    (X : LeftInvariantDerivation IS Spin) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (lieMap (realOfSpinSmoothHom n hQ) X) =
      realSpinToSpecialOrthogonalRangeLieEquiv n X := by
  -- Congruence avoids costly `isDefEq` unfolding across the Spin/SO/Spinᶜ Lie-algebra models.
  have h : (lieMap (realToSpecialOrthogonalSmoothRange n hQ)).comp
      (lieMap (realOfSpinSmoothHom n hQ)) =
      (realSpinToSpecialOrthogonalRangeLieEquiv n).toLieHom :=
    calc
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ)).comp (lieMap (realOfSpinSmoothHom n hQ))
        = lieMap ((realToSpecialOrthogonalSmoothRange n hQ).comp (realOfSpinSmoothHom n hQ)) :=
        (lieMap_comp _ _).symm
      _ = lieMap (realSpinToSpecialOrthogonalSmoothRange n) :=
        congrArg _root_.lieMap (realToSpecialOrthogonalSmoothRange_comp_ofSpin n hQ)
      _ = (realSpinToSpecialOrthogonalRangeLieEquiv n).toLieHom :=
        (realSpinToSpecialOrthogonalRangeLieEquiv_toLieHom n).symm
  exact DFunLike.congr_fun h X

/-- The differential of the descended rotation homomorphism vanishes on the central circle. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (lieMap (realOfCircleSmoothHom n hQ) Z) =
      0 := by
  have h : (lieMap (realToSpecialOrthogonalSmoothRange n hQ)).comp
      (lieMap (realOfCircleSmoothHom n hQ)) = 0 :=
    calc
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ)).comp (lieMap (realOfCircleSmoothHom n hQ))
        = lieMap ((realToSpecialOrthogonalSmoothRange n hQ).comp (realOfCircleSmoothHom n hQ)) :=
        (lieMap_comp _ _).symm
      _ = lieMap 1 :=
        congrArg _root_.lieMap (realToSpecialOrthogonalSmoothRange_comp_ofCircle n hQ)
      _ = 0 := lieMap_one
  exact DFunLike.congr_fun h Z

/-- The differential of the descended rotation homomorphism vanishes on `realDetLieLift`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_realDetLieLift (a : ℝ) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realDetLieLift n hQ a) = 0 := by
  calc
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realDetLieLift n hQ a)
      = lieMap (realToSpecialOrthogonalSmoothRange n hQ)
          (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (ofCircleContinuousMonoidHom _ hQ)
            (circleLieAlgebraEquiv.symm (a / 2))) :=
      congrArg (lieMap (realToSpecialOrthogonalSmoothRange n hQ)) (realDetLieLift_apply n hQ a)
    _ = lieMap (realToSpecialOrthogonalSmoothRange n hQ)
          (lieMap (realOfCircleSmoothHom n hQ) (circleLieAlgebraEquiv.symm (a / 2))) :=
      congrArg (lieMap (realToSpecialOrthogonalSmoothRange n hQ))
        (DFunLike.congr_fun (lieMap_realOfCircleSmoothHom n hQ) _).symm
    _ = 0 := lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom n hQ _

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
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realSpinOrthogonalLieLift n hQ Ω) = Ω := by
  calc
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realSpinOrthogonalLieLift n hQ Ω)
      = lieMap (realToSpecialOrthogonalSmoothRange n hQ)
          (lieMap (realOfSpinSmoothHom n hQ)
            ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)) :=
      congrArg (lieMap (realToSpecialOrthogonalSmoothRange n hQ))
        (realSpinOrthogonalLieLift_apply n hQ Ω)
    _ = realSpinToSpecialOrthogonalRangeLieEquiv n
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω) :=
      lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom n hQ _
    _ = Ω := (realSpinToSpecialOrthogonalRangeLieEquiv n).apply_symm_apply Ω

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

/-- Evaluating `realSoLieLift` on the skew-matrix coordinate of `Ω` recovers
`realSpinOrthogonalLieLift`. -/
@[simp]
theorem realSoLieLift_realCliffordSpecialOrthogonalLieEquivSo
    (Ω : LeftInvariantDerivation ISO SORange) :
    realSoLieLift n hQ (realCliffordSpecialOrthogonalLieEquivSo n Ω) =
      realSpinOrthogonalLieLift n hQ Ω := by
  calc
    realSoLieLift n hQ (realCliffordSpecialOrthogonalLieEquivSo n Ω)
      = realSpinOrthogonalLieLift n hQ
          ((realCliffordSpecialOrthogonalLieEquivSo n).symm
            (realCliffordSpecialOrthogonalLieEquivSo n Ω)) :=
      realSoLieLift_apply n hQ _
    _ = realSpinOrthogonalLieLift n hQ Ω :=
      congrArg (realSpinOrthogonalLieLift n hQ)
        ((realCliffordSpecialOrthogonalLieEquivSo n).symm_apply_apply Ω)

/-- Pushing `realSoLieLift` forward along `Spinᶜ(n) → SO(n)` recovers the inverse of
`realCliffordSpecialOrthogonalLieEquivSo`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_realSoLieLift
    (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realSoLieLift n hQ A) =
      (realCliffordSpecialOrthogonalLieEquivSo n).symm A := by
  calc
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realSoLieLift n hQ A)
      = lieMap (realToSpecialOrthogonalSmoothRange n hQ)
          (realSpinOrthogonalLieLift n hQ ((realCliffordSpecialOrthogonalLieEquivSo n).symm A)) :=
      congrArg (lieMap (realToSpecialOrthogonalSmoothRange n hQ)) (realSoLieLift_apply n hQ A)
    _ = (realCliffordSpecialOrthogonalLieEquivSo n).symm A :=
      lieMap_realToSpecialOrthogonalSmoothRange_realSpinOrthogonalLieLift n hQ _

/-- `realSoLieLift` lands in the kernel of the determinant differential. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realSoLieLift
    (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    d (realSoLieLift n hQ A) = 0 := by
  calc
    d (realSoLieLift n hQ A)
      = d (realSpinOrthogonalLieLift n hQ ((realCliffordSpecialOrthogonalLieEquivSo n).symm A)) :=
      congrArg d (realSoLieLift_apply n hQ A)
    _ = 0 := lieWeight_detContinuousMonoidHom_realSpinOrthogonalLieLift n hQ _

/-- `realSoLieLift` lands in the kernel of `lieMap (realDetSmoothHom n hQ)`. -/
@[simp]
theorem lieMap_realDetSmoothHom_realSoLieLift
    (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    lieMap (realDetSmoothHom n hQ) (realSoLieLift n hQ A) = 0 := by
  calc
    lieMap (realDetSmoothHom n hQ) (realSoLieLift n hQ A)
      = lieMap (realDetSmoothHom n hQ)
          (realSpinOrthogonalLieLift n hQ ((realCliffordSpecialOrthogonalLieEquivSo n).symm A)) :=
      congrArg (lieMap (realDetSmoothHom n hQ)) (realSoLieLift_apply n hQ A)
    _ = 0 := lieMap_realDetSmoothHom_realSpinOrthogonalLieLift n hQ _

/-! ### Bijectivity and local diffeomorphism of `Spinᶜ(n) → SO(n) × U(1)` -/

private theorem prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_lift
    (p : LeftInvariantDerivation ISO SORange × LeftInvariantDerivation (𝓡 1) Circle) :
    TauCeti.Lie.prodLieEquiv (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ)
      (realSpinOrthogonalLieLift n hQ p.1 +
        lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2))) = p := by
  refine (TauCeti.Lie.prodLieEquiv_lieMap_prod
    (realToSpecialOrthogonalSmoothRange n hQ) (realDetSmoothHom n hQ) _).trans ?_
  refine Prod.ext ?_ ?_
  · calc
      lieMap (realToSpecialOrthogonalSmoothRange n hQ)
          (realSpinOrthogonalLieLift n hQ p.1 +
            lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2))
        = lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realSpinOrthogonalLieLift n hQ p.1) +
            lieMap (realToSpecialOrthogonalSmoothRange n hQ)
              (lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2)) :=
        map_add _ _ _
      _ = p.1 + 0 :=
        congrArg₂ (· + ·)
          (lieMap_realToSpecialOrthogonalSmoothRange_realSpinOrthogonalLieLift n hQ p.1)
          (lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom n hQ _)
      _ = p.1 := add_zero p.1
  · calc
      lieMap (realDetSmoothHom n hQ)
          (realSpinOrthogonalLieLift n hQ p.1 +
            lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2))
        = lieMap (realDetSmoothHom n hQ) (realSpinOrthogonalLieLift n hQ p.1) +
            lieMap (realDetSmoothHom n hQ)
              (lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2)) :=
        map_add _ _ _
      _ = 0 + (2 : ℝ) • ((1 / 2 : ℝ) • p.2) :=
        congrArg₂ (· + ·)
          (lieMap_realDetSmoothHom_realSpinOrthogonalLieLift n hQ p.1)
          (lieMap_realDetSmoothHom_lieMap_realOfCircleSmoothHom n hQ _)
      _ = p.2 := by rw [zero_add, smul_smul]; norm_num

/-- Reconstructing an element of `𝔰𝔭𝔦𝔫ᶜ(n)` from its orthogonal projection and determinant weight
recovers the element. -/
@[simp]
theorem realSpinOrthogonalLieLift_add_realDetLieLift (Y : 𝔤) :
    realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y) +
        realDetLieLift n hQ (d Y) =
      Y := by
  -- Use `symm` + `calc` to avoid costly `isDefEq` unfolding across the Spin/SO/Spinᶜ Lie models.
  let p := (realMkLieEquiv n hQ).symm Y
  have hXZ : Y = lieMap (realOfSpinSmoothHom n hQ) p.1 + lieMap (realOfCircleSmoothHom n hQ) p.2 :=
    ((realMkLieEquiv n hQ).apply_symm_apply Y).symm.trans (realMkLieEquiv_apply n hQ p)
  have hSO : lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y =
      realSpinToSpecialOrthogonalRangeLieEquiv n p.1 :=
    calc
      lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y
        = lieMap (realToSpecialOrthogonalSmoothRange n hQ)
            (lieMap (realOfSpinSmoothHom n hQ) p.1) +
          lieMap (realToSpecialOrthogonalSmoothRange n hQ)
            (lieMap (realOfCircleSmoothHom n hQ) p.2) :=
        (congrArg (lieMap (realToSpecialOrthogonalSmoothRange n hQ)) hXZ).trans (map_add _ _ _)
      _ = realSpinToSpecialOrthogonalRangeLieEquiv n p.1 + 0 :=
        congrArg₂ (· + ·)
          (lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom n hQ p.1)
          (lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom n hQ p.2)
      _ = realSpinToSpecialOrthogonalRangeLieEquiv n p.1 := add_zero _
  have hd : d Y = d (lieMap (realOfCircleSmoothHom n hQ) p.2) :=
    calc
      d Y = d (lieMap (realOfSpinSmoothHom n hQ) p.1) +
              d (lieMap (realOfCircleSmoothHom n hQ) p.2) :=
        (congrArg d hXZ).trans (map_add d _ _)
      _ = 0 + d (lieMap (realOfCircleSmoothHom n hQ) p.2) :=
        congrArg (· + _) (lieWeight_detContinuousMonoidHom_lieMap_realOfSpinSmoothHom n hQ p.1)
      _ = d (lieMap (realOfCircleSmoothHom n hQ) p.2) := zero_add _
  have hX : realSpinOrthogonalLieLift n hQ (realSpinToSpecialOrthogonalRangeLieEquiv n p.1) =
      lieMap (realOfSpinSmoothHom n hQ) p.1 :=
    calc
      realSpinOrthogonalLieLift n hQ (realSpinToSpecialOrthogonalRangeLieEquiv n p.1)
        = lieMap (realOfSpinSmoothHom n hQ)
            ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
              (realSpinToSpecialOrthogonalRangeLieEquiv n p.1)) :=
        realSpinOrthogonalLieLift_apply n hQ _
      _ = lieMap (realOfSpinSmoothHom n hQ) p.1 :=
        congrArg (lieMap (realOfSpinSmoothHom n hQ))
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm_apply_apply p.1)
  have hZ : realDetLieLift n hQ (d (lieMap (realOfCircleSmoothHom n hQ) p.2)) =
      lieMap (realOfCircleSmoothHom n hQ) p.2 :=
    calc
      realDetLieLift n hQ (d (lieMap (realOfCircleSmoothHom n hQ) p.2))
        = realDetLieLift n hQ (d (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
            (ofCircleContinuousMonoidHom _ hQ) p.2)) :=
        congrArg (fun W ↦ realDetLieLift n hQ (d W))
          (DFunLike.congr_fun (lieMap_realOfCircleSmoothHom n hQ) p.2)
      _ = realDetLieLift n hQ (2 * circleLieAlgebraEquiv p.2) :=
        congrArg (realDetLieLift n hQ)
          (lieWeight_detContinuousMonoidHom_lieMap_ofCircleContinuousMonoidHom n hQ p.2)
      _ = ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (ofCircleContinuousMonoidHom _ hQ)
            (circleLieAlgebraEquiv.symm (2 * circleLieAlgebraEquiv p.2 / 2)) :=
        realDetLieLift_apply n hQ _
      _ = ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (ofCircleContinuousMonoidHom _ hQ) p.2 :=
        congrArg (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
          (ofCircleContinuousMonoidHom _ hQ)) <| by
          rw [mul_div_cancel_left₀ _ two_ne_zero, LinearEquiv.symm_apply_apply]
      _ = lieMap (realOfCircleSmoothHom n hQ) p.2 :=
        (DFunLike.congr_fun (lieMap_realOfCircleSmoothHom n hQ) p.2).symm
  calc
    realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y) +
        realDetLieLift n hQ (d Y)
      = realSpinOrthogonalLieLift n hQ (realSpinToSpecialOrthogonalRangeLieEquiv n p.1) +
          realDetLieLift n hQ (d (lieMap (realOfCircleSmoothHom n hQ) p.2)) :=
      congrArg₂ (fun Ω a ↦ realSpinOrthogonalLieLift n hQ Ω + realDetLieLift n hQ a) hSO hd
    _ = lieMap (realOfSpinSmoothHom n hQ) p.1 + lieMap (realOfCircleSmoothHom n hQ) p.2 :=
      congrArg₂ (· + ·) hX hZ
    _ = Y := hXZ.symm

/-- The inverse of `realMkLieEquiv` projects onto `𝔰𝔭𝔦𝔫(n)` via `Spinᶜ(n) → SO(n)` and halves the
differential of `det` on `Lie(U(1))`. -/
@[simp]
theorem realMkLieEquiv_symm_apply (Y : 𝔤) :
    (realMkLieEquiv n hQ).symm Y =
      ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y),
      (1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y) := by
  apply (realMkLieEquiv n hQ).injective
  have hhalf (a : ℝ) : (1 / 2 : ℝ) * a = a / 2 := by ring
  have hcirc : circleLieAlgebraEquiv ((1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y) =
      circleLieAlgebraEquiv (circleLieAlgebraEquiv.symm (d Y / 2)) :=
    calc
      circleLieAlgebraEquiv ((1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y)
        = (1 / 2 : ℝ) * circleLieAlgebraEquiv (lieMap (realDetSmoothHom n hQ) Y) :=
        (circleLieAlgebraEquiv.map_smul (1 / 2 : ℝ) _).trans (smul_eq_mul _ _)
      _ = (1 / 2 : ℝ) * d Y :=
        congrArg ((1 / 2 : ℝ) * ·) (circleLieAlgebraEquiv_lieMap_realDetSmoothHom n hQ Y)
      _ = d Y / 2 := hhalf (d Y)
      _ = circleLieAlgebraEquiv (circleLieAlgebraEquiv.symm (d Y / 2)) :=
        (circleLieAlgebraEquiv.apply_symm_apply _).symm
  have hZ : lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y) =
      realDetLieLift n hQ (d Y) :=
    calc
      lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y)
        = ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (ofCircleContinuousMonoidHom _ hQ)
            ((1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y) :=
        DFunLike.congr_fun (lieMap_realOfCircleSmoothHom n hQ) _
      _ = ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (ofCircleContinuousMonoidHom _ hQ)
            (circleLieAlgebraEquiv.symm (d Y / 2)) :=
        congrArg (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
          (ofCircleContinuousMonoidHom _ hQ)) (circleLieAlgebraEquiv.injective hcirc)
      _ = realDetLieLift n hQ (d Y) := (realDetLieLift_apply n hQ (d Y)).symm
  calc
    realMkLieEquiv n hQ ((realMkLieEquiv n hQ).symm Y)
      = Y := (realMkLieEquiv n hQ).apply_symm_apply Y
    _ = realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y) +
          realDetLieLift n hQ (d Y) :=
      (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y).symm
    _ = lieMap (realOfSpinSmoothHom n hQ)
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
            (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y)) +
          lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y) :=
      congrArg₂ (· + ·) (realSpinOrthogonalLieLift_apply n hQ _) hZ.symm
    _ = realMkLieEquiv n hQ
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
            (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y),
          (1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y) :=
      (realMkLieEquiv_apply n hQ
        ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
          (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y),
        (1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y)).symm

/-- The Lie map of the paired smooth homomorphism `Spinᶜ(n) → SO(n) × U(1)` is bijective in every
positive dimension (`realCliffordForm n 0 ≠ 0`). -/
theorem lieMap_realToSpecialOrthogonalProdDet_bijective :
    Function.Bijective (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ)) :=
  ⟨fun Y₁ Y₂ h ↦ by
    have hprod : (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y₁,
        lieMap (realDetSmoothHom n hQ) Y₁) =
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y₂,
        lieMap (realDetSmoothHom n hQ) Y₂) :=
      calc
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y₁,
            lieMap (realDetSmoothHom n hQ) Y₁)
          = TauCeti.Lie.prodLieEquiv
              (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ) Y₁) :=
          (TauCeti.Lie.prodLieEquiv_lieMap_prod
            (realToSpecialOrthogonalSmoothRange n hQ) (realDetSmoothHom n hQ) Y₁).symm
        _ = TauCeti.Lie.prodLieEquiv
              (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ) Y₂) :=
          congrArg (TauCeti.Lie.prodLieEquiv (I := ISO) (I' := 𝓡 1)) h
        _ = (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y₂,
              lieMap (realDetSmoothHom n hQ) Y₂) :=
          TauCeti.Lie.prodLieEquiv_lieMap_prod
            (realToSpecialOrthogonalSmoothRange n hQ) (realDetSmoothHom n hQ) Y₂
    have hSO := congrArg Prod.fst hprod
    have hd : d Y₁ = d Y₂ :=
      calc
        d Y₁ = circleLieAlgebraEquiv (lieMap (realDetSmoothHom n hQ) Y₁) :=
          (circleLieAlgebraEquiv_lieMap_realDetSmoothHom n hQ Y₁).symm
        _ = circleLieAlgebraEquiv (lieMap (realDetSmoothHom n hQ) Y₂) :=
          congrArg circleLieAlgebraEquiv (congrArg Prod.snd hprod)
        _ = d Y₂ := circleLieAlgebraEquiv_lieMap_realDetSmoothHom n hQ Y₂
    calc
      Y₁ = realSpinOrthogonalLieLift n hQ
          (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y₁) + realDetLieLift n hQ (d Y₁) :=
        (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y₁).symm
      _ = realSpinOrthogonalLieLift n hQ
          (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y₂) + realDetLieLift n hQ (d Y₂) :=
        congrArg₂ (fun Ω a ↦ realSpinOrthogonalLieLift n hQ Ω + realDetLieLift n hQ a) hSO hd
      _ = Y₂ := realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y₂,
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
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y, lieMap (realDetSmoothHom n hQ) Y) := by
  simp only [realToSpecialOrthogonalProdDetLieEquiv, LieEquiv.trans_apply,
    TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply, realToSpecialOrthogonalProdDetSmoothHom,
    TauCeti.Lie.prodLieEquiv_lieMap_prod]

@[simp]
theorem realToSpecialOrthogonalProdDetLieEquiv_symm_apply
    (p : LeftInvariantDerivation ISO SORange × LeftInvariantDerivation (𝓡 1) Circle) :
    (realToSpecialOrthogonalProdDetLieEquiv n hQ).symm p =
      realSpinOrthogonalLieLift n hQ p.1 +
        lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2) := by
  apply (realToSpecialOrthogonalProdDetLieEquiv n hQ).injective
  calc
    realToSpecialOrthogonalProdDetLieEquiv n hQ
        ((realToSpecialOrthogonalProdDetLieEquiv n hQ).symm p)
      = p := (realToSpecialOrthogonalProdDetLieEquiv n hQ).apply_symm_apply p
    _ = TauCeti.Lie.prodLieEquiv (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ)
          (realSpinOrthogonalLieLift n hQ p.1 +
            lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2))) :=
      (prodLieEquiv_lieMap_realToSpecialOrthogonalProdDet_lift n hQ p).symm
    _ = realToSpecialOrthogonalProdDetLieEquiv n hQ
          (realSpinOrthogonalLieLift n hQ p.1 +
            lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2)) := by
      simp only [realToSpecialOrthogonalProdDetLieEquiv, LieEquiv.trans_apply,
        TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply]

/-! ### Identification of the determinant kernel with `𝔰𝔭𝔦𝔫(n)` -/

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
        have hd0 : realDetLieLift n hQ (d Y.1) = 0 :=
          (congrArg (realDetLieLift n hQ)
            ((mem_ker_lieMap_detContinuousMonoidHom_iff n hQ Y.1).mp Y.2)).trans (map_zero _)
        refine ⟨(realSpinToSpecialOrthogonalRangeLieEquiv n).symm
          (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1), Subtype.ext ?_⟩
        change lieMap (realOfSpinSmoothHom n hQ)
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
            (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1)) = Y.1
        calc
          lieMap (realOfSpinSmoothHom n hQ)
              ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
                (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1))
            = realSpinOrthogonalLieLift n hQ
                (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1) :=
            (realSpinOrthogonalLieLift_apply n hQ _).symm
          _ = realSpinOrthogonalLieLift n hQ
                (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1) + 0 :=
            (add_zero _).symm
          _ = realSpinOrthogonalLieLift n hQ
                (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1) +
                realDetLieLift n hQ (d Y.1) :=
            congrArg (realSpinOrthogonalLieLift n hQ _ + ·) hd0.symm
          _ = Y.1 := realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y.1⟩

@[simp]
theorem coe_realOfSpinLieEquivDetKer_apply (X : LeftInvariantDerivation IS Spin) :
    (realOfSpinLieEquivDetKer n hQ X : 𝔤) = lieMap (realOfSpinSmoothHom n hQ) X :=
  (rfl)

@[simp]
theorem realOfSpinLieEquivDetKer_symm_apply
    (Y : (ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1) (detContinuousMonoidHom _ hQ)).ker) :
    (realOfSpinLieEquivDetKer n hQ).symm Y =
      (realSpinToSpecialOrthogonalRangeLieEquiv n).symm
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1) := by
  apply (realOfSpinLieEquivDetKer n hQ).injective
  apply Subtype.ext
  have hdY : realDetLieLift n hQ (d Y.1) = 0 :=
    (congrArg (realDetLieLift n hQ)
      ((mem_ker_lieMap_detContinuousMonoidHom_iff n hQ Y.1).mp Y.2)).trans (map_zero _)
  calc
    (realOfSpinLieEquivDetKer n hQ ((realOfSpinLieEquivDetKer n hQ).symm Y) : 𝔤)
      = Y.1 := congrArg Subtype.val ((realOfSpinLieEquivDetKer n hQ).apply_symm_apply Y)
    _ = realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1) +
          realDetLieLift n hQ (d Y.1) :=
      (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y.1).symm
    _ = realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1) +
          0 :=
      congrArg (realSpinOrthogonalLieLift n hQ _ + ·) hdY
    _ = realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1) :=
      add_zero _
    _ = (realOfSpinLieEquivDetKer n hQ
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
            (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.1)) : 𝔤) :=
      (realSpinOrthogonalLieLift_apply n hQ _).trans
        (coe_realOfSpinLieEquivDetKer_apply n hQ _).symm

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
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y, d Y) := by
  simp [realToSpecialOrthogonalProdDetLinearEquiv, circleLieAlgebraEquiv_lieMap_realDetSmoothHom]

@[simp]
theorem realToSpecialOrthogonalProdDetLinearEquiv_symm_apply
    (p : LeftInvariantDerivation ISO SORange × ℝ) :
    (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm p =
      realSpinOrthogonalLieLift n hQ p.1 + realDetLieLift n hQ p.2 := by
  apply (realToSpecialOrthogonalProdDetLinearEquiv n hQ).injective
  simp

/-- In skew-symmetric matrix coordinates, `𝔰𝔭𝔦𝔫ᶜ(n)` splits linearly as `so(n, ℝ) × ℝ`. -/
def realLinearEquivSoProdReal : 𝔤 ≃ₗ[ℝ] (LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :=
  (realToSpecialOrthogonalProdDetLinearEquiv n hQ).trans
    (LinearEquiv.prodCongr (realCliffordSpecialOrthogonalLieEquivSo n).toLinearEquiv
      (LinearEquiv.refl ℝ ℝ))

@[simp]
theorem realLinearEquivSoProdReal_apply (Y : 𝔤) :
    realLinearEquivSoProdReal n hQ Y =
      (realCliffordSpecialOrthogonalLieEquivSo n
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y), d Y) := by
  simp [realLinearEquivSoProdReal]

@[simp]
theorem realLinearEquivSoProdReal_symm_apply
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    (realLinearEquivSoProdReal n hQ).symm p =
      realSoLieLift n hQ p.1 + realDetLieLift n hQ p.2 := by
  apply (realLinearEquivSoProdReal n hQ).injective
  simp

/-- **Affine shift in the determinant component.** Shifting the determinant parameter by `b` adds
the half-speed central lift `realDetLieLift n hQ b` while leaving the orthogonal part unchanged. -/
theorem realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right
    (Ω : LeftInvariantDerivation ISO SORange) (a b : ℝ) :
    (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a + b) =
      (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a) + realDetLieLift n hQ b := by
  simp [add_assoc]

/-- The Lie bracket of two lifted pairs `(Ω₁, a₁)` and `(Ω₂, a₂)` depends only on the orthogonal
bracket `⁅Ω₁, Ω₂⁆`, because the central determinant lift brackets trivially. -/
theorem lie_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (Ω₁ Ω₂ : LeftInvariantDerivation ISO SORange) (a₁ a₂ : ℝ) :
    ⁅(realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω₁, a₁),
        (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω₂, a₂)⁆ =
      realSpinOrthogonalLieLift n hQ ⁅Ω₁, Ω₂⁆ := by
  simp [← LieHom.map_lie]

/-- Exponentiating a lifted pair `(Ω, a)` multiplies the `Spin` lift of `exp Ω` by the half-speed
central phase `ofCircle _ hQ (Circle.exp (a / 2))`. -/
theorem lieExp_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (Ω : LeftInvariantDerivation ISO SORange) (a : ℝ) :
    lieExp ((realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) =
      ofSpin _ hQ (lieExp ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)) *
        ofCircle _ hQ (Circle.exp (a / 2)) := by
  calc
    lieExp ((realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a))
      = lieExp (realSpinOrthogonalLieLift n hQ Ω + realDetLieLift n hQ a) :=
      congrArg lieExp (realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (Ω, a))
    _ = lieExp (realSpinOrthogonalLieLift n hQ Ω) * ofCircle _ hQ (Circle.exp (a / 2)) :=
      lieExp_add_realDetLieLift n hQ _ a
    _ = lieExp (lieMap (realOfSpinSmoothHom n hQ)
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)) *
          ofCircle _ hQ (Circle.exp (a / 2)) :=
      congrArg (· * _) (congrArg lieExp (realSpinOrthogonalLieLift_apply n hQ Ω))
    _ = ofSpin _ hQ (lieExp ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)) *
          ofCircle _ hQ (Circle.exp (a / 2)) :=
      congrArg (· * _) <| (map_lieExp (realOfSpinSmoothHom n hQ) _).symm.trans
        (realOfSpinSmoothHom_apply n hQ _)

/-! ### `Spinᶜ` adjoint equivariance of the orthogonal lift -/

/-- Under the connection-splitting equivalence, the `Spinᶜ(n)` adjoint action acts on the
orthogonal component through the descended rotation map `Spinᶜ(n) → SO(n)` and fixes the
determinant weight. -/
theorem realToSpecialOrthogonalProdDetLinearEquiv_Ad (g : SpinC) (Y : 𝔤) :
    realToSpecialOrthogonalProdDetLinearEquiv n hQ (TauCeti.Lie.Ad (I := IC) g Y) =
      (TauCeti.Lie.Ad (I := ISO) (realToSpecialOrthogonalSmoothRange n hQ g)
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y), d Y) := by
  simp [ContinuousMonoidHom.lieWeight_Ad]

/-- **Adjoint equivariance of the connection/curvature lift.** Conjugating a lifted pair `(Ω, a)`
by `g ∈ Spinᶜ(n)` acts on `Ω` by the `SO(n)` adjoint of the descended rotation of `g` and fixes
`a`. -/
theorem Ad_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (g : SpinC) (Ω : LeftInvariantDerivation ISO SORange) (a : ℝ) :
    TauCeti.Lie.Ad (I := IC) g ((realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) =
      (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm
        (TauCeti.Lie.Ad (I := ISO) (realToSpecialOrthogonalSmoothRange n hQ g) Ω, a) := by
  apply (realToSpecialOrthogonalProdDetLinearEquiv n hQ).injective
  refine (realToSpecialOrthogonalProdDetLinearEquiv_Ad n hQ g _).trans ?_
  simp

/-- **`Spinᶜ` equivariance of the lifted orthogonal Lie homomorphism.** For every `g ∈ Spinᶜ(n)`
and `Ω ∈ 𝔰𝔬(n)`, `Ad_g` transports the lifted orthogonal element through the descended rotation of
`g` in `SO(n)`, with no global `Spin(n)` lift required. -/
@[simp]
theorem Ad_realSpinOrthogonalLieLift
    (g : SpinC) (Ω : LeftInvariantDerivation ISO SORange) :
    TauCeti.Lie.Ad (I := IC) g (realSpinOrthogonalLieLift n hQ Ω) =
      realSpinOrthogonalLieLift n hQ
        (TauCeti.Lie.Ad (I := ISO) (realToSpecialOrthogonalSmoothRange n hQ g) Ω) := by
  simpa using Ad_realToSpecialOrthogonalProdDetLinearEquiv_symm n hQ g Ω 0

end CliffordAlgebra.spinCGroup
