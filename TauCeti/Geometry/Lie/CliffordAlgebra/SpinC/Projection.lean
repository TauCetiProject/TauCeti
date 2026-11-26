/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Naturality
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.LieAlgebra
public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Determinant
public import TauCeti.Geometry.Lie.Prod

/-!
# The Lie-algebra projection splitting of compact `Spinᶜ`

The compact group `Spinᶜ(n)` sits in two smooth central double covers: the defining quotient
`Spin(n) × U(1) → Spinᶜ(n)` by `{1, (-1, -1)}` and the frame-and-determinant homomorphism
`Spinᶜ(n) → SO(n) × U(1)` sending `[s, z]` to `(π(s), z²)`.

Because `Spin(n) → SO(n)` has invertible differential and `det` has weight two on the central
circle, whenever `realCliffordForm n 0 ≠ 0` the paired smooth homomorphism `Spinᶜ(n) → SO(n) × U(1)`
has bijective Lie map and is a smooth local diffeomorphism. It induces
`realToSpecialOrthogonalProdDetLieEquiv : 𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ⁅ℝ⁆ 𝔰𝔬(n) × Lie(U(1))` and, via
`circleLieAlgebraEquiv`, `realToSpecialOrthogonalProdDetLinearEquiv : 𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ[ℝ] 𝔰𝔬(n) × ℝ`,
lifting `(Ω, a)` to `realSpinOrthogonalLieLift n hQ Ω + realDetLieLift n hQ a`.

Naturality of the group adjoint along `Spinᶜ(n) → SO(n)` and `Ad`-invariance of the determinant
weight imply that `realSpinOrthogonalLieLift` intertwines the `Spinᶜ(n)` and `SO(n)` adjoint
actions, so `𝔰𝔬(n)`-valued curvature operators in associated `Spinᶜ` bundles descend without a
global `Spin` lift.

## Main definitions

* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalSmoothRange` and
  `realToSpecialOrthogonalProdDetSmoothHom`: the smooth rotation and frame-and-determinant
  homomorphisms.
* `CliffordAlgebra.spinCGroup.realSpinOrthogonalLieLift`, `realSoLieLift`, and
  `realOfSpinLieEquivDetKer`: the canonical `𝔰𝔬(n)` lift into `𝔰𝔭𝔦𝔫ᶜ(n)` and equivalence
  `𝔰𝔭𝔦𝔫(n) ≃ₗ⁅ℝ⁆ ker(d det)`.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalProdDetLieEquiv`,
  `realToSpecialOrthogonalProdDetLinearEquiv`, and `realLinearEquivSoProdReal`: the Lie and
  weight-normalized splittings of `𝔰𝔭𝔦𝔫ᶜ(n)`.

## Main results

* `CliffordAlgebra.spinCGroup.isLocalDiffeomorph_realToSpecialOrthogonalProdDetSmoothHom`: the
  smooth frame-and-determinant homomorphism `Spinᶜ(n) → SO(n) × U(1)` is a local diffeomorphism.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right`,
  `Ad_realSpinOrthogonalLieLift`, and `Ad_realToSpecialOrthogonalProdDetLinearEquiv_symm`: affine
  determinant shift and `Spinᶜ(n)`-equivariance of the orthogonal and full curvature lifts.

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
  contMDiff_toFun := (contMDiff_iff_contMDiff_comp_mk n hQ _).mpr <|
    ((realSpinToSpecialOrthogonalSmoothRange n).contMDiff_toFun.comp contMDiff_fst).congr fun p ↦
      (congrArg (realCliffordSpecialOrthogonalContinuousMulEquivRange n)
        (toSpecialOrthogonal_mk (realCliffordForm n 0) hQ p)).trans
          (realSpinToSpecialOrthogonalSmoothRange_apply n p.1).symm

@[simp]
theorem realToSpecialOrthogonalSmoothRange_apply (x : SpinC) :
    realToSpecialOrthogonalSmoothRange n hQ x =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (toSpecialOrthogonal (realCliffordForm n 0) hQ x) := (rfl)

@[simp]
theorem realToSpecialOrthogonalSmoothRange_comp_realOfSpinSmoothHom :
    (realToSpecialOrthogonalSmoothRange n hQ).comp (realOfSpinSmoothHom n hQ) =
      realSpinToSpecialOrthogonalSmoothRange n :=
  DFunLike.coe_injective <| funext fun s ↦ by simp [toSpecialOrthogonal_ofSpin]

@[simp]
theorem realToSpecialOrthogonalSmoothRange_comp_realOfCircleSmoothHom :
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
  simp only [realMkLieEquiv, LieEquiv.trans_apply,
    TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply]
  exact (congrArg (lieMap (realMkSmoothHom n hQ)) (TauCeti.Lie.prodLieEquiv_symm_eq_add p)).trans <|
    (map_add (lieMap (realMkSmoothHom n hQ)) _ _).trans <|
      congrArg₂ (· + ·)
        (lieMap_lieMap_of_comp_eq (realMkSmoothHom_comp_inl n hQ) p.1)
        (lieMap_lieMap_of_comp_eq (realMkSmoothHom_comp_inr n hQ) p.2)

/-- The differential of `ofSpin : Spin(n) → Spinᶜ(n)` is injective. -/
theorem lieMap_realOfSpinSmoothHom_injective :
    Function.Injective (lieMap (realOfSpinSmoothHom n hQ)) := fun X Y hXY ↦ by
  -- Congruence avoids costly `isDefEq` unfolding across the Spinᶜ Lie-algebra model.
  have h : (X, (0 : LeftInvariantDerivation (𝓡 1) Circle)) = (Y, 0) :=
    (realMkLieEquiv n hQ).injective <|
      (realMkLieEquiv_apply n hQ (X, 0)).trans <|
        (congrArg (· + _) hXY).trans (realMkLieEquiv_apply n hQ (Y, 0)).symm
  exact congrArg Prod.fst h

/-- On `𝔰𝔭𝔦𝔫(n)`, the differential of the descended rotation homomorphism recovers the differential
of the Spin projection. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom
    (X : LeftInvariantDerivation IS Spin) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (lieMap (realOfSpinSmoothHom n hQ) X) =
      realSpinToSpecialOrthogonalRangeLieEquiv n X := by
  rw [lieMap_lieMap_of_comp_eq (realToSpecialOrthogonalSmoothRange_comp_realOfSpinSmoothHom n hQ),
    realSpinToSpecialOrthogonalRangeLieEquiv_apply]

/-- The differential of the descended rotation homomorphism vanishes on the central circle. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ)
      (lieMap (realOfCircleSmoothHom n hQ) Z) = 0 := by
  rw [lieMap_lieMap_of_comp_eq (realToSpecialOrthogonalSmoothRange_comp_realOfCircleSmoothHom n hQ),
    lieMap_one, zero_apply]

/-- The differential of the descended rotation homomorphism vanishes on `realDetLieLift`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_realDetLieLift (a : ℝ) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realDetLieLift n hQ a) = 0 := by
  -- Congruence avoids costly `isDefEq` unfolding across the Spinᶜ Lie-algebra model.
  exact (congrArg (lieMap (realToSpecialOrthogonalSmoothRange n hQ))
    (realDetLieLift_eq_lieMap_realOfCircleSmoothHom n hQ a)).trans
    (lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom n hQ _)

/-- The canonical Lie-algebra lift `𝔰𝔬(n) →ₗ⁅ℝ⁆ 𝔰𝔭𝔦𝔫ᶜ(n)`, obtained by inverting the differential
of `Spin(n) → SO(n)` and pushing forward along `ofSpin : Spin(n) → Spinᶜ(n)`. Unlike the
group-level maps, this infinitesimal lift exists canonically with no choice of sign. -/
def realSpinOrthogonalLieLift : LeftInvariantDerivation ISO SORange →ₗ⁅ℝ⁆ 𝔤 :=
  (lieMap (realOfSpinSmoothHom n hQ)).comp
    (realSpinToSpecialOrthogonalRangeLieEquiv n).symm.toLieHom

theorem realSpinOrthogonalLieLift_apply (Ω : LeftInvariantDerivation ISO SORange) :
    realSpinOrthogonalLieLift n hQ Ω =
      lieMap (realOfSpinSmoothHom n hQ)
        ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω) := (rfl)

/-- On the differential of the Spin projection, the orthogonal Lie lift recovers the differential
of `ofSpin`. -/
@[simp]
theorem realSpinOrthogonalLieLift_lieMap_realSpinToSpecialOrthogonalSmoothRange
    (X : LeftInvariantDerivation IS Spin) :
    realSpinOrthogonalLieLift n hQ (lieMap (realSpinToSpecialOrthogonalSmoothRange n) X) =
      lieMap (realOfSpinSmoothHom n hQ) X := by
  rw [← realSpinToSpecialOrthogonalRangeLieEquiv_apply, realSpinOrthogonalLieLift_apply,
    LieEquiv.symm_apply_apply]

/-- The orthogonal Lie lift is a right inverse of the differential of `Spinᶜ(n) → SO(n)`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_realSpinOrthogonalLieLift
    (Ω : LeftInvariantDerivation ISO SORange) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realSpinOrthogonalLieLift n hQ Ω) = Ω := by
  rw [realSpinOrthogonalLieLift_apply,
    lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom,
    LieEquiv.apply_symm_apply]

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
      realSpinOrthogonalLieLift n hQ
        ((realCliffordSpecialOrthogonalLieEquivSo n).symm A) := (rfl)

/-- Evaluating `realSoLieLift` on the skew-matrix coordinate of `Ω` recovers
`realSpinOrthogonalLieLift`. -/
@[simp]
theorem realSoLieLift_realCliffordSpecialOrthogonalLieEquivSo
    (Ω : LeftInvariantDerivation ISO SORange) :
    realSoLieLift n hQ (realCliffordSpecialOrthogonalLieEquivSo n Ω) =
      realSpinOrthogonalLieLift n hQ Ω := by
  -- Congruence avoids costly `isDefEq` unfolding across the Spinᶜ Lie-algebra model.
  exact (realSoLieLift_apply n hQ _).trans <| congrArg (realSpinOrthogonalLieLift n hQ)
    ((realCliffordSpecialOrthogonalLieEquivSo n).symm_apply_apply Ω)

/-- Pushing `realSoLieLift` forward along `Spinᶜ(n) → SO(n)` recovers the inverse of
`realCliffordSpecialOrthogonalLieEquivSo`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalSmoothRange_realSoLieLift
    (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    lieMap (realToSpecialOrthogonalSmoothRange n hQ) (realSoLieLift n hQ A) =
      (realCliffordSpecialOrthogonalLieEquivSo n).symm A := by
  rw [realSoLieLift_apply, lieMap_realToSpecialOrthogonalSmoothRange_realSpinOrthogonalLieLift]

/-- `realSoLieLift` lands in the kernel of the determinant differential. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realSoLieLift
    (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    d (realSoLieLift n hQ A) = 0 := by
  rw [realSoLieLift_apply, lieWeight_detContinuousMonoidHom_realSpinOrthogonalLieLift]

/-- `realSoLieLift` lands in the kernel of `lieMap (realDetSmoothHom n hQ)`. -/
@[simp]
theorem lieMap_realDetSmoothHom_realSoLieLift
    (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    lieMap (realDetSmoothHom n hQ) (realSoLieLift n hQ A) = 0 := by
  rw [realSoLieLift_apply, lieMap_realDetSmoothHom_realSpinOrthogonalLieLift]

/-! ### Bijectivity and local diffeomorphism of `Spinᶜ(n) → SO(n) × U(1)` -/

private theorem prodLieEquiv_lieMap_realToSpecialOrthogonalProdDetSmoothHom_lift
    (p : LeftInvariantDerivation ISO SORange × LeftInvariantDerivation (𝓡 1) Circle) :
    TauCeti.Lie.prodLieEquiv (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ)
      (realSpinOrthogonalLieLift n hQ p.1 +
        lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2))) = p := by
  ext <;> simp [realToSpecialOrthogonalProdDetSmoothHom, smul_smul]

/-- Reconstructing an element of `𝔰𝔭𝔦𝔫ᶜ(n)` from its orthogonal projection and determinant weight
recovers the element. -/
@[simp]
theorem realSpinOrthogonalLieLift_add_realDetLieLift (Y : 𝔤) :
    realSpinOrthogonalLieLift n hQ (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y) +
        realDetLieLift n hQ (d Y) = Y := by
  obtain ⟨p, rfl⟩ := EquivLike.surjective (realMkLieEquiv n hQ) Y
  simp only [realMkLieEquiv_apply, map_add,
    lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom,
    realSpinToSpecialOrthogonalRangeLieEquiv_apply,
    lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfCircleSmoothHom, add_zero,
    realSpinOrthogonalLieLift_lieMap_realSpinToSpecialOrthogonalSmoothRange,
    lieWeight_detContinuousMonoidHom_lieMap_realOfSpinSmoothHom, zero_add,
    realDetLieLift_lieWeight_lieMap_realOfCircleSmoothHom]

/-- The inverse of `realMkLieEquiv` projects onto `𝔰𝔭𝔦𝔫(n)` via `Spinᶜ(n) → SO(n)` and halves the
differential of `det` on `Lie(U(1))`. -/
@[simp]
theorem realMkLieEquiv_symm_apply (Y : 𝔤) :
    (realMkLieEquiv n hQ).symm Y =
      ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y),
      (1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y) := by
  -- Congruence avoids costly `isDefEq` unfolding across the Spinᶜ Lie-algebra model.
  apply EquivLike.injective (realMkLieEquiv n hQ)
  have hZ : lieMap (realOfCircleSmoothHom n hQ)
      ((1 / 2 : ℝ) • lieMap (realDetSmoothHom n hQ) Y) = realDetLieLift n hQ (d Y) := by
    refine (congrArg (lieMap (realOfCircleSmoothHom n hQ)) ?_).trans
      (realDetLieLift_eq_lieMap_realOfCircleSmoothHom n hQ (d Y)).symm
    apply circleLieAlgebraEquiv.injective
    rw [map_smul, circleLieAlgebraEquiv_lieMap_realDetSmoothHom,
      LinearEquiv.apply_symm_apply, smul_eq_mul]
    ring
  exact ((realMkLieEquiv n hQ).apply_symm_apply Y).trans <|
    (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y).symm.trans <|
      (congrArg₂ (· + ·) (realSpinOrthogonalLieLift_apply n hQ _) hZ.symm).trans
        (realMkLieEquiv_apply n hQ (_, _)).symm

/-- The Lie map of the paired smooth homomorphism `Spinᶜ(n) → SO(n) × U(1)` is bijective in every
positive dimension (`realCliffordForm n 0 ≠ 0`). -/
theorem lieMap_realToSpecialOrthogonalProdDetSmoothHom_bijective :
    Function.Bijective (lieMap (realToSpecialOrthogonalProdDetSmoothHom n hQ)) :=
  ⟨fun Y₁ Y₂ h ↦ by
    have hSO : lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y₁ =
        lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y₂ := by
      simpa only [realToSpecialOrthogonalProdDetSmoothHom, TauCeti.Lie.lieMap_fst_lieMap_prod]
        using congrArg (lieMap ContMDiffMonoidMorphism.fst) h
    have hd : d Y₁ = d Y₂ := by
      simpa only [realToSpecialOrthogonalProdDetSmoothHom, TauCeti.Lie.lieMap_snd_lieMap_prod,
        circleLieAlgebraEquiv_lieMap_realDetSmoothHom]
        using congrArg (fun Z ↦ circleLieAlgebraEquiv (lieMap ContMDiffMonoidMorphism.snd Z)) h
    -- Congruence avoids costly `isDefEq` unfolding across the Spinᶜ Lie-algebra model.
    exact (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y₁).symm.trans <|
      (congrArg₂ (fun Ω a ↦ realSpinOrthogonalLieLift n hQ Ω + realDetLieLift n hQ a) hSO hd).trans
        (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y₂),
  fun P ↦ ⟨_, (TauCeti.Lie.prodLieEquiv (I := ISO) (I' := 𝓡 1)).injective <|
    prodLieEquiv_lieMap_realToSpecialOrthogonalProdDetSmoothHom_lift n hQ
      (TauCeti.Lie.prodLieEquiv (I := ISO) (I' := 𝓡 1) P)⟩⟩

/-- **The frame-and-determinant map `Spinᶜ(n) → SO(n) × U(1)` is a smooth local diffeomorphism.** -/
theorem isLocalDiffeomorph_realToSpecialOrthogonalProdDetSmoothHom :
    IsLocalDiffeomorph IC ISOProd ∞ (realToSpecialOrthogonalProdDetSmoothHom n hQ) :=
  (realToSpecialOrthogonalProdDetSmoothHom n hQ).isLocalDiffeomorph_of_lieMap_bijective
    (lieMap_realToSpecialOrthogonalProdDetSmoothHom_bijective n hQ)

/-- The Lie-algebra equivalence `𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ⁅ℝ⁆ (𝔰𝔬(n) × Lie(U(1)))` induced by the smooth
frame-and-determinant homomorphism. -/
def realToSpecialOrthogonalProdDetLieEquiv :
    𝔤 ≃ₗ⁅ℝ⁆ (LeftInvariantDerivation ISO SORange × LeftInvariantDerivation (𝓡 1) Circle) :=
  (TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt (realToSpecialOrthogonalProdDetSmoothHom n hQ)
    (isLocalDiffeomorph_realToSpecialOrthogonalProdDetSmoothHom n hQ 1)).trans
      (TauCeti.Lie.prodLieEquiv (I := ISO) (I' := 𝓡 1))

@[simp]
theorem realToSpecialOrthogonalProdDetLieEquiv_apply (Y : 𝔤) :
    realToSpecialOrthogonalProdDetLieEquiv n hQ Y =
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y, lieMap (realDetSmoothHom n hQ) Y) := by
  simp [realToSpecialOrthogonalProdDetLieEquiv, realToSpecialOrthogonalProdDetSmoothHom]

@[simp]
theorem realToSpecialOrthogonalProdDetLieEquiv_symm_apply
    (p : LeftInvariantDerivation ISO SORange × LeftInvariantDerivation (𝓡 1) Circle) :
    (realToSpecialOrthogonalProdDetLieEquiv n hQ).symm p =
      realSpinOrthogonalLieLift n hQ p.1 +
        lieMap (realOfCircleSmoothHom n hQ) ((1 / 2 : ℝ) • p.2) := by
  apply EquivLike.injective (realToSpecialOrthogonalProdDetLieEquiv n hQ)
  refine ((realToSpecialOrthogonalProdDetLieEquiv n hQ).apply_symm_apply p).trans <|
    (prodLieEquiv_lieMap_realToSpecialOrthogonalProdDetSmoothHom_lift n hQ p).symm.trans ?_
  simp only [realToSpecialOrthogonalProdDetLieEquiv, LieEquiv.trans_apply,
    TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply]

/-! ### Identification of the determinant kernel with `𝔰𝔭𝔦𝔫(n)` -/

/-- The Lie-algebra equivalence `𝔰𝔭𝔦𝔫(n) ≃ₗ⁅ℝ⁆ ker(d det)` induced by `ofSpin`. -/
def realOfSpinLieEquivDetKer :
    LeftInvariantDerivation IS Spin ≃ₗ⁅ℝ⁆ (lieMap (realDetSmoothHom n hQ)).ker where
  toFun X := ⟨lieMap (realOfSpinSmoothHom n hQ) X,
    (mem_ker_lieMap_realDetSmoothHom_iff n hQ _).mpr
      (lieWeight_detContinuousMonoidHom_lieMap_realOfSpinSmoothHom n hQ X)⟩
  invFun Y := (realSpinToSpecialOrthogonalRangeLieEquiv n).symm
    (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.val)
  map_add' X Y := Subtype.ext ((lieMap (realOfSpinSmoothHom n hQ)).map_add X Y)
  map_smul' c X := Subtype.ext ((lieMap (realOfSpinSmoothHom n hQ)).map_smul c X)
  map_lie' {X Y} := Subtype.ext ((lieMap (realOfSpinSmoothHom n hQ)).map_lie X Y)
  left_inv X := by
    dsimp only
    rw [lieMap_realToSpecialOrthogonalSmoothRange_lieMap_realOfSpinSmoothHom,
      LieEquiv.symm_apply_apply]
  right_inv Y := Subtype.ext <| by
    -- Rewriting directly in `𝔤` times out in `isDefEq` on `realSpinLieModel`; congruence avoids it.
    have hd0 : realDetLieLift n hQ (d Y.val) = 0 := by
      rw [(mem_ker_lieMap_realDetSmoothHom_iff n hQ Y.val).mp Y.property, map_zero]
    exact (realSpinOrthogonalLieLift_apply n hQ _).symm.trans <| (add_zero _).symm.trans <|
      (congrArg (realSpinOrthogonalLieLift n hQ _ + ·) hd0.symm).trans
        (realSpinOrthogonalLieLift_add_realDetLieLift n hQ Y.val)

@[simp]
theorem coe_realOfSpinLieEquivDetKer_apply (X : LeftInvariantDerivation IS Spin) :
    (realOfSpinLieEquivDetKer n hQ X : 𝔤) = lieMap (realOfSpinSmoothHom n hQ) X := (rfl)

@[simp]
theorem realOfSpinLieEquivDetKer_symm_apply
    (Y : (lieMap (realDetSmoothHom n hQ)).ker) :
    (realOfSpinLieEquivDetKer n hQ).symm Y =
      (realSpinToSpecialOrthogonalRangeLieEquiv n).symm
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y.val) := (rfl)

/-! ### Weight-normalized connection and curvature splitting -/

/-- The weight-normalized linear equivalence `𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ[ℝ] (𝔰𝔬(n) × ℝ)` pairing the differential
of `Spinᶜ(n) → SO(n)` with the determinant weight `d`; its inverse lifts `(Ω, a)` to
`realSpinOrthogonalLieLift n hQ Ω + realDetLieLift n hQ a`. -/
def realToSpecialOrthogonalProdDetLinearEquiv :
    𝔤 ≃ₗ[ℝ] (LeftInvariantDerivation ISO SORange × ℝ) :=
  (realToSpecialOrthogonalProdDetLieEquiv n hQ).toLinearEquiv.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ _) circleLieAlgebraEquiv)

@[simp]
theorem realToSpecialOrthogonalProdDetLinearEquiv_apply (Y : 𝔤) :
    realToSpecialOrthogonalProdDetLinearEquiv n hQ Y =
      (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y, d Y) := by
  simp [realToSpecialOrthogonalProdDetLinearEquiv]

@[simp]
theorem realToSpecialOrthogonalProdDetLinearEquiv_symm_apply
    (p : LeftInvariantDerivation ISO SORange × ℝ) :
    (realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm p =
      realSpinOrthogonalLieLift n hQ p.1 + realDetLieLift n hQ p.2 :=
  (realToSpecialOrthogonalProdDetLinearEquiv n hQ).injective <| by simp

/-- In skew-symmetric matrix coordinates, `𝔰𝔭𝔦𝔫ᶜ(n)` splits linearly as `so(n, ℝ) × ℝ`. -/
def realLinearEquivSoProdReal : 𝔤 ≃ₗ[ℝ] (LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :=
  (realToSpecialOrthogonalProdDetLinearEquiv n hQ).trans
    (LinearEquiv.prodCongr (realCliffordSpecialOrthogonalLieEquivSo n).toLinearEquiv (.refl ℝ ℝ))

@[simp]
theorem realLinearEquivSoProdReal_apply (Y : 𝔤) :
    realLinearEquivSoProdReal n hQ Y =
      (realCliffordSpecialOrthogonalLieEquivSo n
        (lieMap (realToSpecialOrthogonalSmoothRange n hQ) Y), d Y) := by
  simp [realLinearEquivSoProdReal]

@[simp]
theorem realLinearEquivSoProdReal_symm_apply (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    (realLinearEquivSoProdReal n hQ).symm p =
      realSoLieLift n hQ p.1 + realDetLieLift n hQ p.2 :=
  (realLinearEquivSoProdReal n hQ).injective <| by simp

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
        ofCircle _ hQ (Circle.exp (a / 2)) :=
  (congrArg lieExp (realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (Ω, a))).trans <|
    (lieExp_add_realDetLieLift n hQ _ a).trans <| congrArg (· * _) <|
      (congrArg lieExp (realSpinOrthogonalLieLift_apply n hQ Ω)).trans <|
        (map_lieExp (realOfSpinSmoothHom n hQ) _).symm.trans (realOfSpinSmoothHom_apply n hQ _)

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
        (TauCeti.Lie.Ad (I := ISO) (realToSpecialOrthogonalSmoothRange n hQ g) Ω, a) :=
  (realToSpecialOrthogonalProdDetLinearEquiv n hQ).injective <|
    (realToSpecialOrthogonalProdDetLinearEquiv_Ad n hQ g _).trans (by simp)

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
