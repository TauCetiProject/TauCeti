/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.LieAlgebra
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Covering

/-!
# The Spinᶜ rotation-and-determinant projection and Lie-algebra splitting

The compact `Spinᶜ(n)` group projects onto the special orthogonal group via `[s, z] ↦ π(s)` and
onto the circle via the weight-two determinant `[s, z] ↦ z²`. Realizing `SO(n)` on its closed
matrix-units range `SpecialOrthogonalUnitsRange(n)` gives smooth homomorphisms

* `realToSpecialOrthogonalRange : Spinᶜ(n) →ₜ* SpecialOrthogonalUnitsRange(n)`, and
* `realToSpecialOrthogonalProdDetRange : Spinᶜ(n) →ₜ* SpecialOrthogonalUnitsRange(n) × Circle`.

Differentiating these homomorphisms yields the second fundamental exact sequence of `Lie(Spinᶜ(n))`
and the `𝔰𝔬(n) ⊕ ℝ` connection-lifting isomorphism:

* the Lie differential of `realToSpecialOrthogonalRange` vanishes on the central determinant lift
  (its kernel is `range (realDetLieLift n hQ)`) and restricts on `ofSpin_* (Lie(Spin(n)))` to the
  invertible Spin-to-`SO(n)` differential `realSpinToSpecialOrthogonalLieEquiv`;
* the paired projection `realToSpecialOrthogonalProdDetRange` has bijective Lie map, so it is a
  smooth local diffeomorphism and a two-sheeted smooth covering map with smooth local sections
  through every fiber point;
* combining the inverse Spin-to-`SO(n)` differential with `realSpinProdDetLinearEquiv` produces
  linear equivalences
  `realSpecialOrthogonalProdDetLinearEquiv : Lie(SO(n)) × ℝ ≃ₗ[ℝ] Lie(Spinᶜ(n))` and
  `realSoProdDetLinearEquiv : 𝔰𝔬(n) × ℝ ≃ₗ[ℝ] Lie(Spinᶜ(n))` whose inverse sends any
  `Y ∈ Lie(Spinᶜ(n))` to `(π_*(Y), d det(Y))`, preserves Lie brackets via
  `⁅(A, a), (B, b)⁆ = (⁅A, B⁆, 0)`, and is `Ad`-equivariant under every `g ∈ Spinᶜ(n)` via
  `Ad(g) (Y_SO, a) = (Ad(π(g)) Y_SO, a)`.

## Main definitions

* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalRange` and
  `realToSpecialOrthogonalSmoothRange`: the rotation homomorphism from `Spinᶜ(n)` to the closed
  `SO(n)` matrix-units carrier.
* `CliffordAlgebra.spinCGroup.realSpinToSpecialOrthogonalLieEquiv`: the Lie-algebra isomorphism
  `Lie(Spin(n)) ≃ₗ⁅ℝ⁆ Lie(SO(n))` on the native compact Spin carrier.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalProdDetRange` and
  `realToSpecialOrthogonalProdDetSmoothRange`: the paired rotation-and-determinant homomorphism
  `Spinᶜ(n) → SO(n) × Circle`.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalProdDetLieEquiv`: the Lie-algebra isomorphism
  `Lie(Spinᶜ(n)) ≃ₗ⁅ℝ⁆ Lie(SO(n)) × Lie(Circle)`.
* `CliffordAlgebra.spinCGroup.realSpecialOrthogonalProdDetLinearEquiv` and
  `realSoProdDetLinearEquiv`: the `Lie(SO(n)) × ℝ` and `𝔰𝔬(n) × ℝ` splittings of `Lie(Spinᶜ(n))`.

## Main results

* `CliffordAlgebra.spinCGroup.ker_lieMap_realToSpecialOrthogonalRange_toLinearMap`: the kernel of
  the rotation differential is the central determinant line `range (realDetLieLift n hQ)`.
* `CliffordAlgebra.spinCGroup.realSpecialOrthogonalProdDetLinearEquiv_symm_apply`: every element of
  `Lie(Spinᶜ(n))` is reconstructed from its `Lie(SO(n))` projection and its normalized determinant
  weight.
* `CliffordAlgebra.spinCGroup.lie_realSoProdDetLinearEquiv`: bracket preservation in `𝔰𝔬(n) × ℝ`
  coordinates.
* `CliffordAlgebra.spinCGroup.Ad_realSpecialOrthogonalProdDetLinearEquiv`: full `Spinᶜ(n)` adjoint
  equivariance of the `Lie(SO(n)) × ℝ` lift.
* `CliffordAlgebra.spinCGroup.isLocalDiffeomorph_realToSpecialOrthogonalProdDetSmoothRange`,
  `isCoveringMap_realToSpecialOrthogonalProdDetRange`, and
  `exists_realSpinCSmoothCoveringTrivialization`: smooth covering trivializations with smooth local
  sections through every point of the fiber.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Manifold TauCeti TauCeti.CliffordAlgebra
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace CliffordAlgebra.spinCGroup

variable (n : ℕ) (hQ : realCliffordForm n 0 ≠ 0)

local notation "IS" => 𝓘(ℝ, realSpinLieModel n)
local notation "IC" => ModelWithCorners.prod IS (𝓡 1)

local notation "SpinUnitsRange" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpecialOrthogonalUnitsRange" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))

local notation "SpecialOrthogonalLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) SpecialOrthogonalUnitsRange)

local notation "ISO" => 𝓘(ℝ, SpecialOrthogonalLieModel)
local notation "ISP" => ModelWithCorners.prod ISO (𝓡 1)
local notation "G" => spinCGroup (realCliffordForm n 0) hQ
local notation "𝔤" => LeftInvariantDerivation IC G
local notation "𝔰" => LeftInvariantDerivation IS (spinGroup (realCliffordForm n 0))
local notation "𝔬" => LeftInvariantDerivation ISO SpecialOrthogonalUnitsRange
local notation "d" => ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ)

/-- The Lie-algebra isomorphism `Lie(Spin(n)) ≃ₗ⁅ℝ⁆ Lie(SO(n))` from native compact Spin to the
closed `SO(n)` matrix-units carrier. -/
def realSpinToSpecialOrthogonalLieEquiv : 𝔰 ≃ₗ⁅ℝ⁆ 𝔬 :=
  (realSpinLieEquivUnitsRange n).trans (realCliffordSpinToSpecialOrthogonalRangeLieEquiv n)

/-- Evaluation of `realSpinToSpecialOrthogonalLieEquiv`. -/
@[simp]
theorem realSpinToSpecialOrthogonalLieEquiv_apply (X : 𝔰) :
    realSpinToSpecialOrthogonalLieEquiv n X =
      realCliffordSpinToSpecialOrthogonalRangeLieEquiv n (realSpinLieEquivUnitsRange n X) :=
  (rfl)

/-- The rotation homomorphism on compact `Spinᶜ(n)` into the closed `SO(n)` matrix-units
carrier. -/
def realToSpecialOrthogonalRange : G →ₜ* SpecialOrthogonalUnitsRange where
  toMonoidHom :=
    (realCliffordSpecialOrthogonalContinuousMulEquivCarrierRange n).toMonoidHom.comp
      (toSpecialOrthogonal (realCliffordForm n 0) hQ)
  continuous_toFun :=
    (realCliffordSpecialOrthogonalContinuousMulEquivCarrierRange n).continuous.comp
      (continuous_toSpecialOrthogonal (realCliffordForm n 0) hQ)

/-- `realToSpecialOrthogonalRange` transports `toSpecialOrthogonal` into the matrix-units range. -/
theorem realToSpecialOrthogonalRange_apply (g : G) :
    realToSpecialOrthogonalRange n hQ g =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (toSpecialOrthogonal (realCliffordForm n 0) hQ g) :=
  realCliffordSpecialOrthogonalContinuousMulEquivCarrierRange_apply n _

/-- The smooth rotation homomorphism on compact `Spinᶜ(n)`. -/
def realToSpecialOrthogonalSmoothRange :
    ContMDiffMonoidMorphism IC ISO ∞ G SpecialOrthogonalUnitsRange :=
  (realToSpecialOrthogonalRange n hQ).toContMDiffMonoidMorphism IC ISO

/-- `realToSpecialOrthogonalSmoothRange` has the same underlying map as
`realToSpecialOrthogonalRange`. -/
@[simp]
theorem realToSpecialOrthogonalSmoothRange_apply (g : G) :
    realToSpecialOrthogonalSmoothRange n hQ g = realToSpecialOrthogonalRange n hQ g :=
  congrFun
    (ContinuousMonoidHom.coe_toContMDiffMonoidMorphism (I := IC) (I' := ISO)
      (realToSpecialOrthogonalRange n hQ)) g

/-- The rotation projection is trivial on the central circle of `Spinᶜ(n)`. -/
@[simp]
theorem realToSpecialOrthogonalRange_comp_ofCircleContinuousMonoidHom :
    (realToSpecialOrthogonalRange n hQ).comp (ofCircleContinuousMonoidHom _ hQ) = 1 :=
  ContinuousMonoidHom.ext fun z ↦ by
    rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, ContinuousMonoidHom.coe_one,
      Pi.one_apply, ofCircleContinuousMonoidHom_apply, realToSpecialOrthogonalRange_apply,
      toSpecialOrthogonal_ofCircle, map_one]

/-- Restricting `realToSpecialOrthogonalRange` to `Spin(n)` recovers the compact Spin projection
into `SO(n)`. -/
@[simp]
theorem realToSpecialOrthogonalRange_comp_ofSpinContinuousMonoidHom :
    (realToSpecialOrthogonalRange n hQ).comp (ofSpinContinuousMonoidHom _ hQ) =
      (realCliffordSpinToSpecialOrthogonalCarrierRange n).comp
        (realCliffordSpinContinuousMulEquivUnitsRange n :
          spinGroup (realCliffordForm n 0) →ₜ* SpinUnitsRange) :=
  ContinuousMonoidHom.ext fun s ↦ by
    rw [ContinuousMonoidHom.coe_comp, Function.comp_apply,
      ContinuousMonoidHom.coe_comp, Function.comp_apply,
      ofSpinContinuousMonoidHom_apply, realToSpecialOrthogonalRange_apply,
      toSpecialOrthogonal_ofSpin, realCliffordSpecialOrthogonalContinuousMulEquivRange_apply]
    simp only [ContinuousMonoidHom.coe_coe, realCliffordSpinContinuousMulEquivUnitsRange_apply,
      realCliffordSpinToSpecialOrthogonalCarrierRange_apply]
    exact (realCliffordSpinToSpecialOrthogonalRange_apply_toUnits n s).symm

local notation "πO" =>
  ContinuousMonoidHom.lieMap (I := IC) (I' := ISO) (realToSpecialOrthogonalRange n hQ)

/-- The Lie differential of `realToSpecialOrthogonalRange` vanishes on the central circle Lie
algebra. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_lieMap_ofCircle
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    πO (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
      (ofCircleContinuousMonoidHom _ hQ) Z) = 0 := by
  have h := LieHom.congr_fun
    (ContinuousMonoidHom.lieMap_comp (I := 𝓡 1) (I' := IC) (I'' := ISO)
      (ofCircleContinuousMonoidHom _ hQ) (realToSpecialOrthogonalRange n hQ)) Z
  simpa only [LieHom.comp_apply, realToSpecialOrthogonalRange_comp_ofCircleContinuousMonoidHom,
    ContinuousMonoidHom.lieMap_one, zero_apply] using h.symm

/-- The Lie differential of `realToSpecialOrthogonalRange` vanishes on `realDetLieLift`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_realDetLieLift (a : ℝ) :
    πO (realDetLieLift n hQ a) = 0 :=
  (congrArg (πO) (realDetLieLift_apply n hQ a)).trans
    (lieMap_realToSpecialOrthogonalRange_lieMap_ofCircle n hQ _)

/-- On `ofSpin_* X`, the Lie differential of `realToSpecialOrthogonalRange` agrees with
`realSpinToSpecialOrthogonalLieEquiv`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_lieMap_ofSpin (X : 𝔰) :
    πO (ContinuousMonoidHom.lieMap (I := IS) (I' := IC)
      (ofSpinContinuousMonoidHom _ hQ) X) = realSpinToSpecialOrthogonalLieEquiv n X := by
  have hlie := LieHom.congr_fun
    (congrArg (ContinuousMonoidHom.lieMap (I := IS) (I' := ISO))
      (realToSpecialOrthogonalRange_comp_ofSpinContinuousMonoidHom n hQ)) X
  simpa only [ContinuousMonoidHom.lieMap_comp (I := IS) (I' := IC) (I'' := ISO),
    ContinuousMonoidHom.lieMap_comp (I := IS) (I' := IS) (I'' := ISO),
    LieHom.comp_apply, realSpinToSpecialOrthogonalLieEquiv_apply,
    realCliffordSpinToSpecialOrthogonalRangeLieEquiv_apply,
    realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_continuousMonoidHomLieMap,
    realSpinLieEquivUnitsRange_apply] using hlie

/-- Evaluating the rotation differential on `realSpinProdDetLinearEquiv (X, a)` projects onto the
Spin factor via `realSpinToSpecialOrthogonalLieEquiv`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_realSpinProdDetLinearEquiv (p : 𝔰 × ℝ) :
    πO (realSpinProdDetLinearEquiv n hQ p) = realSpinToSpecialOrthogonalLieEquiv n p.1 :=
  (congrArg (πO) (realSpinProdDetLinearEquiv_apply n hQ p)).trans <| (map_add (πO) _ _).trans <|
    (congrArg₂ (· + ·) (lieMap_realToSpecialOrthogonalRange_lieMap_ofSpin n hQ p.1)
      (lieMap_realToSpecialOrthogonalRange_realDetLieLift n hQ p.2)).trans (add_zero _)

/-- **Exactness of the rotation differential**: the kernel of `(realToSpecialOrthogonalRange)_*` is
precisely the central determinant line `range (realDetLieLift n hQ)`. -/
@[simp]
theorem ker_lieMap_realToSpecialOrthogonalRange_toLinearMap :
    LinearMap.ker (πO).toLinearMap = LinearMap.range (realDetLieLift n hQ) := by
  refine SetLike.ext fun Y ↦ ⟨fun hY ↦ ?_, ?_⟩
  · let p := (realSpinProdDetLinearEquiv n hQ).symm Y
    have hp : realSpinProdDetLinearEquiv n hQ p = Y :=
      (realSpinProdDetLinearEquiv n hQ).apply_symm_apply Y
    have hp1 : p.1 = 0 := EquivLike.injective (realSpinToSpecialOrthogonalLieEquiv n) <|
      (lieMap_realToSpecialOrthogonalRange_realSpinProdDetLinearEquiv n hQ p).symm.trans <|
        (congrArg (πO) hp).trans (hY.trans (map_zero _).symm)
    exact ⟨p.2, by simpa only [realSpinProdDetLinearEquiv_apply, hp1, map_zero, zero_add] using hp⟩
  · rintro ⟨a, rfl⟩
    exact lieMap_realToSpecialOrthogonalRange_realDetLieLift n hQ a

/-- The paired rotation-and-determinant continuous homomorphism
`Spinᶜ(n) →ₜ* SpecialOrthogonalUnitsRange(n) × Circle`. -/
def realToSpecialOrthogonalProdDetRange : G →ₜ* SpecialOrthogonalUnitsRange × Circle :=
  (realToSpecialOrthogonalRange n hQ).prod (detContinuousMonoidHom _ hQ)

/-- Pointwise evaluation of `realToSpecialOrthogonalProdDetRange`. -/
@[simp]
theorem realToSpecialOrthogonalProdDetRange_apply (g : G) :
    realToSpecialOrthogonalProdDetRange n hQ g =
      (realToSpecialOrthogonalRange n hQ g, det (realCliffordForm n 0) hQ g) :=
  Prod.ext rfl (detContinuousMonoidHom_apply _ hQ g)

/-- The paired rotation-and-determinant smooth homomorphism on compact `Spinᶜ(n)`. -/
def realToSpecialOrthogonalProdDetSmoothRange :
    ContMDiffMonoidMorphism IC ISP ∞ G (SpecialOrthogonalUnitsRange × Circle) :=
  (realToSpecialOrthogonalProdDetRange n hQ).toContMDiffMonoidMorphism IC ISP

/-- `realToSpecialOrthogonalProdDetSmoothRange` has the same underlying map as
`realToSpecialOrthogonalProdDetRange`. -/
@[simp]
theorem realToSpecialOrthogonalProdDetSmoothRange_apply (g : G) :
    realToSpecialOrthogonalProdDetSmoothRange n hQ g =
      realToSpecialOrthogonalProdDetRange n hQ g :=
  congrFun
    (ContinuousMonoidHom.coe_toContMDiffMonoidMorphism (I := IC) (I' := ISP)
      (realToSpecialOrthogonalProdDetRange n hQ)) g

/-- **The `Lie(SO(n)) × ℝ` splitting of `Lie(Spinᶜ(n))`**. It lifts an infinitesimal orthogonal
transformation via `(realSpinToSpecialOrthogonalLieEquiv n).symm` and a determinant weight via
`realDetLieLift`. -/
def realSpecialOrthogonalProdDetLinearEquiv : (𝔬 × ℝ) ≃ₗ[ℝ] 𝔤 :=
  (LinearEquiv.prodCongr (realSpinToSpecialOrthogonalLieEquiv n).symm.toLinearEquiv
    (LinearEquiv.refl ℝ ℝ)).trans (realSpinProdDetLinearEquiv n hQ)

/-- Evaluation of `realSpecialOrthogonalProdDetLinearEquiv` in terms of
`realSpinProdDetLinearEquiv`. -/
theorem realSpecialOrthogonalProdDetLinearEquiv_apply (p : 𝔬 × ℝ) :
    realSpecialOrthogonalProdDetLinearEquiv n hQ p =
      realSpinProdDetLinearEquiv n hQ ((realSpinToSpecialOrthogonalLieEquiv n).symm p.1, p.2) :=
  (rfl)

/-- Projecting `realSpecialOrthogonalProdDetLinearEquiv (W, a)` to `Lie(SO(n))` recovers `W`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_realSpecialOrthogonalProdDetLinearEquiv (p : 𝔬 × ℝ) :
    πO (realSpecialOrthogonalProdDetLinearEquiv n hQ p) = p.1 :=
  (lieMap_realToSpecialOrthogonalRange_realSpinProdDetLinearEquiv n hQ
    ((realSpinToSpecialOrthogonalLieEquiv n).symm p.1, p.2)).trans
      ((realSpinToSpecialOrthogonalLieEquiv n).apply_symm_apply p.1)

/-- Evaluating the determinant weight on `realSpecialOrthogonalProdDetLinearEquiv (W, a)` recovers
`a`. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realSpecialOrthogonalProdDetLinearEquiv (p : 𝔬 × ℝ) :
    d (realSpecialOrthogonalProdDetLinearEquiv n hQ p) = p.2 :=
  lieWeight_detContinuousMonoidHom_realSpinProdDetLinearEquiv n hQ
    ((realSpinToSpecialOrthogonalLieEquiv n).symm p.1, p.2)

/-- **Canonical coordinates on `Lie(Spinᶜ(n))`**: the inverse of
`realSpecialOrthogonalProdDetLinearEquiv` sends every `Y ∈ Lie(Spinᶜ(n))` to its rotation
differential and normalized determinant weight `(π_*(Y), d det(Y))`. -/
@[simp]
theorem realSpecialOrthogonalProdDetLinearEquiv_symm_apply (Y : 𝔤) :
    (realSpecialOrthogonalProdDetLinearEquiv n hQ).symm Y = (πO Y, d Y) := by
  let p := (realSpecialOrthogonalProdDetLinearEquiv n hQ).symm Y
  have hp := (realSpecialOrthogonalProdDetLinearEquiv n hQ).apply_symm_apply Y
  exact Prod.ext
    ((lieMap_realToSpecialOrthogonalRange_realSpecialOrthogonalProdDetLinearEquiv
      n hQ p).symm.trans (congrArg (πO) hp))
    ((lieWeight_detContinuousMonoidHom_realSpecialOrthogonalProdDetLinearEquiv
      n hQ p).symm.trans (congrArg d hp))

/-- Lie brackets in `Lie(SO(n)) × ℝ` coordinates preserve the `Lie(SO(n))` bracket and annihilate
the central determinant parameter. -/
@[simp]
theorem lie_realSpecialOrthogonalProdDetLinearEquiv (p q : 𝔬 × ℝ) :
    ⁅realSpecialOrthogonalProdDetLinearEquiv n hQ p,
        realSpecialOrthogonalProdDetLinearEquiv n hQ q⁆ =
      realSpecialOrthogonalProdDetLinearEquiv n hQ (⁅p.1, q.1⁆, 0) :=
  lie_realSpinProdDetLinearEquiv_comp_lieEquiv n hQ
    (realSpinToSpecialOrthogonalLieEquiv n).symm p q

/-- **Full `Spinᶜ(n)` adjoint equivariance of the `Lie(SO(n)) × ℝ` lift**: any `g ∈ Spinᶜ(n)` acts
through its `SO(n)` image on the first component and trivially on the determinant component. -/
@[simp]
theorem Ad_realSpecialOrthogonalProdDetLinearEquiv (g : G) (p : 𝔬 × ℝ) :
    Lie.Ad (I := IC) g (realSpecialOrthogonalProdDetLinearEquiv n hQ p) =
      realSpecialOrthogonalProdDetLinearEquiv n hQ
        (Lie.Ad (I := ISO) (realToSpecialOrthogonalRange n hQ g) p.1, p.2) :=
  (realSpecialOrthogonalProdDetLinearEquiv n hQ).symm.injective <|
    (realSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ _).trans <|
      (Prod.ext
        ((ContinuousMonoidHom.lieMap_Ad (realToSpecialOrthogonalRange n hQ) g _).trans <|
          congrArg _ (lieMap_realToSpecialOrthogonalRange_realSpecialOrthogonalProdDetLinearEquiv
            n hQ p))
        ((ContinuousMonoidHom.lieWeight_Ad (detContinuousMonoidHom _ hQ) g _).trans
          (lieWeight_detContinuousMonoidHom_realSpecialOrthogonalProdDetLinearEquiv n hQ p))).trans
        ((realSpecialOrthogonalProdDetLinearEquiv n hQ).symm_apply_apply _).symm

/-- **The `𝔰𝔬(n) × ℝ` splitting of `Lie(Spinᶜ(n))`**, lifting a skew-symmetric matrix and a real
determinant parameter to `Lie(Spinᶜ(n))`. -/
def realSoProdDetLinearEquiv : (LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) ≃ₗ[ℝ] 𝔤 :=
  (LinearEquiv.prodCongr (realCliffordSpecialOrthogonalLieEquivSo n).symm.toLinearEquiv
    (LinearEquiv.refl ℝ ℝ)).trans (realSpecialOrthogonalProdDetLinearEquiv n hQ)

/-- Evaluation of `realSoProdDetLinearEquiv` in terms of
`realSpecialOrthogonalProdDetLinearEquiv`. -/
theorem realSoProdDetLinearEquiv_apply (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    realSoProdDetLinearEquiv n hQ p =
      realSpecialOrthogonalProdDetLinearEquiv n hQ
        ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1, p.2) :=
  (rfl)

/-- Projecting `realSoProdDetLinearEquiv (A, a)` to `𝔰𝔬(n)` recovers `A`. -/
@[simp]
theorem realCliffordSpecialOrthogonalLieEquivSo_lieMap_realSoProdDetLinearEquiv
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    realCliffordSpecialOrthogonalLieEquivSo n (πO (realSoProdDetLinearEquiv n hQ p)) = p.1 :=
  (congrArg (realCliffordSpecialOrthogonalLieEquivSo n)
    (lieMap_realToSpecialOrthogonalRange_realSpecialOrthogonalProdDetLinearEquiv n hQ
      ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1, p.2))).trans
    ((realCliffordSpecialOrthogonalLieEquivSo n).apply_symm_apply p.1)

/-- Evaluating the determinant weight on `realSoProdDetLinearEquiv (A, a)` recovers `a`. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realSoProdDetLinearEquiv
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    d (realSoProdDetLinearEquiv n hQ p) = p.2 :=
  lieWeight_detContinuousMonoidHom_realSpecialOrthogonalProdDetLinearEquiv n hQ
    ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1, p.2)

/-- Inverse of `realSoProdDetLinearEquiv`: it returns the skew-symmetric matrix coordinate of the
rotation differential together with the normalized determinant weight. -/
@[simp]
theorem realSoProdDetLinearEquiv_symm_apply (Y : 𝔤) :
    (realSoProdDetLinearEquiv n hQ).symm Y =
      (realCliffordSpecialOrthogonalLieEquivSo n (πO Y), d Y) :=
  (realSoProdDetLinearEquiv n hQ).injective <|
    ((realSoProdDetLinearEquiv n hQ).apply_symm_apply Y).trans <|
      ((realSpecialOrthogonalProdDetLinearEquiv n hQ).apply_symm_apply Y).symm.trans <|
        (congrArg (realSpecialOrthogonalProdDetLinearEquiv n hQ)
          (realSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ Y)).trans <|
          congrArg (fun W : 𝔬 ↦ realSpecialOrthogonalProdDetLinearEquiv n hQ (W, d Y))
            ((realCliffordSpecialOrthogonalLieEquivSo n).symm_apply_apply _).symm

/-- Lie brackets in `𝔰𝔬(n) × ℝ` coordinates preserve the matrix commutator on `𝔰𝔬(n)` and
annihilate the central determinant parameter. -/
@[simp]
theorem lie_realSoProdDetLinearEquiv (p q : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    ⁅realSoProdDetLinearEquiv n hQ p, realSoProdDetLinearEquiv n hQ q⁆ =
      realSoProdDetLinearEquiv n hQ (⁅p.1, q.1⁆, 0) :=
  lie_realSpinProdDetLinearEquiv_comp_lieEquiv n hQ
    ((realCliffordSpecialOrthogonalLieEquivSo n).symm.trans
      (realSpinToSpecialOrthogonalLieEquiv n).symm) p q

/-- Compatibility of the two routes from native Spin to skew matrices: taking quadratic Clifford
coordinates then applying `realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv` agrees with
projecting to `Lie(SO(n))` via `realSpinToSpecialOrthogonalLieEquiv` then taking skew-matrix
coordinates. -/
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv_realSpinLieEquivQuadratic
    (X : 𝔰) :
    realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv n (realSpinLieEquivQuadratic n X) =
      realCliffordSpecialOrthogonalLieEquivSo n (realSpinToSpecialOrthogonalLieEquiv n X) := by
  simp only [realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv_apply,
    realCliffordSpinToSpecialOrthogonalCoordinateLieHom_apply, realSpinLieEquivQuadratic_apply,
    LieEquiv.symm_apply_apply, realSpinToSpecialOrthogonalLieEquiv_apply,
    realCliffordSpinToSpecialOrthogonalRangeLieEquiv_apply]

/-- Comparison between `𝔰𝔬(n) × ℝ` coordinates and quadratic Clifford–determinant coordinates on
`Lie(Spinᶜ(n))` via the Spin-to-`𝔰𝔬(n)` coordinate equivalence
`realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv`. -/
theorem realSoProdDetLinearEquiv_eq_realQuadraticProdDetLinearEquiv
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    realSoProdDetLinearEquiv n hQ p =
      realQuadraticProdDetLinearEquiv n hQ
        ((realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv n).symm p.1, p.2) := by
  rw [realSoProdDetLinearEquiv_apply, realSpecialOrthogonalProdDetLinearEquiv_apply,
    realQuadraticProdDetLinearEquiv_apply]
  let X : 𝔰 := (realSpinLieEquivQuadratic n).symm
    ((realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv n).symm p.1)
  have hcomp : p.1 =
      realCliffordSpecialOrthogonalLieEquivSo n (realSpinToSpecialOrthogonalLieEquiv n X) := by
    simpa only [X, LieEquiv.apply_symm_apply] using
      realCliffordSpinToSpecialOrthogonalCoordinateLieEquiv_realSpinLieEquivQuadratic n X
  have hspin : (realSpinToSpecialOrthogonalLieEquiv n).symm
        ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1) = X := by
    rw [hcomp, LieEquiv.symm_apply_apply, LieEquiv.symm_apply_apply]
  rw [hspin]

/-- The Lie differential of the paired rotation-and-determinant homomorphism
`Spinᶜ(n) → SO(n) × Circle` is bijective. -/
theorem lieMap_realToSpecialOrthogonalProdDetRange_bijective :
    Function.Bijective
      (ContinuousMonoidHom.lieMap (I := IC) (I' := ISP)
        (realToSpecialOrthogonalProdDetRange n hQ)) := by
  let e : 𝔤 ≃ₗ[ℝ] 𝔬 × LeftInvariantDerivation (𝓡 1) Circle :=
    (realSpecialOrthogonalProdDetLinearEquiv n hQ).symm.trans
      (LinearEquiv.prodCongr (LinearEquiv.refl ℝ 𝔬) circleLieAlgebraEquiv.symm)
  have hfun :
      (fun Y : 𝔤 ↦ (πO Y, ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1)
          (detContinuousMonoidHom _ hQ) Y)) = ⇑e := by
    funext Y
    dsimp only [e]
    rw [LinearEquiv.trans_apply, realSpecialOrthogonalProdDetLinearEquiv_symm_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      ContinuousMonoidHom.lieWeight_apply, LinearEquiv.symm_apply_apply]
  unfold realToSpecialOrthogonalProdDetRange
  rw [TauCeti.Lie.bijective_lieMap_prod_iff, hfun]
  exact e.bijective

/-- The Lie-algebra equivalence `Lie(Spinᶜ(n)) ≃ₗ⁅ℝ⁆ Lie(SO(n)) × Lie(Circle)` induced by the
paired rotation-and-determinant projection. -/
def realToSpecialOrthogonalProdDetLieEquiv :
    𝔤 ≃ₗ⁅ℝ⁆ 𝔬 × LeftInvariantDerivation (𝓡 1) Circle :=
  (LieEquiv.ofBijective
    (ContinuousMonoidHom.lieMap (I := IC) (I' := ISP)
      (realToSpecialOrthogonalProdDetRange n hQ))
    (lieMap_realToSpecialOrthogonalProdDetRange_bijective n hQ)).trans
      TauCeti.Lie.prodLieEquiv

/-- `realToSpecialOrthogonalProdDetLieEquiv` acts by the rotation and determinant Lie maps. -/
@[simp]
theorem realToSpecialOrthogonalProdDetLieEquiv_apply (Y : 𝔤) :
    realToSpecialOrthogonalProdDetLieEquiv n hQ Y =
      (πO Y, ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1) (detContinuousMonoidHom _ hQ) Y) := by
  unfold realToSpecialOrthogonalProdDetLieEquiv realToSpecialOrthogonalProdDetRange
  exact TauCeti.Lie.prodLieEquiv_continuousMonoidHom_lieMap_prod
    (realToSpecialOrthogonalRange n hQ) (detContinuousMonoidHom _ hQ) Y

/-- The paired rotation-and-determinant homomorphism is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_realToSpecialOrthogonalProdDetRange :
    IsLocalDiffeomorph IC ISP ∞ (realToSpecialOrthogonalProdDetRange n hQ) :=
  ContinuousMonoidHom.isLocalDiffeomorph_of_lieMap_bijective
    (realToSpecialOrthogonalProdDetRange n hQ)
    (lieMap_realToSpecialOrthogonalProdDetRange_bijective n hQ)

/-- The smooth bundled rotation-and-determinant homomorphism is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_realToSpecialOrthogonalProdDetSmoothRange :
    IsLocalDiffeomorph IC ISP ∞ (realToSpecialOrthogonalProdDetSmoothRange n hQ) := by
  have hcoe : ⇑(realToSpecialOrthogonalProdDetSmoothRange n hQ) =
      ⇑(realToSpecialOrthogonalProdDetRange n hQ) :=
    funext (realToSpecialOrthogonalProdDetSmoothRange_apply n hQ)
  exact hcoe.symm ▸ isLocalDiffeomorph_realToSpecialOrthogonalProdDetRange n hQ

/-- The paired rotation-and-determinant homomorphism `Spinᶜ(n) → SO(n) × Circle` is surjective. -/
theorem realToSpecialOrthogonalProdDetRange_surjective :
    Function.Surjective (realToSpecialOrthogonalProdDetRange n hQ) := by
  rintro ⟨y, z⟩
  obtain ⟨g, hg⟩ := toSpecialOrthogonal_prod_det_surjective (realCliffordForm n 0) hQ
    (spinToSpecialOrthogonal_surjective_of_posDef (realCliffordForm n 0)
      (posDef_realCliffordForm_zero n))
    ((realCliffordSpecialOrthogonalContinuousMulEquivRange n).symm y, z)
  refine ⟨g, (realToSpecialOrthogonalProdDetRange_apply n hQ g).trans
    (Prod.ext ?_ (Prod.mk.inj hg).2)⟩
  rw [realToSpecialOrthogonalRange_apply]
  exact (congrArg (realCliffordSpecialOrthogonalContinuousMulEquivRange n) (Prod.mk.inj hg).1).trans
    ((realCliffordSpecialOrthogonalContinuousMulEquivRange n).apply_symm_apply y)

/-- The paired rotation-and-determinant homomorphism is a topological covering map onto
`SpecialOrthogonalUnitsRange(n) × Circle`. -/
theorem isCoveringMap_realToSpecialOrthogonalProdDetRange :
    IsCoveringMap (realToSpecialOrthogonalProdDetRange n hQ) := by
  let e : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) × Circle ≃ₜ
      SpecialOrthogonalUnitsRange × Circle :=
    Homeomorph.prodCongr
      (realCliffordSpecialOrthogonalContinuousMulEquivCarrierRange n).toHomeomorph
      (Homeomorph.refl Circle)
  have hfun : ⇑(realToSpecialOrthogonalProdDetRange n hQ) =
      e ∘ ((toSpecialOrthogonal (realCliffordForm n 0) hQ).prod
        (det (realCliffordForm n 0) hQ)) :=
    funext (realToSpecialOrthogonalProdDetRange_apply n hQ)
  exact hfun.symm ▸ (isQuotientCoveringMap_toSpecialOrthogonal_prod_det (realCliffordForm n 0) hQ
    (Or.inl (posDef_realCliffordForm_zero n))).isCoveringMap.homeomorph_comp e

/-- Every pair `(y, z)` of an orthogonal frame transformation and determinant phase has an evenly
covered neighborhood over which every sheet is a smooth local section into `Spinᶜ(n)` passing
through its prescribed fiber lift. -/
theorem exists_realSpinCSmoothCoveringTrivialization
    (y : SpecialOrthogonalUnitsRange × Circle) :
    ∃ t : Bundle.Trivialization
        ((realToSpecialOrthogonalProdDetSmoothRange n hQ) ⁻¹' {y})
        (realToSpecialOrthogonalProdDetSmoothRange n hQ),
      y ∈ t.baseSet ∧
      (∀ a : (realToSpecialOrthogonalProdDetSmoothRange n hQ) ⁻¹' {y},
        t.toOpenPartialHomeomorph.symm (y, a) = a) ∧
      ∀ a : (realToSpecialOrthogonalProdDetSmoothRange n hQ) ⁻¹' {y},
        ContMDiffOn ISP IC ∞
          (fun w ↦ t.toOpenPartialHomeomorph.symm (w, a)) t.baseSet := by
  have hmap : ⇑(realToSpecialOrthogonalProdDetSmoothRange n hQ) =
      ⇑(realToSpecialOrthogonalProdDetRange n hQ) :=
    funext (realToSpecialOrthogonalProdDetSmoothRange_apply n hQ)
  have hcov : IsCoveringMap (realToSpecialOrthogonalProdDetSmoothRange n hQ) :=
    hmap.symm ▸ isCoveringMap_realToSpecialOrthogonalProdDetRange n hQ
  exact hcov.exists_trivialization_contMDiffOn_symm
    (isLocalDiffeomorph_realToSpecialOrthogonalProdDetSmoothRange n hQ)
    ((hmap.symm ▸ realToSpecialOrthogonalProdDetRange_surjective n hQ) y)

end CliffordAlgebra.spinCGroup
