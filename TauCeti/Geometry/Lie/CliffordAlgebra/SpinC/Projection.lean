/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.LieAlgebra
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Covering
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.LieAlgebra
public import TauCeti.Algebra.Lie.Abelian
import TauCeti.Algebra.Lie.Basic

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
  smooth local diffeomorphism and a smooth quotient covering map (with the same kernel as the
  native projection `toSpecialOrthogonal.prod det`) having smooth local sections through every
  fiber point;
* combining the inverse Spin-to-`SO(n)` differential with `realSpinProdDetLinearEquiv` produces
  the Lie-algebra equivalence
  `realToSoProdDetLieEquiv : Lie(Spinᶜ(n)) ≃ₗ⁅ℝ⁆ 𝔰𝔬(n) × AbelianLieAlgebra ℝ`,
  together with the linear splittings
  `realSpecialOrthogonalProdDetLinearEquiv : Lie(SO(n)) × ℝ ≃ₗ[ℝ] Lie(Spinᶜ(n))` and
  `realSoProdDetLinearEquiv : 𝔰𝔬(n) × ℝ ≃ₗ[ℝ] Lie(Spinᶜ(n))` (derived from
  `realToSoProdDetLieEquiv`) whose inverse sends any `Y ∈ Lie(Spinᶜ(n))` to `(π_*(Y), d det(Y))`,
  preserves Lie brackets via `⁅(A, a), (B, b)⁆ = (⁅A, B⁆, 0)`, and is `Ad`-equivariant under every
  `g ∈ Spinᶜ(n)` via `Ad(g) (Y_SO, a) = (Ad(π(g)) Y_SO, a)`.

## Main definitions

* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalRange`: the rotation homomorphism from
  `Spinᶜ(n)` to the closed `SO(n)` matrix-units carrier.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalProdDetRange`: the paired
  rotation-and-determinant homomorphism `Spinᶜ(n) → SO(n) × Circle`.
* `CliffordAlgebra.spinCGroup.realToSpecialOrthogonalProdDetLieEquiv`: the Lie-algebra isomorphism
  `Lie(Spinᶜ(n)) ≃ₗ⁅ℝ⁆ Lie(SO(n)) × Lie(Circle)`.
* `CliffordAlgebra.spinCGroup.realToSoProdDetLieEquiv`: the normalized Lie-algebra isomorphism
  `Lie(Spinᶜ(n)) ≃ₗ⁅ℝ⁆ 𝔰𝔬(n) × AbelianLieAlgebra ℝ`.
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
* `CliffordAlgebra.spinCGroup.Ad_realSpecialOrthogonalProdDetLinearEquiv` and
  `Ad_realSoProdDetLinearEquiv`: full `Spinᶜ(n)` adjoint equivariance of the `Lie(SO(n)) × ℝ` and
  `𝔰𝔬(n) × ℝ` lifts.
* `CliffordAlgebra.spinCGroup.ker_realToSpecialOrthogonalProdDetRange`,
  `isQuotientCoveringMap_realToSpecialOrthogonalProdDetRange`,
  `isLocalDiffeomorph_realToSpecialOrthogonalProdDetRange`,
  `isCoveringMap_realToSpecialOrthogonalProdDetRange`, and
  `exists_realSpinCSmoothCoveringTrivialization`: kernel comparison, quotient-covering property,
  local diffeomorphism, and smooth covering trivializations with smooth local sections through
  every point of the fiber.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Manifold TauCeti TauCeti.CliffordAlgebra
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

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

private def realSpecialOrthogonalContinuousMulEquivRange :
    QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) ≃ₜ*
      SpecialOrthogonalUnitsRange where
  toMulEquiv := (realCliffordSpecialOrthogonalContinuousMulEquivRange n).toMulEquiv
  continuous_toFun :=
    -- `realCliffordSpecialOrthogonalContinuousMulEquivRange` uses the entrywise matrix topology,
    -- while this file selects `Matrix.linftyOpTopologicalSpace`; both agree by
    -- `Matrix.linftyOpTopologicalSpace_eq`.
    (Matrix.linftyOpTopologicalSpace_eq (Fin n) (Fin n) ℝ).symm ▸
      (realCliffordSpecialOrthogonalContinuousMulEquivRange n).continuous_toFun
  continuous_invFun :=
    (Matrix.linftyOpTopologicalSpace_eq (Fin n) (Fin n) ℝ).symm ▸
      (realCliffordSpecialOrthogonalContinuousMulEquivRange n).continuous_invFun

private theorem realSpecialOrthogonalContinuousMulEquivRange_apply
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) :
    realSpecialOrthogonalContinuousMulEquivRange n g =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n g :=
  -- Both continuous equivalences wrap the same underlying `toMulEquiv`.
  rfl

/-- The rotation homomorphism on compact `Spinᶜ(n)` into the closed `SO(n)` matrix-units
carrier. -/
def realToSpecialOrthogonalRange : G →ₜ* SpecialOrthogonalUnitsRange where
  toMonoidHom :=
    (realSpecialOrthogonalContinuousMulEquivRange n).toMonoidHom.comp
      (toSpecialOrthogonal (realCliffordForm n 0) hQ)
  continuous_toFun :=
    (realSpecialOrthogonalContinuousMulEquivRange n).continuous.comp
      (continuous_toSpecialOrthogonal_pi (realCliffordForm n 0) hQ)

/-- `realToSpecialOrthogonalRange` transports `toSpecialOrthogonal` into the matrix-units range. -/
theorem realToSpecialOrthogonalRange_apply (g : G) :
    realToSpecialOrthogonalRange n hQ g =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (toSpecialOrthogonal (realCliffordForm n 0) hQ g) :=
  realSpecialOrthogonalContinuousMulEquivRange_apply n
    (toSpecialOrthogonal (realCliffordForm n 0) hQ g)

/-- On a quotient representative `[s, z]`, `realToSpecialOrthogonalRange` evaluates to the matrix
of `π(s)`. -/
@[simp]
theorem realToSpecialOrthogonalRange_mk (p : spinGroup (realCliffordForm n 0) × Circle) :
    realToSpecialOrthogonalRange n hQ (mk _ hQ p) =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (spinToSpecialOrthogonal (realCliffordForm n 0) p.1) := by
  rw [realToSpecialOrthogonalRange_apply, toSpecialOrthogonal_mk]

/-- On `ofSpin s`, `realToSpecialOrthogonalRange` evaluates to the matrix of `π(s)`. -/
@[simp]
theorem realToSpecialOrthogonalRange_ofSpin (s : spinGroup (realCliffordForm n 0)) :
    realToSpecialOrthogonalRange n hQ (ofSpin _ hQ s) =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (spinToSpecialOrthogonal (realCliffordForm n 0) s) := by
  rw [realToSpecialOrthogonalRange_apply, toSpecialOrthogonal_ofSpin]

/-- On the central circle inclusion `ofCircle z`, `realToSpecialOrthogonalRange` is trivial. -/
@[simp]
theorem realToSpecialOrthogonalRange_ofCircle (z : Circle) :
    realToSpecialOrthogonalRange n hQ (ofCircle _ hQ z) = 1 := by
  rw [realToSpecialOrthogonalRange_apply, toSpecialOrthogonal_ofCircle, map_one]

/-- The rotation projection is trivial on the central circle of `Spinᶜ(n)`. -/
@[simp]
theorem realToSpecialOrthogonalRange_comp_ofCircleContinuousMonoidHom :
    (realToSpecialOrthogonalRange n hQ).comp (ofCircleContinuousMonoidHom _ hQ) = 1 := by
  ext z
  simp

/-- The compact real Spin projection between the closed units-range carriers, viewed on the
operator-norm matrix topology of `SpecialOrthogonalUnitsRange(n)`. -/
def realSpinToSpecialOrthogonalRange : SpinUnitsRange →ₜ* SpecialOrthogonalUnitsRange where
  toMonoidHom := (realCliffordSpinToSpecialOrthogonalRange n).toMonoidHom
  continuous_toFun :=
    -- `realCliffordSpinToSpecialOrthogonalRange` uses the entrywise matrix topology, while this
    -- file selects `Matrix.linftyOpTopologicalSpace` (`Matrix.linftyOpTopologicalSpace_eq`).
    (Matrix.linftyOpTopologicalSpace_eq (Fin n) (Fin n) ℝ).symm ▸
      (realCliffordSpinToSpecialOrthogonalRange n).continuous

/-- Pointwise evaluation of `realSpinToSpecialOrthogonalRange` agrees with
`realCliffordSpinToSpecialOrthogonalRange`. -/
@[simp]
theorem realSpinToSpecialOrthogonalRange_apply (x : SpinUnitsRange) :
    realSpinToSpecialOrthogonalRange n x =
      realCliffordSpinToSpecialOrthogonalRange n x :=
  -- Both continuous homomorphisms share the same underlying `toMonoidHom`.
  (rfl)

/-- Restricting `realToSpecialOrthogonalRange` to `Spin(n)` recovers the compact Spin projection
into `SO(n)`. -/
@[simp]
theorem realToSpecialOrthogonalRange_comp_ofSpinContinuousMonoidHom :
    (realToSpecialOrthogonalRange n hQ).comp (ofSpinContinuousMonoidHom _ hQ) =
      (realSpinToSpecialOrthogonalRange n).comp
        (realCliffordSpinContinuousMulEquivUnitsRange n :
          spinGroup (realCliffordForm n 0) →ₜ* SpinUnitsRange) := by
  ext1 s
  rw [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_comp,
    Function.comp_apply, Function.comp_apply, ContinuousMonoidHom.coe_coe,
    ofSpinContinuousMonoidHom_apply, realToSpecialOrthogonalRange_ofSpin,
    realSpinToSpecialOrthogonalRange_apply,
    realCliffordSpecialOrthogonalContinuousMulEquivRange_apply,
    realCliffordSpinContinuousMulEquivUnitsRange_apply]
  exact (realCliffordSpinToSpecialOrthogonalRange_apply_toUnits n s).symm

local notation "πO" =>
  ContinuousMonoidHom.lieMap (I := IC) (I' := ISO) (realToSpecialOrthogonalRange n hQ)

/-- The Lie differential of `realToSpecialOrthogonalRange` vanishes on the central circle Lie
algebra. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_lieMap_ofCircleContinuousMonoidHom
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    πO (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
      (ofCircleContinuousMonoidHom _ hQ) Z) = 0 := by
  rw [← ContinuousMonoidHom.lieMap_comp_apply (I := 𝓡 1) (I' := IC) (I'' := ISO)
      (ofCircleContinuousMonoidHom _ hQ) (realToSpecialOrthogonalRange n hQ) Z,
    realToSpecialOrthogonalRange_comp_ofCircleContinuousMonoidHom,
    ContinuousMonoidHom.lieMap_one, zero_apply]

/-- The Lie differential of `realToSpecialOrthogonalRange` vanishes on `realDetLieLift`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_realDetLieLift (a : ℝ) :
    πO (realDetLieLift n hQ a) = 0 :=
  (congrArg (πO) (realDetLieLift_apply n hQ a)).trans
    (lieMap_realToSpecialOrthogonalRange_lieMap_ofCircleContinuousMonoidHom n hQ _)

/-- On `ofSpin_* X`, the Lie differential of `realToSpecialOrthogonalRange` agrees with
`realSpinToSpecialOrthogonalLieEquiv`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_lieMap_ofSpinContinuousMonoidHom (X : 𝔰) :
    πO (ContinuousMonoidHom.lieMap (I := IS) (I' := IC)
      (ofSpinContinuousMonoidHom _ hQ) X) = realSpinToSpecialOrthogonalLieEquiv n X := by
  -- Factor through the composite `Spin(n) → Spinᶜ(n) → SO(n)`, which agrees with the compact
  -- Spin-to-SO(n) projection on `SpinUnitsRange(n)`.
  calc
    πO (ContinuousMonoidHom.lieMap (I := IS) (I' := IC)
        (ofSpinContinuousMonoidHom _ hQ) X)
      = ContinuousMonoidHom.lieMap (I := IS) (I' := ISO)
          ((realToSpecialOrthogonalRange n hQ).comp (ofSpinContinuousMonoidHom _ hQ)) X :=
        (ContinuousMonoidHom.lieMap_comp_apply (I := IS) (I' := IC) (I'' := ISO)
          (ofSpinContinuousMonoidHom _ hQ) (realToSpecialOrthogonalRange n hQ) X).symm
    _ = ContinuousMonoidHom.lieMap (I := IS) (I' := ISO)
          ((realSpinToSpecialOrthogonalRange n).comp
            (realCliffordSpinContinuousMulEquivUnitsRange n :
              spinGroup (realCliffordForm n 0) →ₜ* SpinUnitsRange)) X := by
        rw [realToSpecialOrthogonalRange_comp_ofSpinContinuousMonoidHom]
    _ = realSpinToSpecialOrthogonalLieEquiv n X := by
        symm
        simp only [realSpinToSpecialOrthogonalLieEquiv_apply,
          realCliffordSpinToSpecialOrthogonalRangeLieEquiv_apply,
          realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_continuousMonoidHomLieMap,
          realSpinLieEquivUnitsRange_apply]
        exact (ContinuousMonoidHom.lieMap_comp_apply (I := IS) (I' := IS) (I'' := ISO)
          (realCliffordSpinContinuousMulEquivUnitsRange n :
            spinGroup (realCliffordForm n 0) →ₜ* SpinUnitsRange)
          (realSpinToSpecialOrthogonalRange n) X).symm

/-- Evaluating the rotation differential on `realSpinProdDetLinearEquiv (X, a)` projects onto the
Spin factor via `realSpinToSpecialOrthogonalLieEquiv`. -/
@[simp]
theorem lieMap_realToSpecialOrthogonalRange_realSpinProdDetLinearEquiv (p : 𝔰 × ℝ) :
    πO (realSpinProdDetLinearEquiv n hQ p) = realSpinToSpecialOrthogonalLieEquiv n p.1 := by
  rw [realSpinProdDetLinearEquiv_apply]
  simp only [map_add, lieMap_realToSpecialOrthogonalRange_lieMap_ofSpinContinuousMonoidHom,
    lieMap_realToSpecialOrthogonalRange_realDetLieLift, add_zero]

/-- **Exactness of the rotation differential**: the kernel of `(realToSpecialOrthogonalRange)_*` is
precisely the central determinant line `range (realDetLieLift n hQ)`. -/
@[simp]
theorem ker_lieMap_realToSpecialOrthogonalRange_toLinearMap :
    LinearMap.ker (πO).toLinearMap = LinearMap.range (realDetLieLift n hQ) := by
  ext Y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hY
    let p := (realSpinProdDetLinearEquiv n hQ).symm Y
    have hp : realSpinProdDetLinearEquiv n hQ p = Y :=
      (realSpinProdDetLinearEquiv n hQ).apply_symm_apply Y
    have hp1 : p.1 = 0 := by
      apply EquivLike.injective (realSpinToSpecialOrthogonalLieEquiv n)
      rw [← lieMap_realToSpecialOrthogonalRange_realSpinProdDetLinearEquiv n hQ p, hp,
        ← LieHom.coe_toLinearMap, hY, map_zero]
    exact ⟨p.2, by simpa only [realSpinProdDetLinearEquiv_apply, hp1, map_zero, zero_add] using hp⟩
  · rintro ⟨a, rfl⟩
    rw [LieHom.coe_toLinearMap]
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
    πO (realSpecialOrthogonalProdDetLinearEquiv n hQ p) = p.1 := by
  rw [realSpecialOrthogonalProdDetLinearEquiv_apply,
    lieMap_realToSpecialOrthogonalRange_realSpinProdDetLinearEquiv, LieEquiv.apply_symm_apply]

/-- Evaluating the determinant weight on `realSpecialOrthogonalProdDetLinearEquiv (W, a)` recovers
`a`. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realSpecialOrthogonalProdDetLinearEquiv (p : 𝔬 × ℝ) :
    d (realSpecialOrthogonalProdDetLinearEquiv n hQ p) = p.2 := by
  rw [realSpecialOrthogonalProdDetLinearEquiv_apply,
    lieWeight_detContinuousMonoidHom_realSpinProdDetLinearEquiv]

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
      realSpecialOrthogonalProdDetLinearEquiv n hQ (⁅p.1, q.1⁆, 0) := by
  simp only [realSpecialOrthogonalProdDetLinearEquiv_apply,
    lie_realSpinProdDetLinearEquiv_comp_lieEquiv]

/-- **Full `Spinᶜ(n)` adjoint equivariance of the `Lie(SO(n)) × ℝ` lift**: any `g ∈ Spinᶜ(n)` acts
through its `SO(n)` image on the first component and trivially on the determinant component. -/
@[simp]
theorem Ad_realSpecialOrthogonalProdDetLinearEquiv (g : G) (p : 𝔬 × ℝ) :
    Lie.Ad (I := IC) g (realSpecialOrthogonalProdDetLinearEquiv n hQ p) =
      realSpecialOrthogonalProdDetLinearEquiv n hQ
        (Lie.Ad (I := ISO) (realToSpecialOrthogonalRange n hQ g) p.1, p.2) := by
  apply (realSpecialOrthogonalProdDetLinearEquiv n hQ).symm.injective
  rw [realSpecialOrthogonalProdDetLinearEquiv_symm_apply, LinearEquiv.symm_apply_apply]
  apply Prod.ext
  · simp only [ContinuousMonoidHom.lieMap_Ad,
      lieMap_realToSpecialOrthogonalRange_realSpecialOrthogonalProdDetLinearEquiv]
  · simp only [ContinuousMonoidHom.lieWeight_Ad,
      lieWeight_detContinuousMonoidHom_realSpecialOrthogonalProdDetLinearEquiv]

private def realToSpecialOrthogonalProdCircleLinearEquiv :
    𝔤 ≃ₗ[ℝ] 𝔬 × LeftInvariantDerivation (𝓡 1) Circle :=
  (realSpecialOrthogonalProdDetLinearEquiv n hQ).symm.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ 𝔬) circleLieAlgebraEquiv.symm)

private theorem realToSpecialOrthogonalProdCircleLinearEquiv_apply (Y : 𝔤) :
    realToSpecialOrthogonalProdCircleLinearEquiv n hQ Y =
      (πO Y, ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1)
        (detContinuousMonoidHom _ hQ) Y) := by
  rw [realToSpecialOrthogonalProdCircleLinearEquiv, LinearEquiv.trans_apply,
    realSpecialOrthogonalProdDetLinearEquiv_symm_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, ContinuousMonoidHom.lieWeight_apply, LinearEquiv.symm_apply_apply]

/-- The Lie differential of the paired rotation-and-determinant homomorphism
`Spinᶜ(n) → SO(n) × Circle` is bijective. -/
theorem lieMap_realToSpecialOrthogonalProdDetRange_bijective :
    Function.Bijective
      (ContinuousMonoidHom.lieMap (I := IC) (I' := ISP)
        (realToSpecialOrthogonalProdDetRange n hQ)) := by
  have hfun :
      (fun Y : 𝔤 ↦ (πO Y, ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1)
          (detContinuousMonoidHom _ hQ) Y)) =
        realToSpecialOrthogonalProdCircleLinearEquiv n hQ :=
    funext fun Y ↦ (realToSpecialOrthogonalProdCircleLinearEquiv_apply n hQ Y).symm
  unfold realToSpecialOrthogonalProdDetRange
  rw [TauCeti.Lie.bijective_lieMap_prod_iff, hfun]
  exact (realToSpecialOrthogonalProdCircleLinearEquiv n hQ).bijective

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
  rw [realToSpecialOrthogonalProdDetLieEquiv, LieEquiv.trans_apply,
    LieEquiv.ofBijective_apply, realToSpecialOrthogonalProdDetRange,
    TauCeti.Lie.prodLieEquiv_continuousMonoidHom_lieMap_prod]

/-- Inverse of `realToSpecialOrthogonalProdDetLieEquiv`: it lifts a pair `(W, X)` of
`Lie(SO(n)) × Lie(Circle)` via `realSpecialOrthogonalProdDetLinearEquiv` and
`circleLieAlgebraEquiv`. -/
@[simp]
theorem realToSpecialOrthogonalProdDetLieEquiv_symm_apply
    (p : 𝔬 × LeftInvariantDerivation (𝓡 1) Circle) :
    (realToSpecialOrthogonalProdDetLieEquiv n hQ).symm p =
      realSpecialOrthogonalProdDetLinearEquiv n hQ (p.1, circleLieAlgebraEquiv p.2) := by
  apply (realToSpecialOrthogonalProdDetLieEquiv n hQ).symm_apply_eq.mpr
  rw [realToSpecialOrthogonalProdDetLieEquiv_apply,
    ← realToSpecialOrthogonalProdCircleLinearEquiv_apply,
    realToSpecialOrthogonalProdCircleLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  exact Prod.ext rfl (LinearEquiv.symm_apply_apply _ _).symm

private def realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv :
    (𝔬 × LeftInvariantDerivation (𝓡 1) Circle) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ × AbelianLieAlgebra ℝ where
  __ := LinearEquiv.prodCongr
    (realCliffordSpecialOrthogonalLieEquivSo n).toLinearEquiv
    (circleLieAlgebraEquiv.trans (AbelianLieAlgebra.equiv ℝ ℝ).symm)
  map_lie' {p q} := Prod.ext
    ((realCliffordSpecialOrthogonalLieEquivSo n).map_lie p.1 q.1)
    (by
      simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_toLinearMap, LinearEquiv.prodCongr_apply]
      rw [← LieHom.snd_apply (R := ℝ), (LieHom.snd ℝ _ _).map_lie, LieHom.snd_apply,
        LieHom.snd_apply, LieModule.IsTrivial.trivial, map_zero,
        ← LieHom.snd_apply (R := ℝ), (LieHom.snd ℝ _ _).map_lie,
        AbelianLieAlgebra.lie_eq_zero])

private theorem realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv_apply
    (p : 𝔬 × LeftInvariantDerivation (𝓡 1) Circle) :
    realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv n p =
      (realCliffordSpecialOrthogonalLieEquivSo n p.1,
        (AbelianLieAlgebra.equiv ℝ ℝ).symm (circleLieAlgebraEquiv p.2)) :=
  -- `realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv.toLinearEquiv` is built via
  -- `__ := LinearEquiv.prodCongr ...`, so evaluation unfolds definitionally to both factors.
  rfl

private theorem realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv_symm_apply
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × AbelianLieAlgebra ℝ) :
    (realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv n).symm p =
      ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1,
        circleLieAlgebraEquiv.symm (AbelianLieAlgebra.equiv ℝ ℝ p.2)) := by
  apply (realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv n).symm_apply_eq.mpr
  rw [realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv_apply]
  simp only [LieEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

/-- **The `𝔰𝔬(n) × AbelianLieAlgebra ℝ` Lie-algebra equivalence of `Lie(Spinᶜ(n))`**: it pairs
the skew-symmetric matrix rotation differential with the normalized determinant weight. -/
def realToSoProdDetLieEquiv :
    𝔤 ≃ₗ⁅ℝ⁆ LieAlgebra.Orthogonal.so (Fin n) ℝ × AbelianLieAlgebra ℝ :=
  (realToSpecialOrthogonalProdDetLieEquiv n hQ).trans
    (realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv n)

/-- Forward evaluation of `realToSoProdDetLieEquiv` in skew-matrix and determinant coordinates. -/
@[simp]
theorem realToSoProdDetLieEquiv_apply (Y : 𝔤) :
    realToSoProdDetLieEquiv n hQ Y =
      (realCliffordSpecialOrthogonalLieEquivSo n (πO Y),
        (AbelianLieAlgebra.equiv ℝ ℝ).symm (d Y)) := by
  rw [realToSoProdDetLieEquiv, LieEquiv.trans_apply, realToSpecialOrthogonalProdDetLieEquiv_apply]
  exact Prod.ext rfl (congrArg (AbelianLieAlgebra.equiv ℝ ℝ).symm
    (ContinuousMonoidHom.lieWeight_apply _ Y).symm)

/-- Inverse evaluation of `realToSoProdDetLieEquiv`. -/
@[simp]
theorem realToSoProdDetLieEquiv_symm_apply
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × AbelianLieAlgebra ℝ) :
    (realToSoProdDetLieEquiv n hQ).symm p =
      realSpecialOrthogonalProdDetLinearEquiv n hQ
        ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1,
          AbelianLieAlgebra.equiv ℝ ℝ p.2) := by
  rw [realToSoProdDetLieEquiv, LieEquiv.symm_trans, LieEquiv.trans_apply,
    realSpecialOrthogonalProdCircleToSoProdAbelianLieEquiv_symm_apply,
    realToSpecialOrthogonalProdDetLieEquiv_symm_apply, LinearEquiv.apply_symm_apply]

/-- **The `𝔰𝔬(n) × ℝ` splitting of `Lie(Spinᶜ(n))`**, lifting a skew-symmetric matrix and a real
determinant parameter to `Lie(Spinᶜ(n))`, obtained as the linear view of
`realToSoProdDetLieEquiv`. -/
def realSoProdDetLinearEquiv : (LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) ≃ₗ[ℝ] 𝔤 :=
  (LinearEquiv.prodCongr (LinearEquiv.refl ℝ _) (AbelianLieAlgebra.equiv ℝ ℝ).symm).trans
    (realToSoProdDetLieEquiv n hQ).symm.toLinearEquiv

/-- Evaluation of `realSoProdDetLinearEquiv` in terms of
`realSpecialOrthogonalProdDetLinearEquiv`. -/
theorem realSoProdDetLinearEquiv_apply (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    realSoProdDetLinearEquiv n hQ p =
      realSpecialOrthogonalProdDetLinearEquiv n hQ
        ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1, p.2) := by
  rw [realSoProdDetLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LieEquiv.coe_toLinearEquiv, realToSoProdDetLieEquiv_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- Projecting `realSoProdDetLinearEquiv (A, a)` to `𝔰𝔬(n)` recovers `A`. -/
@[simp]
theorem realCliffordSpecialOrthogonalLieEquivSo_lieMap_realSoProdDetLinearEquiv
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    realCliffordSpecialOrthogonalLieEquivSo n (πO (realSoProdDetLinearEquiv n hQ p)) = p.1 := by
  rw [realSoProdDetLinearEquiv_apply,
    lieMap_realToSpecialOrthogonalRange_realSpecialOrthogonalProdDetLinearEquiv,
    LieEquiv.apply_symm_apply]

/-- Evaluating the determinant weight on `realSoProdDetLinearEquiv (A, a)` recovers `a`. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realSoProdDetLinearEquiv
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    d (realSoProdDetLinearEquiv n hQ p) = p.2 := by
  rw [realSoProdDetLinearEquiv_apply,
    lieWeight_detContinuousMonoidHom_realSpecialOrthogonalProdDetLinearEquiv]

/-- Inverse of `realSoProdDetLinearEquiv`: it returns the skew-symmetric matrix coordinate of the
rotation differential together with the normalized determinant weight. -/
@[simp]
theorem realSoProdDetLinearEquiv_symm_apply (Y : 𝔤) :
    (realSoProdDetLinearEquiv n hQ).symm Y =
      (realCliffordSpecialOrthogonalLieEquivSo n (πO Y), d Y) := by
  rw [realSoProdDetLinearEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.prodCongr_symm,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    LinearEquiv.symm_symm]
  have hsymm :
      ((realToSoProdDetLieEquiv n hQ).symm.toLinearEquiv).symm Y =
        realToSoProdDetLieEquiv n hQ Y :=
    (LinearEquiv.symm_apply_eq _).mpr
      (by rw [LieEquiv.coe_toLinearEquiv, LieEquiv.symm_apply_apply])
  rw [hsymm, realToSoProdDetLieEquiv_apply, LinearEquiv.apply_symm_apply]

/-- Lie brackets in `𝔰𝔬(n) × ℝ` coordinates preserve the matrix commutator on `𝔰𝔬(n)` and
annihilate the central determinant parameter. -/
@[simp]
theorem lie_realSoProdDetLinearEquiv (p q : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    ⁅realSoProdDetLinearEquiv n hQ p, realSoProdDetLinearEquiv n hQ q⁆ =
      realSoProdDetLinearEquiv n hQ (⁅p.1, q.1⁆, 0) := by
  simp only [realSoProdDetLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LieEquiv.coe_toLinearEquiv]
  rw [← (realToSoProdDetLieEquiv n hQ).symm.map_lie]
  have hlie :
      ⁅(p.1, (AbelianLieAlgebra.equiv ℝ ℝ).symm p.2),
        (q.1, (AbelianLieAlgebra.equiv ℝ ℝ).symm q.2)⁆ =
      (⁅p.1, q.1⁆, (AbelianLieAlgebra.equiv ℝ ℝ).symm 0) :=
    Prod.ext rfl ((AbelianLieAlgebra.lie_eq_zero _ _).trans (map_zero _).symm)
  rw [hlie]

private theorem coe_realCliffordSpecialOrthogonalLieEquivSo_Ad
    (u : SpecialOrthogonalUnitsRange) (W : 𝔬) :
    ((realCliffordSpecialOrthogonalLieEquivSo n (Lie.Ad (I := ISO) u W) :
        LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      ((u : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
        ((realCliffordSpecialOrthogonalLieEquivSo n W :
          LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
        ((u : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  rw [coe_realCliffordSpecialOrthogonalLieEquivSo_apply,
    TauCeti.Lie.EmbeddedLieSubgroupData.lieMapSubtypeVal_apply,
    ContMDiffMonoidMorphism.lieMap_Ad,
    TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply,
    TauCeti.Lie.unitsLieAlgebraLieEquiv_apply, TauCeti.Lie.unitsLieAlgebraEquiv_Ad,
    ← TauCeti.Lie.unitsLieAlgebraLieEquiv_apply,
    ← TauCeti.Lie.EmbeddedLieSubgroupData.lieMapSubtypeVal_apply,
    ← coe_realCliffordSpecialOrthogonalLieEquivSo_apply]
  have hu : ((u : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) ∈
      Matrix.specialOrthogonalGroup (Fin n) ℝ :=
    (QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff n
      (u : GL (Fin n) ℝ)).mp u.property
  rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv hu.1.2]
  -- `GL (Fin n) ℝ` is definitionally `(Matrix (Fin n) (Fin n) ℝ)ˣ` and `u.val` is
  -- `(u : GL (Fin n) ℝ)`.
  rfl

/-- **Full `Spinᶜ(n)` adjoint equivariance of the `𝔰𝔬(n) × ℝ` lift**: any `g ∈ Spinᶜ(n)` acts on
the rotation matrix component by conjugation by its projected special-orthogonal matrix and fixes
the determinant component. -/
@[simp]
theorem Ad_realSoProdDetLinearEquiv (g : G) (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    Lie.Ad (I := IC) g (realSoProdDetLinearEquiv n hQ p) =
      realSoProdDetLinearEquiv n hQ
        (⟨((realToSpecialOrthogonalRange n hQ g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
            (p.1 : Matrix (Fin n) (Fin n) ℝ) *
            ((realToSpecialOrthogonalRange n hQ g : GL (Fin n) ℝ) :
              Matrix (Fin n) (Fin n) ℝ)ᵀ,
          by
            simpa only [LieAlgebra.Orthogonal.mem_so, skewAdjoint.mem_iff,
              Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
              skewAdjoint.conjugate (R := Matrix (Fin n) (Fin n) ℝ)
                (by simpa only [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
                  Matrix.conjTranspose_eq_transpose_of_trivial, ← LieAlgebra.Orthogonal.mem_so]
                  using p.1.property)
                ((realToSpecialOrthogonalRange n hQ g : GL (Fin n) ℝ) :
                  Matrix (Fin n) (Fin n) ℝ)⟩, p.2) := by
  apply (realSoProdDetLinearEquiv n hQ).symm.injective
  rw [realSoProdDetLinearEquiv_symm_apply, LinearEquiv.symm_apply_apply]
  apply Prod.ext
  · apply Subtype.ext
    rw [ContinuousMonoidHom.lieMap_Ad, coe_realCliffordSpecialOrthogonalLieEquivSo_Ad,
      realCliffordSpecialOrthogonalLieEquivSo_lieMap_realSoProdDetLinearEquiv]
  · simp only [ContinuousMonoidHom.lieWeight_Ad,
      lieWeight_detContinuousMonoidHom_realSoProdDetLinearEquiv]

/-- Comparison between `𝔰𝔬(n) × ℝ` coordinates and quadratic Clifford–determinant coordinates on
`Lie(Spinᶜ(n))` via `CliffordAlgebra.matrixSoEquivQuadratic`. -/
theorem realSoProdDetLinearEquiv_eq_realQuadraticProdDetLinearEquiv
    (p : LieAlgebra.Orthogonal.so (Fin n) ℝ × ℝ) :
    realSoProdDetLinearEquiv n hQ p =
      realQuadraticProdDetLinearEquiv n hQ
        (matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
          (realCliffordFormZeroIsometryWeightedSumSquares n) p.1, p.2) := by
  rw [realSoProdDetLinearEquiv_apply, realSpecialOrthogonalProdDetLinearEquiv_apply,
    realQuadraticProdDetLinearEquiv_apply]
  let X : 𝔰 := (realSpinLieEquivQuadratic n).symm
    (matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
      (realCliffordFormZeroIsometryWeightedSumSquares n) p.1)
  have hcomp : p.1 = realSpinLieEquivSo n X := by
    apply (matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
      (realCliffordFormZeroIsometryWeightedSumSquares n)).injective
    simp only [LieEquiv.coe_toLieHom]
    rw [← realSpinLieEquivQuadratic_eq_matrixSoEquivQuadratic_realSpinLieEquivSo]
    exact ((realSpinLieEquivQuadratic n).apply_symm_apply _).symm
  have hspin : (realSpinToSpecialOrthogonalLieEquiv n).symm
        ((realCliffordSpecialOrthogonalLieEquivSo n).symm p.1) = X := by
    rw [hcomp, realSpinLieEquivSo_eq, LieEquiv.trans_apply,
      LieEquiv.symm_apply_apply, LieEquiv.symm_apply_apply]
  rw [hspin]

/-- The paired rotation-and-determinant homomorphism is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_realToSpecialOrthogonalProdDetRange :
    IsLocalDiffeomorph IC ISP ∞ (realToSpecialOrthogonalProdDetRange n hQ) :=
  ContinuousMonoidHom.isLocalDiffeomorph_of_lieMap_bijective
    (realToSpecialOrthogonalProdDetRange n hQ)
    (lieMap_realToSpecialOrthogonalProdDetRange_bijective n hQ)

private def realSpecialOrthogonalProdCircleHomeomorph :
    QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) × Circle ≃ₜ
      SpecialOrthogonalUnitsRange × Circle :=
  Homeomorph.prodCongr
    (realSpecialOrthogonalContinuousMulEquivRange n).toHomeomorph
    (Homeomorph.refl Circle)

private theorem coe_realToSpecialOrthogonalProdDetRange :
    ⇑(realToSpecialOrthogonalProdDetRange n hQ) =
      realSpecialOrthogonalProdCircleHomeomorph n ∘
        ((toSpecialOrthogonal (realCliffordForm n 0) hQ).prod
          (det (realCliffordForm n 0) hQ)) := by
  funext g
  apply Prod.ext
  · exact (realToSpecialOrthogonalRange_apply n hQ g).trans
      (realSpecialOrthogonalContinuousMulEquivRange_apply n _).symm
  · exact detContinuousMonoidHom_apply _ hQ g

/-- The kernel of the smooth bundled projection `realToSpecialOrthogonalProdDetRange` coincides
with the kernel of the native rotation-and-determinant projection. -/
theorem ker_realToSpecialOrthogonalProdDetRange :
    (realToSpecialOrthogonalProdDetRange n hQ).ker =
      ((toSpecialOrthogonal (realCliffordForm n 0) hQ).prod
        (det (realCliffordForm n 0) hQ)).ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  have hf :
      (realToSpecialOrthogonalProdDetRange n hQ).toMonoidHom g =
        realToSpecialOrthogonalProdDetRange n hQ g :=
    DFunLike.congr_fun
      (ContinuousMonoidHom.coe_toMonoidHom (realToSpecialOrthogonalProdDetRange n hQ)) g
  rw [hf, realToSpecialOrthogonalProdDetRange_apply, MonoidHom.prod_apply, Prod.mk_eq_one,
    Prod.mk_eq_one, realToSpecialOrthogonalRange_apply,
    map_eq_one_iff _ (realCliffordSpecialOrthogonalContinuousMulEquivRange n).injective]

/-- The paired rotation-and-determinant homomorphism `Spinᶜ(n) → SO(n) × Circle` is a quotient
covering map by its kernel. -/
theorem isQuotientCoveringMap_realToSpecialOrthogonalProdDetRange :
    IsQuotientCoveringMap (realToSpecialOrthogonalProdDetRange n hQ)
      (realToSpecialOrthogonalProdDetRange n hQ).ker := by
  rw [ker_realToSpecialOrthogonalProdDetRange, coe_realToSpecialOrthogonalProdDetRange]
  exact (isQuotientCoveringMap_toSpecialOrthogonal_prod_det (realCliffordForm n 0) hQ
    (Or.inl (posDef_realCliffordForm_zero n))).homeomorph_comp
      (realSpecialOrthogonalProdCircleHomeomorph n)

/-- The paired rotation-and-determinant homomorphism `Spinᶜ(n) → SO(n) × Circle` is surjective. -/
theorem realToSpecialOrthogonalProdDetRange_surjective :
    Function.Surjective (realToSpecialOrthogonalProdDetRange n hQ) :=
  (isQuotientCoveringMap_realToSpecialOrthogonalProdDetRange n hQ).surjective

/-- The paired rotation-and-determinant homomorphism is a topological covering map onto
`SpecialOrthogonalUnitsRange(n) × Circle`. -/
theorem isCoveringMap_realToSpecialOrthogonalProdDetRange :
    IsCoveringMap (realToSpecialOrthogonalProdDetRange n hQ) :=
  (isQuotientCoveringMap_realToSpecialOrthogonalProdDetRange n hQ).isCoveringMap

/-- Every pair `(y, z)` of an orthogonal frame transformation and determinant phase has an evenly
covered neighborhood over which every sheet is a smooth local section into `Spinᶜ(n)` passing
through its prescribed fiber lift. -/
theorem exists_realSpinCSmoothCoveringTrivialization
    (y : SpecialOrthogonalUnitsRange × Circle) :
    ∃ t : Bundle.Trivialization
        ((realToSpecialOrthogonalProdDetRange n hQ) ⁻¹' {y})
        (realToSpecialOrthogonalProdDetRange n hQ),
      y ∈ t.baseSet ∧
      (∀ a : (realToSpecialOrthogonalProdDetRange n hQ) ⁻¹' {y},
        t.toOpenPartialHomeomorph.symm (y, a) = a) ∧
      ∀ a : (realToSpecialOrthogonalProdDetRange n hQ) ⁻¹' {y},
        ContMDiffOn ISP IC ∞
          (fun w ↦ t.toOpenPartialHomeomorph.symm (w, a)) t.baseSet :=
  (isCoveringMap_realToSpecialOrthogonalProdDetRange n hQ).exists_trivialization_contMDiffOn_symm
    (isLocalDiffeomorph_realToSpecialOrthogonalProdDetRange n hQ)
    (realToSpecialOrthogonalProdDetRange_surjective n hQ y)

end CliffordAlgebra.spinCGroup
