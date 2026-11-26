/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.EvenRepresentation
public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Projection
public import TauCeti.Geometry.Lie.Exponential.Units.Representation

/-!
# Differentiating weight-one even Clifford actions of compact `Spinᶜ`

Any `ℝ`-algebra homomorphism `f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A` into a
finite-dimensional normed `ℂ`-algebra `A` extends to a smooth weight-one homomorphism
`Spinᶜ(n) → Aˣ` sending `[s, z]` to `z • f(s)`: the central element `(-1, -1)` acts by
`(-1) • f(-1) = 1`, so the covering homomorphism descends smoothly through the central quotient.

Composing its Lie map with `unitsLieAlgebraEquiv` yields `f.realSpinCEvenLieLinearMap hQ :
𝔰𝔭𝔦𝔫ᶜ(n) →ₗ[ℝ] A`:
* On `𝔰𝔭𝔦𝔫(n)` it evaluates `f` on the quadratic Clifford coordinate, and on `realDetLieLift n hQ a`
  it acts by `(ia / 2) • 1`.
* Under `(Ω, a) ∈ 𝔰𝔬(n) × ℝ`, it splits additively into the lifted orthogonal Clifford action of `Ω`
  plus `(ia / 2) • 1`; in `so(n, ℝ)` coordinates, the orthogonal term applies `f` to the normalized
  exterior bivector.
* Conjugating the lifted orthogonal operator by `g ∈ Spinᶜ(n)` acts on `Ω` via `Spinᶜ(n) → SO(n)`,
  and when `f.realSpinCEvenSmoothHom hQ` takes values in `unitary A`, its differentiated operators
  are skew-adjoint.

## Main definitions

* `AlgHom.realSpinCEvenSmoothHom` and `AlgHom.realSpinCEvenLieLinearMap`: the smooth weight-one
  unit-group representation of `Spinᶜ(n)` and its differentiated `ℝ`-linear representation in `A`.

## Main results

* `AlgHom.realSpinCEvenLieLinearMap_lie`, `AlgHom.realSpinCEvenLieLinearMap_Ad`,
  `AlgHom.exp_smul_realSpinCEvenLieLinearMap`, and
  `AlgHom.hasDerivAt_realSpinCEvenSmoothHom_lieExp_smul_zero`: commutator, `Ad`, exponential, and
  time-zero derivative laws.
* `AlgHom.realSpinCEvenLieLinearMap_realDetLieLift`,
  `AlgHom.realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm`,
  `AlgHom.realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right`, and
  `AlgHom.realSpinCEvenLieLinearMap_realSoLieLift`: central `(ia / 2) • 1` action, curvature
  splitting, affine determinant shift, and normalized-bivector formula on `so(n, ℝ)`.
* `AlgHom.conj_realSpinCEvenSmoothHom_realSpinOrthogonalLieLift` and
  `AlgHom.star_realSpinCEvenLieLinearMap`: `Spinᶜ(n)`-equivariance of the lifted orthogonal operator
  and skew-adjointness for unitary actions.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

open Manifold TauCeti TauCeti.CliffordAlgebra CliffordAlgebra
open scoped ContDiff Manifold Matrix.Norms.Operator

namespace AlgHom

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℂ A]
  [IsScalarTower ℝ ℂ A] [FiniteDimensional ℂ A]

/-- Real normed-space structure on `A` inherited from `[NormedAlgebra ℝ A]`. -/
local instance instNormedSpaceRealOfNormedAlgebra : NormedSpace ℝ A :=
  NormedAlgebra.toNormedSpace A
/-- Finite-dimensional real vector-space structure inherited from `ℂ`. -/
local instance : FiniteDimensional ℝ A := Module.Finite.trans ℂ A
/-- Completeness of the finite-dimensional normed `ℂ`-algebra `A`. -/
local instance : CompleteSpace A := FiniteDimensional.completeSpace ℂ A

local notation "IS" => 𝓘(ℝ, realSpinLieModel n)
local notation "ISO" => 𝓘(ℝ, realSpecialOrthogonalLieModel n)
local notation "IC" => ModelWithCorners.prod IS (𝓡 1)
local notation "Spin" => spinGroup (realCliffordForm n 0)
local notation "SORange" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))
local notation "SpinC" => fun hQ => spinCGroup (realCliffordForm n 0) hQ

local notation "Even" => CliffordAlgebra.even (realCliffordForm n 0)

private def realSpinCCoverEvenHom (f : Even →ₐ[ℝ] A) : Spin × Circle →* Aˣ where
  toFun p := f.realSpinEvenSmoothHom p.1 *
    Units.map (Algebra.ofId ℂ A).toMonoidHom (Circle.toUnits p.2)
  map_one' := by simp
  map_mul' p q := Units.ext <| by simp [Algebra.algebraMap_eq_smul_one]

private theorem realSpinCCoverEvenHom_negOne (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0) :
    realSpinCCoverEvenHom f (spinGroup.negOne (realCliffordForm n 0) hQ, -1) = 1 := by
  apply Units.ext
  have hs : spinGroupToEven (realCliffordForm n 0)
      (spinGroup.negOne (realCliffordForm n 0) hQ) = -1 :=
    Subtype.ext <| (coe_spinGroupToEven_apply _ _).trans (spinGroup.coe_negOne _ hQ)
  simp [realSpinCCoverEvenHom, hs]

/-- The smooth weight-one homomorphism `Spinᶜ(n) → Aˣ` induced by an algebra homomorphism out of
the even Clifford algebra into a finite-dimensional normed `ℂ`-algebra `A`. -/
def realSpinCEvenSmoothHom (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0) :
    ContMDiffMonoidMorphism IC 𝓘(ℝ, A) ∞ (SpinC hQ) Aˣ where
  toMonoidHom := spinCGroup.lift (realCliffordForm n 0) hQ (realSpinCCoverEvenHom f)
    (realSpinCCoverEvenHom_negOne f hQ)
  contMDiff_toFun := by
    let φz : Circle →ₜ* Aˣ :=
      ⟨(Units.map (Algebra.ofId ℂ A).toMonoidHom).comp Circle.toUnits,
        ((continuous_algebraMap ℂ A).units_map (Algebra.ofId ℂ A).toMonoidHom).comp
          (Continuous.of_coeHom_comp (f := Circle.toUnits) continuous_subtypeVal)⟩
    apply (spinCGroup.contMDiff_iff_contMDiff_comp_mk n hQ _).mpr
    refine ((f.realSpinEvenSmoothHom.contMDiff_toFun.comp contMDiff_fst).mul
      ((φz.toContMDiffMonoidMorphism (𝓡 1) 𝓘(ℝ, A)).contMDiff_toFun.comp
        contMDiff_snd)).congr fun p ↦ ?_
    exact (spinCGroup.lift_mk (realCliffordForm n 0) hQ (realSpinCCoverEvenHom f)
      (realSpinCCoverEvenHom_negOne f hQ) p).trans <|
      congrArg (f.realSpinEvenSmoothHom p.1 * ·)
        (congrFun (φz.coe_toContMDiffMonoidMorphism (I := 𝓡 1) (I' := 𝓘(ℝ, A))) p.2).symm

/-- On a cover representative `(s, z)`, the smooth action acts by `z • f(s)`. -/
@[simp]
theorem coe_realSpinCEvenSmoothHom_mk (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0)
    (p : Spin × Circle) :
    ((f.realSpinCEvenSmoothHom hQ (spinCGroup.mk (realCliffordForm n 0) hQ p) : Aˣ) : A) =
      (p.2 : ℂ) • f (spinGroupToEven (realCliffordForm n 0) p.1) := by
  have h : f.realSpinCEvenSmoothHom hQ (spinCGroup.mk (realCliffordForm n 0) hQ p) =
      realSpinCCoverEvenHom f p :=
    spinCGroup.lift_mk (realCliffordForm n 0) hQ (realSpinCCoverEvenHom f)
      (realSpinCCoverEvenHom_negOne f hQ) p
  rw [congrArg Units.val h]
  simp [realSpinCCoverEvenHom, Algebra.algebraMap_eq_smul_one]

/-- Restricting `realSpinCEvenSmoothHom` to `Spin(n)` evaluates `f` on the even Spin element. -/
@[simp]
theorem coe_realSpinCEvenSmoothHom_ofSpin (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0)
    (s : Spin) :
    ((f.realSpinCEvenSmoothHom hQ (spinCGroup.ofSpin (realCliffordForm n 0) hQ s) : Aˣ) : A) =
      f (spinGroupToEven (realCliffordForm n 0) s) := by
  rw [spinCGroup.ofSpin_apply, coe_realSpinCEvenSmoothHom_mk, Circle.coe_one, one_smul]

/-- Restricting `realSpinCEvenSmoothHom` to the central circle acts with weight one. -/
@[simp]
theorem coe_realSpinCEvenSmoothHom_ofCircle (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0)
    (z : Circle) :
    ((f.realSpinCEvenSmoothHom hQ (spinCGroup.ofCircle (realCliffordForm n 0) hQ z) : Aˣ) : A) =
      (z : ℂ) • (1 : A) := by
  rw [spinCGroup.ofCircle_apply, coe_realSpinCEvenSmoothHom_mk, map_one, map_one]

/-- Composing `realSpinCEvenSmoothHom` with `realOfSpinSmoothHom` recovers the smooth compact-Spin
action `AlgHom.realSpinEvenSmoothHom`. -/
@[simp]
theorem realSpinCEvenSmoothHom_comp_realOfSpinSmoothHom
    (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0) :
    (f.realSpinCEvenSmoothHom hQ).comp (spinCGroup.realOfSpinSmoothHom n hQ) =
      f.realSpinEvenSmoothHom :=
  DFunLike.coe_injective <| funext fun s ↦ Units.ext <| by
    simp only [ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
      spinCGroup.realOfSpinSmoothHom_apply, coe_realSpinCEvenSmoothHom_ofSpin,
      coe_realSpinEvenSmoothHom_apply]

/-! ### The differentiated representation on `𝔰𝔭𝔦𝔫ᶜ(n)` -/

/-- The differentiated `ℝ`-linear representation `𝔰𝔭𝔦𝔫ᶜ(n) →ₗ[ℝ] A` induced by an even Clifford
algebra homomorphism `f`, obtained by composing the Lie map of `f.realSpinCEvenSmoothHom hQ` with
the canonical algebra coordinates on `Lie(Aˣ)`. -/
def realSpinCEvenLieLinearMap (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0) :
    LeftInvariantDerivation IC (SpinC hQ) →ₗ[ℝ] A :=
  (unitsLieAlgebraEquiv (R := A)).toLinearMap.comp
    (lieMap (f.realSpinCEvenSmoothHom hQ)).toLinearMap

@[simp↓ high]
theorem unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom (f : Even →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (X : LeftInvariantDerivation IC (SpinC hQ)) :
    unitsLieAlgebraEquiv (lieMap (f.realSpinCEvenSmoothHom hQ) X) =
      f.realSpinCEvenLieLinearMap hQ X := (rfl)

/-- `realSpinCEvenLieLinearMap` sends the Lie bracket on `𝔰𝔭𝔦𝔫ᶜ(n)` to the associative commutator in
`A`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_lie (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0)
    (X Y : LeftInvariantDerivation IC (SpinC hQ)) :
    f.realSpinCEvenLieLinearMap hQ ⁅X, Y⁆ =
      f.realSpinCEvenLieLinearMap hQ X * f.realSpinCEvenLieLinearMap hQ Y -
        f.realSpinCEvenLieLinearMap hQ Y * f.realSpinCEvenLieLinearMap hQ X := by
  simp only [← unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom, LieHom.map_lie,
    TauCeti.Lie.unitsLieAlgebraEquiv_lie]

/-- `realSpinCEvenLieLinearMap` intertwines the `Spinᶜ(n)` group adjoint with unit conjugation in
`A`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_Ad (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0)
    (g : SpinC hQ) (X : LeftInvariantDerivation IC (SpinC hQ)) :
    f.realSpinCEvenLieLinearMap hQ (TauCeti.Lie.Ad (I := IC) g X) =
      (f.realSpinCEvenSmoothHom hQ g : A) * f.realSpinCEvenLieLinearMap hQ X *
        ((f.realSpinCEvenSmoothHom hQ g)⁻¹ : Aˣ) := by
  simp only [← unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom,
    ContMDiffMonoidMorphism.lieMap_Ad, TauCeti.Lie.unitsLieAlgebraEquiv_Ad]

/-- The algebra exponential of `t • f.realSpinCEvenLieLinearMap hQ X` equals the group action of
`lieExp (t • X)`. -/
theorem exp_smul_realSpinCEvenLieLinearMap (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0)
    (t : ℝ) (X : LeftInvariantDerivation IC (SpinC hQ)) :
    NormedSpace.exp (t • f.realSpinCEvenLieLinearMap hQ X) =
      f.realSpinCEvenSmoothHom hQ (lieExp (t • X)) :=
  (f.realSpinCEvenSmoothHom hQ).exp_smul_unitsLieAlgebraEquiv_lieMap t X

/-- Differentiating `t ↦ (f.realSpinCEvenSmoothHom hQ (lieExp (t • X)) : A)` at `0` recovers
`f.realSpinCEvenLieLinearMap hQ X`. -/
theorem hasDerivAt_realSpinCEvenSmoothHom_lieExp_smul_zero (f : Even →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (X : LeftInvariantDerivation IC (SpinC hQ)) :
    HasDerivAt (fun t : ℝ ↦ (f.realSpinCEvenSmoothHom hQ (lieExp (t • X)) : A))
      (f.realSpinCEvenLieLinearMap hQ X) 0 :=
  (f.realSpinCEvenSmoothHom hQ).hasDerivAt_coe_lieExp_smul_zero X

/-- On the image of `𝔰𝔭𝔦𝔫(n)` in `𝔰𝔭𝔦𝔫ᶜ(n)`, `realSpinCEvenLieLinearMap` evaluates `f` on the
quadratic Clifford coordinate. -/
@[simp]
theorem realSpinCEvenLieLinearMap_lieMap_realOfSpinSmoothHom (f : Even →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (X : LeftInvariantDerivation IS Spin) :
    f.realSpinCEvenLieLinearMap hQ (lieMap (spinCGroup.realOfSpinSmoothHom n hQ) X) =
      f ⟨realCliffordSpinLieEquivQuadratic n (realSpinLieEquivUnitsRange n X),
        quadraticLieSubalgebra_le_even _
          (realCliffordSpinLieEquivQuadratic n (realSpinLieEquivUnitsRange n X)).property⟩ :=
  -- Congruence avoids costly `isDefEq` unfolding across the Spin/Spinᶜ Lie-algebra models.
  (congrArg unitsLieAlgebraEquiv
    (lieMap_lieMap_of_comp_eq (f.realSpinCEvenSmoothHom_comp_realOfSpinSmoothHom hQ) X)).trans <|
    (TauCeti.Lie.unitsLieAlgebraLieEquiv_apply _).symm.trans
      (f.unitsLieAlgebraLieEquiv_lieMap_realSpinEvenSmoothHom X)

/-- On the central determinant lift `realDetLieLift n hQ a`, the differentiated weight-one action
acts by the scalar `(ia / 2) • 1`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_realDetLieLift (f : Even →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (a : ℝ) :
    f.realSpinCEvenLieLinearMap hQ (spinCGroup.realDetLieLift n hQ a) =
      (Complex.I * (a / 2)) • (1 : A) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  refine TauCeti.eq_of_forall_exp_smul_eq fun t ↦ ?_
  simp only [f.exp_smul_realSpinCEvenLieLinearMap, spinCGroup.lieExp_smul_realDetLieLift,
    coe_realSpinCEvenSmoothHom_ofCircle, Circle.coe_exp, Complex.exp_eq_exp_ℂ]
  rw [← Algebra.algebraMap_eq_smul_one (NormedSpace.exp _), NormedSpace.algebraMap_exp_comm,
    Algebra.algebraMap_eq_smul_one, ← smul_assoc, Complex.real_smul]
  congr 2; push_cast; ring

/-- On the canonical orthogonal Lie lift `realSpinOrthogonalLieLift n hQ Ω`, the differentiated
action evaluates `f` on the quadratic Clifford lift of `Ω`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_realSpinOrthogonalLieLift (f : Even →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (Ω : LeftInvariantDerivation ISO SORange) :
    f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ Ω) =
      f ⟨realCliffordSpinLieEquivQuadratic n
          ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω),
        quadraticLieSubalgebra_le_even _
          (realCliffordSpinLieEquivQuadratic n
            ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)).property⟩ := by
  -- Congruence avoids costly `isDefEq` unfolding across the Spin/SO Lie-subalgebra models.
  let q₁ := realCliffordSpinLieEquivQuadratic n
    (realSpinLieEquivUnitsRange n ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω))
  let q₂ := realCliffordSpinLieEquivQuadratic n
    ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)
  exact (congrArg (f.realSpinCEvenLieLinearMap hQ)
    (spinCGroup.realSpinOrthogonalLieLift_apply n hQ Ω)).trans <|
    (f.realSpinCEvenLieLinearMap_lieMap_realOfSpinSmoothHom hQ _).trans <|
      congrArg f <| (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl_apply n q₁).symm.trans <|
        (congrArg (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl n)
          (congrArg (realCliffordSpinLieEquivQuadratic n)
            (realSpinLieEquivUnitsRange_realSpinToSpecialOrthogonalRangeLieEquiv_symm n Ω))).trans
          (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl_apply n q₂)

/-- On `so(n, ℝ)` coordinates, the canonical orthogonal Lie lift acts by `f` applied to the
normalized exterior bivector of the skew-symmetric matrix. -/
theorem realSpinCEvenLieLinearMap_realSoLieLift (f : Even →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (M : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    let Q := QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSoLieLift n hQ M) =
      f (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl n
        (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0)
          ((bivectorEquivSo n ℝ).symm M))) := by
  let Q := QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ)
  let _ := bivectorLieRing Q
  let _ := bivectorLieAlgebra Q
  -- Congruence avoids costly `isDefEq` unfolding across the Spin/SO Lie-subalgebra models.
  let q := realCliffordSpinLieEquivQuadratic n
    ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).symm
      ((realCliffordSpecialOrthogonalLieEquivSo n).symm M))
  exact (congrArg (f.realSpinCEvenLieLinearMap hQ)
    (spinCGroup.realSoLieLift_apply n hQ M)).trans <|
    (f.realSpinCEvenLieLinearMap_realSpinOrthogonalLieLift hQ _).trans <|
      congrArg f <| (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl_apply n q).symm.trans <|
        congrArg (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl n)
          (realCliffordSpinLieEquivQuadratic_realCliffordSpinToSpecialOrthogonalRangeLieEquiv_symm
            n M)

/-- **Connection and curvature splitting in an even Clifford representation.** Under the
weight-normalized equivalence `𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ[ℝ] 𝔰𝔬(n) × ℝ`, a pair `(Ω, a)` acts additively by the
lifted orthogonal Clifford operator of `Ω` plus `(ia / 2) • 1`. -/
theorem realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0) (Ω : LeftInvariantDerivation ISO SORange)
    (a : ℝ) :
    f.realSpinCEvenLieLinearMap hQ
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) =
      f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ Ω) +
        (Complex.I * (a / 2)) • (1 : A) := by
  simp only [spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_apply, map_add,
    f.realSpinCEvenLieLinearMap_realDetLieLift]

/-- **Affine determinant shift in an even Clifford representation.** Shifting the determinant
parameter from `a` to `a + b` adds `(ib / 2) • 1` while leaving the orthogonal part unchanged. -/
theorem realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right
    (f : Even →ₐ[ℝ] A) (hQ : realCliffordForm n 0 ≠ 0) (Ω : LeftInvariantDerivation ISO SORange)
    (a b : ℝ) :
    f.realSpinCEvenLieLinearMap hQ
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a + b)) =
      f.realSpinCEvenLieLinearMap hQ
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) +
        (Complex.I * (b / 2)) • (1 : A) := by
  simp only [spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right, map_add,
    f.realSpinCEvenLieLinearMap_realDetLieLift]

/-- **`Spinᶜ(n)` conjugation equivariance of the lifted orthogonal operator.** Conjugating the
differentiated action of `realSpinOrthogonalLieLift n hQ Ω` by `g ∈ Spinᶜ(n)` acts on `Ω` through
the `SO(n)` adjoint of the descended rotation of `g`. -/
theorem conj_realSpinCEvenSmoothHom_realSpinOrthogonalLieLift (f : Even →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (g : SpinC hQ) (Ω : LeftInvariantDerivation ISO SORange) :
    (f.realSpinCEvenSmoothHom hQ g : A) *
        f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ Ω) *
        ((f.realSpinCEvenSmoothHom hQ g)⁻¹ : Aˣ) =
      f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ
        (TauCeti.Lie.Ad (I := ISO) (spinCGroup.realToSpecialOrthogonalSmoothRange n hQ g) Ω)) := by
  simp only [← f.realSpinCEvenLieLinearMap_Ad, spinCGroup.Ad_realSpinOrthogonalLieLift]

/-- If `f.realSpinCEvenSmoothHom hQ` takes values in `unitary A`, then every element in the image
of `f.realSpinCEvenLieLinearMap hQ` is skew-adjoint. -/
theorem star_realSpinCEvenLieLinearMap [StarRing A] [ContinuousStar A] (f : Even →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0)
    (hf : ∀ g : SpinC hQ, (f.realSpinCEvenSmoothHom hQ g : A) ∈ unitary A)
    (X : LeftInvariantDerivation IC (SpinC hQ)) :
    star (f.realSpinCEvenLieLinearMap hQ X) = -f.realSpinCEvenLieLinearMap hQ X :=
  (f.realSpinCEvenSmoothHom hQ).star_unitsLieAlgebraEquiv_lieMap hf X

end AlgHom
