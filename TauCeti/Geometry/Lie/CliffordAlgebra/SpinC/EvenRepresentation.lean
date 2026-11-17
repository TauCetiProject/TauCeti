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

Composing its Lie map with `unitsLieAlgebraEquiv` yields the differentiated representation
`f.realSpinCEvenLieLinearMap hQ : 𝔰𝔭𝔦𝔫ᶜ(n) →ₗ[ℝ] A` into `A`:

* On `𝔰𝔭𝔦𝔫(n)` it evaluates `f` on the quadratic Clifford coordinate.
* On the central determinant lift `realDetLieLift n hQ a` it acts by `(ia / 2) • 1`.
* Under the connection-and-curvature splitting `(Ω, a) ∈ 𝔰𝔬(n) × ℝ`, it decomposes additively into
  the lifted orthogonal Clifford action of `Ω` plus `(ia / 2) • 1`; in skew-symmetric matrix
  coordinates `M ∈ so(n, ℝ)`, the orthogonal term is `f` applied to the normalized exterior
  bivector of `M`.
* Conjugating the lifted orthogonal operator by `g ∈ Spinᶜ(n)` transforms `Ω` by the `SO(n)` adjoint
  of the descended rotation of `g`, so the orthogonal curvature operator in any associated `Spinᶜ`
  bundle descends without choosing a global `Spin(n)` structure.
* If the smooth group action takes values in `unitary A` for a continuous star-ring structure on
  `A`, every element in the image of `f.realSpinCEvenLieLinearMap hQ` is skew-adjoint.

## Main definitions

* `AlgHom.realSpinCEvenSmoothHom`: the smooth weight-one unit-group representation of `Spinᶜ(n)`
  induced by an even Clifford algebra homomorphism into `A`.
* `AlgHom.realSpinCEvenLieLinearMap`: the differentiated `ℝ`-linear representation of `𝔰𝔭𝔦𝔫ᶜ(n)`
  in ambient algebra coordinates.

## Main results

* `AlgHom.realSpinCEvenLieLinearMap_lie` and `AlgHom.realSpinCEvenLieLinearMap_Ad`: commutator and
  `Spinᶜ(n)`-conjugation compatibility.
* `AlgHom.exp_smul_realSpinCEvenLieLinearMap` and
  `AlgHom.hasDerivAt_realSpinCEvenSmoothHom_lieExp_smul_zero`: exponential-ray generation and
  time-zero derivative of the smooth weight-one action.
* `AlgHom.realSpinCEvenLieLinearMap_realDetLieLift`: the central determinant lift acts by
  `(ia / 2) • 1`.
* `AlgHom.realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm` and
  `AlgHom.realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right`:
  additive connection/curvature splitting and affine determinant shift.
* `AlgHom.realSpinCEvenLieLinearMap_realSoLieLift`: explicit normalized-bivector formula on
  `so(n, ℝ)`.
* `AlgHom.conj_realSpinCEvenSmoothHom_realSpinOrthogonalLieLift`: `Spinᶜ(n)`-equivariance of the
  lifted orthogonal curvature action through `Spinᶜ(n) → SO(n)`.
* `AlgHom.star_realSpinCEvenLieLinearMap`: skew-adjointness of the differentiated representation of
  a unitary smooth weight-one action.

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

private def realSpinEvenSmoothHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A) :
    ContMDiffMonoidMorphism IS 𝓘(ℝ, A) ∞ Spin Aˣ :=
  f.realCliffordSpinEvenSmoothHom.comp (realSpinToUnitsRangeSmoothHom n)

@[simp]
private theorem coe_realSpinEvenSmoothHom_apply
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A) (s : Spin) :
    ((realSpinEvenSmoothHom f s : Aˣ) : A) =
      f (spinGroupToEven (realCliffordForm n 0) s) := by
  rw [realSpinEvenSmoothHom, ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    realCliffordSpinEvenSmoothHom_apply]
  apply congrArg f
  apply Subtype.ext
  simp [spinGroup.val_toUnits_apply, coe_spinGroupToEven_apply]

private def realSpinCCoverEvenHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A) :
    Spin × Circle →* Aˣ where
  toFun p := realSpinEvenSmoothHom f p.1 *
    Units.map (Algebra.ofId ℂ A).toMonoidHom (Circle.toUnits p.2)
  map_one' := by simp
  map_mul' p q := Units.ext <| by
    simp [Algebra.algebraMap_eq_smul_one]

private theorem realSpinCCoverEvenHom_negOne
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) :
    realSpinCCoverEvenHom f (spinGroup.negOne (realCliffordForm n 0) hQ, -1) = 1 := by
  apply Units.ext
  have hs : spinGroupToEven (realCliffordForm n 0)
      (spinGroup.negOne (realCliffordForm n 0) hQ) = -1 :=
    Subtype.ext <| (coe_spinGroupToEven_apply _ _).trans (spinGroup.coe_negOne _ hQ)
  simp [realSpinCCoverEvenHom, hs]

/-- The smooth weight-one homomorphism `Spinᶜ(n) → Aˣ` induced by an algebra homomorphism out of
the even Clifford algebra into a finite-dimensional normed `ℂ`-algebra `A`. -/
def realSpinCEvenSmoothHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) :
    ContMDiffMonoidMorphism IC 𝓘(ℝ, A) ∞ (SpinC hQ) Aˣ where
  toMonoidHom := spinCGroup.lift (realCliffordForm n 0) hQ (realSpinCCoverEvenHom f)
    (realSpinCCoverEvenHom_negOne f hQ)
  contMDiff_toFun := by
    let φz : Circle →ₜ* Aˣ :=
      ⟨(Units.map (Algebra.ofId ℂ A).toMonoidHom).comp Circle.toUnits,
        ((continuous_algebraMap ℂ A).units_map (Algebra.ofId ℂ A).toMonoidHom).comp
          (Continuous.of_coeHom_comp (f := Circle.toUnits) continuous_subtype_val)⟩
    apply (spinCGroup.contMDiff_iff_contMDiff_comp_mk n hQ _).mpr
    refine (((realSpinEvenSmoothHom f).contMDiff_toFun.comp contMDiff_fst).mul
      ((φz.toContMDiffMonoidMorphism (𝓡 1) 𝓘(ℝ, A)).contMDiff_toFun.comp
        contMDiff_snd)).congr fun p ↦ ?_
    exact (spinCGroup.lift_mk (realCliffordForm n 0) hQ (realSpinCCoverEvenHom f)
      (realSpinCCoverEvenHom_negOne f hQ) p).trans <|
      congrArg (realSpinEvenSmoothHom f p.1 * ·)
        (congrFun (φz.coe_toContMDiffMonoidMorphism (I := 𝓡 1) (I' := 𝓘(ℝ, A))) p.2).symm

/-- On a cover representative `(s, z)`, the smooth action acts by `z • f(s)`. -/
@[simp]
theorem coe_realSpinCEvenSmoothHom_mk
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (p : Spin × Circle) :
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
theorem coe_realSpinCEvenSmoothHom_ofSpin
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (s : Spin) :
    ((f.realSpinCEvenSmoothHom hQ (spinCGroup.ofSpin (realCliffordForm n 0) hQ s) : Aˣ) : A) =
      f (spinGroupToEven (realCliffordForm n 0) s) := by
  rw [spinCGroup.ofSpin_apply, coe_realSpinCEvenSmoothHom_mk, Circle.coe_one, one_smul]

/-- Restricting `realSpinCEvenSmoothHom` to the central circle acts with weight one. -/
@[simp]
theorem coe_realSpinCEvenSmoothHom_ofCircle
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (z : Circle) :
    ((f.realSpinCEvenSmoothHom hQ (spinCGroup.ofCircle (realCliffordForm n 0) hQ z) : Aˣ) : A) =
      (z : ℂ) • (1 : A) := by
  rw [spinCGroup.ofCircle_apply, coe_realSpinCEvenSmoothHom_mk, map_one, map_one]

/-- Composing `realSpinCEvenSmoothHom` with `realOfSpinSmoothHom` recovers the smooth compact-Spin
action transported along `realSpinToUnitsRangeSmoothHom`. -/
@[simp]
theorem realSpinCEvenSmoothHom_comp_ofSpin
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) :
    (f.realSpinCEvenSmoothHom hQ).comp (spinCGroup.realOfSpinSmoothHom n hQ) =
      f.realCliffordSpinEvenSmoothHom.comp (realSpinToUnitsRangeSmoothHom n) :=
  DFunLike.coe_injective <| funext fun s ↦ Units.ext <| by
    simp only [ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
      spinCGroup.realOfSpinSmoothHom_apply, coe_realSpinCEvenSmoothHom_ofSpin,
      ← coe_realSpinEvenSmoothHom_apply, realSpinEvenSmoothHom]

/-! ### The differentiated representation on `𝔰𝔭𝔦𝔫ᶜ(n)` -/

/-- The differentiated `ℝ`-linear representation `𝔰𝔭𝔦𝔫ᶜ(n) →ₗ[ℝ] A` induced by an even Clifford
algebra homomorphism `f`, obtained by composing the Lie map of `f.realSpinCEvenSmoothHom hQ` with
the canonical algebra coordinates on `Lie(Aˣ)`. -/
def realSpinCEvenLieLinearMap
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) :
    LeftInvariantDerivation IC (SpinC hQ) →ₗ[ℝ] A :=
  (unitsLieAlgebraEquiv (R := A)).toLinearMap.comp
    (lieMap (f.realSpinCEvenSmoothHom hQ)).toLinearMap

@[simp↓ high]
theorem unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (X : LeftInvariantDerivation IC (SpinC hQ)) :
    unitsLieAlgebraEquiv (lieMap (f.realSpinCEvenSmoothHom hQ) X) =
      f.realSpinCEvenLieLinearMap hQ X :=
  (rfl)

/-- `realSpinCEvenLieLinearMap` sends the Lie bracket on `𝔰𝔭𝔦𝔫ᶜ(n)` to the associative commutator in
`A`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_lie
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (X Y : LeftInvariantDerivation IC (SpinC hQ)) :
    f.realSpinCEvenLieLinearMap hQ ⁅X, Y⁆ =
      f.realSpinCEvenLieLinearMap hQ X * f.realSpinCEvenLieLinearMap hQ Y -
        f.realSpinCEvenLieLinearMap hQ Y * f.realSpinCEvenLieLinearMap hQ X := by
  simp only [← unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom, LieHom.map_lie,
    TauCeti.Lie.unitsLieAlgebraEquiv_lie]

/-- `realSpinCEvenLieLinearMap` intertwines the `Spinᶜ(n)` group adjoint with unit conjugation in
`A`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_Ad
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (g : SpinC hQ)
    (X : LeftInvariantDerivation IC (SpinC hQ)) :
    f.realSpinCEvenLieLinearMap hQ (TauCeti.Lie.Ad (I := IC) g X) =
      (f.realSpinCEvenSmoothHom hQ g : A) * f.realSpinCEvenLieLinearMap hQ X *
        ((f.realSpinCEvenSmoothHom hQ g)⁻¹ : Aˣ) := by
  simp only [← unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom,
    ContMDiffMonoidMorphism.lieMap_Ad, TauCeti.Lie.unitsLieAlgebraEquiv_Ad]

/-- The algebra exponential of `t • f.realSpinCEvenLieLinearMap hQ X` equals the group action of
`lieExp (t • X)`. -/
theorem exp_smul_realSpinCEvenLieLinearMap
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (t : ℝ) (X : LeftInvariantDerivation IC (SpinC hQ)) :
    NormedSpace.exp (t • f.realSpinCEvenLieLinearMap hQ X) =
      f.realSpinCEvenSmoothHom hQ (lieExp (t • X)) :=
  (f.realSpinCEvenSmoothHom hQ).exp_smul_unitsLieAlgebraEquiv_lieMap t X

/-- Differentiating `t ↦ (f.realSpinCEvenSmoothHom hQ (lieExp (t • X)) : A)` at `0` recovers
`f.realSpinCEvenLieLinearMap hQ X`. -/
theorem hasDerivAt_realSpinCEvenSmoothHom_lieExp_smul_zero
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (X : LeftInvariantDerivation IC (SpinC hQ)) :
    HasDerivAt (fun t : ℝ ↦ (f.realSpinCEvenSmoothHom hQ (lieExp (t • X)) : A))
      (f.realSpinCEvenLieLinearMap hQ X) 0 :=
  (f.realSpinCEvenSmoothHom hQ).hasDerivAt_coe_lieExp_smul_zero X

/-- On the image of `𝔰𝔭𝔦𝔫(n)` in `𝔰𝔭𝔦𝔫ᶜ(n)`, `realSpinCEvenLieLinearMap` evaluates `f` on the
quadratic Clifford coordinate. -/
@[simp]
theorem realSpinCEvenLieLinearMap_lieMap_realOfSpinSmoothHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (X : LeftInvariantDerivation IS Spin) :
    f.realSpinCEvenLieLinearMap hQ (lieMap (spinCGroup.realOfSpinSmoothHom n hQ) X) =
      f ⟨realCliffordSpinLieEquivQuadratic n (realSpinLieEquivUnitsRange n X),
        quadraticLieSubalgebra_le_even _
          (realCliffordSpinLieEquivQuadratic n (realSpinLieEquivUnitsRange n X)).property⟩ := by
  -- Congruence avoids costly `isDefEq` unfolding across the Spin/Spinᶜ Lie-algebra models.
  have hcomp : (lieMap (f.realSpinCEvenSmoothHom hQ)).comp
        (lieMap (spinCGroup.realOfSpinSmoothHom n hQ)) =
      (lieMap f.realCliffordSpinEvenSmoothHom).comp
        (realSpinLieEquivUnitsRange n).toLieHom :=
    calc
      (lieMap (f.realSpinCEvenSmoothHom hQ)).comp (lieMap (spinCGroup.realOfSpinSmoothHom n hQ))
        = lieMap ((f.realSpinCEvenSmoothHom hQ).comp (spinCGroup.realOfSpinSmoothHom n hQ)) :=
        (lieMap_comp _ _).symm
      _ = lieMap (f.realCliffordSpinEvenSmoothHom.comp (realSpinToUnitsRangeSmoothHom n)) :=
        congrArg _root_.lieMap (f.realSpinCEvenSmoothHom_comp_ofSpin hQ)
      _ = (lieMap f.realCliffordSpinEvenSmoothHom).comp
            (lieMap (realSpinToUnitsRangeSmoothHom n)) :=
        lieMap_comp _ _
      _ = (lieMap f.realCliffordSpinEvenSmoothHom).comp
            (realSpinLieEquivUnitsRange n).toLieHom :=
        congrArg (lieMap f.realCliffordSpinEvenSmoothHom).comp
          (realSpinLieEquivUnitsRange_toLieHom n).symm
  calc
    f.realSpinCEvenLieLinearMap hQ (lieMap (spinCGroup.realOfSpinSmoothHom n hQ) X)
      = unitsLieAlgebraEquiv (lieMap f.realCliffordSpinEvenSmoothHom
          (realSpinLieEquivUnitsRange n X)) :=
      congrArg unitsLieAlgebraEquiv (DFunLike.congr_fun hcomp X)
    _ = TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap f.realCliffordSpinEvenSmoothHom
          (realSpinLieEquivUnitsRange n X)) :=
      (TauCeti.Lie.unitsLieAlgebraLieEquiv_apply _).symm
    _ = _ := unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinEvenSmoothHom f _

/-- On the central determinant lift `realDetLieLift n hQ a`, the differentiated weight-one action
acts by the scalar `(ia / 2) • 1`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_realDetLieLift
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (a : ℝ) :
    f.realSpinCEvenLieLinearMap hQ (spinCGroup.realDetLieLift n hQ a) =
      (Complex.I * (a / 2)) • (1 : A) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  apply TauCeti.eq_of_forall_exp_smul_eq
  intro t
  simp only [f.exp_smul_realSpinCEvenLieLinearMap, spinCGroup.lieExp_smul_realDetLieLift,
    coe_realSpinCEvenSmoothHom_ofCircle, Circle.coe_exp, Complex.exp_eq_exp_ℂ]
  rw [← Algebra.algebraMap_eq_smul_one (NormedSpace.exp _), NormedSpace.algebraMap_exp_comm,
    Algebra.algebraMap_eq_smul_one, ← smul_assoc, Complex.real_smul]
  congr 2; push_cast; ring

/-- On the canonical orthogonal Lie lift `realSpinOrthogonalLieLift n hQ Ω`, the differentiated
action evaluates `f` on the quadratic Clifford lift of `Ω`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_realSpinOrthogonalLieLift
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
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
  calc
    f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ Ω)
      = f.realSpinCEvenLieLinearMap hQ
          (lieMap (spinCGroup.realOfSpinSmoothHom n hQ)
            ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)) :=
      congrArg (f.realSpinCEvenLieLinearMap hQ)
        (spinCGroup.realSpinOrthogonalLieLift_apply n hQ Ω)
    _ = f ⟨q₁, quadraticLieSubalgebra_le_even _ q₁.property⟩ :=
      f.realSpinCEvenLieLinearMap_lieMap_realOfSpinSmoothHom hQ _
    _ = f ⟨q₂, quadraticLieSubalgebra_le_even _ q₂.property⟩ :=
      congrArg f <| (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl_apply n q₁).symm.trans <|
        (congrArg (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl n)
          (congrArg (realCliffordSpinLieEquivQuadratic n)
            (realSpinLieEquivUnitsRange_realSpinToSpecialOrthogonalRangeLieEquiv_symm n Ω))).trans
          (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl_apply n q₂)

/-- On `so(n, ℝ)` coordinates, the canonical orthogonal Lie lift acts by `f` applied to the
normalized exterior bivector of the skew-symmetric matrix. -/
theorem realSpinCEvenLieLinearMap_realSoLieLift
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
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
  calc
    f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSoLieLift n hQ M)
      = f.realSpinCEvenLieLinearMap hQ
          (spinCGroup.realSpinOrthogonalLieLift n hQ
            ((realCliffordSpecialOrthogonalLieEquivSo n).symm M)) :=
      congrArg (f.realSpinCEvenLieLinearMap hQ) (spinCGroup.realSoLieLift_apply n hQ M)
    _ = f ⟨q, quadraticLieSubalgebra_le_even _ q.property⟩ :=
      f.realSpinCEvenLieLinearMap_realSpinOrthogonalLieLift hQ _
    _ = f (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl n
          (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0)
            ((bivectorEquivSo n ℝ).symm M))) :=
      congrArg f <| (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl_apply n q).symm.trans <|
        congrArg (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl n)
          (realCliffordSpinLieEquivQuadratic_realCliffordSpinToSpecialOrthogonalRangeLieEquiv_symm
            n M)

/-- **Connection and curvature splitting in an even Clifford representation.** Under the
weight-normalized equivalence `𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ[ℝ] 𝔰𝔬(n) × ℝ`, a pair `(Ω, a)` acts additively by the
lifted orthogonal Clifford operator of `Ω` plus `(ia / 2) • 1`. -/
theorem realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (Ω : LeftInvariantDerivation ISO SORange) (a : ℝ) :
    f.realSpinCEvenLieLinearMap hQ
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) =
      f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ Ω) +
        (Complex.I * (a / 2)) • (1 : A) := by
  simp only [spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_apply, map_add,
    f.realSpinCEvenLieLinearMap_realDetLieLift]

/-- **Affine determinant shift in an even Clifford representation.** Shifting the determinant
parameter from `a` to `a + b` adds `(ib / 2) • 1` while leaving the orthogonal part unchanged. -/
theorem realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (Ω : LeftInvariantDerivation ISO SORange) (a b : ℝ) :
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
theorem conj_realSpinCEvenSmoothHom_realSpinOrthogonalLieLift
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (g : SpinC hQ)
    (Ω : LeftInvariantDerivation ISO SORange) :
    (f.realSpinCEvenSmoothHom hQ g : A) *
        f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ Ω) *
        ((f.realSpinCEvenSmoothHom hQ g)⁻¹ : Aˣ) =
      f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ
        (TauCeti.Lie.Ad (I := ISO)
          (spinCGroup.realToSpecialOrthogonalSmoothRange n hQ g) Ω)) := by
  simp only [← f.realSpinCEvenLieLinearMap_Ad, spinCGroup.Ad_realSpinOrthogonalLieLift]

/-- If `f.realSpinCEvenSmoothHom hQ` takes values in `unitary A`, then every element in the image
of `f.realSpinCEvenLieLinearMap hQ` is skew-adjoint. -/
theorem star_realSpinCEvenLieLinearMap [StarRing A] [ContinuousStar A]
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0)
    (hf : ∀ g : SpinC hQ, (f.realSpinCEvenSmoothHom hQ g : A) ∈ unitary A)
    (X : LeftInvariantDerivation IC (SpinC hQ)) :
    star (f.realSpinCEvenLieLinearMap hQ X) = -f.realSpinCEvenLieLinearMap hQ X :=
  (f.realSpinCEvenSmoothHom hQ).star_unitsLieAlgebraEquiv_lieMap hf X

end AlgHom
