/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.EvenRepresentation
public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Projection
public import TauCeti.Geometry.Lie.Exponential.Unitary

/-!
# Differentiating weight-one even Clifford actions of compact `Spinᶜ`

Any `ℝ`-algebra homomorphism `f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A` into a
finite-dimensional normed `ℂ`-algebra `A` extends to a smooth weight-one homomorphism
`Spinᶜ(n) → Aˣ` sending `[s, z]` to `z • f(s)`: the central element `(-1, -1)` acts by
`(-1) • f(-1) = 1`, so the covering homomorphism descends smoothly through the central quotient.

Composing its Lie map with `TauCeti.unitsLieAlgebraEquiv` yields the differentiated representation
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
attribute [local instance] TauCeti.normedAlgebraRatOfReal
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [FiniteDimensional ℂ A]

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
  f.realCliffordSpinEvenSmoothHom.comp (realSpinSmoothEquivUnitsRange n)

@[simp]
private theorem coe_realSpinEvenSmoothHom_apply
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A) (s : Spin) :
    ((realSpinEvenSmoothHom f s : Aˣ) : A) =
      f (spinGroupToEven (realCliffordForm n 0) s) := by
  have h : realSpinEvenSmoothHom f s =
      f.realCliffordSpinEvenSmoothHom (realSpinSmoothEquivUnitsRange n s) :=
    congrFun (ContMDiffMonoidMorphism.coe_comp
      f.realCliffordSpinEvenSmoothHom (realSpinSmoothEquivUnitsRange n)) s
  refine (congrArg Units.val h).trans
    ((realCliffordSpinEvenSmoothHom_apply f (realSpinSmoothEquivUnitsRange n s)).trans ?_)
  apply congrArg f
  apply Subtype.ext
  have hs : (((realSpinSmoothEquivUnitsRange n s).1 :
      (CliffordAlgebra (realCliffordForm n 0))ˣ) :
      CliffordAlgebra (realCliffordForm n 0)) = s := by
    rw [realSpinSmoothEquivUnitsRange_apply, realCliffordSpinContinuousMulEquivUnitsRange_apply]
    rfl
  exact hs.trans (coe_spinGroupToEven_apply (realCliffordForm n 0) s).symm

private def realSpinCCoverEvenHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A) :
    Spin × Circle →* Aˣ where
  toFun p := realSpinEvenSmoothHom f p.1 *
    Units.map (Algebra.ofId ℂ A).toMonoidHom (Circle.toUnits p.2)
  map_one' := by simp
  map_mul' p q := by
    have hz (z : Circle) :
        ((Units.map (Algebra.ofId ℂ A).toMonoidHom (Circle.toUnits z) : Aˣ) : A) =
          (z : ℂ) • (1 : A) := by
      simp [Algebra.algebraMap_eq_smul_one]
    apply Units.ext
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul, hz,
      mul_smul_comm, smul_mul_assoc, mul_one]

private theorem realSpinCCoverEvenHom_negOne
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) :
    realSpinCCoverEvenHom f (spinGroup.negOne (realCliffordForm n 0) hQ, -1) = 1 := by
  have hz (z : Circle) :
      ((Units.map (Algebra.ofId ℂ A).toMonoidHom (Circle.toUnits z) : Aˣ) : A) =
        (z : ℂ) • (1 : A) := by
    simp [Algebra.algebraMap_eq_smul_one]
  apply Units.ext
  have hs : spinGroupToEven (realCliffordForm n 0)
      (spinGroup.negOne (realCliffordForm n 0) hQ) = -1 := by
    apply Subtype.ext
    exact (coe_spinGroupToEven_apply _ _).trans (spinGroup.coe_negOne _ hQ)
  simp only [realSpinCCoverEvenHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.val_one,
    coe_realSpinEvenSmoothHom_apply, hs, map_neg, map_one, hz,
    Circle.coe_neg, Circle.coe_one, neg_smul, one_smul, neg_mul_neg, mul_one]

/-- The smooth weight-one homomorphism `Spinᶜ(n) → Aˣ` induced by an algebra homomorphism out of
the even Clifford algebra into a finite-dimensional normed `ℂ`-algebra `A`. -/
def realSpinCEvenSmoothHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) :
    ContMDiffMonoidMorphism IC 𝓘(ℝ, A) ∞ (SpinC hQ) Aˣ where
  toMonoidHom := spinCGroup.lift (realCliffordForm n 0) hQ (realSpinCCoverEvenHom f)
    (realSpinCCoverEvenHom_negOne f hQ)
  contMDiff_toFun := by
    have hz (z : Circle) :
        ((Units.map (Algebra.ofId ℂ A).toMonoidHom (Circle.toUnits z) : Aˣ) : A) =
          (z : ℂ) • (1 : A) := by
      simp [Algebra.algebraMap_eq_smul_one]
    let φz : Circle →ₜ* Aˣ :=
      ⟨(Units.map (Algebra.ofId ℂ A).toMonoidHom).comp Circle.toUnits,
        Continuous.of_coeHom_comp <|
          (continuous_subtype_val.smul (continuous_const (y := (1 : A)))).congr
            fun z ↦ (hz z).symm⟩
    apply (spinCGroup.contMDiff_iff_contMDiff_comp_mk n hQ _).mpr
    refine (((realSpinEvenSmoothHom f).contMDiff_toFun.comp contMDiff_fst).mul
      ((φz.toContMDiffMonoidMorphism (𝓡 1) 𝓘(ℝ, A)).contMDiff_toFun.comp
        contMDiff_snd)).congr fun p ↦ ?_
    refine (spinCGroup.lift_mk (realCliffordForm n 0) hQ (realSpinCCoverEvenHom f)
      (realSpinCCoverEvenHom_negOne f hQ) p).trans ?_
    exact congrArg (realSpinEvenSmoothHom f p.1 * ·)
      (congrFun (φz.coe_toContMDiffMonoidMorphism (I := 𝓡 1) (I' := 𝓘(ℝ, A))) p.2).symm

/-- On a cover representative `(s, z)`, the smooth action acts by `z • f(s)`. -/
@[simp]
theorem coe_realSpinCEvenSmoothHom_mk
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (p : Spin × Circle) :
    ((f.realSpinCEvenSmoothHom hQ (spinCGroup.mk (realCliffordForm n 0) hQ p) : Aˣ) : A) =
      (p.2 : ℂ) • f (spinGroupToEven (realCliffordForm n 0) p.1) := by
  have hz (z : Circle) :
      ((Units.map (Algebra.ofId ℂ A).toMonoidHom (Circle.toUnits z) : Aˣ) : A) =
        (z : ℂ) • (1 : A) := by
    simp [Algebra.algebraMap_eq_smul_one]
  have h : f.realSpinCEvenSmoothHom hQ (spinCGroup.mk (realCliffordForm n 0) hQ p) =
      realSpinCCoverEvenHom f p :=
    spinCGroup.lift_mk (realCliffordForm n 0) hQ (realSpinCCoverEvenHom f)
      (realSpinCCoverEvenHom_negOne f hQ) p
  rw [congrArg Units.val h]
  simp only [realSpinCCoverEvenHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul,
    coe_realSpinEvenSmoothHom_apply, hz, mul_smul_comm, mul_one]

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
action transported along `realSpinSmoothEquivUnitsRange`. -/
@[simp]
theorem realSpinCEvenSmoothHom_comp_ofSpin
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) :
    (f.realSpinCEvenSmoothHom hQ).comp (spinCGroup.realOfSpinSmoothHom n hQ) =
      f.realCliffordSpinEvenSmoothHom.comp (realSpinSmoothEquivUnitsRange n) := by
  apply DFunLike.coe_injective
  funext s
  apply Units.ext
  simp only [ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    spinCGroup.realOfSpinSmoothHom_apply, coe_realSpinCEvenSmoothHom_ofSpin]
  exact (coe_realSpinEvenSmoothHom_apply f s).symm.trans
    (congrArg Units.val (congrFun (ContMDiffMonoidMorphism.coe_comp
      f.realCliffordSpinEvenSmoothHom (realSpinSmoothEquivUnitsRange n)) s))

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
  let DX := lieMap (f.realSpinCEvenSmoothHom hQ) X
  let DY := lieMap (f.realSpinCEvenSmoothHom hQ) Y
  have hX : TauCeti.Lie.unitsLieAlgebraLieEquiv DX = f.realSpinCEvenLieLinearMap hQ X :=
    (TauCeti.Lie.unitsLieAlgebraLieEquiv_apply DX).trans
      (f.unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom hQ X)
  have hY : TauCeti.Lie.unitsLieAlgebraLieEquiv DY = f.realSpinCEvenLieLinearMap hQ Y :=
    (TauCeti.Lie.unitsLieAlgebraLieEquiv_apply DY).trans
      (f.unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom hQ Y)
  have h0 : f.realSpinCEvenLieLinearMap hQ ⁅X, Y⁆ =
      TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap (f.realSpinCEvenSmoothHom hQ) ⁅X, Y⁆) :=
    (f.unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom hQ ⁅X, Y⁆).symm.trans
      (TauCeti.Lie.unitsLieAlgebraLieEquiv_apply _).symm
  have h1 := (congrArg TauCeti.Lie.unitsLieAlgebraLieEquiv
    ((lieMap (f.realSpinCEvenSmoothHom hQ)).map_lie X Y)).trans
    ((TauCeti.Lie.unitsLieAlgebraLieEquiv.map_lie DX DY).trans
      (LieRing.of_associative_ring_bracket _ _))
  have h2 := congrArg₂ HSub.hSub (congrArg₂ HMul.hMul hX hY) (congrArg₂ HMul.hMul hY hX)
  exact h0.trans (h1.trans h2)

/-- `realSpinCEvenLieLinearMap` intertwines the `Spinᶜ(n)` group adjoint with unit conjugation in
`A`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_Ad
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (g : SpinC hQ)
    (X : LeftInvariantDerivation IC (SpinC hQ)) :
    f.realSpinCEvenLieLinearMap hQ (TauCeti.Lie.Ad (I := IC) g X) =
      (f.realSpinCEvenSmoothHom hQ g : A) * f.realSpinCEvenLieLinearMap hQ X *
        ((f.realSpinCEvenSmoothHom hQ g)⁻¹ : Aˣ) :=
  (congrArg unitsLieAlgebraEquiv
    (lieMap_Ad (f.realSpinCEvenSmoothHom hQ) g X)).trans
    (TauCeti.Lie.unitsLieAlgebraEquiv_Ad (f.realSpinCEvenSmoothHom hQ g)
      (lieMap (f.realSpinCEvenSmoothHom hQ) X))

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
  have hcomp : lieMap (f.realSpinCEvenSmoothHom hQ)
        (lieMap (spinCGroup.realOfSpinSmoothHom n hQ) X) =
      lieMap f.realCliffordSpinEvenSmoothHom (realSpinLieEquivUnitsRange n X) := by
    calc
      lieMap (f.realSpinCEvenSmoothHom hQ) (lieMap (spinCGroup.realOfSpinSmoothHom n hQ) X) =
          lieMap ((f.realSpinCEvenSmoothHom hQ).comp (spinCGroup.realOfSpinSmoothHom n hQ)) X :=
        (DFunLike.congr_fun
          (lieMap_comp (spinCGroup.realOfSpinSmoothHom n hQ)
            (f.realSpinCEvenSmoothHom hQ)) X).symm
      _ = lieMap (f.realCliffordSpinEvenSmoothHom.comp (realSpinSmoothEquivUnitsRange n)) X :=
        DFunLike.congr_fun (congrArg _root_.lieMap (f.realSpinCEvenSmoothHom_comp_ofSpin hQ)) X
      _ = lieMap f.realCliffordSpinEvenSmoothHom
            (lieMap (realSpinSmoothEquivUnitsRange n) X) :=
        DFunLike.congr_fun
          (lieMap_comp (realSpinSmoothEquivUnitsRange n) f.realCliffordSpinEvenSmoothHom) X
      _ = lieMap f.realCliffordSpinEvenSmoothHom (realSpinLieEquivUnitsRange n X) :=
        congrArg (lieMap f.realCliffordSpinEvenSmoothHom)
          (realSpinLieEquivUnitsRange_apply n X).symm
  exact (congrArg unitsLieAlgebraEquiv hcomp).trans
    ((TauCeti.Lie.unitsLieAlgebraLieEquiv_apply _).symm.trans
      (unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinEvenSmoothHom f
        (realSpinLieEquivUnitsRange n X)))

/-- On the central determinant lift `realDetLieLift n hQ a`, the differentiated weight-one action
acts by the scalar `(ia / 2) • 1`. -/
@[simp]
theorem realSpinCEvenLieLinearMap_realDetLieLift
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (a : ℝ) :
    f.realSpinCEvenLieLinearMap hQ (spinCGroup.realDetLieLift n hQ a) =
      (Complex.I * (a / 2)) • (1 : A) := by
  apply TauCeti.eq_of_forall_exp_smul_eq
  intro t
  have h_units (Y : LeftInvariantDerivation 𝓘(ℝ, A) Aˣ) :
      ((lieExp (t • Y) : Aˣ) : A) = NormedSpace.exp (t • unitsLieAlgebraEquiv Y) := by
    rw [lieExp_eq_expUnit, map_smul, TauCeti.expUnit_coe]
  have hcont : Continuous (algebraMap ℂ A) :=
    (continuous_id.smul continuous_const).congr fun z ↦ (Algebra.algebraMap_eq_smul_one z).symm
  have h_circle : ((f.realSpinCEvenSmoothHom hQ
        (spinCGroup.ofCircle (realCliffordForm n 0) hQ (Circle.exp (t * a / 2))) : Aˣ) : A) =
      NormedSpace.exp (t • ((Complex.I * (a / 2)) • (1 : A))) := by
    have := IsScalarTower.restrictScalars ℝ ℂ A
    rw [coe_realSpinCEvenSmoothHom_ofCircle, Circle.coe_exp, Complex.exp_eq_exp_ℂ,
      ← Algebra.algebraMap_eq_smul_one, NormedSpace.map_exp (algebraMap ℂ A) hcont,
      Algebra.algebraMap_eq_smul_one]
    congr 1
    rw [← smul_assoc, Complex.real_smul]
    congr 1
    push_cast
    ring
  let D := lieMap (f.realSpinCEvenSmoothHom hQ) (spinCGroup.realDetLieLift n hQ a)
  have hsmul : lieMap (f.realSpinCEvenSmoothHom hQ) (t • spinCGroup.realDetLieLift n hQ a) =
      t • D := (lieMap (f.realSpinCEvenSmoothHom hQ)).map_smul t _
  have h := congrArg Units.val
    (map_lieExp (f.realSpinCEvenSmoothHom hQ) (t • spinCGroup.realDetLieLift n hQ a))
  have hlhs : ((lieExp (lieMap (f.realSpinCEvenSmoothHom hQ)
        (t • spinCGroup.realDetLieLift n hQ a)) : Aˣ) : A) =
      NormedSpace.exp (t • f.realSpinCEvenLieLinearMap hQ (spinCGroup.realDetLieLift n hQ a)) :=
    (congrArg (fun Y ↦ ((lieExp Y : Aˣ) : A)) hsmul).trans
      ((h_units D).trans (congrArg (fun x ↦ NormedSpace.exp (t • x))
        (f.unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom hQ _)))
  have hrhs : ((f.realSpinCEvenSmoothHom hQ
        (lieExp (t • spinCGroup.realDetLieLift n hQ a)) : Aˣ) : A) =
      NormedSpace.exp (t • ((Complex.I * (a / 2)) • (1 : A))) :=
    (congrArg (fun x ↦ ((f.realSpinCEvenSmoothHom hQ x : Aˣ) : A))
      (spinCGroup.lieExp_smul_realDetLieLift n hQ t a)).trans h_circle
  exact hlhs.symm.trans (h.symm.trans hrhs)

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
  let Y := (realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω
  have hcomp_range : (realCliffordSpinToSpecialOrthogonalSmoothRange n).comp
      (realSpinSmoothEquivUnitsRange n) = realSpinToSpecialOrthogonalSmoothRange n := by
    apply DFunLike.coe_injective
    funext s
    simp only [ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
      realSpinSmoothEquivUnitsRange_apply, realCliffordSpinToSpecialOrthogonalSmoothRange_apply,
      realCliffordSpinContinuousMulEquivUnitsRange_apply,
      realCliffordSpinToSpecialOrthogonalRange_apply_toUnits,
      realCliffordSpecialOrthogonalContinuousMulEquivRange_apply,
      realSpinToSpecialOrthogonalSmoothRange_apply]
  have hsymm : realSpinLieEquivUnitsRange n Y =
      (realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω := by
    apply (realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).injective
    calc
      realCliffordSpinToSpecialOrthogonalRangeLieEquiv n (realSpinLieEquivUnitsRange n Y) =
          realCliffordSpinToSpecialOrthogonalRangeLieMap n
            (lieMap (realSpinSmoothEquivUnitsRange n) Y) :=
        (realCliffordSpinToSpecialOrthogonalRangeLieEquiv_apply n _).trans
          (congrArg _ (realSpinLieEquivUnitsRange_apply n Y))
      _ = lieMap (realCliffordSpinToSpecialOrthogonalSmoothRange n)
            (lieMap (realSpinSmoothEquivUnitsRange n) Y) :=
        DFunLike.congr_fun (realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_lieMap n) _
      _ = lieMap ((realCliffordSpinToSpecialOrthogonalSmoothRange n).comp
            (realSpinSmoothEquivUnitsRange n)) Y :=
        (DFunLike.congr_fun (lieMap_comp (realSpinSmoothEquivUnitsRange n)
          (realCliffordSpinToSpecialOrthogonalSmoothRange n)) Y).symm
      _ = lieMap (realSpinToSpecialOrthogonalSmoothRange n) Y :=
        DFunLike.congr_fun (congrArg _root_.lieMap hcomp_range) Y
      _ = realSpinToSpecialOrthogonalRangeLieEquiv n Y :=
        (realSpinToSpecialOrthogonalRangeLieEquiv_apply n Y).symm
      _ = Ω := (realSpinToSpecialOrthogonalRangeLieEquiv n).apply_symm_apply Ω
      _ = realCliffordSpinToSpecialOrthogonalRangeLieEquiv n
            ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω) :=
        ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).apply_symm_apply Ω).symm
  refine (congrArg (f.realSpinCEvenLieLinearMap hQ)
    (spinCGroup.realSpinOrthogonalLieLift_apply n hQ Ω)).trans ?_
  refine (f.realSpinCEvenLieLinearMap_lieMap_realOfSpinSmoothHom hQ Y).trans ?_
  apply congrArg f
  apply Subtype.ext
  exact congrArg (Subtype.val : quadraticLieSubalgebra (realCliffordForm n 0) → _)
    (congrArg (realCliffordSpinLieEquivQuadratic n) hsymm)

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
  let Ω := (realCliffordSpecialOrthogonalLieEquivSo n).symm M
  let X := (realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω
  let x := realCliffordSpinLieEquivQuadratic n X
  let z := (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0)).symm x
  have hx : (realCliffordSpinLieEquivQuadratic n).symm x = X :=
    (realCliffordSpinLieEquivQuadratic n).symm_apply_apply X
  have hzx : bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0) z = x :=
    (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0)).apply_symm_apply x
  have hΩ : realCliffordSpinToSpecialOrthogonalRangeLieMap n X = Ω :=
    (realCliffordSpinToSpecialOrthogonalRangeLieEquiv_apply n X).symm.trans
      ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).apply_symm_apply Ω)
  have hz : M = bivectorEquivSo n ℝ z := by
    calc
      M = realCliffordSpecialOrthogonalLieEquivSo n
            (realCliffordSpinToSpecialOrthogonalRangeLieMap n X) :=
        ((realCliffordSpecialOrthogonalLieEquivSo n).apply_symm_apply M).symm.trans
          (congrArg (realCliffordSpecialOrthogonalLieEquivSo n) hΩ.symm)
      _ = realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x :=
        (congrArg (fun Y ↦ realCliffordSpecialOrthogonalLieEquivSo n
          (realCliffordSpinToSpecialOrthogonalRangeLieMap n Y)) hx).symm.trans
          (realCliffordSpinToSpecialOrthogonalCoordinateLieHom_apply n x).symm
      _ = bivectorEquivSo n ℝ z :=
        (congrArg (realCliffordSpinToSpecialOrthogonalCoordinateLieHom n) hzx).symm.trans
          (realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_bivectorEquivSo n z)
  have hinv : (bivectorEquivSo n ℝ).symm M = z :=
    (congrArg (bivectorEquivSo n ℝ).symm hz).trans ((bivectorEquivSo n ℝ).symm_apply_apply z)
  refine (congrArg (f.realSpinCEvenLieLinearMap hQ)
    (spinCGroup.realSoLieLift_apply n hQ M)).trans ?_
  refine (f.realSpinCEvenLieLinearMap_realSpinOrthogonalLieLift hQ Ω).trans ?_
  apply congrArg f
  apply Subtype.ext
  exact (congrArg (Subtype.val : quadraticLieSubalgebra (realCliffordForm n 0) → _) hzx).symm.trans
    ((congrArg (Subtype.val : quadraticLieSubalgebra (realCliffordForm n 0) → _)
      (congrArg (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0))
        hinv.symm)).trans
      (congrArg Subtype.val (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl_apply n _)).symm)

/-- **Connection and curvature splitting in an even Clifford representation.** Under the
weight-normalized equivalence `𝔰𝔭𝔦𝔫ᶜ(n) ≃ₗ[ℝ] 𝔰𝔬(n) × ℝ`, a pair `(Ω, a)` acts additively by the
lifted orthogonal Clifford operator of `Ω` plus `(ia / 2) • 1`. -/
theorem realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (Ω : LeftInvariantDerivation ISO SORange) (a : ℝ) :
    f.realSpinCEvenLieLinearMap hQ
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) =
      f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ Ω) +
        (Complex.I * (a / 2)) • (1 : A) :=
  (congrArg (f.realSpinCEvenLieLinearMap hQ)
    (spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_apply n hQ (Ω, a))).trans
    ((map_add (f.realSpinCEvenLieLinearMap hQ) _ _).trans
      (congrArg (f.realSpinCEvenLieLinearMap hQ (spinCGroup.realSpinOrthogonalLieLift n hQ Ω) + ·)
        (f.realSpinCEvenLieLinearMap_realDetLieLift hQ a)))

/-- **Affine determinant shift in an even Clifford representation.** Shifting the determinant
parameter from `a` to `a + b` adds `(ib / 2) • 1` while leaving the orthogonal part unchanged. -/
theorem realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (Ω : LeftInvariantDerivation ISO SORange) (a b : ℝ) :
    f.realSpinCEvenLieLinearMap hQ
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a + b)) =
      f.realSpinCEvenLieLinearMap hQ
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv n hQ).symm (Ω, a)) +
        (Complex.I * (b / 2)) • (1 : A) :=
  (congrArg (f.realSpinCEvenLieLinearMap hQ)
    (spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right n hQ Ω a b)).trans
    ((map_add (f.realSpinCEvenLieLinearMap hQ) _ _).trans
      (congrArg _ (f.realSpinCEvenLieLinearMap_realDetLieLift hQ b)))

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
          (spinCGroup.realToSpecialOrthogonalSmoothRange n hQ g) Ω)) :=
  (f.realSpinCEvenLieLinearMap_Ad hQ g (spinCGroup.realSpinOrthogonalLieLift n hQ Ω)).symm.trans
    (congrArg (f.realSpinCEvenLieLinearMap hQ)
      (spinCGroup.Ad_realSpinOrthogonalLieLift n hQ g Ω))

/-- The algebra exponential of `t • f.realSpinCEvenLieLinearMap hQ X` equals the group action of
`lieExp (t • X)`. -/
theorem exp_smul_realSpinCEvenLieLinearMap
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0) (t : ℝ) (X : LeftInvariantDerivation IC (SpinC hQ)) :
    NormedSpace.exp (t • f.realSpinCEvenLieLinearMap hQ X) =
      f.realSpinCEvenSmoothHom hQ (lieExp (t • X)) := by
  have h_units (Y : LeftInvariantDerivation 𝓘(ℝ, A) Aˣ) :
      ((lieExp (t • Y) : Aˣ) : A) = NormedSpace.exp (t • unitsLieAlgebraEquiv Y) := by
    rw [lieExp_eq_expUnit, map_smul, TauCeti.expUnit_coe]
  let D := lieMap (f.realSpinCEvenSmoothHom hQ) X
  have h1 : NormedSpace.exp (t • f.realSpinCEvenLieLinearMap hQ X) =
      ((lieExp (t • D) : Aˣ) : A) :=
    (congrArg (fun a ↦ NormedSpace.exp (t • a))
      (f.unitsLieAlgebraEquiv_lieMap_realSpinCEvenSmoothHom hQ X).symm).trans
      (h_units D).symm
  have h2 : ((lieExp (t • D) : Aˣ) : A) =
      ((lieExp (lieMap (f.realSpinCEvenSmoothHom hQ) (t • X)) : Aˣ) : A) :=
    congrArg (fun Y ↦ ((lieExp Y : Aˣ) : A))
      ((lieMap (f.realSpinCEvenSmoothHom hQ)).map_smul t X).symm
  have h3 : ((lieExp (lieMap (f.realSpinCEvenSmoothHom hQ) (t • X)) : Aˣ) : A) =
      f.realSpinCEvenSmoothHom hQ (lieExp (t • X)) :=
    (congrArg Units.val (map_lieExp (f.realSpinCEvenSmoothHom hQ) (t • X))).symm
  exact h1.trans (h2.trans h3)

/-- If `f.realSpinCEvenSmoothHom hQ` takes values in `unitary A`, then every element in the image
of `f.realSpinCEvenLieLinearMap hQ` is skew-adjoint. -/
theorem star_realSpinCEvenLieLinearMap [StarRing A] [ContinuousStar A]
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (hQ : realCliffordForm n 0 ≠ 0)
    (hf : ∀ g : SpinC hQ, (f.realSpinCEvenSmoothHom hQ g : A) ∈ unitary A)
    (X : LeftInvariantDerivation IC (SpinC hQ)) :
    star (f.realSpinCEvenLieLinearMap hQ X) = -f.realSpinCEvenLieLinearMap hQ X :=
  skewAdjoint.mem_iff.mp <|
    (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint _).mp fun t ↦
      (f.exp_smul_realSpinCEvenLieLinearMap hQ t X).symm ▸ hf (lieExp (t • X))

end AlgHom
