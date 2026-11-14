/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.EvenRepresentation
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth half-spin representations of the Spinᶜ quotient and their Lie-algebra actions

An orthonormal frame compares compact coordinate Spin with the negative-metric geometric
Clifford model. The weight-one half-spin action is already smooth on the covering group.
Here it descends smoothly through the actual diagonal central quotient, acting on the actual
chirality eigenspaces rather than on separately chosen matrix spaces.

The descended actions preserve the Hermitian inner product when Clifford generators are
skew-adjoint. In complex rank two their determinant is the weight-two character `[s,z] ↦ z²`.
The central determinant half-parameter path has operator-norm derivative `(ia/2) Id` at the
identity. No choice of orientation of the frame is needed to descend the action on a fixed
eigenspace; identifying the two coordinate SU(2) factors with positive and negative chirality
requires a positively oriented frame separately.

Viewing the smooth half-spin action as a unit-valued homomorphism via
`AlgHom.realSpinCEvenSmoothHom` differentiates it to the `ℝ`-linear Lie representation
`Orientation.realSpinCHalfSpinLieLinearMap` on `𝔰𝔭𝔦𝔫ᶜ(4)`:

* It sends the Lie bracket on `𝔰𝔭𝔦𝔫ᶜ(4)` to the operator commutator and intertwines the `Spinᶜ(4)`
  group adjoint with spinor conjugation.
* Under the connection-and-curvature splitting `𝔰𝔭𝔦𝔫ᶜ(4) ≃ₗ[ℝ] 𝔰𝔬(4) × ℝ`, a pair `(Ω, a)` acts by
  the lifted orthogonal half-spin operator of `Ω` plus `(ia / 2) • 1`, shifting `a` to `a + c`
  adds `(ic / 2) • 1`, and conjugating the lifted orthogonal operator by `g ∈ Spinᶜ(4)` transforms
  `Ω` through the descended `SO(4)` rotation of `g`.
* When the Clifford generators are skew-adjoint on a Hermitian Clifford module, every operator in
  the image of `Orientation.realSpinCHalfSpinLieLinearMap` is skew-adjoint.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

namespace Orientation

open Module Module.End Manifold TauCeti TauCeti.CliffordAlgebra CliffordAlgebra
open scoped Manifold ContDiff InnerProductSpace Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "hQ₀" => b.ne_zero_of_neg_norm_sq hQ
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos
local notation "I" => ModelWithCorners.prod 𝓘(ℝ, realSpinLieModel 4) (𝓡 1)

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

/-- The smooth weight-one half-spin representation of compact Spinᶜ(4), after comparison
with the negative-metric Clifford model in the frame `b`. -/
def realSpinCHalfSpinSmoothHom : ContMDiffMonoidMorphism I 𝓘(ℝ, S →L[ℂ] S) ∞
    SpinC (S →L[ℂ] S) where
  toMonoidHom := (Module.End.toContinuousLinearMap S).toMonoidHom.comp
    ((spinCGroupHalfSpinRep o ρ ε hQ₀).comp (b.realSpinCGroupHom hQ hpos hQ₀))
  contMDiff_toFun := by
    apply (spinCGroup.contMDiff_iff_contMDiff_comp_mk 4 hpos _).mpr
    have h := (contMDiff_realSpinCHalfSpinRep o hQ b ρ ε).comp
      (((realSpinDiffeomorphUnitsRange 4).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
    convert h using 1
    funext p
    apply ContinuousLinearMap.ext
    intro ψ
    simp only [Function.comp_apply, realSpinDiffeomorphUnitsRange_apply,
      ContinuousMulEquiv.symm_apply_apply]
    simp only [MulEquiv.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_comp, MonoidHom.coe_ofClass, MulEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, Function.comp_apply, OrthonormalBasis.realSpinCGroupHom_mk,
      spinCGroupHalfSpinRep_mk, Module.End.toContinuousLinearMap_apply,
      LinearMap.coe_toContinuousLinearMap']

/-- The smooth action is the algebraic quotient action after the Spinᶜ frame comparison. -/
theorem realSpinCHalfSpinSmoothHom_apply (hQ₀' : Q ≠ 0) (x : SpinC) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε x =
      (spinCGroupHalfSpinRep o ρ ε hQ₀'
        (b.realSpinCGroupHom hQ hpos hQ₀' x)).toContinuousLinearMap :=
  (rfl)

/-- On representatives the descended representation is `z ρ_spin(s)` in the selected frame. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_mk (s : spinGroup (realCliffordForm 4 0)) (z : Circle) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.mk _ hpos (s, z)) =
      (spinCHalfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s, z)).toContinuousLinearMap := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    OrthonormalBasis.realSpinCGroupHom_mk, spinCGroupHalfSpinRep_mk]

/-- The central circle acts with weight one on spinors. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_ofCircle (z : Circle) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofCircle _ hpos z) =
      (z : ℂ) • (1 : S →L[ℂ] S) := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    OrthonormalBasis.realSpinCGroupHom_ofCircle, spinCGroupHalfSpinRep_ofCircle]
  exact map_smul (Module.End.toContinuousLinearMap S) (z : ℂ) 1

section DeterminantDerivative

-- Match the normed-algebra parent structures used by the framed smooth representation.
/-- Operator-norm ring structure on half-spin endomorphisms. -/
local instance : NormedRing (S →L[ℂ] S) := ContinuousLinearMap.toNormedRing
/-- Complex normed-space structure on half-spin endomorphisms. -/
local instance : NormedSpace ℂ (S →L[ℂ] S) := ContinuousLinearMap.toNormedSpace
/-- The underlying real normed algebra of half-spin endomorphisms. -/
local instance : NormedAlgebra ℝ (S →L[ℂ] S) := NormedAlgebra.complexToReal
/-- The real scalar action selected by the normed-algebra structure. -/
local instance : NormedSpace ℝ (S →L[ℂ] S) :=
  NormedAlgebra.toNormedSpace (𝕜 := ℝ) (S →L[ℂ] S)

/-- Along a determinant parameter with velocity `a`, the half-spin action has operator-norm
derivative `(ia/2) Id` times the phase at time `t`. Differentiation is over `ℝ`. -/
theorem hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift (a t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε
      (lieExp (s • spinCGroup.realDetLieLift 4 hpos a)))
      ((Complex.I * (a / 2) * (Circle.exp (t * a / 2) : ℂ)) • (1 : S →L[ℂ] S)) t := by
  simp only [spinCGroup.lieExp_smul_realDetLieLift, realSpinCHalfSpinSmoothHom_ofCircle,
    Circle.coe_exp]
  have harg : HasDerivAt (fun s : ℝ ↦ ((s * a / 2 : ℝ) : ℂ) * Complex.I)
      (((a / 2 : ℝ) : ℂ) * Complex.I) t := by
    simpa only [one_mul, id_eq] using
      ((((hasDerivAt_id t).mul_const a).div_const 2).ofReal_comp).mul_const Complex.I
  convert ((Complex.hasDerivAt_exp _).comp t harg).smul_const (1 : S →L[ℂ] S) using 1
  · funext s
    simp only [Function.comp_apply]
  · congr 1
    push_cast
    ring

/-- At the identity the determinant ray acts infinitesimally by `(ia/2) Id`. -/
theorem hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift_zero (a : ℝ) :
    HasDerivAt (fun s : ℝ ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε
      (lieExp (s • spinCGroup.realDetLieLift 4 hpos a)))
      ((Complex.I * (a / 2)) • (1 : S →L[ℂ] S)) 0 := by
  simpa using
    hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift o hQ b ρ ε a 0

end DeterminantDerivative

/-- Restriction to Spin is the half-spin action in the selected frame. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_ofSpin (s : spinGroup (realCliffordForm 4 0)) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofSpin _ hpos s) =
      (halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s)).toContinuousLinearMap := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    OrthonormalBasis.realSpinCGroupHom_ofSpin, spinCGroupHalfSpinRep_ofSpin]

/-- The half-spin action is smooth jointly in the Spinᶜ element and spinor. -/
theorem contMDiff_realSpinCHalfSpinSmoothHom_apply :
    ContMDiff (ModelWithCorners.prod I 𝓘(ℝ, S)) 𝓘(ℝ, S) ∞
      (fun p : SpinC × S ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε p.1 p.2) :=
  (((ContinuousLinearMap.restrictScalarsL ℂ S S ℝ ℝ).contDiff.contMDiff.comp
    (realSpinCHalfSpinSmoothHom o hQ b ρ ε).contMDiff_toFun).comp
      contMDiff_fst).clm_apply contMDiff_snd

/-- Odd Clifford multiplication intertwines the two descended half-spin actions, with
vectors rotated by the actual Spinᶜ frame projection and then compared through `b`. -/
theorem realSpinCHalfSpinSmoothHom_comp_halfSpinCliffordMul
    (x : SpinC) (v : Fin (4 + 0) → ℝ) :
    (realSpinCHalfSpinSmoothHom o hQ b ρ (-ε) x).toLinearMap ∘ₗ
        halfSpinCliffordMul o ρ ε (b.negRealCliffordFormIsometryEquiv hQ v) =
      halfSpinCliffordMul o ρ ε (b.negRealCliffordFormIsometryEquiv hQ
        ((spinCGroup.toSpecialOrthogonal _ hpos x :
          (Fin (4 + 0) → ℝ) ≃ₗ[ℝ] (Fin (4 + 0) → ℝ)) v)) ∘ₗ
        (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).toLinearMap := by
  simp only [realSpinCHalfSpinSmoothHom_apply o hQ b _ _ hQ₀,
    LinearMap.coe_toContinuousLinearMap]
  rw [spinCGroupHalfSpinRep_comp_halfSpinCliffordMul,
    OrthonormalBasis.toSpecialOrthogonal_realSpinCGroupHom_apply]

/-- In complex rank two the determinant of the descended half-spin action is the
weight-two character, not the weight-one spinor character. -/
@[simp]
theorem det_realSpinCHalfSpinSmoothHom (h₂ : finrank ℂ S = 2) (x : SpinC) :
    LinearMap.det (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).toLinearMap =
      (spinCGroup.det _ hpos x : ℂ) := by
  rw [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    LinearMap.coe_toContinuousLinearMap, det_spinCGroupHalfSpinRep o ρ ε hQ₀ hQ h₂,
    OrthonormalBasis.det_realSpinCGroupHom]

section LieRepresentation

local notation "ISO" => 𝓘(ℝ, realSpecialOrthogonalLieModel 4)
local notation "SORange" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm 4 0 : QuadraticForm ℝ (Fin 4 → ℝ)))

/-- Completeness of the finite-dimensional chirality eigenspace `S`. -/
local instance : CompleteSpace S := FiniteDimensional.completeSpace ℂ S

section PrivateBridge

/-- Operator-norm ring structure on half-spin endomorphisms. -/
local instance : NormedRing (S →L[ℂ] S) := ContinuousLinearMap.toNormedRing
/-- Complex normed-space structure on half-spin endomorphisms. -/
local instance : NormedSpace ℂ (S →L[ℂ] S) := ContinuousLinearMap.toNormedSpace
/-- Real normed-algebra structure restricted from `ℂ` on half-spin endomorphisms. -/
local instance (priority := 2000) : NormedAlgebra ℝ (S →L[ℂ] S) :=
  NormedAlgebra.complexToReal
/-- Real algebra structure matching `NormedAlgebra.complexToReal`. -/
local instance (priority := 2000) : Algebra ℝ (S →L[ℂ] S) :=
  NormedAlgebra.complexToReal.toAlgebra
/-- Real normed-space structure matching `NormedAlgebra.complexToReal`. -/
local instance (priority := 2000) : NormedSpace ℝ (S →L[ℂ] S) :=
  NormedSpace.complexToReal

private def framedSpinCHalfSpinAction :
    even (realCliffordForm 4 0) →ₐ[ℝ] (S →L[ℂ] S) :=
  have := IsScalarTower.restrictScalars ℝ ℂ (S →L[ℂ] S)
  ((Module.End.toContinuousLinearMap (𝕜 := ℂ) S).toAlgHom.restrictScalars ℝ).comp
    ((evenHalfSpinAction o ρ ε).comp (b.realEvenCliffordEquiv hQ).toAlgHom)

private theorem framedSpinCHalfSpinAction_apply (u : even (realCliffordForm 4 0)) :
    framedSpinCHalfSpinAction o hQ b ρ ε u =
      LinearMap.toContinuousLinearMap
        ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ u)) :=
  (rfl)

private def realSpinCHalfSpinUnitsSmoothHom :=
  AlgHom.realSpinCEvenSmoothHom (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos

private def rawSpinCHalfSpinLieLinearMap :=
  AlgHom.realSpinCEvenLieLinearMap (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos

private theorem rawSpinCHalfSpinLieLinearMap_add
    (X Y : LeftInvariantDerivation I SpinC) :
    rawSpinCHalfSpinLieLinearMap o hQ b ρ ε (X + Y) =
      rawSpinCHalfSpinLieLinearMap o hQ b ρ ε X +
        rawSpinCHalfSpinLieLinearMap o hQ b ρ ε Y :=
  map_add (rawSpinCHalfSpinLieLinearMap o hQ b ρ ε) X Y

private theorem rawSpinCHalfSpinLieLinearMap_smul
    (r : ℝ) (X : LeftInvariantDerivation I SpinC) :
    rawSpinCHalfSpinLieLinearMap o hQ b ρ ε (r • X) =
      (algebraMap ℝ ℂ r) • rawSpinCHalfSpinLieLinearMap o hQ b ρ ε X :=
  map_smul (rawSpinCHalfSpinLieLinearMap o hQ b ρ ε) r X

end PrivateBridge

private theorem coe_realSpinCHalfSpinUnitsSmoothHom_apply (x : SpinC) :
    (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε x : S →L[ℂ] S) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε x :=
  (spinCGroup.mk_surjective (realCliffordForm 4 0) hpos x).elim fun ⟨s, z⟩ hx ↦ by
    have hlhs : (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε x : S →L[ℂ] S) =
        (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε
          (spinCGroup.mk (realCliffordForm 4 0) hpos (s, z)) : S →L[ℂ] S) :=
      congrArg (fun y ↦ (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε y : S →L[ℂ] S)) hx.symm
    have hrhs : realSpinCHalfSpinSmoothHom o hQ b ρ ε
          (spinCGroup.mk (realCliffordForm 4 0) hpos (s, z)) =
        realSpinCHalfSpinSmoothHom o hQ b ρ ε x :=
      congrArg (realSpinCHalfSpinSmoothHom o hQ b ρ ε) hx
    have h1 := AlgHom.coe_realSpinCEvenSmoothHom_mk (A := S →L[ℂ] S)
      (framedSpinCHalfSpinAction o hQ b ρ ε) hpos (s, z)
    have h2 : (z : ℂ) • framedSpinCHalfSpinAction o hQ b ρ ε
          (spinGroupToEven (realCliffordForm 4 0) s) =
        realSpinCHalfSpinSmoothHom o hQ b ρ ε
          (spinCGroup.mk (realCliffordForm 4 0) hpos (s, z)) := by
      rw [framedSpinCHalfSpinAction_apply, realSpinCHalfSpinSmoothHom_mk]
      apply ContinuousLinearMap.ext
      intro ψ
      simp only [smul_apply, LinearMap.coe_toContinuousLinearMap',
        spinCHalfSpinRep_apply, LinearMap.smul_apply, halfSpinRep_apply,
        OrthonormalBasis.spinGroupToEven_realSpinGroupEquiv]
    exact hlhs.trans (h1.trans (h2.trans hrhs))

private theorem inv_coe_realSpinCHalfSpinUnitsSmoothHom_apply (x : SpinC) :
    (((realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε x)⁻¹ : _) : S →L[ℂ] S) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε x⁻¹ :=
  (congrArg Units.val (map_inv (realSpinCHalfSpinUnitsSmoothHom o hQ b ρ ε) x)).symm.trans
    (coe_realSpinCHalfSpinUnitsSmoothHom_apply o hQ b ρ ε x⁻¹)

/-- The differentiated `ℝ`-linear half-spin representation `𝔰𝔭𝔦𝔫ᶜ(4) →ₗ[ℝ] (S →L[ℂ] S)` on a
chirality eigenspace `S` in the orthonormal frame `b`. -/
def realSpinCHalfSpinLieLinearMap :
    LeftInvariantDerivation I SpinC →ₗ[ℝ] (S →L[ℂ] S) where
  toFun X := rawSpinCHalfSpinLieLinearMap o hQ b ρ ε X
  map_add' X Y := rawSpinCHalfSpinLieLinearMap_add o hQ b ρ ε X Y
  map_smul' r X := by
    refine (rawSpinCHalfSpinLieLinearMap_smul o hQ b ρ ε r X).trans ?_
    have := IsScalarTower.restrictScalars ℝ ℂ W
    ext ψ
    exact algebraMap_smul ℂ r _

/-- `realSpinCHalfSpinLieLinearMap` sends the Lie bracket on `𝔰𝔭𝔦𝔫ᶜ(4)` to the operator
commutator on `S`. -/
@[simp]
theorem realSpinCHalfSpinLieLinearMap_lie (X Y : LeftInvariantDerivation I SpinC) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε ⁅X, Y⁆ =
      realSpinCHalfSpinLieLinearMap o hQ b ρ ε X *
          realSpinCHalfSpinLieLinearMap o hQ b ρ ε Y -
        realSpinCHalfSpinLieLinearMap o hQ b ρ ε Y *
          realSpinCHalfSpinLieLinearMap o hQ b ρ ε X := by
  have h := AlgHom.realSpinCEvenLieLinearMap_lie (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos X Y
  exact h

/-- `realSpinCHalfSpinLieLinearMap` intertwines the `Spinᶜ(4)` group adjoint with conjugation by
`realSpinCHalfSpinSmoothHom`. -/
@[simp]
theorem realSpinCHalfSpinLieLinearMap_Ad (g : SpinC) (X : LeftInvariantDerivation I SpinC) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε (TauCeti.Lie.Ad g X) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε g *
        realSpinCHalfSpinLieLinearMap o hQ b ρ ε X *
        realSpinCHalfSpinSmoothHom o hQ b ρ ε g⁻¹ := by
  have h := AlgHom.realSpinCEvenLieLinearMap_Ad (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos g X
  exact h.trans (congrArg₂ HMul.hMul
    (congrArg (· * realSpinCHalfSpinLieLinearMap o hQ b ρ ε X)
      (coe_realSpinCHalfSpinUnitsSmoothHom_apply o hQ b ρ ε g))
    (inv_coe_realSpinCHalfSpinUnitsSmoothHom_apply o hQ b ρ ε g))

/-- The central determinant lift `realDetLieLift 4 hpos a` acts infinitesimally on half-spinors by
`(ia / 2) • 1`. -/
@[simp]
theorem realSpinCHalfSpinLieLinearMap_realDetLieLift (a : ℝ) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε (spinCGroup.realDetLieLift 4 hpos a) =
      (Complex.I * (a / 2)) • (1 : S →L[ℂ] S) := by
  have h := AlgHom.realSpinCEvenLieLinearMap_realDetLieLift (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos a
  exact h

/-- On the canonical orthogonal Lie lift `realSpinOrthogonalLieLift 4 hpos Ω`, the differentiated
half-spin action is the framed even Clifford action on the quadratic Clifford lift of `Ω`. -/
@[simp]
theorem realSpinCHalfSpinLieLinearMap_realSpinOrthogonalLieLift
    (Ω : LeftInvariantDerivation ISO SORange) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε (spinCGroup.realSpinOrthogonalLieLift 4 hpos Ω) =
      LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
        ⟨realCliffordSpinLieEquivQuadratic 4
            ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv 4).symm Ω),
          quadraticLieSubalgebra_le_even _
            (realCliffordSpinLieEquivQuadratic 4
              ((realCliffordSpinToSpecialOrthogonalRangeLieEquiv 4).symm Ω)).property⟩)) := by
  have h := AlgHom.realSpinCEvenLieLinearMap_realSpinOrthogonalLieLift (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos Ω
  exact h.trans (framedSpinCHalfSpinAction_apply o hQ b ρ ε _)

/-- In skew-symmetric matrix coordinates `M ∈ so(4, ℝ)`, the lifted orthogonal action on
half-spinors evaluates the framed even Clifford representation on the normalized exterior bivector
of `M`. -/
theorem realSpinCHalfSpinLieLinearMap_realSoLieLift
    (M : LieAlgebra.Orthogonal.so (Fin 4) ℝ) :
    let Q₀ := QuadraticMap.weightedSumSquares ℝ (1 : Fin 4 → ℝ)
    letI := bivectorLieRing Q₀
    letI := bivectorLieAlgebra Q₀
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε (spinCGroup.realSoLieLift 4 hpos M) =
      LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
        (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl 4
          (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm 4 0)
            ((bivectorEquivSo 4 ℝ).symm M))))) := by
  let Q₀ := QuadraticMap.weightedSumSquares ℝ (1 : Fin 4 → ℝ)
  let _ := bivectorLieRing Q₀
  let _ := bivectorLieAlgebra Q₀
  have h := AlgHom.realSpinCEvenLieLinearMap_realSoLieLift (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos M
  exact h.trans (framedSpinCHalfSpinAction_apply o hQ b ρ ε _)

/-- **Connection and curvature splitting on half-spinors.** Under `𝔰𝔭𝔦𝔫ᶜ(4) ≃ₗ[ℝ] 𝔰𝔬(4) × ℝ`, an
orthogonal-plus-determinant Lie element `(Ω, a)` acts by the lifted orthogonal half-spin operator
of `Ω` plus `(ia / 2) • 1`. -/
theorem realSpinCHalfSpinLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm
    (Ω : LeftInvariantDerivation ISO SORange) (a : ℝ) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv 4 hpos).symm (Ω, a)) =
      realSpinCHalfSpinLieLinearMap o hQ b ρ ε
          (spinCGroup.realSpinOrthogonalLieLift 4 hpos Ω) +
        (Complex.I * (a / 2)) • (1 : S →L[ℂ] S) := by
  have h :=
    AlgHom.realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm (A := S →L[ℂ] S)
      (framedSpinCHalfSpinAction o hQ b ρ ε) hpos Ω a
  exact h

/-- **Affine determinant shift on half-spinors.** Shifting the determinant component from `a` to
`a + c` adds `(ic / 2) • 1` while leaving the orthogonal term unchanged. -/
theorem realSpinCHalfSpinLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right
    (Ω : LeftInvariantDerivation ISO SORange) (a c : ℝ) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv 4 hpos).symm (Ω, a + c)) =
      realSpinCHalfSpinLieLinearMap o hQ b ρ ε
          ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv 4 hpos).symm (Ω, a)) +
        (Complex.I * (c / 2)) • (1 : S →L[ℂ] S) := by
  have h :=
    AlgHom.realSpinCEvenLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right
      (A := S →L[ℂ] S) (framedSpinCHalfSpinAction o hQ b ρ ε) hpos Ω a c
  exact h

/-- **`Spinᶜ(4)` conjugation equivariance of the lifted orthogonal half-spin operator.**
Conjugating the lifted orthogonal operator of `Ω` by `g ∈ Spinᶜ(4)` acts on `Ω` through the
`SO(4)` adjoint of the descended rotation of `g`, without choosing a `Spin(4)` lift of `g`. -/
theorem conj_realSpinCHalfSpinSmoothHom_realSpinOrthogonalLieLift
    (g : SpinC) (Ω : LeftInvariantDerivation ISO SORange) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε g *
        realSpinCHalfSpinLieLinearMap o hQ b ρ ε
          (spinCGroup.realSpinOrthogonalLieLift 4 hpos Ω) *
        realSpinCHalfSpinSmoothHom o hQ b ρ ε g⁻¹ =
      realSpinCHalfSpinLieLinearMap o hQ b ρ ε (spinCGroup.realSpinOrthogonalLieLift 4 hpos
        (TauCeti.Lie.Ad (spinCGroup.realToSpecialOrthogonalSmoothRange 4 hpos g) Ω)) := by
  have h := AlgHom.conj_realSpinCEvenSmoothHom_realSpinOrthogonalLieLift (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos g Ω
  exact (congrArg₂ HMul.hMul
    (congrArg (· * realSpinCHalfSpinLieLinearMap o hQ b ρ ε
        (spinCGroup.realSpinOrthogonalLieLift 4 hpos Ω))
      (coe_realSpinCHalfSpinUnitsSmoothHom_apply o hQ b ρ ε g).symm)
    (inv_coe_realSpinCHalfSpinUnitsSmoothHom_apply o hQ b ρ ε g).symm).trans h

end LieRepresentation

end Normed

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

/-- The descended action is unitary when the Clifford generators are skew-adjoint. -/
theorem inner_realSpinCHalfSpinSmoothHom_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (x : SpinC) (ψ χ : S) :
    ⟪realSpinCHalfSpinSmoothHom o hQ b ρ ε x ψ,
      realSpinCHalfSpinSmoothHom o hQ b ρ ε x χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  simp only [realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hQ₀,
    LinearMap.coe_toContinuousLinearMap']
  exact inner_spinCGroupHalfSpinRep_apply_spinCGroupHalfSpinRep_apply o ε hρ hQ₀ _ ψ χ

section SkewAdjoint

/-- Completeness of the finite-dimensional chirality eigenspace `S`. -/
local instance : CompleteSpace S := FiniteDimensional.completeSpace ℂ S

/-- On a Hermitian Clifford module with skew-adjoint vector generators, the descended smooth
half-spin operators lie in the unitary group of `S →L[ℂ] S`. -/
theorem realSpinCHalfSpinSmoothHom_mem_unitary
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (x : SpinC) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε x ∈ unitary (S →L[ℂ] S) :=
  IsUnit.mem_unitary_of_star_mul_self
    ((Group.isUnit x).map (realSpinCHalfSpinSmoothHom o hQ b ρ ε))
    ((realSpinCHalfSpinSmoothHom o hQ b ρ ε x).inner_map_map_iff_adjoint_comp_self.mp
      (inner_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hρ x))

/-- On a Hermitian Clifford module with skew-adjoint vector generators, every operator in the image
of `realSpinCHalfSpinLieLinearMap` is skew-adjoint. -/
@[simp]
theorem adjoint_realSpinCHalfSpinLieLinearMap
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (X : LeftInvariantDerivation I SpinC) :
    ContinuousLinearMap.adjoint (realSpinCHalfSpinLieLinearMap o hQ b ρ ε X) =
      -realSpinCHalfSpinLieLinearMap o hQ b ρ ε X := by
  have : ContinuousStar (S →L[ℂ] S) := ⟨ContinuousLinearMap.adjoint.continuous⟩
  have h := AlgHom.star_realSpinCEvenLieLinearMap (A := S →L[ℂ] S)
    (framedSpinCHalfSpinAction o hQ b ρ ε) hpos
    (fun g ↦ (coe_realSpinCHalfSpinUnitsSmoothHom_apply o hQ b ρ ε g).symm ▸
      realSpinCHalfSpinSmoothHom_mem_unitary o hQ b ρ ε hρ g) X
  exact (ContinuousLinearMap.star_eq_adjoint
    (realSpinCHalfSpinLieLinearMap o hQ b ρ ε X)).symm.trans h

/-- Infinitesimal unitarity of the differentiated half-spin representation on a Hermitian Clifford
module with skew-adjoint vector generators. -/
theorem inner_realSpinCHalfSpinLieLinearMap_add_inner_right
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (X : LeftInvariantDerivation I SpinC) (ψ χ : S) :
    ⟪realSpinCHalfSpinLieLinearMap o hQ b ρ ε X ψ, χ⟫_ℂ +
      ⟪ψ, realSpinCHalfSpinLieLinearMap o hQ b ρ ε X χ⟫_ℂ = 0 := by
  let T := realSpinCHalfSpinLieLinearMap o hQ b ρ ε X
  have hT : ContinuousLinearMap.adjoint T = -T :=
    adjoint_realSpinCHalfSpinLieLinearMap o hQ b ρ ε hρ X
  calc
    ⟪T ψ, χ⟫_ℂ + ⟪ψ, T χ⟫_ℂ = ⟪ψ, ContinuousLinearMap.adjoint T χ⟫_ℂ + ⟪ψ, T χ⟫_ℂ :=
      congrArg (· + ⟪ψ, T χ⟫_ℂ) (ContinuousLinearMap.adjoint_inner_right T ψ χ).symm
    _ = ⟪ψ, (-T) χ⟫_ℂ + ⟪ψ, T χ⟫_ℂ :=
      congrArg (fun S' : S →L[ℂ] S ↦ ⟪ψ, S' χ⟫_ℂ + _) hT
    _ = 0 := by rw [neg_apply, inner_neg_right, neg_add_cancel]

end SkewAdjoint

end Orientation
