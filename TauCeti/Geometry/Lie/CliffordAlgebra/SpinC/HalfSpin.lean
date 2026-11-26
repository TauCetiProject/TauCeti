/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.EvenRepresentation
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.Determinant.Basic

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

The type synonym `Orientation.SpinCHalfSpinor` of a chirality eigenspace carries the descended
action as a smooth `Spinᶜ(4)`-action. In complex rank two every alternating two-form on it, with
values in the determinant representation `CliffordAlgebra.spinCGroup.DetFiber`, is equivariant
(`Orientation.SpinCHalfSpinor.alternatingMap_apply_smul`). When the Clifford generators act
skew-adjointly the action is isometric (`Orientation.SpinCHalfSpinor.isIsometricSMul`).

Viewing the framed even Clifford action `Orientation.realEvenHalfSpinAction` as a unit-valued
smooth homomorphism via `AlgHom.realSpinCEvenSmoothHom` differentiates it to
`Orientation.realSpinCHalfSpinLieLinearMap` on `𝔰𝔭𝔦𝔫ᶜ(4)`: it generates the exponential rays
(`Orientation.exp_smul_realSpinCHalfSpinLieLinearMap`,
`Orientation.hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_zero`), preserves commutators and
`Spinᶜ(4)` conjugation, splits `(Ω, a) ∈ 𝔰𝔬(4) × ℝ` into the lifted orthogonal half-spin operator of
`Ω` plus `(ia / 2) • 1` with `Spinᶜ(4) → SO(4)` equivariance and affine determinant shift, and
takes skew-adjoint values when the Clifford vector generators are skew-adjoint.

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

/-! ### The half-spinor representation spaces -/

/-- The `ε`-eigenspace of the chirality element on the Clifford module `W`, on which `Spinᶜ(4)`
acts by the weight-one half-spin representation `[s, z] ↦ z ρ(s)`
(`Orientation.realSpinCHalfSpinSmoothHom`), compared with the geometric Clifford model through
the orthonormal frame `b`. It is the model fiber of the spinor bundle `W^ε`. -/
def SpinCHalfSpinor (_o : Orientation ℝ V (Fin 4)) (_hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (_b : OrthonormalBasis (Fin 4) ℝ V) (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ) :
    Type _ :=
  eigenspace (ρ (chirality Q _o)) ε

namespace SpinCHalfSpinor

instance : NormedAddCommGroup (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (NormedAddCommGroup S)

instance : NormedSpace ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (NormedSpace ℂ S)

instance : FiniteDimensional ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (FiniteDimensional ℂ S)

/-- The half-spinor model is the `ε`-eigenspace of the chirality element. -/
def linearEquiv : SpinCHalfSpinor o hQ b ρ ε ≃ₗ[ℂ] S :=
  LinearEquiv.refl ℂ _

omit [FiniteDimensional ℂ W] in
/-- The identification of the half-spinor model with the chirality eigenspace of `W` preserves
norms. -/
@[simp]
theorem norm_linearEquiv (ψ : SpinCHalfSpinor o hQ b ρ ε) :
    ‖(linearEquiv o hQ b ρ ε ψ : W)‖ = ‖ψ‖ :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- The half-spinor model has the dimension of the chirality eigenspace. -/
theorem finrank_eq : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = finrank ℂ S :=
  (linearEquiv o hQ b ρ ε).finrank_eq

/-- `Spinᶜ(4)` acts on the half-spinor model by the half-spin representation. -/
instance : DistribMulAction SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  letI : DistribMulAction SpinC S :=
    DistribMulAction.compHom S (realSpinCHalfSpinSmoothHom o hQ b ρ ε).toMonoidHom
  inferInstanceAs (DistribMulAction SpinC S)

/-- Under the identification with the chirality eigenspace, `Spinᶜ(4)` acts on the half-spinor
model by the half-spin representation. -/
@[simp]
theorem linearEquiv_smul (x : SpinC) (ψ : SpinCHalfSpinor o hQ b ρ ε) :
    linearEquiv o hQ b ρ ε (x • ψ) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε x (linearEquiv o hQ b ρ ε ψ) := (rfl)

/-- The action of `Spinᶜ(4)` on the half-spinor model, transported from the chirality
eigenspace. -/
theorem smul_def (x : SpinC) (ψ : SpinCHalfSpinor o hQ b ρ ε) :
    x • ψ = (linearEquiv o hQ b ρ ε).symm
      (realSpinCHalfSpinSmoothHom o hQ b ρ ε x (linearEquiv o hQ b ρ ε ψ)) := by
  rw [LinearEquiv.eq_symm_apply, linearEquiv_smul]

instance : SMulCommClass SpinC ℂ (SpinCHalfSpinor o hQ b ρ ε) where
  smul_comm x c ψ := (linearEquiv o hQ b ρ ε).injective <| by
    simp only [linearEquiv_smul, map_smul]

instance : SMulCommClass SpinC ℝ (SpinCHalfSpinor o hQ b ρ ε) where
  smul_comm x c ψ := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_comm]

/-- The half-spin action is smooth. -/
instance : ContMDiffSMul I 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε) ∞ SpinC
    (SpinCHalfSpinor o hQ b ρ ε) where
  contMDiff_smul := by
    let e : SpinCHalfSpinor o hQ b ρ ε ≃L[ℝ] S :=
      ((linearEquiv o hQ b ρ ε).toContinuousLinearEquiv).restrictScalars ℝ
    have he : ContMDiff (ModelWithCorners.prod I 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε))
        (ModelWithCorners.prod I 𝓘(ℝ, S)) ∞
        (fun p : SpinC × SpinCHalfSpinor o hQ b ρ ε ↦ (p.1, e p.2)) :=
      contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)
    simp only [smul_def]
    exact e.symm.contDiff.contMDiff.comp
      ((contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε).comp he)

instance : ContinuousSMul SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  ContMDiffSMul.continuousSMul («I» := I) (I' := 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε)) ∞

/-- The action of `g` on the half-spinor model, as a linear map, has the determinant of the
half-spin representation at `g`. -/
theorem det_toLinearMap (g : SpinC) :
    LinearMap.det (DistribSMul.toLinearMap ℂ (SpinCHalfSpinor o hQ b ρ ε) g) =
      LinearMap.det (realSpinCHalfSpinSmoothHom o hQ b ρ ε g).toLinearMap :=
  LinearMap.det_eq_of_comp_eq (linearEquiv o hQ b ρ ε)
    (LinearMap.ext fun ψ ↦ linearEquiv_smul o hQ b ρ ε g ψ)

/-- If the half-spinor model is two-dimensional, every alternating two-form on it with values
in the model determinant fiber is `Spinᶜ(4)`-equivariant: the half-spin action has determinant
`[s, z] ↦ z²`, the determinant character. -/
theorem alternatingMap_apply_smul (h₂ : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = 2)
    (η : SpinCHalfSpinor o hQ b ρ ε [⋀^Fin 2]→ₗ[ℂ] spinCGroup.DetFiber 4 hpos) (g : SpinC)
    (v : Fin 2 → SpinCHalfSpinor o hQ b ρ ε) :
    η (fun i ↦ g • v i) = g • η v := by
  have h := congrArg (fun η' ↦ η' v) (AlternatingMap.compLinearMap_eq_det_smul
    (Module.finBasisOfFinrankEq ℂ (SpinCHalfSpinor o hQ b ρ ε) h₂) η
    (DistribSMul.toLinearMap ℂ _ g))
  simp only [AlternatingMap.compLinearMap_apply, DistribSMul.toLinearMap_apply,
    smul_apply, det_toLinearMap,
    det_realSpinCHalfSpinSmoothHom o hQ b ρ ε ((finrank_eq o hQ b ρ ε).symm.trans h₂)] at h
  rw [h, spinCGroup.DetFiber.smul_def]

end SpinCHalfSpinor

end Normed

/-! ### Differentiated Lie-algebra action -/

section DifferentiatedAction

/-- Completeness of a finite-dimensional chirality eigenspace. -/
local instance instCompleteSpaceHalfSpin {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ) :
    CompleteSpace (eigenspace (ρ (chirality Q o)) ε) :=
  FiniteDimensional.completeSpace ℂ _

/-- Real normed-algebra structure on half-spin endomorphisms compatible with
`ContinuousLinearMap.toNormedSpace`. -/
local instance instNormedAlgebraRealHalfSpin {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ) :
    NormedAlgebra ℝ (eigenspace (ρ (chirality Q o)) ε →L[ℂ] eigenspace (ρ (chirality Q o)) ε) :=
  { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }

section LieRepresentation

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε
local notation "ISO" => 𝓘(ℝ, realSpecialOrthogonalLieModel 4)
local notation "SORange" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm 4 0 : QuadraticForm ℝ (Fin 4 → ℝ)))

/-- Operator-norm ring structure on half-spin endomorphisms. -/
local instance instNormedRingHalfSpinLie : NormedRing (S →L[ℂ] S) :=
  ContinuousLinearMap.toNormedRing

/-- The framed even Clifford action on the `ε`-eigenspace `S` of the chirality element, valued in
continuous linear endomorphisms after comparing `CliffordAlgebra.even (realCliffordForm 4 0)` with
`CliffordAlgebra.even Q` in the orthonormal frame `b`. -/
def realEvenHalfSpinAction : even (realCliffordForm 4 0) →ₐ[ℝ] (S →L[ℂ] S) :=
  ((Module.End.toContinuousLinearMap (𝕜 := ℂ) S).toAlgHom.restrictScalars ℝ).comp
    ((evenHalfSpinAction o ρ ε).comp (b.realEvenCliffordEquiv hQ).toAlgHom)

/-- `realEvenHalfSpinAction` evaluates `evenHalfSpinAction` after the frame comparison
`OrthonormalBasis.realEvenCliffordEquiv`, as a continuous linear endomorphism. -/
@[simp]
theorem realEvenHalfSpinAction_apply (u : even (realCliffordForm 4 0)) :
    realEvenHalfSpinAction o hQ b ρ ε u =
      LinearMap.toContinuousLinearMap
        ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ u)) := (rfl)

/-- The unit-valued smooth homomorphism induced by `realEvenHalfSpinAction` via
`AlgHom.realSpinCEvenSmoothHom` coerces pointwise to `realSpinCHalfSpinSmoothHom`. -/
theorem coe_realEvenHalfSpinAction_realSpinCEvenSmoothHom (x : SpinC) :
    ((realEvenHalfSpinAction o hQ b ρ ε).realSpinCEvenSmoothHom hpos x : S →L[ℂ] S) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε x :=
  -- `Exists.elim` + congruence avoids costly motive/`isDefEq` unfolding on `realSpinLieModel 4`.
  (spinCGroup.mk_surjective (realCliffordForm 4 0) hpos x).elim fun p hx ↦ by
    have hmk : (p.2 : ℂ) • realEvenHalfSpinAction o hQ b ρ ε
          (spinGroupToEven (realCliffordForm 4 0) p.1) =
        realSpinCHalfSpinSmoothHom o hQ b ρ ε
          (spinCGroup.mk (realCliffordForm 4 0) hpos (p.1, p.2)) := by
      ext ψ
      simp only [realEvenHalfSpinAction_apply, realSpinCHalfSpinSmoothHom_mk, smul_apply,
        LinearMap.coe_toContinuousLinearMap', spinCHalfSpinRep_apply, LinearMap.smul_apply,
        halfSpinRep_apply, OrthonormalBasis.spinGroupToEven_realSpinGroupEquiv]
    exact (congrArg (fun y ↦
      ((realEvenHalfSpinAction o hQ b ρ ε).realSpinCEvenSmoothHom hpos y : S →L[ℂ] S))
        hx.symm).trans <|
      (AlgHom.coe_realSpinCEvenSmoothHom_mk (A := S →L[ℂ] S)
        (realEvenHalfSpinAction o hQ b ρ ε) hpos (p.1, p.2)).trans <|
        hmk.trans (congrArg (realSpinCHalfSpinSmoothHom o hQ b ρ ε) hx)

/-- The differentiated `ℝ`-linear half-spin representation `𝔰𝔭𝔦𝔫ᶜ(4) →ₗ[ℝ] (S →L[ℂ] S)` on a
chirality eigenspace `S` in the orthonormal frame `b`. -/
def realSpinCHalfSpinLieLinearMap : LeftInvariantDerivation I SpinC →ₗ[ℝ] (S →L[ℂ] S) :=
  AlgHom.realSpinCEvenLieLinearMap (A := S →L[ℂ] S) (realEvenHalfSpinAction o hQ b ρ ε) hpos

/-- `realSpinCHalfSpinLieLinearMap` is `AlgHom.realSpinCEvenLieLinearMap` applied to
`realEvenHalfSpinAction`. -/
theorem realSpinCHalfSpinLieLinearMap_eq (X : LeftInvariantDerivation I SpinC) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε X =
      AlgHom.realSpinCEvenLieLinearMap (A := S →L[ℂ] S)
        (realEvenHalfSpinAction o hQ b ρ ε) hpos X := (rfl)

/-- The operator-norm exponential of `t • realSpinCHalfSpinLieLinearMap o hQ b ρ ε X` equals the
smooth half-spin action on `lieExp (t • X)`. -/
theorem exp_smul_realSpinCHalfSpinLieLinearMap
    (t : ℝ) (X : LeftInvariantDerivation I SpinC) :
    NormedSpace.exp (t • realSpinCHalfSpinLieLinearMap o hQ b ρ ε X) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε (lieExp (t • X)) := by
  simp only [realSpinCHalfSpinLieLinearMap_eq, AlgHom.exp_smul_realSpinCEvenLieLinearMap,
    coe_realEvenHalfSpinAction_realSpinCEvenSmoothHom]

/-- Differentiating the smooth half-spin action along a Lie-group exponential ray at `t = 0`
recovers `realSpinCHalfSpinLieLinearMap o hQ b ρ ε X`. -/
theorem hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_zero
    (X : LeftInvariantDerivation I SpinC) :
    HasDerivAt (fun t : ℝ ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε (lieExp (t • X)))
      (realSpinCHalfSpinLieLinearMap o hQ b ρ ε X) 0 := by
  simpa only [realSpinCHalfSpinLieLinearMap_eq,
    coe_realEvenHalfSpinAction_realSpinCEvenSmoothHom] using
    AlgHom.hasDerivAt_realSpinCEvenSmoothHom_lieExp_smul_zero
      (A := S →L[ℂ] S) (realEvenHalfSpinAction o hQ b ρ ε) hpos X

/-- `realSpinCHalfSpinLieLinearMap` sends the Lie bracket on `𝔰𝔭𝔦𝔫ᶜ(4)` to the operator
commutator on `S`. -/
@[simp]
theorem realSpinCHalfSpinLieLinearMap_lie (X Y : LeftInvariantDerivation I SpinC) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε ⁅X, Y⁆ =
      realSpinCHalfSpinLieLinearMap o hQ b ρ ε X * realSpinCHalfSpinLieLinearMap o hQ b ρ ε Y -
        realSpinCHalfSpinLieLinearMap o hQ b ρ ε Y *
          realSpinCHalfSpinLieLinearMap o hQ b ρ ε X := by
  simp only [realSpinCHalfSpinLieLinearMap_eq, AlgHom.realSpinCEvenLieLinearMap_lie]

/-- `realSpinCHalfSpinLieLinearMap` intertwines the `Spinᶜ(4)` group adjoint with conjugation by
`realSpinCHalfSpinSmoothHom`. -/
@[simp]
theorem realSpinCHalfSpinLieLinearMap_Ad (g : SpinC) (X : LeftInvariantDerivation I SpinC) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε (TauCeti.Lie.Ad g X) =
      realSpinCHalfSpinSmoothHom o hQ b ρ ε g * realSpinCHalfSpinLieLinearMap o hQ b ρ ε X *
        realSpinCHalfSpinSmoothHom o hQ b ρ ε g⁻¹ := by
  simp only [realSpinCHalfSpinLieLinearMap_eq, AlgHom.realSpinCEvenLieLinearMap_Ad, ← map_inv,
    coe_realEvenHalfSpinAction_realSpinCEvenSmoothHom]

/-- The central determinant lift `realDetLieLift 4 hpos a` acts infinitesimally on half-spinors by
`(ia / 2) • 1`. -/
@[simp]
theorem realSpinCHalfSpinLieLinearMap_realDetLieLift (a : ℝ) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε (spinCGroup.realDetLieLift 4 hpos a) =
      (Complex.I * (a / 2)) • (1 : S →L[ℂ] S) := by
  simp only [realSpinCHalfSpinLieLinearMap_eq, AlgHom.realSpinCEvenLieLinearMap_realDetLieLift]

/-- At the identity the determinant ray acts infinitesimally by `(ia/2) Id`. -/
theorem hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_realDetLieLift_zero (a : ℝ) :
    HasDerivAt (fun s : ℝ ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε
      (lieExp (s • spinCGroup.realDetLieLift 4 hpos a)))
      ((Complex.I * (a / 2)) • (1 : S →L[ℂ] S)) 0 := by
  simpa only [realSpinCHalfSpinLieLinearMap_realDetLieLift] using
    hasDerivAt_realSpinCHalfSpinSmoothHom_lieExp_smul_zero o hQ b ρ ε
      (spinCGroup.realDetLieLift 4 hpos a)

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
  simp only [realSpinCHalfSpinLieLinearMap_eq,
    AlgHom.realSpinCEvenLieLinearMap_realSpinOrthogonalLieLift, realEvenHalfSpinAction_apply]

/-- In skew-symmetric matrix coordinates `M ∈ so(4, ℝ)`, the lifted orthogonal action on
half-spinors evaluates the framed even Clifford representation on the normalized exterior bivector
of `M`. -/
theorem realSpinCHalfSpinLieLinearMap_realSoLieLift (M : LieAlgebra.Orthogonal.so (Fin 4) ℝ) :
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
  simp only [realSpinCHalfSpinLieLinearMap_eq, AlgHom.realSpinCEvenLieLinearMap_realSoLieLift,
    realEvenHalfSpinAction_apply]

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
  simp only [spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_apply, map_add,
    realSpinCHalfSpinLieLinearMap_realDetLieLift]

/-- **Affine determinant shift on half-spinors.** Shifting the determinant component from `a` to
`a + c` adds `(ic / 2) • 1` while leaving the orthogonal term unchanged. -/
theorem realSpinCHalfSpinLieLinearMap_realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right
    (Ω : LeftInvariantDerivation ISO SORange) (a c : ℝ) :
    realSpinCHalfSpinLieLinearMap o hQ b ρ ε
        ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv 4 hpos).symm (Ω, a + c)) =
      realSpinCHalfSpinLieLinearMap o hQ b ρ ε
          ((spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv 4 hpos).symm (Ω, a)) +
        (Complex.I * (c / 2)) • (1 : S →L[ℂ] S) := by
  simp only [spinCGroup.realToSpecialOrthogonalProdDetLinearEquiv_symm_add_right, map_add,
    realSpinCHalfSpinLieLinearMap_realDetLieLift]

/-- **`Spinᶜ(4)` conjugation equivariance of the lifted orthogonal half-spin operator.**
Conjugating the lifted orthogonal operator of `Ω` by `g ∈ Spinᶜ(4)` acts on `Ω` through the
`SO(4)` adjoint of the descended rotation of `g`, without choosing a `Spin(4)` lift of `g`. -/
theorem conj_realSpinCHalfSpinSmoothHom_realSpinOrthogonalLieLift
    (g : SpinC) (Ω : LeftInvariantDerivation ISO SORange) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε g *
        realSpinCHalfSpinLieLinearMap o hQ b ρ ε (spinCGroup.realSpinOrthogonalLieLift 4 hpos Ω) *
        realSpinCHalfSpinSmoothHom o hQ b ρ ε g⁻¹ =
      realSpinCHalfSpinLieLinearMap o hQ b ρ ε (spinCGroup.realSpinOrthogonalLieLift 4 hpos
        (TauCeti.Lie.Ad (spinCGroup.realToSpecialOrthogonalSmoothRange 4 hpos g) Ω)) := by
  simp only [← realSpinCHalfSpinLieLinearMap_Ad, spinCGroup.Ad_realSpinOrthogonalLieLift]

end LieRepresentation

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

/-- The half-spinor model of a Hermitian Clifford module is a complex inner product space. -/
instance : InnerProductSpace ℂ (SpinCHalfSpinor o hQ b ρ ε) :=
  inferInstanceAs (InnerProductSpace ℂ S)

omit [FiniteDimensional ℂ W] in
/-- The identification of the half-spinor model with the chirality eigenspace of `W` preserves
inner products. -/
@[simp]
theorem SpinCHalfSpinor.inner_linearEquiv_linearEquiv (ψ χ : SpinCHalfSpinor o hQ b ρ ε) :
    ⟪(SpinCHalfSpinor.linearEquiv o hQ b ρ ε ψ : W),
      (SpinCHalfSpinor.linearEquiv o hQ b ρ ε χ : W)⟫_ℂ = ⟪ψ, χ⟫_ℂ :=
  (rfl)

/-- If the Clifford generators act skew-adjointly on `W`, `Spinᶜ(4)` acts unitarily on the
half-spinor model. -/
theorem SpinCHalfSpinor.inner_smul_smul (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (g : SpinC) (ψ χ : SpinCHalfSpinor o hQ b ρ ε) : ⟪g • ψ, g • χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  rw [← SpinCHalfSpinor.inner_linearEquiv_linearEquiv, SpinCHalfSpinor.linearEquiv_smul,
    SpinCHalfSpinor.linearEquiv_smul, ← Submodule.coe_inner,
    inner_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hρ, Submodule.coe_inner,
    SpinCHalfSpinor.inner_linearEquiv_linearEquiv]

/-- If the Clifford generators act skew-adjointly on `W`, `Spinᶜ(4)` acts isometrically on the
half-spinor model. -/
theorem SpinCHalfSpinor.isIsometricSMul (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    IsIsometricSMul SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  ⟨fun g ↦ AddMonoidHomClass.isometry_of_norm (DistribSMul.toAddMonoidHom _ g) fun ψ ↦ by
    rw [DistribSMul.toAddMonoidHom_apply, @norm_eq_sqrt_re_inner ℂ,
      @norm_eq_sqrt_re_inner ℂ, SpinCHalfSpinor.inner_smul_smul o hQ b ρ ε hρ]⟩

section SkewAdjoint

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
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (X : LeftInvariantDerivation I SpinC) :
    ContinuousLinearMap.adjoint (realSpinCHalfSpinLieLinearMap o hQ b ρ ε X) =
      -realSpinCHalfSpinLieLinearMap o hQ b ρ ε X := by
  have : ContinuousStar (S →L[ℂ] S) := ⟨ContinuousLinearMap.adjoint.continuous⟩
  simp only [← ContinuousLinearMap.star_eq_adjoint, realSpinCHalfSpinLieLinearMap_eq]
  exact AlgHom.star_realSpinCEvenLieLinearMap (A := S →L[ℂ] S)
    (realEvenHalfSpinAction o hQ b ρ ε) hpos
    (fun g ↦ by simpa only [coe_realEvenHalfSpinAction_realSpinCEvenSmoothHom] using
      realSpinCHalfSpinSmoothHom_mem_unitary o hQ b ρ ε hρ g) X

/-- Infinitesimal unitarity of the differentiated half-spin representation on a Hermitian Clifford
module with skew-adjoint vector generators. -/
theorem inner_realSpinCHalfSpinLieLinearMap_add_inner_right
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (X : LeftInvariantDerivation I SpinC) (ψ χ : S) :
    ⟪realSpinCHalfSpinLieLinearMap o hQ b ρ ε X ψ, χ⟫_ℂ +
      ⟪ψ, realSpinCHalfSpinLieLinearMap o hQ b ρ ε X χ⟫_ℂ = 0 := by
  simp only [← ContinuousLinearMap.adjoint_inner_right,
    adjoint_realSpinCHalfSpinLieLinearMap o hQ b ρ ε hρ, neg_apply, inner_neg_right, neg_add_cancel]

end SkewAdjoint

end DifferentiatedAction

end Orientation
