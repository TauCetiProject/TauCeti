/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Basic
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Smooth half-spin representations of the Spinᶜ quotient

An orthonormal frame compares compact coordinate Spin with the negative-metric geometric
Clifford model. The weight-one half-spin action is already smooth on the covering group.
Here it descends smoothly through the actual diagonal central quotient, acting on the actual
chirality eigenspaces rather than on separately chosen matrix spaces.

The descended actions preserve the Hermitian inner product when Clifford generators are
skew-adjoint. In complex rank two their determinant is the weight-two character `[s,z] ↦ z²`.
No choice of orientation of the frame is needed to descend the action on a fixed eigenspace;
the identification of the two coordinate SU(2) factors with positive and negative chirality
requires a positively oriented frame separately.

The type synonym `Orientation.SpinCHalfSpinor` of a chirality eigenspace carries the descended
action as a smooth `Spinᶜ(4)`-action. In complex rank two every alternating two-form on it, with
values in the determinant representation `CliffordAlgebra.spinCGroup.DetFiber`, is equivariant
(`Orientation.SpinCHalfSpinor.alternatingMap_apply_smul`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

namespace Orientation

open Module Module.End Manifold TauCeti TauCeti.CliffordAlgebra CliffordAlgebra
open scoped Manifold ContDiff InnerProductSpace

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
@[expose]
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
/-- The identification of the half-spinor model with the chirality eigenspace is the
identity. -/
@[simp]
theorem linearEquiv_apply (ψ : SpinCHalfSpinor o hQ b ρ ε) : linearEquiv o hQ b ρ ε ψ = ψ :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- The inverse identification of the chirality eigenspace with the half-spinor model is the
identity. -/
@[simp]
theorem linearEquiv_symm_apply (ψ : S) : (linearEquiv o hQ b ρ ε).symm ψ = ψ :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- The half-spinor model has the dimension of the chirality eigenspace. -/
theorem finrank_eq : finrank ℂ (SpinCHalfSpinor o hQ b ρ ε) = finrank ℂ S :=
  (linearEquiv o hQ b ρ ε).finrank_eq

/-- `Spinᶜ(4)` acts on the half-spinor model by the half-spin representation. -/
instance : DistribMulAction SpinC (SpinCHalfSpinor o hQ b ρ ε) :=
  DistribMulAction.compHom S (realSpinCHalfSpinSmoothHom o hQ b ρ ε).toMonoidHom

/-- The action of `Spinᶜ(4)` on the half-spinor model is evaluation of the half-spin
representation. -/
theorem smul_def (x : SpinC) (ψ : SpinCHalfSpinor o hQ b ρ ε) :
    x • ψ = realSpinCHalfSpinSmoothHom o hQ b ρ ε x ψ := (rfl)

instance : SMulCommClass SpinC ℂ (SpinCHalfSpinor o hQ b ρ ε) where
  smul_comm x c ψ := by
    simp only [smul_def]
    exact (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).map_smul c ψ

instance : SMulCommClass SpinC ℝ (SpinCHalfSpinor o hQ b ρ ε) where
  smul_comm x c ψ := by
    simp only [smul_def]
    exact (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).map_smul_of_tower c ψ

/-- The half-spin action is smooth. -/
instance : ContMDiffSMul I 𝓘(ℝ, SpinCHalfSpinor o hQ b ρ ε) ∞ SpinC
    (SpinCHalfSpinor o hQ b ρ ε) where
  contMDiff_smul := by
    simp only [smul_def]
    exact contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε

instance : ContinuousSMul SpinC (SpinCHalfSpinor o hQ b ρ ε) where
  continuous_smul := by
    simp only [smul_def]
    exact (contMDiff_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε).continuous

/-- The action of `g` on the half-spinor model, as a linear map, has the determinant of the
half-spin representation at `g`. -/
theorem det_toLinearMap (g : SpinC) :
    LinearMap.det (DistribSMul.toLinearMap ℂ (SpinCHalfSpinor o hQ b ρ ε) g) =
      LinearMap.det (realSpinCHalfSpinSmoothHom o hQ b ρ ε g).toLinearMap := by
  have h : (linearEquiv o hQ b ρ ε).toLinearMap ∘ₗ
      DistribSMul.toLinearMap ℂ (SpinCHalfSpinor o hQ b ρ ε) g ∘ₗ
        (linearEquiv o hQ b ρ ε).symm.toLinearMap =
      (realSpinCHalfSpinSmoothHom o hQ b ρ ε g).toLinearMap := by
    refine LinearMap.ext fun ψ ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      linearEquiv_symm_apply, linearEquiv_apply, ContinuousLinearMap.coe_coe]
    exact (DistribSMul.toLinearMap_apply ℂ (SpinCHalfSpinor o hQ b ρ ε) g ψ).trans
      (smul_def o hQ b ρ ε g ψ)
  rw [← h, LinearMap.det_conj]

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

/-- If the Clifford generators act skew-adjointly on `W`, `Spinᶜ(4)` acts unitarily on the
half-spinor model. -/
theorem SpinCHalfSpinor.inner_smul_smul (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (g : SpinC) (ψ χ : SpinCHalfSpinor o hQ b ρ ε) : ⟪g • ψ, g • χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  rw [SpinCHalfSpinor.smul_def, SpinCHalfSpinor.smul_def]
  exact inner_realSpinCHalfSpinSmoothHom_apply o hQ b ρ ε hρ g ψ χ

end Orientation
