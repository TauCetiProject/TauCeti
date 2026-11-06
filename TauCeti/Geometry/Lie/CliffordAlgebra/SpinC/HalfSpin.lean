/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Basic
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.HalfSpin

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
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos
local notation "I" => ModelWithCorners.prod 𝓘(ℝ, realSpinLieModel 4) (𝓡 1)

section Normed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

/-- The covering-group action in continuous endomorphisms, after the frame comparison. -/
private def framedSpinCHalfSpinHom :
    spinGroup (realCliffordForm 4 0) × Circle →* (S →L[ℂ] S) :=
  (Module.End.toContinuousLinearMap S).toMonoidHom.comp
    ((spinCHalfSpinRep o ρ ε).comp
      ((b.realSpinGroupEquiv hQ).toMonoidHom.prodMap (MonoidHom.id Circle)))

private theorem framedSpinCHalfSpinHom_apply
    (s : spinGroup (realCliffordForm 4 0)) (z : Circle) :
    framedSpinCHalfSpinHom o hQ b ρ ε (s, z) =
      (spinCHalfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s, z)).toContinuousLinearMap :=
  (rfl)

private theorem framedSpinCHalfSpinHom_negOne :
    framedSpinCHalfSpinHom o hQ b ρ ε (spinGroup.negOne _ hpos, -1) = 1 := by
  have hn : spinGroupToEven (realCliffordForm 4 0) (spinGroup.negOne _ hpos) = -1 := by
    ext
    simp
  rw [framedSpinCHalfSpinHom_apply, spinCHalfSpinRep_apply, halfSpinRep_apply,
    OrthonormalBasis.spinGroupToEven_realSpinGroupEquiv, hn, map_neg, map_one, map_neg, map_one]
  ext ψ
  simp

/-- The smooth weight-one half-spin representation of compact Spinᶜ(4), after comparison
with the negative-metric Clifford model in the frame `b`. -/
def realSpinCHalfSpinSmoothHom : ContMDiffMonoidMorphism I 𝓘(ℝ, S →L[ℂ] S) ∞
    SpinC (S →L[ℂ] S) where
  toMonoidHom := spinCGroup.lift _ hpos (framedSpinCHalfSpinHom o hQ b ρ ε)
    (framedSpinCHalfSpinHom_negOne o hQ b ρ ε)
  contMDiff_toFun := by
    apply (spinCGroup.contMDiff_real_iff 4 hpos _).mpr
    have h := (contMDiff_realSpinCHalfSpinRep o hQ b ρ ε).comp
      (((realSpinDiffeomorphUnitsRange 4).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
    convert h using 1
    funext p
    simp only [Function.comp_apply, realSpinDiffeomorphUnitsRange_apply,
      ContinuousMulEquiv.symm_apply_apply]
    exact spinCGroup.lift_mk ..

/-- On representatives the descended representation is `z ρ_spin(s)` in the selected frame. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_mk (s : spinGroup (realCliffordForm 4 0)) (z : Circle) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.mk _ hpos (s, z)) =
      (spinCHalfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s, z)).toContinuousLinearMap :=
  spinCGroup.lift_mk ..

/-- The central circle acts with weight one on spinors. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_ofCircle (z : Circle) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofCircle _ hpos z) =
      (z : ℂ) • (1 : S →L[ℂ] S) := by
  rw [spinCGroup.ofCircle_apply, realSpinCHalfSpinSmoothHom_mk, map_one]
  ext ψ
  simp

/-- Restriction to Spin is the half-spin action in the selected frame. -/
@[simp]
theorem realSpinCHalfSpinSmoothHom_ofSpin (s : spinGroup (realCliffordForm 4 0)) :
    realSpinCHalfSpinSmoothHom o hQ b ρ ε (spinCGroup.ofSpin _ hpos s) =
      (halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s)).toContinuousLinearMap := by
  rw [spinCGroup.ofSpin_apply, realSpinCHalfSpinSmoothHom_mk]
  simp

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
  revert x
  refine (spinCGroup.mk_surjective (realCliffordForm 4 0) hpos).forall.mpr ?_
  rintro ⟨s, z⟩
  simp only [realSpinCHalfSpinSmoothHom_mk, LinearMap.coe_toContinuousLinearMap,
    spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply]
  rw [← OrthonormalBasis.spinVectorAction_realSpinGroupEquiv]
  exact spinCHalfSpinRep_comp_halfSpinCliffordMul o ρ ε _ _

/-- In complex rank two the determinant of the descended half-spin action is the
weight-two character, not the weight-one spinor character. -/
theorem det_realSpinCHalfSpinSmoothHom (h₂ : finrank ℂ S = 2) (x : SpinC) :
    LinearMap.det (realSpinCHalfSpinSmoothHom o hQ b ρ ε x).toLinearMap =
      (spinCGroup.det _ hpos x : ℂ) := by
  revert x
  refine (spinCGroup.mk_surjective (realCliffordForm 4 0) hpos).forall.mpr ?_
  rintro ⟨s, z⟩
  simp only [realSpinCHalfSpinSmoothHom_mk, LinearMap.coe_toContinuousLinearMap,
    spinCGroup.det_mk, Circle.coe_pow]
  exact det_spinCHalfSpinRep o ρ ε hQ h₂ _ z

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
  revert x
  refine (spinCGroup.mk_surjective (realCliffordForm 4 0) hpos).forall.mpr ?_
  rintro ⟨s, z⟩
  rw [realSpinCHalfSpinSmoothHom_mk]
  exact inner_spinCHalfSpinRep_apply_spinCHalfSpinRep_apply o ε hρ _ ψ χ

end Orientation
