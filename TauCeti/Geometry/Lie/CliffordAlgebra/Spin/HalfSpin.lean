/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.EvenRepresentation
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Smooth half-spin actions in an orthonormal frame

For a negative-metric Clifford module on an oriented real four-space, the half-spin actions
act on the actual complex eigenspaces of the chirality operator. An orthonormal frame compares
the positive coordinate Spin group with this negative-metric model. This file constructs its
smooth half-spin representations, identifies them with the algebraic representations under
that comparison, and computes their differentials in quadratic Clifford coordinates.

The source is the embedded compact Spin carrier in Clifford units, with its established Lie
group structure. The weight-one action of its product with the circle is smooth as well,
including joint smoothness in the group element and the half-spinor. These are actions on the
covering group, not a smooth structure on the central quotient `Spinᶜ(4)`.

## Main results

* `Orientation.realHalfSpinSmoothHom`: the smooth action on a chirality eigenspace.
* `Orientation.realHalfSpinSmoothHom_apply`: comparison with `halfSpinRep` in the frame.
* `Orientation.unitsLieAlgebraLieEquiv_lieMap_realHalfSpinSmoothHom`: its differential.
* `Orientation.contMDiff_realSpinCHalfSpinRep_apply`: joint smoothness of the weight-one
  action on the product with the circle.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.

The smooth restriction and differential reuse `AlgHom.realCliffordSpinEvenSmoothHom`.
-/

public section

noncomputable section

namespace Orientation

open Module Module.End Manifold TauCeti CliffordAlgebra TauCeti.CliffordAlgebra
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] finrank_real_complex_fact'

local notation "SpinRange" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm 4 0))

local notation "SpinModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm 4 0))) SpinRange)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "S" => eigenspace (ρ (chirality Q o)) ε

-- Use the normed-ring and normed-algebra parent structures consistently in the units model;
-- the default endomorphism instances can select different scalar-action presentations.
/-- The half-spin endomorphisms use their operator-norm ring structure in the units model. -/
local instance : NormedRing (S →L[ℂ] S) := ContinuousLinearMap.toNormedRing

/-- The complex normed-space structure of the half-spin endomorphisms. -/
local instance : NormedSpace ℂ (S →L[ℂ] S) := ContinuousLinearMap.toNormedSpace

/-- The underlying real normed algebra of the half-spin endomorphisms. -/
local instance : NormedAlgebra ℝ (S →L[ℂ] S) := NormedAlgebra.complexToReal

/-- The real model space uses the scalar action of its normed-algebra structure. -/
local instance : NormedSpace ℝ (S →L[ℂ] S) :=
  NormedAlgebra.toNormedSpace (𝕜 := ℝ) (S →L[ℂ] S)

local instance : CompleteSpace S := FiniteDimensional.complete ℂ S

local instance : CompleteSpace (S →L[ℂ] S) := FiniteDimensional.complete ℂ _

/-- The framed even Clifford action on the chosen chirality eigenspace, in continuous
endomorphisms rather than algebraic endomorphisms. -/
private def framedHalfSpinAction :
    even (realCliffordForm 4 0) →ₐ[ℝ] (S →L[ℂ] S) :=
  ((Module.End.toContinuousLinearMap (𝕜 := ℂ) S).toAlgHom.restrictScalars ℝ).comp
    ((evenHalfSpinAction o ρ ε).comp (b.realEvenCliffordEquiv hQ).toAlgHom)

/-- The smooth half-spin representation of the embedded compact coordinate Spin group, on the
actual chirality eigenspace of the negative-metric Clifford module in the frame `b`. -/
def realHalfSpinSmoothHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinModel) 𝓘(ℝ, S →L[ℂ] S) ∞ SpinRange (S →L[ℂ] S)ˣ :=
  AlgHom.realCliffordSpinEvenSmoothHom (A := S →L[ℂ] S) (framedHalfSpinAction o hQ b ρ ε)

/-- The smooth half-spin representation agrees with the algebraic one under the frame
comparison from positive coordinate Spin to the negative-metric Spin group. -/
@[simp]
theorem realHalfSpinSmoothHom_apply (g : SpinRange) :
    (realHalfSpinSmoothHom o hQ b ρ ε g : S →L[ℂ] S) =
      (halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ
        ((realCliffordSpinContinuousMulEquivUnitsRange 4).symm g))).toContinuousLinearMap := by
  obtain ⟨s, rfl⟩ := (realCliffordSpinContinuousMulEquivUnitsRange 4).surjective g
  simp only [realHalfSpinSmoothHom, AlgHom.realCliffordSpinEvenSmoothHom_apply,
    framedHalfSpinAction, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    AlgEquiv.coe_toAlgHom, halfSpinRep_apply, OrthonormalBasis.spinGroupToEven_realSpinGroupEquiv,
    ContinuousMulEquiv.symm_apply_apply]
  have hs : spinGroupToEven (realCliffordForm 4 0) s =
      ⟨s, spinGroup.mem_even s.property⟩ :=
    Subtype.ext (coe_spinGroupToEven_apply _ s)
  simp [hs, Module.End.toContinuousLinearMap, LinearMap.toContinuousLinearMap,
    realCliffordSpinContinuousMulEquivUnitsRange_apply]

/-- In quadratic Clifford coordinates, the differentiated half-spin action is the framed even
Clifford action restricted to the same chirality eigenspace. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMap_realHalfSpinSmoothHom
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinModel) SpinRange) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv (R := S →L[ℂ] S)
        (lieMap (realHalfSpinSmoothHom o hQ b ρ ε) X) =
      LinearMap.toContinuousLinearMap ((evenHalfSpinAction o ρ ε) (b.realEvenCliffordEquiv hQ
        ⟨realCliffordSpinLieEquivQuadratic 4 X,
          quadraticLieSubalgebra_le_even _ (realCliffordSpinLieEquivQuadratic 4 X).property⟩)) :=
  AlgHom.unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinEvenSmoothHom
    (framedHalfSpinAction o hQ b ρ ε) X

/-- The framed algebraic half-spin representation is smooth in operator norm. -/
theorem contMDiff_realHalfSpinRep :
    ContMDiff 𝓘(ℝ, SpinModel) 𝓘(ℝ, S →L[ℂ] S) ∞
      (fun g : SpinRange ↦ (halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ
        ((realCliffordSpinContinuousMulEquivUnitsRange 4).symm g))).toContinuousLinearMap) := by
  apply (Units.contMDiff_val.comp (realHalfSpinSmoothHom o hQ b ρ ε).contMDiff_toFun).congr
  intro g
  exact (realHalfSpinSmoothHom_apply o hQ b ρ ε g).symm

/-- The framed half-spin action is smooth jointly in the Spin element and the spinor. -/
theorem contMDiff_realHalfSpinRep_apply :
    ContMDiff (𝓘(ℝ, SpinModel).prod 𝓘(ℝ, S)) 𝓘(ℝ, S) ∞
      (fun p : SpinRange × S ↦ halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ
        ((realCliffordSpinContinuousMulEquivUnitsRange 4).symm p.1)) p.2) :=
  (((ContinuousLinearMap.restrictScalarsL ℂ S S ℝ ℝ).contDiff.contMDiff.comp
    (contMDiff_realHalfSpinRep o hQ b ρ ε)).comp contMDiff_fst).clm_apply contMDiff_snd

/-- The weight-one half-spin representation on the covering group `Spin(4) × U(1)` is smooth
in operator norm after the frame comparison. -/
theorem contMDiff_realSpinCHalfSpinRep :
    ContMDiff (𝓘(ℝ, SpinModel).prod (𝓡 1)) 𝓘(ℝ, S →L[ℂ] S) ∞
      (fun p : SpinRange × Circle ↦ (spinCHalfSpinRep o ρ ε
        (b.realSpinGroupEquiv hQ ((realCliffordSpinContinuousMulEquivUnitsRange 4).symm p.1),
          p.2)).toContinuousLinearMap) := by
  have hz : ContMDiff (𝓘(ℝ, SpinModel).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : SpinRange × Circle ↦ (p.2 : ℂ)) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  have hs : ContDiff ℝ ∞ (fun p : ℂ × (S →L[ℂ] S) ↦ p.1 • p.2) := contDiff_smul
  convert hs.contMDiff.comp
    (hz.prodMk_space ((contMDiff_realHalfSpinRep o hQ b ρ ε).comp contMDiff_fst)) using 1
  funext p
  ext ψ
  simp

/-- The weight-one covering-group action is smooth jointly in the group element and the
half-spinor. -/
theorem contMDiff_realSpinCHalfSpinRep_apply :
    ContMDiff ((𝓘(ℝ, SpinModel).prod (𝓡 1)).prod 𝓘(ℝ, S)) 𝓘(ℝ, S) ∞
      (fun p : (SpinRange × Circle) × S ↦ spinCHalfSpinRep o ρ ε
        (b.realSpinGroupEquiv hQ ((realCliffordSpinContinuousMulEquivUnitsRange 4).symm p.1.1),
          p.1.2) p.2) :=
  (((ContinuousLinearMap.restrictScalarsL ℂ S S ℝ ℝ).contDiff.contMDiff.comp
    (contMDiff_realSpinCHalfSpinRep o hQ b ρ ε)).comp contMDiff_fst).clm_apply contMDiff_snd

end Orientation
