/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Representation
public import TauCeti.RepresentationTheory.Spin.Representation

/-!
# Differentiating even Clifford actions of compact real Spin

The compact real Spin group lies in the even Clifford subalgebra. Consequently an action of the
even Clifford algebra, including either half-spin action after scalar extension to `ℂ` and passage
to finite-dimensional matrix coordinates, restricts to a smooth action of compact Spin. Its
differential is the original even action evaluated on the quadratic Clifford coordinate of the Spin
Lie algebra.

This complements `AlgHom.realCliffordSpinSmoothHom`, which applies to actions of the full real
Clifford algebra. A half-spin summand is preserved only by the even subalgebra, so it does not in
general extend to such a full action. The construction here first maps the closed Spin carrier into
the units of the real even subalgebra and then reuses `AlgHom.unitsSmoothHom`.

## Main results

* `AlgHom.realCliffordSpinEvenSmoothHom`: the smooth compact-Spin action induced by an algebra
  homomorphism out of the even Clifford algebra.
* `AlgHom.unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinEvenSmoothHom`: the differential is the
  action of the corresponding quadratic Clifford element.
* `AlgHom.lieMap_realCliffordSpinEvenSmoothHom_eq`: the corresponding equality of Lie-algebra
  homomorphisms.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 2 and 5.
-/

public section

open Manifold TauCeti TauCeti.CliffordAlgebra CliffordAlgebra
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- The real even Clifford algebra uses its normed-algebra normed-space structure. -/
local instance normedSpaceEven (n : ℕ) :
    NormedSpace ℝ (CliffordAlgebra.even (realCliffordForm n 0)) :=
  NormedAlgebra.toNormedSpace _

namespace CliffordAlgebra

/-- The inclusion of the quadratic Lie subalgebra of the compact real Clifford algebra into its
even subalgebra. -/
def realQuadraticLieSubalgebraEvenIncl (n : ℕ) :
    LieHom ℝ (quadraticLieSubalgebra (realCliffordForm n 0))
      (even (realCliffordForm n 0)) where
  toLinearMap :=
    { toFun := fun x ↦ ⟨x, quadraticLieSubalgebra_le_even _ x.property⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_lie' := by
    intro x y
    apply Subtype.ext
    rfl

@[simp]
theorem realQuadraticLieSubalgebraEvenIncl_apply
    (n : ℕ) (x : quadraticLieSubalgebra (realCliffordForm n 0)) :
    realQuadraticLieSubalgebraEvenIncl n x =
      ⟨x, quadraticLieSubalgebra_le_even _ x.property⟩ :=
  (rfl)

end CliffordAlgebra

namespace AlgHom

local notation "SpinUnitsRange(" n ")" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpinLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n)))

private def spinToEvenHom (n : ℕ) :
    SpinUnitsRange(n) →* (CliffordAlgebra.even (realCliffordForm n 0))ˣ :=
  (spinGroupToEven (realCliffordForm n 0)).toHomUnits.comp
    (realCliffordSpinContinuousMulEquivUnitsRange n).symm.toMonoidHom

@[simp]
private theorem spinToEvenHom_apply (n : ℕ) (g : SpinUnitsRange(n)) :
    spinToEvenHom n g =
      (spinGroupToEven (realCliffordForm n 0)).toHomUnits
        ((realCliffordSpinContinuousMulEquivUnitsRange n).symm g) :=
  rfl

private theorem spinToEvenHom_continuous (n : ℕ) : Continuous (spinToEvenHom n) := by
  apply Continuous.of_coeHom_comp
  have h : Continuous (fun g : SpinUnitsRange(n) ↦
      (⟨(((realCliffordSpinContinuousMulEquivUnitsRange n).symm g :
        spinGroup (realCliffordForm n 0)) : CliffordAlgebra (realCliffordForm n 0)),
        spinGroup.mem_even ((realCliffordSpinContinuousMulEquivUnitsRange n).symm g).2⟩ :
          CliffordAlgebra.even (realCliffordForm n 0))) :=
    (continuous_subtype_val.comp
      (realCliffordSpinContinuousMulEquivUnitsRange n).symm.continuous).subtype_mk _
  apply h.congr
  intro g
  apply Subtype.ext
  exact (coe_spinGroupToEven_apply _ _).symm

local instance completeEven (n : ℕ) :
    CompleteSpace (CliffordAlgebra.even (realCliffordForm n 0)) :=
  FiniteDimensional.complete ℝ _

/-- The smooth inclusion of the closed compact-Spin carrier into the units of the real even
Clifford algebra. -/
private def realCliffordSpinToEvenSmoothRange (n : ℕ) :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel(n))
      𝓘(ℝ, CliffordAlgebra.even (realCliffordForm n 0)) ∞
      (SpinUnitsRange(n)) (CliffordAlgebra.even (realCliffordForm n 0))ˣ :=
  (⟨spinToEvenHom n, spinToEvenHom_continuous n⟩ :
    SpinUnitsRange(n) →ₜ* (CliffordAlgebra.even (realCliffordForm n 0))ˣ)
      |>.toContMDiffMonoidMorphism _ _

/-- The smooth inclusion sends a Spin element to the same element, regarded as an even Clifford
unit. -/
@[simp]
private theorem realCliffordSpinToEvenSmoothRange_apply (n : ℕ) (g : SpinUnitsRange(n)) :
    realCliffordSpinToEvenSmoothRange n g =
      (spinGroupToEven (realCliffordForm n 0)).toHomUnits
        ((realCliffordSpinContinuousMulEquivUnitsRange n).symm g) := by
  simp only [realCliffordSpinToEvenSmoothRange,
    ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
  exact spinToEvenHom_apply n g

/-- The inverse range equivalence preserves the underlying Clifford-algebra value. -/
private theorem coe_realCliffordSpinContinuousMulEquivUnitsRange_symm_apply
    (n : ℕ) (g : SpinUnitsRange(n)) :
    (((realCliffordSpinContinuousMulEquivUnitsRange n).symm g :
      spinGroup (realCliffordForm n 0)) : CliffordAlgebra (realCliffordForm n 0)) =
        ((g.1 : (CliffordAlgebra (realCliffordForm n 0))ˣ) :
          CliffordAlgebra (realCliffordForm n 0)) := by
  have hg := congrArg (fun z : SpinUnitsRange(n) ↦
    ((z.1 : (CliffordAlgebra (realCliffordForm n 0))ˣ) :
      CliffordAlgebra (realCliffordForm n 0)))
    ((realCliffordSpinContinuousMulEquivUnitsRange n).apply_symm_apply g)
  -- `spinGroup.toUnits` has the Spin element as its value field definitionally.
  change ((spinGroup.toUnits
    ((realCliffordSpinContinuousMulEquivUnitsRange n).symm g) :
      (CliffordAlgebra (realCliffordForm n 0))ˣ) :
        CliffordAlgebra (realCliffordForm n 0)) = _
  simpa only [realCliffordSpinContinuousMulEquivUnitsRange_apply] using hg

/-- In the ambient Clifford algebra, the differential of the even inclusion has the established
quadratic Clifford coordinate. -/
@[simp↓ high]
private theorem coe_unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinToEvenSmoothRange
    (n : ℕ) (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n))) :
    ((TauCeti.Lie.unitsLieAlgebraLieEquiv
        (lieMap (realCliffordSpinToEvenSmoothRange n) X) :
      CliffordAlgebra.even (realCliffordForm n 0)) :
      CliffordAlgebra (realCliffordForm n 0)) =
        realCliffordSpinLieEquivQuadratic n X := by
  let _ : NormedSpace ℝ (CliffordAlgebra.even (realCliffordForm n 0)) :=
    NormedAlgebra.toNormedSpace _
  let val : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ]
      CliffordAlgebra (realCliffordForm n 0) :=
    (CliffordAlgebra.even (realCliffordForm n 0)).val
  let φ := val.unitsSmoothHom.comp (realCliffordSpinToEvenSmoothRange n)
  have hcomp : φ = (realCliffordSpinEmbeddedLieSubgroupData n).subtypeVal := by
    apply DFunLike.coe_injective
    funext g
    apply Units.ext
    simp only [φ, ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
      unitsSmoothHom_apply, Units.coe_map, realCliffordSpinToEvenSmoothRange_apply,
      MonoidHom.coe_toHomUnits,
      TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply, val]
    exact (coe_spinGroupToEven_apply _ _).trans
      (coe_realCliffordSpinContinuousMulEquivUnitsRange_symm_apply n g)
  have h := unitsLieAlgebraLieEquiv_lieMap_unitsSmoothHom val
    (lieMap (realCliffordSpinToEvenSmoothRange n) X)
  have hcompmap : lieMap φ X =
      (lieMap val.unitsSmoothHom) (lieMap (realCliffordSpinToEvenSmoothRange n) X) := by
    simp only [φ, lieMap_comp, LieHom.comp_apply]
  have hmap : lieMap φ X =
      (realCliffordSpinEmbeddedLieSubgroupData n).lieMapSubtypeVal X := by
    exact (congrArg (fun ψ ↦ lieMap ψ X) hcomp).trans
      ((realCliffordSpinEmbeddedLieSubgroupData n).lieMapSubtypeVal_apply X).symm
  calc
    _ = TauCeti.Lie.unitsLieAlgebraLieEquiv
        ((lieMap val.unitsSmoothHom) (lieMap (realCliffordSpinToEvenSmoothRange n) X)) := h.symm
    _ = TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap φ X) :=
      congrArg TauCeti.Lie.unitsLieAlgebraLieEquiv hcompmap.symm
    _ = TauCeti.Lie.unitsLieAlgebraLieEquiv
        ((realCliffordSpinEmbeddedLieSubgroupData n).lieMapSubtypeVal X) :=
      congrArg TauCeti.Lie.unitsLieAlgebraLieEquiv hmap
    _ = _ :=
      unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_realCliffordSpinLieEquivQuadratic n X

variable {n : ℕ} {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

/-- The smooth compact-Spin action induced by an action of the real even Clifford algebra. -/
def realCliffordSpinEvenSmoothHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A) :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel(n)) 𝓘(ℝ, A) ∞
      (SpinUnitsRange(n)) Aˣ :=
  f.unitsSmoothHom.comp (realCliffordSpinToEvenSmoothRange n)

/-- The smooth action is the given even Clifford action on the underlying Spin element. -/
@[simp]
theorem realCliffordSpinEvenSmoothHom_apply
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A) (g : SpinUnitsRange(n)) :
    ((f.realCliffordSpinEvenSmoothHom g : Aˣ) : A) =
      f ⟨((g.1 : (CliffordAlgebra (realCliffordForm n 0))ˣ) :
          CliffordAlgebra (realCliffordForm n 0)), by
        exact (coe_realCliffordSpinContinuousMulEquivUnitsRange_symm_apply n g) ▸
          spinGroup.mem_even
            ((realCliffordSpinContinuousMulEquivUnitsRange n).symm g).property⟩ := by
  simp only [realCliffordSpinEvenSmoothHom, ContMDiffMonoidMorphism.coe_comp,
    Function.comp_apply, unitsSmoothHom_apply, realCliffordSpinToEvenSmoothRange_apply,
    Units.coe_map, MonoidHom.coe_toHomUnits]
  apply congrArg f
  apply Subtype.ext
  exact (coe_spinGroupToEven_apply _ _).trans
    (coe_realCliffordSpinContinuousMulEquivUnitsRange_symm_apply n g)

/-- A full Clifford action restricted through the even subalgebra gives its existing smooth
compact-Spin action. -/
theorem realCliffordSpinEvenSmoothHom_comp_val
    (F : CliffordAlgebra (realCliffordForm n 0) →ₐ[ℝ] A) :
    (F.comp (CliffordAlgebra.even (realCliffordForm n 0)).val).realCliffordSpinEvenSmoothHom =
      F.realCliffordSpinSmoothHom := by
  apply DFunLike.coe_injective
  funext g
  apply Units.ext
  rw [realCliffordSpinEvenSmoothHom_apply, realCliffordSpinSmoothHom_apply]
  simp only [Units.coe_map, AlgHom.coe_comp, Function.comp_apply, Subalgebra.coe_val]
  rfl

/-- The differential of an even Clifford action is that action evaluated on the quadratic
Clifford coordinate of the Spin Lie algebra. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinEvenSmoothHom
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A)
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n))) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap f.realCliffordSpinEvenSmoothHom X) =
      f ⟨realCliffordSpinLieEquivQuadratic n X,
        quadraticLieSubalgebra_le_even _ (realCliffordSpinLieEquivQuadratic n X).property⟩ := by
  simp only [realCliffordSpinEvenSmoothHom, lieMap_comp, LieHom.comp_apply,
    unitsLieAlgebraLieEquiv_lieMap_unitsSmoothHom]
  apply congrArg f
  apply Subtype.ext
  exact coe_unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinToEvenSmoothRange n X

/-- After identifying the source Lie algebra with quadratic Clifford elements, the
differentiated even Clifford action equals its algebraic quadratic action. -/
theorem lieMap_realCliffordSpinEvenSmoothHom_eq
    (f : CliffordAlgebra.even (realCliffordForm n 0) →ₐ[ℝ] A) :
    (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := A)).toLieHom.comp
        ((lieMap f.realCliffordSpinEvenSmoothHom).comp
          (realCliffordSpinLieEquivQuadratic n).symm.toLieHom) =
      f.toLieHom.comp (CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl n) := by
  ext x
  simp only [LieHom.comp_apply, LieEquiv.coe_toLieHom,
    unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinEvenSmoothHom,
    LieEquiv.apply_symm_apply, AlgHom.toLieHom_apply,
    CliffordAlgebra.realQuadraticLieSubalgebraEvenIncl_apply]

end AlgHom
