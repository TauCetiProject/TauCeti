/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.BCH.Local
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility

/-!
# The local Baker--Campbell--Hausdorff map for algebra units

For a finite-dimensional real normed algebra `R`, its units `Rˣ` form a Lie group whose Lie
algebra is canonically linearly equivalent to `R`. This file transports
`NormedSpace.localBCH R` through that equivalence to obtain a local
Baker--Campbell--Hausdorff map on the actual Lie algebra of `Rˣ`.

The transported germ retains the identity laws and analyticity of the algebra-valued germ. Its
image under the abstract Lie-group exponential is the product of the two exponentials, giving a
local group law directly in the derivation model of the Lie algebra.

## Main declarations

* `TauCeti.unitsLocalBCH`: the transported local BCH germ on the Lie algebra of `Rˣ`.
* `TauCeti.unitsLocalBCH_map_unitsLieAlgebraEquiv`: its canonical-coordinate equation.
* `TauCeti.analyticAt_unitsLocalBCH_representative`: analyticity of its representative.
* `TauCeti.unitsLocalBCH_map_lieExp`: the local exponential product equation.
* `TauCeti.eq_unitsLocalBCH_of_tendsto_of_map_lieExp_eq`: uniqueness among small germs with the
  same exponential image.
-/

public section

open Filter Topology

noncomputable section

namespace TauCeti

variable (R : Type*) [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

local instance : CompleteSpace R := FiniteDimensional.complete ℝ R
attribute [local instance] normedAlgebraRatOfReal
local instance : FiniteDimensional ℝ
    (LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- Applying `unitsLieAlgebraEquiv` in both coordinates tends to the origin at the origin. -/
theorem tendsto_unitsLieAlgebraCoordinates :
    Tendsto
      (fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦
        (unitsLieAlgebraEquiv p.1, unitsLieAlgebraEquiv p.2))
      (nhds (0, 0)) (nhds (0, 0)) := by
  let e := unitsLieAlgebraEquiv (R := R)
  change Tendsto (Prod.map e e) (nhds (0, 0)) (nhds (0, 0))
  simpa only [Prod.map, Prod.map_apply, Function.comp_apply,
    LinearEquiv.coe_toContinuousLinearEquiv',
    map_zero] using
    (e.toContinuousLinearEquiv.continuous.tendsto 0).prodMap_nhds
      (e.toContinuousLinearEquiv.continuous.tendsto 0)

/-- The local Baker--Campbell--Hausdorff germ on the Lie algebra of `Rˣ`, obtained by
transporting the canonical algebra-valued germ through `unitsLieAlgebraEquiv`. -/
def unitsLocalBCH :
    Germ (nhds ((0, 0) :
      LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
        LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ))
      (LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ) :=
  ((NormedSpace.localBCH R).compTendsto
      (fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦
        (unitsLieAlgebraEquiv p.1, unitsLieAlgebraEquiv p.2))
      (tendsto_unitsLieAlgebraCoordinates R)).map
    (unitsLieAlgebraEquiv (R := R)).symm

/-- `unitsLocalBCH` is represented by the algebra-valued BCH expression transported back to the
Lie algebra of `Rˣ`. -/
theorem unitsLocalBCH_def :
    unitsLocalBCH R =
      (↑(fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦
        (unitsLieAlgebraEquiv (R := R)).symm
          (NormedSpace.logOneAdd ℝ R
            (NormedSpace.exp (unitsLieAlgebraEquiv p.1) *
              NormedSpace.exp (unitsLieAlgebraEquiv p.2) - 1))) :
        Germ (nhds ((0, 0) :
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
            LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ))
          (LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ)) := by
  rw [unitsLocalBCH, NormedSpace.localBCH_def, Germ.coe_compTendsto, Germ.map_coe]
  -- The named germ equations above leave only the coercion/composition normal form.
  rfl

/-- In the canonical coordinates on the Lie algebra of `Rˣ`, `unitsLocalBCH` is exactly
`NormedSpace.localBCH R`. -/
@[simp]
theorem unitsLocalBCH_map_unitsLieAlgebraEquiv :
    (unitsLocalBCH R).map (unitsLieAlgebraEquiv (R := R)) =
      (NormedSpace.localBCH R).compTendsto
        (fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
            LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦
          (unitsLieAlgebraEquiv p.1, unitsLieAlgebraEquiv p.2))
        (tendsto_unitsLieAlgebraCoordinates R) := by
  rw [unitsLocalBCH, Germ.map_map]
  rw [show (unitsLieAlgebraEquiv (R := R)) ∘
      (unitsLieAlgebraEquiv (R := R)).symm = id by
    funext x
    exact (unitsLieAlgebraEquiv (R := R)).apply_symm_apply x, Germ.map_id]
  rfl

/-- The local Baker--Campbell--Hausdorff germ on the Lie algebra of `Rˣ` takes the value zero at
the origin. -/
@[simp]
theorem unitsLocalBCH_value : (unitsLocalBCH R).value = 0 := by
  rw [unitsLocalBCH_def, Germ.value_ofFun]
  simp only [map_zero, NormedSpace.exp_zero, mul_one, sub_self,
    NormedSpace.logOneAdd_zero, map_zero]

/-- Restricting `unitsLocalBCH` to the first coordinate axis gives the identity germ. -/
@[simp]
theorem unitsLocalBCH_sliceLeft :
    (unitsLocalBCH R).sliceLeft =
      (↑(fun X : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦ X) :
        Germ
          (nhds (0 : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ))
          (LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ)) := by
  let e := unitsLieAlgebraEquiv (R := R)
  have he : Tendsto e (nhds 0) (nhds 0) := by
    simpa only [LinearEquiv.coe_toContinuousLinearEquiv', map_zero] using
      e.toContinuousLinearEquiv.continuous.tendsto 0
  rw [unitsLocalBCH_def, Germ.sliceLeft_coe, Germ.coe_eq]
  filter_upwards [he.eventually (NormedSpace.eventually_logOneAdd_exp_sub_one R)] with X hX
  rw [map_zero, NormedSpace.exp_zero, mul_one, hX, e.symm_apply_apply]

/-- Restricting `unitsLocalBCH` to the second coordinate axis gives the identity germ. -/
@[simp]
theorem unitsLocalBCH_sliceRight :
    (unitsLocalBCH R).sliceRight =
      (↑(fun Y : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦ Y) :
        Germ
          (nhds (0 : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ))
          (LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ)) := by
  let e := unitsLieAlgebraEquiv (R := R)
  have he : Tendsto e (nhds 0) (nhds 0) := by
    simpa only [LinearEquiv.coe_toContinuousLinearEquiv', map_zero] using
      e.toContinuousLinearEquiv.continuous.tendsto 0
  rw [unitsLocalBCH_def, Germ.sliceRight_coe, Germ.coe_eq]
  filter_upwards [he.eventually (NormedSpace.eventually_logOneAdd_exp_sub_one R)] with Y hY
  rw [map_zero, NormedSpace.exp_zero, one_mul, hY, e.symm_apply_apply]

/-- The representative defining `unitsLocalBCH` is analytic at the origin. -/
theorem analyticAt_unitsLocalBCH_representative :
    AnalyticAt ℝ
      (fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦
        (unitsLieAlgebraEquiv (R := R)).symm
          (NormedSpace.logOneAdd ℝ R
            (NormedSpace.exp (unitsLieAlgebraEquiv p.1) *
              NormedSpace.exp (unitsLieAlgebraEquiv p.2) - 1)))
      (0, 0) := by
  let e := unitsLieAlgebraEquiv (R := R)
  have he : AnalyticAt ℝ
      (e : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ → R) 0 :=
    e.toContinuousLinearEquiv.analyticAt 0
  have hc : AnalyticAt ℝ
      (fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦
        (e p.1, e p.2)) (0, 0) :=
    (he.comp_of_eq (analyticAt_fst : AnalyticAt ℝ
      (fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦ p.1) (0, 0)) (by simp)).prod
      (he.comp_of_eq (analyticAt_snd : AnalyticAt ℝ
        (fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
            LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦ p.2) (0, 0)) (by simp))
  have hb := (NormedSpace.analyticAt_localBCH_representative R).comp_of_eq hc (by simp)
  have hs : AnalyticAt ℝ e.symm 0 := e.symm.toContinuousLinearEquiv.analyticAt 0
  simpa only [Function.comp_def, e, map_zero, NormedSpace.exp_zero, mul_one,
    sub_self, NormedSpace.logOneAdd_zero] using hs.comp_of_eq hb (by simp)

/-- The local Baker--Campbell--Hausdorff germ on the Lie algebra of `Rˣ` tends to zero at the
origin. -/
theorem unitsLocalBCH_tendsto : (unitsLocalBCH R).Tendsto (nhds 0) := by
  rw [unitsLocalBCH_def, Germ.coe_tendsto]
  simpa only [map_zero, NormedSpace.exp_zero, mul_one, sub_self,
    NormedSpace.logOneAdd_zero] using
      (analyticAt_unitsLocalBCH_representative R).continuousAt.tendsto

/-- Applying the abstract Lie-group exponential to `unitsLocalBCH` gives the germ of the product
of the two exponentials. -/
@[simp]
theorem unitsLocalBCH_map_lieExp :
    (unitsLocalBCH R).map (lieExp (I := modelWithCornersSelf ℝ R) (G := Rˣ)) =
      (↑(fun p : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ↦
        lieExp (I := modelWithCornersSelf ℝ R) p.1 *
          lieExp (I := modelWithCornersSelf ℝ R) p.2) :
        Germ (nhds ((0, 0) :
          LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
            LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ)) Rˣ) := by
  let e := unitsLieAlgebraEquiv (R := R)
  have hc : Tendsto (fun p ↦ (e p.1, e p.2))
      (nhds ((0, 0) : LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
        LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ))
      (nhds ((0, 0) : R × R)) := tendsto_unitsLieAlgebraCoordinates R
  have h :
      (NormedSpace.localBCH R).map (expUnit (R := R)) =
        (↑(fun p : R × R ↦ expUnit p.1 * expUnit p.2) :
          Germ (nhds ((0, 0) : R × R)) Rˣ) := by
    have h' := NormedSpace.localBCH_map_exp R
    rw [NormedSpace.localBCH_def, Germ.map_coe, Germ.coe_eq] at h'
    rw [NormedSpace.localBCH_def, Germ.map_coe, Germ.coe_eq]
    filter_upwards [h'] with p hp
    apply Units.ext
    simpa only [Function.comp_apply, expUnit_coe, Units.val_mul] using hp
  rw [NormedSpace.localBCH_def, Germ.map_coe, Germ.coe_eq] at h
  rw [unitsLocalBCH_def, Germ.map_coe, Germ.coe_eq]
  filter_upwards [hc.eventually h] with p hp
  apply Units.ext
  simpa only [Function.comp_apply, e, lieExp_eq_expUnit,
    LinearEquiv.apply_symm_apply, expUnit_coe, Units.val_mul] using
      congrArg Units.val hp

/-- A germ tending to zero with the same abstract Lie exponential image as `unitsLocalBCH` equals
`unitsLocalBCH`. -/
theorem eq_unitsLocalBCH_of_tendsto_of_map_lieExp_eq
    (f : Germ (nhds ((0, 0) :
      LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ ×
        LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ))
      (LeftInvariantDerivation (modelWithCornersSelf ℝ R) Rˣ))
    (hf : f.Tendsto (nhds 0))
    (hmap : f.map (lieExp (I := modelWithCornersSelf ℝ R) (G := Rˣ)) =
      (unitsLocalBCH R).map (lieExp (I := modelWithCornersSelf ℝ R) (G := Rˣ))) :
    f = unitsLocalBCH R := by
  let e := unitsLieAlgebraEquiv (R := R)
  induction f using Germ.inductionOn with
  | _ g =>
      rw [Germ.coe_tendsto] at hf
      have he : Tendsto e (nhds 0) (nhds 0) := by
        simpa only [LinearEquiv.coe_toContinuousLinearEquiv', map_zero] using
          e.toContinuousLinearEquiv.continuous.tendsto 0
      have hc : Tendsto (fun p : R × R ↦ (e.symm p.1, e.symm p.2))
          (nhds (0, 0)) (nhds (0, 0)) := by
        change Tendsto (Prod.map e.symm e.symm) (nhds (0, 0)) (nhds (0, 0))
        simpa only [Prod.map, Prod.map_apply, Function.comp_apply,
          LinearEquiv.coe_toContinuousLinearEquiv',
          map_zero] using
          (e.symm.toContinuousLinearEquiv.continuous.tendsto 0).prodMap_nhds
            (e.symm.toContinuousLinearEquiv.continuous.tendsto 0)
      let gR : R × R → R := fun p ↦ e (g (e.symm p.1, e.symm p.2))
      have hgR : Tendsto gR (nhds (0, 0)) (nhds 0) := he.comp (hf.comp hc)
      have hmap' :
          (fun p ↦ lieExp (I := modelWithCornersSelf ℝ R) (g p)) =ᶠ[nhds (0, 0)]
            (fun p ↦ lieExp (I := modelWithCornersSelf ℝ R) p.1 *
              lieExp (I := modelWithCornersSelf ℝ R) p.2) := by
        rw [Germ.map_coe, unitsLocalBCH_map_lieExp, Germ.coe_eq] at hmap
        simpa only [Function.comp_def] using hmap
      have hmapR :
          ((↑gR : Germ (nhds ((0, 0) : R × R)) R).map NormedSpace.exp) =
            (NormedSpace.localBCH R).map NormedSpace.exp := by
        rw [NormedSpace.localBCH_map_exp, Germ.map_coe, Germ.coe_eq]
        filter_upwards [hc.eventually hmap'] with p hp
        have hv := congrArg Units.val hp
        simpa only [Function.comp_apply, gR, e, lieExp_eq_expUnit, expUnit_coe,
          Units.val_mul, e.apply_symm_apply] using hv
      have hg := NormedSpace.eq_localBCH_of_tendsto_of_map_exp_eq R
        (↑gR : Germ (nhds ((0, 0) : R × R)) R) hgR hmapR
      rw [NormedSpace.localBCH_def, Germ.coe_eq] at hg
      rw [unitsLocalBCH_def, Germ.coe_eq]
      filter_upwards [(tendsto_unitsLieAlgebraCoordinates R).eventually hg] with p hp
      simpa only [gR, e, e.symm_apply_apply, e.apply_symm_apply] using congrArg e.symm hp

end TauCeti
