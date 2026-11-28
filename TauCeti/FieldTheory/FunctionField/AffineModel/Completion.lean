/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.Extension
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Adic

/-!
# Affine models and place completions

For a place `P'` of an extension `F' / F`, the centre of `P'` on the local integral closure `𝒪'_P`
(`TauCeti.Place.centerIntegralClosure`) generates the maximal ideal of the completed valuation
ring `𝒪̂_{P'}` under `TauCeti.Place.completionIntegersIntegralClosureHom`.

## Main results

* `TauCeti.Place.map_centerIntegralClosure_completionIntegers`: the centre of `P'` on `𝒪'_P`
  generates the completed maximal ideal `𝔪̂_{P'}`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section I.7 and Section III.1.
* J.-P. Serre, *Local Fields*, Chapter II, Section 3.
-/

public section

noncomputable section

open IsDedekindDomain

namespace TauCeti.Place

section CenterIntegralClosure

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable (k F : Type*) {k' F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **The centre of `P'` on `𝒪'_P` generates the completed maximal ideal `𝔪̂_{P'}`.** -/
@[simp]
theorem map_centerIntegralClosure_completionIntegers
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (P' : Place k' F') :
    letI := (P'.restrict k F).completionIntegersBaseAlgebra P' rfl
    (centerIntegralClosure k F P').asIdeal.map
        (((P'.restrict k F).completionIntegersIntegralClosureHom P' rfl :
          integralClosure (P'.restrict k F).integers F' →+* P'.completionPlace.integers)) =
      IsLocalRing.maximalIdeal P'.completionPlace.integers := by
  let _ := (P'.restrict k F).completionIntegersBaseAlgebra P' rfl
  let w := centerIntegralClosure k F P'
  have hw : P'.valuation = w.valuation F' := (valuation_centerIntegralClosure k F P').symm
  let eB := completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k' F' w P' hw
  have hcomp : eB.toRingHom.comp
        ((P'.restrict k F).completionIntegersIntegralClosureHom P' rfl :
          integralClosure (P'.restrict k F).integers F' →+* P'.completionPlace.integers) =
      algebraMap (integralClosure (P'.restrict k F).integers F') (w.adicCompletionIntegers F') := by
    refine RingHom.ext fun b ↦ Subtype.ext ?_
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe,
      completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply,
      coe_completionIntegersIntegralClosureHom,
      completionEquivAdicCompletionOfValuationEq_completionEmbedding,
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.algebraMap_adicCompletion, Subalgebra.algebraMap_apply]
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq]
  have hmap : ((w.asIdeal.map
      (((P'.restrict k F).completionIntegersIntegralClosureHom P' rfl :
        integralClosure (P'.restrict k F).integers F' →+* P'.completionPlace.integers))).map
      eB.toRingHom) =
      (IsLocalRing.maximalIdeal P'.completionPlace.integers).map eB.toRingHom := by
    rw [Ideal.map_map, hcomp, w.map_asIdeal_adicCompletionIntegers (K := F'),
      RingEquiv.toRingHom_eq_coe]
    exact (IsLocalRing.map_ringEquiv_maximalIdeal eB).symm
  exact eB.idealComapOrderIso.symm.injective hmap

end CenterIntegralClosure

end TauCeti.Place

end
