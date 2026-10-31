/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Plus
public import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.RingTheory.Valuation.Integral.Basic

/-!
# Checks for changes of tensor plus rings

Give `ℚ` the discrete topology and use the two-adic valuation ring as its plus ring.
The two-adic point pulls back along multiplication on the completed self-tensor. Enlarging
either factor plus ring to all of `ℚ` excludes this point: the corresponding coprojection
of `1/2` now belongs to the plus ring. Thus the comparison can give a strict inclusion,
even for complete input rings.
-/

public section

open TauCeti TauCeti.Huber TauCeti.ValuationSpectrum

namespace TensorPlusChecks

/-- The discrete uniformity on the rational check fixture. -/
local instance rationalDiscreteUniformSpace : UniformSpace ℚ := ⊥
local instance : DiscreteTopology ℚ := ⟨rfl⟩
local instance : IsAdicHom (algebraMap ℚ ℚ) := by
  simpa using IsAdicHom.id (A := ℚ)

private def integralPair : Pair ℚ where
  plus := (Rat.padicValuation 2).integer
  isRingOfIntegralElements :=
    { isOpen := isOpen_discrete _
      isIntegrallyClosedIn := inferInstance
      le_powerBoundedSubring := by rw [powerBoundedSubring_eq_top]; exact le_top }

private noncomputable def multiplication : CompletedTensor ℚ ℚ ℚ →+* ℚ :=
  CompletedTensor.lift (RingHom.id ℚ) (RingHom.id ℚ) rfl continuous_id continuous_id

private theorem continuous_multiplication : Continuous multiplication :=
  CompletedTensor.continuous_lift _ _ _ _ _

private noncomputable def point : Spv (CompletedTensor ℚ ℚ ℚ) :=
  comap multiplication (ofValuation (Rat.padicValuation 2))

private theorem point_continuous : point.IsContinuous :=
  ((mem_cont_iff _).mp (cont_eq_univ (A := ℚ) ▸ Set.mem_univ _)).comap
    continuous_multiplication

private theorem point_inl : comap (CompletedTensor.inl ℚ ℚ ℚ) point =
    ofValuation (Rat.padicValuation 2) := by
  rw [point, ← Function.comp_apply (f := comap _), ← comap_comp, multiplication,
    CompletedTensor.lift_comp_inl, comap_id, id]

private theorem point_inr : comap (CompletedTensor.inr ℚ ℚ ℚ) point =
    ofValuation (Rat.padicValuation 2) := by
  rw [point, ← Function.comp_apply (f := comap _), ← comap_comp, multiplication,
    CompletedTensor.lift_comp_inr, comap_id, id]

private theorem point_mem : point ∈ spa (integralPair.completedTensor ℚ integralPair).plus := by
  rw [Pair.completedTensor.mem_spa_iff _ _ point_continuous, point_inl, point_inr]
  have h : ofValuation (Rat.padicValuation 2) ∈ spa integralPair.plus := by
    rw [mem_spa_iff]
    exact ⟨(mem_cont_iff _).mp (cont_eq_univ (A := ℚ) ▸ Set.mem_univ _),
      fun _ ha ↦ (vle_ofValuation _ _ _).mpr (by
        simpa only [integralPair, Valuation.mem_integer_iff, map_one] using ha)⟩
  exact ⟨h, h⟩

private theorem valuationPoint_notMem_full :
    ofValuation (Rat.padicValuation 2) ∉ spa (Pair.discrete ℚ).plus := by
  intro h
  have hh := ((mem_spa_iff _ _).mp h).2 (1 / 2 : ℚ) (by simp)
  rw [vle_ofValuation, map_one, Rat.padicValuation_le_one_iff] at hh
  norm_num at hh

/-- Enlarging only the left plus ring excludes the two-adic point. -/
example : point ∈ spa (integralPair.completedTensor ℚ integralPair).plus ∧
    point ∉ spa ((Pair.discrete ℚ).completedTensor ℚ integralPair).plus := by
  refine ⟨point_mem, fun h ↦ ?_⟩
  have hp : (⟨point, point_mem⟩ : spa (integralPair.completedTensor ℚ integralPair).plus) ∈
      Subtype.val ⁻¹' spa ((Pair.discrete ℚ).completedTensor ℚ integralPair).plus := h
  rw [Pair.completedTensor.spa_plus_eq_inter_preimage] at hp
  have hleft : comap (CompletedTensor.inl ℚ ℚ ℚ) point ∈ spa (Pair.discrete ℚ).plus := by
    simpa only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl]
      using hp.1
  exact valuationPoint_notMem_full (point_inl ▸ hleft)

/-- Enlarging only the right plus ring also excludes the point, independently of the left. -/
example : point ∈ spa (integralPair.completedTensor ℚ integralPair).plus ∧
    point ∉ spa (integralPair.completedTensor ℚ (Pair.discrete ℚ)).plus := by
  refine ⟨point_mem, fun h ↦ ?_⟩
  have hright := ((Pair.completedTensor.mem_spa_iff _ _ point_continuous).mp h).2
  exact valuationPoint_notMem_full (point_inr ▸ hright)

end TensorPlusChecks
