/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.Restricted.UnitGaussValuation

import TauCeti.RingTheory.Huber.Restricted.Comparison

/-!
# Residue reduction on the integral Tate algebra of a normed field

For an ultrametric normed field `K`, the power-bounded subring `K°` is a local ring whose maximal
ideal `K°° = topologicallyNilpotentIdeal K` is open
(`TauCeti.Huber.isOpen_topologicallyNilpotentIdeal`).
Reducing unit-bounded restricted series `f ∈ K°⟨T₁, …, Tₙ⟩` coefficientwise modulo `K°°` via
`Ideal.weightedSubringReduction` and transporting to `IsLocalRing.ResidueField K°` yields a
polynomial reduction homomorphism
`TauCeti.Huber.polydiscReduction n K : K°⟨T₁, …, Tₙ⟩ →+* (IsLocalRing.ResidueField K°)[T₁, …, Tₙ]`.

A series reduces to zero exactly when every coefficient has norm strictly less than `1`, that is,
when `unitGaussValuation n K f.val < 1`; equivalently, its reduction is nonzero if and only if
`unitGaussValuation n K f.val = 1`. Over a complete field `K`, evaluating `f ∈ K°⟨T₁, …, Tₙ⟩` at
a power-bounded tuple `a ∈ (K°)ⁿ` lands in `K°` and commutes with residue reduction.

## Main definitions

* `TauCeti.Huber.polydiscReduction`: coefficientwise reduction
  `K°⟨T₁, …, Tₙ⟩ →+* (IsLocalRing.ResidueField K°)[T₁, …, Tₙ]`.

## Main results

* `TauCeti.Huber.polydiscReduction_def`: unfolding to `Ideal.weightedSubringReduction`.
* `TauCeti.Huber.polydiscReduction_eq_zero_iff` and
  `TauCeti.Huber.polydiscReduction_ne_zero_iff`: vanishing of the reduced polynomial is
  `unitGaussValuation n K f.val < 1`, and nonvanishing is `unitGaussValuation n K f.val = 1`.
* `TauCeti.Huber.weightedEvalHom_mem_powerBoundedSubring_of_mem_weightedSubring`: evaluating a
  unit-bounded series at a power-bounded tuple yields a power-bounded element.
* `TauCeti.Huber.residue_weightedEvalHom_eq_eval_polydiscReduction`: residue reduction commutes
  with evaluation at power-bounded tuples.
* `TauCeti.Huber.norm_weightedEvalHom_eq_one_iff_eval_polydiscReduction_ne_zero`: `‖f(a)‖ = 1` iff
  the reduced polynomial does not vanish at `ā`.
-/

public section

namespace TauCeti.Huber

open Filter Topology
open scoped NNReal

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **Coefficientwise reduction on `K°⟨T₁, …, Tₙ⟩`**, sending a unit-bounded restricted power
series to the polynomial over the residue field `IsLocalRing.ResidueField K°` obtained by reducing
each coefficient. -/
noncomputable def polydiscReduction (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) →+*
      MvPolynomial (Fin n) (IsLocalRing.ResidueField (powerBoundedSubring K)) :=
  (MvPolynomial.map
      (Ideal.Quotient.lift (topologicallyNilpotentIdeal K)
        (IsLocalRing.residue (powerBoundedSubring K))
        fun _ hx ↦ (IsLocalRing.residue_eq_zero_iff _).mpr
          ((maximalIdeal_powerBoundedSubring (K := K)).symm ▸ hx))).comp
    (Ideal.weightedSubringReduction (powerBoundedSubring K) (topologicallyNilpotentIdeal K)
      isOpen_topologicallyNilpotentIdeal)

/-- Unfolding equation bridging `polydiscReduction` to `Ideal.weightedSubringReduction`. -/
theorem polydiscReduction_def :
    polydiscReduction n K =
      (MvPolynomial.map
          (Ideal.Quotient.lift (topologicallyNilpotentIdeal K)
            (IsLocalRing.residue (powerBoundedSubring K))
            fun _ hx ↦ (IsLocalRing.residue_eq_zero_iff _).mpr
              ((maximalIdeal_powerBoundedSubring (K := K)).symm ▸ hx))).comp
        (Ideal.weightedSubringReduction (powerBoundedSubring K) (topologicallyNilpotentIdeal K)
          isOpen_topologicallyNilpotentIdeal) :=
  (rfl)

/-- The reduction of a unit-bounded series vanishes if and only if its unit Gauss valuation is
strictly less than `1`. -/
theorem polydiscReduction_eq_zero_iff
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    polydiscReduction n K f = 0 ↔ unitGaussValuation n K f.val < 1 := by
  let ψ : powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K →+*
      IsLocalRing.ResidueField (powerBoundedSubring K) :=
    Ideal.Quotient.lift (topologicallyNilpotentIdeal K)
      (IsLocalRing.residue (powerBoundedSubring K))
      fun _ hx ↦ (IsLocalRing.residue_eq_zero_iff _).mpr
        ((maximalIdeal_powerBoundedSubring (K := K)).symm ▸ hx)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.lift_mk, IsLocalRing.residue_eq_zero_iff,
      maximalIdeal_powerBoundedSubring] at hq
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hq
  rw [polydiscReduction_def, RingHom.comp_apply,
    (MvPolynomial.map_injective (ψ : _ →+* _) hinj).eq_iff' (map_zero _),
    Ideal.weightedSubringReduction_eq_zero_iff, unitGaussValuation_def,
    weightedGaussValuation_lt_iff]
  refine forall_congr' fun ν ↦ ?_
  rw [mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, NormedField.valuation_apply,
    ← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one]

/-- The reduction of a unit-bounded series is nonzero if and only if its unit Gauss valuation
equals `1`. -/
theorem polydiscReduction_ne_zero_iff
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    polydiscReduction n K f ≠ 0 ↔ unitGaussValuation n K f.val = 1 := by
  rw [Ne, polydiscReduction_eq_zero_iff, not_lt]
  have hle : unitGaussValuation n K f.val ≤ 1 :=
    (unitGaussValuation_le_one_iff_mem_weightedSubring n K).mpr f.property
  exact ⟨fun h ↦ le_antisymm hle h, fun h ↦ h.ge⟩

section EvalReduction

variable [CompleteSpace K]

/-- Evaluating a unit-bounded series at a power-bounded tuple yields a power-bounded element. -/
theorem weightedEvalHom_mem_powerBoundedSubring_of_mem_weightedSubring
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (hb : IsWeightBounded (RingHom.id K) (fun _ : Fin n ↦ ({1} : Set K)) a)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val ∈ powerBoundedSubring K := by
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one]
  refine (norm_weightedEvalHom_le continuousAt_id (C := 1) (fun r ↦ by simp)
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i)) _ f.val).trans ?_
  rw [one_mul, MvPowerSeries.norm_eq_gaussNorm, coe_restrictedMvPowerSeriesGaussEquiv,
    ← coe_unitGaussValuation]
  exact_mod_cast (unitGaussValuation_le_one_iff_mem_weightedSubring n K).mpr f.property

/-- **Reduction commutes with evaluation at power-bounded tuples.** For `f ∈ K°⟨T₁, …, Tₙ⟩` and
`a ∈ (K°)ⁿ`, the residue of `f(a)` in `IsLocalRing.ResidueField K°` equals the value of
`polydiscReduction n K f` at the residue tuple `ā`. -/
theorem residue_weightedEvalHom_eq_eval_polydiscReduction
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (hb : IsWeightBounded (RingHom.id K) (fun _ : Fin n ↦ ({1} : Set K)) a)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    IsLocalRing.residue (powerBoundedSubring K)
        ⟨weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val,
          weightedEvalHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha hb f⟩ =
      MvPolynomial.eval
        (fun i ↦ IsLocalRing.residue (powerBoundedSubring K)
          ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩)
        (polydiscReduction n K f) := by
  have : CompleteSpace (powerBoundedSubring K) :=
    (coe_powerBoundedSubring_eq_closedBall K ▸ Metric.isClosed_closedBall).completeSpace_coe
  let b : Fin n → powerBoundedSubring K := fun i ↦ ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩
  have huniv : TauCeti.Huber.IsBounded (Set.univ : Set (powerBoundedSubring K)) := by
    convert (powerBoundedSubring K).isBounded_preimage_subtype
      (IsUniform.isBounded_powerBoundedSubring (A := K))
    ext x
    exact ⟨fun _ ↦ x.property, fun _ ↦ Set.mem_univ x⟩
  have hb' : IsWeightBounded (RingHom.id (powerBoundedSubring K))
      (fun _ : Fin n ↦ ({1} : Set (powerBoundedSubring K))) b :=
    (isWeightBounded_one_weight_iff _ _).mpr (huniv.subset (Set.subset_univ _))
  have hsub : Continuous (powerBoundedSubring K).subtype := continuous_subtypeVal
  have hext :
      (powerBoundedSubring K).subtype.comp
          (weightedEvalHom isWeightFamily_one_weight continuousAt_id hb') =
        (weightedEvalHom isWeightFamily_one_weight continuousAt_id hb).comp
          (weightedMap hsub isWeightFamily_one_weight isWeightFamily_one_weight
            (fun _ ↦ by simp)) := by
    refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (continuous_subtypeVal.comp (continuous_weightedEvalHom _ _ _))
      ((continuous_weightedEvalHom _ _ _).comp (continuous_weightedMap _ _ _ _))
      (fun c ↦ by
        rw [RingHom.comp_apply, RingHom.comp_apply, weightedEvalHom_weightedC,
          weightedMap_weightedC, weightedEvalHom_weightedC]; rfl)
      (fun i ↦ by
        rw [RingHom.comp_apply, RingHom.comp_apply, weightedEvalHom_weightedX,
          weightedMap_weightedX, weightedEvalHom_weightedX]; rfl)
  have heval :
      (⟨weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val,
          weightedEvalHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha hb f⟩ :
          powerBoundedSubring K) =
        weightedEvalHom isWeightFamily_one_weight continuousAt_id hb'
          ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f) := by
    refine Subtype.ext ?_
    have h := DFunLike.congr_fun hext
      ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f)
    have hval :
        weightedMap hsub isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp)
            ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f) =
          f.val := by
      apply Subtype.ext
      rw [coe_weightedMap, ← coe_weightedRestrictedSubringEquivWeightedSubring,
        RingEquiv.apply_symm_apply]
    simpa [hval] using h.symm
  let ψ : powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K →+*
      IsLocalRing.ResidueField (powerBoundedSubring K) :=
    Ideal.Quotient.lift (topologicallyNilpotentIdeal K)
      (IsLocalRing.residue (powerBoundedSubring K))
      fun _ hx ↦ (IsLocalRing.residue_eq_zero_iff _).mpr
        ((maximalIdeal_powerBoundedSubring (K := K)).symm ▸ hx)
  have hq := congrArg ψ
    (mk_weightedEvalHom_eq_eval₂_restrictedReduction continuousAt_id hb'
      isOpen_topologicallyNilpotentIdeal isOpen_topologicallyNilpotentIdeal le_rfl
      ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f))
  have hid : Ideal.quotientMap (I := topologicallyNilpotentIdeal K)
      (topologicallyNilpotentIdeal K) (RingHom.id (powerBoundedSubring K)) le_rfl =
      RingHom.id _ := RingHom.ext fun q ↦ by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl
  rw [← heval, show ψ (Ideal.Quotient.mk (topologicallyNilpotentIdeal K) _) =
      IsLocalRing.residue (powerBoundedSubring K) _ from rfl,
    hid, MvPolynomial.eval₂_id] at hq
  rw [hq, polydiscReduction_def, RingHom.comp_apply,
    Ideal.weightedSubringReduction_def, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, MvPolynomial.eval_map]
  change ψ (MvPolynomial.eval₂ (RingHom.id _) _ _) = _
  rw [MvPolynomial.hom_eval₂]
  rfl

/-- A unit-bounded series `f ∈ K°⟨T₁, …, Tₙ⟩` evaluates to an element of norm `1` at `a ∈ (K°)ⁿ`
if and only if its reduction does not vanish at the residue tuple `ā`. -/
theorem norm_weightedEvalHom_eq_one_iff_eval_polydiscReduction_ne_zero
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (hb : IsWeightBounded (RingHom.id K) (fun _ : Fin n ↦ ({1} : Set K)) a)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    ‖weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val‖ = 1 ↔
      MvPolynomial.eval
        (fun i ↦ IsLocalRing.residue (powerBoundedSubring K)
          ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩)
        (polydiscReduction n K f) ≠ 0 := by
  have hle : ‖weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp
      (mem_powerBoundedSubring.mp
        (weightedEvalHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha hb f))
  rw [← residue_weightedEvalHom_eq_eval_polydiscReduction a ha hb f, Ne,
    IsLocalRing.residue_eq_zero_iff, maximalIdeal_powerBoundedSubring,
    mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm hle h⟩

end EvalReduction

end TauCeti.Huber
