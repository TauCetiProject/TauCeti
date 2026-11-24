/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.Restricted.UnitGaussValuation

import TauCeti.RingTheory.Huber.Restricted.Comparison
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

/-!
# Residue reduction on the integral Tate algebra of a normed field

For an ultrametric normed field `K`, the power-bounded subring `K°` is a local ring whose maximal
ideal `K°° = topologicallyNilpotentIdeal K` is open
(`TauCeti.Huber.isOpen_topologicallyNilpotentIdeal`), with
`K° ⧸ K°° ≃+* IsLocalRing.ResidueField K°`
(`TauCeti.Huber.powerBoundedSubringQuotientEquivResidueField`). Reducing unit-bounded restricted
series `f ∈ K°⟨T₁, …, Tₙ⟩` coefficientwise modulo `K°°` via `Ideal.weightedSubringReduction` and
transporting along `powerBoundedSubringQuotientEquivResidueField` yields the polynomial reduction
homomorphism
`TauCeti.Huber.polydiscReduction n K : K°⟨T₁, …, Tₙ⟩ →+* (IsLocalRing.ResidueField K°)[T₁, …, Tₙ]`.

A series reduces to zero exactly when every coefficient has norm strictly less than `1`, that is,
when `unitGaussValuation n K f.val < 1`; equivalently, its reduction is nonzero if and only if
`unitGaussValuation n K f.val = 1`. Over a complete field `K`, evaluating `f ∈ K°⟨T₁, …, Tₙ⟩` at
a power-bounded tuple `a ∈ (K°)ⁿ` lands in `K°` and commutes with residue reduction. When `K` is
nontrivially normed, these follow from `TauCeti.MvPowerSeries.restrictedReduction` and
`TauCeti.MvPowerSeries.residue_restrictedEval₂` across `restrictedMvPowerSeriesGaussEquiv`; when `K`
is discrete, all norms on `K \ {0}` equal `1` and every restricted series is a polynomial.

## Main definitions

* `TauCeti.Huber.polydiscReduction`: coefficientwise reduction
  `K°⟨T₁, …, Tₙ⟩ →+* (IsLocalRing.ResidueField K°)[T₁, …, Tₙ]`.

## Main results

* `TauCeti.Huber.polydiscReduction_def`: unfolding to `Ideal.weightedSubringReduction`.
* `TauCeti.Huber.coeff_polydiscReduction`, `TauCeti.Huber.polydiscReduction_weightedPolynomialHom`,
  `TauCeti.Huber.polydiscReduction_weightedC`, `TauCeti.Huber.polydiscReduction_weightedX`, and
  `TauCeti.Huber.polydiscReduction_surjective`: coefficient, generator, and surjectivity API.
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
open scoped NNReal NormedField Valued

section Basic

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **Coefficientwise reduction on `K°⟨T₁, …, Tₙ⟩`**, sending a unit-bounded restricted power
series to the polynomial over the residue field `IsLocalRing.ResidueField K°` obtained by reducing
each coefficient. -/
noncomputable def polydiscReduction (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) →+*
      MvPolynomial (Fin n) (IsLocalRing.ResidueField (powerBoundedSubring K)) :=
  (MvPolynomial.map
      (powerBoundedSubringQuotientEquivResidueField (K := K)).toRingHom).comp
    (Ideal.weightedSubringReduction (powerBoundedSubring K) (topologicallyNilpotentIdeal K)
      isOpen_topologicallyNilpotentIdeal)

/-- Unfolding equation bridging `polydiscReduction` to `Ideal.weightedSubringReduction`. -/
theorem polydiscReduction_def :
    polydiscReduction n K =
      (MvPolynomial.map
          (powerBoundedSubringQuotientEquivResidueField (K := K)).toRingHom).comp
        (Ideal.weightedSubringReduction (powerBoundedSubring K) (topologicallyNilpotentIdeal K)
          isOpen_topologicallyNilpotentIdeal) :=
  (rfl)

/-- Each coefficient of `polydiscReduction n K f` is the residue in `IsLocalRing.ResidueField K°`
of the corresponding coefficient of `f`. -/
@[simp]
theorem coeff_polydiscReduction
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) (ν : Fin n →₀ ℕ) :
    (polydiscReduction n K f).coeff ν =
      IsLocalRing.residue (powerBoundedSubring K)
        ⟨MvPowerSeries.coeff ν ((f.val : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
            isWeightFamily_one_weight) : MvPowerSeries (Fin n) K),
          by simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
            mem_weightedNhd.mp (mem_weightedSubring.mp f.property) ν⟩ := by
  rw [polydiscReduction_def, RingHom.comp_apply, MvPolynomial.coeff_map,
    Ideal.coeff_weightedSubringReduction, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    powerBoundedSubringQuotientEquivResidueField_mk]

/-- On embedded polynomials with coefficients in `K°`, `polydiscReduction` reduces coefficients to
`IsLocalRing.ResidueField K°`. -/
@[simp]
theorem polydiscReduction_weightedPolynomialHom
    (p : MvPolynomial (Fin n) (powerBoundedSubring K)) :
    polydiscReduction n K
        ⟨weightedPolynomialHom (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
            (MvPolynomial.map (powerBoundedSubring K).subtype p),
          weightedPolynomialHom_map_mem_weightedSubring_one_weight (powerBoundedSubring K) p⟩ =
      MvPolynomial.map (IsLocalRing.residue (powerBoundedSubring K)) p := by
  rw [polydiscReduction_def, RingHom.comp_apply,
    Ideal.weightedSubringReduction_weightedPolynomialHom, MvPolynomial.map_map]
  exact congrArg (MvPolynomial.map · p)
    (RingHom.ext powerBoundedSubringQuotientEquivResidueField_mk)

/-- `polydiscReduction` sends constant series in `K°` to constant polynomials over
`IsLocalRing.ResidueField K°`. -/
@[simp]
theorem polydiscReduction_weightedC (a : powerBoundedSubring K) :
    polydiscReduction n K
        ⟨weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight (a : K),
          (weightedC_mem_weightedSubring isWeightFamily_one_weight).mpr a.property⟩ =
      MvPolynomial.C (IsLocalRing.residue (powerBoundedSubring K) a) := by
  simp [polydiscReduction_def]

/-- `polydiscReduction` preserves the coordinate variables. -/
@[simp]
theorem polydiscReduction_weightedX (i : Fin n) :
    polydiscReduction n K
        ⟨weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i,
          weightedX_mem_weightedSubring_one_weight (powerBoundedSubring K) i⟩ =
      MvPolynomial.X i := by
  simp [polydiscReduction_def]

/-- Every polynomial over `IsLocalRing.ResidueField K°` lifts to `K°⟨T₁, …, Tₙ⟩`. -/
theorem polydiscReduction_surjective :
    Function.Surjective (polydiscReduction (n := n) (K := K)) :=
  (MvPolynomial.map_surjective _
      powerBoundedSubringQuotientEquivResidueField.surjective).comp
    (Ideal.weightedSubringReduction_surjective (powerBoundedSubring K)
      (topologicallyNilpotentIdeal K) isOpen_topologicallyNilpotentIdeal)

private noncomputable def toUnitClosedBall
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    Subring.unitClosedBall (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
  ⟨restrictedMvPowerSeriesGaussEquiv f.val,
    TauCeti.MvPowerSeries.mem_unitClosedBall_iff.mpr fun t ↦ by
      simpa [weightMul_one_weight, mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one] using
        mem_weightedNhd.mp (mem_weightedSubring.mp f.property) t⟩

end Basic

private theorem map_polydiscReduction_eq_restrictedReduction
    {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    (polydiscReduction n K f).map
        (IsLocalRing.ResidueField.mapEquiv (powerBoundedSubringEquivInteger (K := K))).toRingHom =
      TauCeti.MvPowerSeries.restrictedReduction (toUnitClosedBall f) := by
  refine MvPolynomial.ext _ _ fun ν ↦ ?_
  rw [MvPolynomial.coeff_map, coeff_polydiscReduction,
    TauCeti.MvPowerSeries.coeff_restrictedReduction, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  refine congrArg (IsLocalRing.residue 𝒪[K]) (Subtype.ext (by simp [toUnitClosedBall]))

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The reduction of a unit-bounded series vanishes if and only if its unit Gauss valuation is
strictly less than `1`. -/
theorem polydiscReduction_eq_zero_iff
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    polydiscReduction n K f = 0 ↔ unitGaussValuation n K f.val < 1 := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with hdisc | ⟨_, rfl⟩
  · have hlt_iff (ν : Fin n →₀ ℕ) :
        ‖MvPowerSeries.coeff ν ((f.val : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
            isWeightFamily_one_weight) : MvPowerSeries (Fin n) K)‖ < 1 ↔
          MvPowerSeries.coeff ν ((f.val : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
              isWeightFamily_one_weight) : MvPowerSeries (Fin n) K) = 0 :=
      ⟨fun h ↦ by_contra fun hne ↦
          h.ne (NormedDivisionRing.norm_eq_one_iff_ne_zero_of_discrete.mpr hne),
        fun h ↦ by simp [h]⟩
    rw [polydiscReduction_def, RingHom.comp_apply,
      (MvPolynomial.map_injective _ powerBoundedSubringQuotientEquivResidueField.injective).eq_iff'
        (map_zero _),
      Ideal.weightedSubringReduction_eq_zero_iff, unitGaussValuation_def,
      weightedGaussValuation_lt_iff]
    refine forall_congr' fun ν ↦ ?_
    rw [mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
      tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, NormedField.valuation_apply,
      ← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one, hlt_iff]
  · let eRes := IsLocalRing.ResidueField.mapEquiv (powerBoundedSubringEquivInteger (K := K))
    rw [← (MvPolynomial.map_injective eRes.toRingHom eRes.injective).eq_iff' (map_zero _),
      map_polydiscReduction_eq_restrictedReduction,
      TauCeti.MvPowerSeries.restrictedReduction_eq_zero_iff, MvPowerSeries.norm_eq_gaussNorm,
      toUnitClosedBall, coe_restrictedMvPowerSeriesGaussEquiv, ← coe_unitGaussValuation]
    exact_mod_cast Iff.rfl

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
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with hdisc | ⟨_, rfl⟩
  · rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one]
    exact NormedDivisionRing.norm_le_one_of_discrete _
  · have ha₁ : ∀ i, ‖a i‖ ≤ 1 := fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i)
    have hev :
        weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val =
          MvPowerSeries.restrictedEval₂ (RingHom.id K) a (fun _ ↦ le_rfl) ha₁
            (toUnitClosedBall f :
              MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) := by
      rw [weightedEvalHom_eq_restrictedEval₂OfBound continuousAt_id (C := 1) (fun _ ↦ by simp) ha₁
        hb, RingHom.restrictedEval₂OfBound_eq_restrictedEval₂ _ _ _ _ (fun _ ↦ le_rfl)]
      rfl
    rw [hev]
    let x : Fin n → 𝒪[K] := fun i ↦ ⟨a i, Valued.integer.mem_iff.mpr (ha₁ i)⟩
    exact (powerBoundedSubring_eq_integer (K := K)).ge
      (TauCeti.MvPowerSeries.restrictedEval₂_mem_integer (RingHom.id K) (fun _ ↦ le_rfl) x
        (toUnitClosedBall f))

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
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with hdisc | ⟨_, rfl⟩
  · have hmem : ∀ x : K, x ∈ powerBoundedSubring K := fun x ↦ by
      rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one]
      exact NormedDivisionRing.norm_le_one_of_discrete x
    let p : MvPolynomial (Fin n) K :=
      (weightedPolynomialEquivOfDiscrete (fun _ : Fin n ↦ ({1} : Set K))
        isWeightFamily_one_weight).symm f.val
    let ι : K →+* powerBoundedSubring K :=
      { toFun := fun x ↦ ⟨x, hmem x⟩
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl }
    have hfval : f.val = weightedPolynomialHom (fun _ : Fin n ↦ ({1} : Set K))
        isWeightFamily_one_weight p :=
      ((weightedPolynomialEquivOfDiscrete_apply p).symm.trans
        ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).apply_symm_apply
          f.val)).symm
    have hfp : f = ⟨weightedPolynomialHom (fun _ : Fin n ↦ ({1} : Set K))
        isWeightFamily_one_weight (MvPolynomial.map (powerBoundedSubring K).subtype (p.map ι)),
        weightedPolynomialHom_map_mem_weightedSubring_one_weight _ _⟩ := by
      refine Subtype.ext (hfval.trans ?_)
      change weightedPolynomialHom _ _ p =
        weightedPolynomialHom _ _ (MvPolynomial.map (powerBoundedSubring K).subtype (p.map ι))
      have hcomp : (powerBoundedSubring K).subtype.comp ι = RingHom.id K :=
        RingHom.ext fun _ ↦ rfl
      rw [MvPolynomial.map_map, hcomp, MvPolynomial.map_id]
    have heval_poly :
        weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val =
          MvPolynomial.eval a p := by
      rw [weightedEvalHom_eq_restrictedEval₂OfBound continuousAt_id (C := 1) (fun _ ↦ by simp)
        (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i)) hb, hfval,
        restrictedMvPowerSeriesGaussEquiv_weightedPolynomialHom,
        RingHom.restrictedEval₂OfBound_polynomial]
      rfl
    conv_rhs => rw [hfp, polydiscReduction_weightedPolynomialHom, MvPolynomial.eval_map]
    rw [MvPolynomial.eval₂_map]
    change (IsLocalRing.residue (powerBoundedSubring K)).comp ι
        (weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val) = _
    rw [heval_poly]
    change (IsLocalRing.residue (powerBoundedSubring K)).comp ι
        (p.eval₂ (RingHom.id K) a) = _
    rw [RingHom.comp_apply, MvPolynomial.hom_eval₂, RingHom.comp_id, MvPolynomial.hom_eval₂]
    exact congrArg (fun g ↦ MvPolynomial.eval₂ _ g p)
      (funext fun i ↦ congrArg (IsLocalRing.residue _) (Subtype.ext rfl))
  · let eInt := powerBoundedSubringEquivInteger (K := K)
    let eRes := IsLocalRing.ResidueField.mapEquiv eInt
    apply eRes.injective
    have ha₁ : ∀ i, ‖a i‖ ≤ 1 := fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i)
    let x : Fin n → Valued.integer K := fun i ↦ ⟨a i, Valued.integer.mem_iff.mpr (ha₁ i)⟩
    have hlhs_val :
        (eInt ⟨weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val,
            weightedEvalHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha hb f⟩ : K) =
          MvPowerSeries.restrictedEval₂ (RingHom.id K) (fun i ↦ (x i : K)) (fun _ ↦ le_rfl)
            (fun i ↦ Valued.integer.mem_iff.mp (x i).property) (toUnitClosedBall f).val := by
      rw [coe_powerBoundedSubringEquivInteger]
      change weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val = _
      rw [weightedEvalHom_eq_restrictedEval₂OfBound continuousAt_id (C := 1) (fun _ ↦ by simp)
        ha₁ hb, RingHom.restrictedEval₂OfBound_eq_restrictedEval₂ _ _ _ _ (fun _ ↦ le_rfl)]
      rfl
    have hres_lhs :
        eRes (IsLocalRing.residue (powerBoundedSubring K)
          ⟨weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val,
            weightedEvalHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha hb f⟩) =
          IsLocalRing.residue (Valued.integer K)
            ⟨MvPowerSeries.restrictedEval₂ (RingHom.id K) (fun i ↦ (x i : K)) (fun _ ↦ le_rfl)
                (fun i ↦ Valued.integer.mem_iff.mp (x i).property) (toUnitClosedBall f).val,
              TauCeti.MvPowerSeries.restrictedEval₂_mem_integer (RingHom.id K) (fun _ ↦ le_rfl) x
                (toUnitClosedBall f)⟩ := by
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      exact congrArg (IsLocalRing.residue (Valued.integer K)) (Subtype.ext hlhs_val)
    have hid_map : IsLocalRing.ResidueField.map ((RingHom.id K).integerRestrict (fun _ ↦ le_rfl)) =
        RingHom.id (IsLocalRing.ResidueField (Valued.integer K)) := by
      refine RingHom.ext fun q ↦ ?_
      obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective q
      rw [IsLocalRing.ResidueField.map_residue]
      exact congrArg (IsLocalRing.residue (Valued.integer K)) (Subtype.ext (by simp))
    rw [hres_lhs, TauCeti.MvPowerSeries.residue_restrictedEval₂, hid_map, MvPolynomial.eval₂_id,
      ← map_polydiscReduction_eq_restrictedReduction, MvPolynomial.eval_map]
    change _ = eRes.toRingHom ((polydiscReduction n K f).eval₂ (RingHom.id _) _)
    rw [MvPolynomial.hom_eval₂, RingHom.comp_id]
    refine congrArg (fun g ↦ MvPolynomial.eval₂ _ g _) (funext fun i ↦ ?_)
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue _) (Subtype.ext (by simp [eInt, x]))

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
