/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.Restricted.UnitGaussValuation
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Subring

import TauCeti.RingTheory.Huber.Restricted.Comparison
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

/-!
# Residue reduction on the integral Tate algebra of a normed field

For an ultrametric normed field `K`, the power-bounded subring `K°` is a local ring whose maximal
ideal `K°° = topologicallyNilpotentIdeal K` is open
(`TauCeti.Huber.isOpen_topologicallyNilpotentIdeal`), with canonical residue-field isomorphism
`K° ⧸ K°° ≃+* 𝓀[K]` (`TauCeti.Huber.canonicalReductionRingEquivResidueField`). Reducing unit-bounded
restricted series `f ∈ K°⟨T₁, …, Tₙ⟩` coefficientwise modulo `K°°` via `Ideal.restrictedReduction`
across `TauCeti.Huber.weightedRestrictedSubringEquivWeightedSubring` and transporting along
`canonicalReductionRingEquivResidueField` yields the polynomial reduction homomorphism
`TauCeti.Huber.polydiscReduction n K : K°⟨T₁, …, Tₙ⟩ →+* 𝓀[K][T₁, …, Tₙ]`.

A series reduces to zero exactly when every coefficient has norm strictly less than `1`, that is,
when `unitGaussValuation n K f.val < 1`; equivalently, its reduction is nonzero if and only if
`unitGaussValuation n K f.val = 1`. Over a complete field `K`, evaluating `f ∈ K°⟨T₁, …, Tₙ⟩` at
a power-bounded tuple `a ∈ (K°)ⁿ` factors through `K°⟨T₁, …, Tₙ⟩` via
`TauCeti.Huber.weightedRestrictedSubringEquivWeightedSubring` and therefore lands in `K°` and
commutes with residue reduction by `TauCeti.Huber.mk_weightedEvalHom_eq_eval₂_restrictedReduction`.

## Main definitions

* `TauCeti.Huber.polydiscReduction`: coefficientwise reduction
  `K°⟨T₁, …, Tₙ⟩ →+* 𝓀[K][T₁, …, Tₙ]`.

## Main results

* `TauCeti.Huber.polydiscReduction_def`: unfolding to `Ideal.restrictedReduction`,
  `weightedRestrictedSubringEquivWeightedSubring`, and `canonicalReductionRingEquivResidueField`.
* `TauCeti.Huber.coeff_polydiscReduction`, `TauCeti.Huber.polydiscReduction_weightedPolynomialHom`,
  `TauCeti.Huber.polydiscReduction_weightedC`, `TauCeti.Huber.polydiscReduction_weightedX`, and
  `TauCeti.Huber.polydiscReduction_surjective`: coefficient, generator, and surjectivity API.
* `TauCeti.Huber.polydiscReduction_eq_zero_iff` and
  `TauCeti.Huber.polydiscReduction_ne_zero_iff`: vanishing of the reduced polynomial is
  `unitGaussValuation n K f.val < 1`, and nonvanishing is `unitGaussValuation n K f.val = 1`.
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
series to the polynomial over the residue field `𝓀[K]` obtained by reducing each coefficient. -/
noncomputable def polydiscReduction (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) →+*
      MvPolynomial (Fin n) 𝓀[K] :=
  (MvPolynomial.map (canonicalReductionRingEquivResidueField (K := K)).toRingHom).comp
    ((Ideal.restrictedReduction (topologicallyNilpotentIdeal K)
        isOpen_topologicallyNilpotentIdeal).comp
      (weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm.toRingHom)

/-- Unfolding equation bridging `polydiscReduction` to `Ideal.restrictedReduction` and
`canonicalReductionRingEquivResidueField`. -/
theorem polydiscReduction_def :
    polydiscReduction n K =
      (MvPolynomial.map (canonicalReductionRingEquivResidueField (K := K)).toRingHom).comp
        ((Ideal.restrictedReduction (topologicallyNilpotentIdeal K)
            isOpen_topologicallyNilpotentIdeal).comp
          (weightedRestrictedSubringEquivWeightedSubring
            (powerBoundedSubring K)).symm.toRingHom) :=
  (rfl)

/-- Each coefficient of `polydiscReduction n K f` is the residue in `𝓀[K]` of the corresponding
coefficient of `f`. -/
@[simp]
theorem coeff_polydiscReduction
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) (ν : Fin n →₀ ℕ) :
    (polydiscReduction n K f).coeff ν =
      IsLocalRing.residue 𝒪[K]
        ⟨MvPowerSeries.coeff ν ((f.val : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
            isWeightFamily_one_weight) : MvPowerSeries (Fin n) K),
          (powerBoundedSubring_eq_integer (K := K)).le (by
            simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
              mem_weightedNhd.mp (mem_weightedSubring.mp f.property) ν)⟩ := by
  rw [polydiscReduction_def, RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.coeff_map,
    Ideal.coeff_restrictedReduction, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    canonicalReductionRingEquivResidueField_mk]
  refine congrArg (IsLocalRing.residue 𝒪[K]) (Subtype.ext ?_)
  simp [coeff_weightedRestrictedSubringEquivWeightedSubring_symm]

/-- On embedded polynomials with coefficients in `K°`, `polydiscReduction` reduces coefficients to
`𝓀[K]`. -/
@[simp]
theorem polydiscReduction_weightedPolynomialHom
    (p : MvPolynomial (Fin n) (powerBoundedSubring K)) :
    polydiscReduction n K
        ⟨weightedPolynomialHom (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
            (MvPolynomial.map (powerBoundedSubring K).subtype p),
          weightedPolynomialHom_map_mem_weightedSubring_one_weight (powerBoundedSubring K) p⟩ =
      MvPolynomial.map
        ((IsLocalRing.residue 𝒪[K]).comp powerBoundedSubringEquivInteger.toRingHom) p := by
  rw [polydiscReduction_def, RingHom.comp_apply, RingHom.comp_apply]
  dsimp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [weightedRestrictedSubringEquivWeightedSubring_symm_weightedPolynomialHom,
    Ideal.restrictedReduction_weightedPolynomialHom, MvPolynomial.map_map]
  exact congrArg (MvPolynomial.map · p)
    (RingHom.ext fun x ↦ canonicalReductionRingEquivResidueField_mk x)

/-- `polydiscReduction` sends constant series in `K°` to constant polynomials over `𝓀[K]`. -/
@[simp]
theorem polydiscReduction_weightedC (a : powerBoundedSubring K) :
    polydiscReduction n K
        ⟨weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight (a : K),
          (weightedC_mem_weightedSubring isWeightFamily_one_weight).mpr a.property⟩ =
      MvPolynomial.C (IsLocalRing.residue 𝒪[K] (powerBoundedSubringEquivInteger a)) := by
  simp [polydiscReduction_def]

/-- `polydiscReduction` preserves the coordinate variables. -/
@[simp]
theorem polydiscReduction_weightedX (i : Fin n) :
    polydiscReduction n K
        ⟨weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i,
          weightedX_mem_weightedSubring_one_weight (powerBoundedSubring K) i⟩ =
      MvPolynomial.X i := by
  simp [polydiscReduction_def]

/-- Every polynomial over `𝓀[K]` lifts to `K°⟨T₁, …, Tₙ⟩`. -/
theorem polydiscReduction_surjective :
    Function.Surjective (polydiscReduction (n := n) (K := K)) :=
  (MvPolynomial.map_surjective _ canonicalReductionRingEquivResidueField.surjective).comp
    ((Ideal.restrictedReduction_surjective (topologicallyNilpotentIdeal K)
        isOpen_topologicallyNilpotentIdeal).comp
      (weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm.surjective)

private noncomputable def toUnitClosedBall
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    Subring.unitClosedBall (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
  ⟨restrictedMvPowerSeriesGaussEquiv f.val,
    TauCeti.MvPowerSeries.mem_unitClosedBall_iff.mpr fun t ↦ by
      simpa [weightMul_one_weight, mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one] using
        mem_weightedNhd.mp (mem_weightedSubring.mp f.property) t⟩

end Basic

private theorem polydiscReduction_eq_restrictedReduction
    {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    polydiscReduction n K f =
      TauCeti.MvPowerSeries.restrictedReduction (toUnitClosedBall f) := by
  refine MvPolynomial.ext _ _ fun ν ↦ ?_
  rw [coeff_polydiscReduction, TauCeti.MvPowerSeries.coeff_restrictedReduction]
  refine congrArg (IsLocalRing.residue 𝒪[K]) (Subtype.ext ?_)
  simp [toUnitClosedBall]

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
    rw [polydiscReduction_def, RingHom.comp_apply, RingHom.comp_apply,
      (MvPolynomial.map_injective _ canonicalReductionRingEquivResidueField.injective).eq_iff'
        (map_zero _),
      Ideal.restrictedReduction_eq_zero_iff, unitGaussValuation_def,
      weightedGaussValuation_lt_iff]
    refine forall_congr' fun ν ↦ ?_
    rw [mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
      tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    dsimp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [coeff_weightedRestrictedSubringEquivWeightedSubring_symm, NormedField.valuation_apply,
      ← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one, hlt_iff]
  · rw [polydiscReduction_eq_restrictedReduction,
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

private lemma isWeightBounded_powerBoundedSubring
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)) :
    IsWeightBounded (RingHom.id (powerBoundedSubring K))
      (fun _ : Fin n ↦ ({1} : Set (powerBoundedSubring K)))
      (fun i ↦ ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩) :=
  (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun _ ↦
    isPowerBounded_iff.mpr
      ((Subring.isBounded_preimage_subtype (powerBoundedSubring K)
        (IsUniform.isBounded_powerBoundedSubring (A := K))).subset fun _ _ ↦ SetLike.coe_mem _)

variable [CompleteSpace K]

private theorem coe_weightedEvalHom_symm
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (hb : IsWeightBounded (RingHom.id K) (fun _ : Fin n ↦ ({1} : Set K)) a)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    ((weightedEvalHom isWeightFamily_one_weight continuousAt_id
        (isWeightBounded_powerBoundedSubring a ha)
        ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f) :
        powerBoundedSubring K) : K) =
      weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val := by
  have hcont : Continuous (powerBoundedSubring K).subtype := continuous_subtypeVal
  let toSub := weightedMap (k := n) (φ := (powerBoundedSubring K).subtype) hcont
    isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp)
  have hExt := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := (powerBoundedSubring K).subtype.comp (weightedEvalHom isWeightFamily_one_weight
      continuousAt_id (isWeightBounded_powerBoundedSubring a ha)))
    (g := (weightedEvalHom isWeightFamily_one_weight continuousAt_id hb).comp toSub)
    (hcont.comp (continuous_weightedEvalHom _ _ _))
    ((continuous_weightedEvalHom _ _ _).comp (continuous_weightedMap _ _ _ _))
    (fun c ↦ by
      dsimp only [toSub, RingHom.comp_apply]
      rw [weightedEvalHom_weightedC, weightedMap_weightedC, weightedEvalHom_weightedC]
      rfl)
    (fun i ↦ by
      dsimp only [toSub, RingHom.comp_apply]
      rw [weightedEvalHom_weightedX, weightedMap_weightedX, weightedEvalHom_weightedX]
      rfl)
  have htoSub : ∀ g, toSub g = (weightedRestrictedSubringEquivWeightedSubring
      (powerBoundedSubring K) g).val := fun g ↦ Subtype.ext (by
    dsimp only [toSub]
    rw [coe_weightedMap, coe_weightedRestrictedSubringEquivWeightedSubring])
  have hval : toSub ((weightedRestrictedSubringEquivWeightedSubring
      (powerBoundedSubring K)).symm f) = f.val := by
    rw [htoSub, (weightedRestrictedSubringEquivWeightedSubring _).apply_symm_apply]
  simpa only [RingHom.comp_apply, Subring.coe_subtype, hval]
    using RingHom.congr_fun hExt
      ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f)

/-- **Reduction commutes with evaluation at power-bounded tuples.** For `f ∈ K°⟨T₁, …, Tₙ⟩` and
`a ∈ (K°)ⁿ`, the residue of `f(a)` in `𝓀[K]` equals the value of `polydiscReduction n K f` at the
residue tuple `ā`. -/
theorem residue_weightedEvalHom_eq_eval_polydiscReduction
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (hb : IsWeightBounded (RingHom.id K) (fun _ : Fin n ↦ ({1} : Set K)) a)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K))
    (hf : weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val ∈ 𝒪[K]) :
    IsLocalRing.residue 𝒪[K]
        ⟨weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val, hf⟩ =
      MvPolynomial.eval
        (fun i ↦ IsLocalRing.residue 𝒪[K]
          ⟨a i, (powerBoundedSubring_eq_integer (K := K)).le
            (mem_powerBoundedSubring.mpr (ha i))⟩)
        (polydiscReduction n K f) := by
  let g := (weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f
  have hsub :
      (⟨weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val,
          (powerBoundedSubring_eq_integer (K := K)).ge hf⟩ :
          powerBoundedSubring K) =
        weightedEvalHom isWeightFamily_one_weight continuousAt_id
          (isWeightBounded_powerBoundedSubring a ha) g :=
    Subtype.ext (coe_weightedEvalHom_symm a ha hb f).symm
  have hres_lhs :
      (⟨weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val, hf⟩ : 𝒪[K]) =
        powerBoundedSubringEquivInteger
          (weightedEvalHom isWeightFamily_one_weight continuousAt_id
            (isWeightBounded_powerBoundedSubring a ha) g) :=
    Subtype.ext (by rw [coe_powerBoundedSubringEquivInteger, ← hsub])
  rw [hres_lhs, ← canonicalReductionRingEquivResidueField_mk,
    mk_weightedEvalHom_eq_eval₂_restrictedReduction continuousAt_id
      (isWeightBounded_powerBoundedSubring a ha) isOpen_topologicallyNilpotentIdeal
      isOpen_topologicallyNilpotentIdeal (by simp) g]
  have hid : Ideal.quotientMap (topologicallyNilpotentIdeal K)
        (RingHom.id (powerBoundedSubring K)) (by simp) =
      RingHom.id (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) :=
    RingHom.ext fun q ↦ by obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q; rfl
  rw [hid, ← RingEquiv.coe_toRingHom, MvPolynomial.hom_eval₂, RingHom.comp_id,
    ← MvPolynomial.eval_map]
  simp only [polydiscReduction_def, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, canonicalReductionRingEquivResidueField_mk, g]
  refine congrArg (MvPolynomial.eval · _) (funext fun i ↦ congrArg (IsLocalRing.residue 𝒪[K]) ?_)
  exact Subtype.ext (coe_powerBoundedSubringEquivInteger _)

/-- A unit-bounded series `f ∈ K°⟨T₁, …, Tₙ⟩` evaluates to an element of norm `1` at `a ∈ (K°)ⁿ`
if and only if its reduction does not vanish at the residue tuple `ā`. -/
theorem norm_weightedEvalHom_eq_one_iff_eval_polydiscReduction_ne_zero
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (hb : IsWeightBounded (RingHom.id K) (fun _ : Fin n ↦ ({1} : Set K)) a)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    ‖weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val‖ = 1 ↔
      MvPolynomial.eval
        (fun i ↦ IsLocalRing.residue 𝒪[K]
          ⟨a i, (powerBoundedSubring_eq_integer (K := K)).le
            (mem_powerBoundedSubring.mpr (ha i))⟩)
        (polydiscReduction n K f) ≠ 0 := by
  let y : powerBoundedSubring K :=
    ⟨weightedEvalHom isWeightFamily_one_weight continuousAt_id hb f.val,
      coe_weightedEvalHom_symm a ha hb f ▸ SetLike.coe_mem _⟩
  have hle : ‖(y : K)‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp y.property)
  have hy : (⟨(y : K), (powerBoundedSubring_eq_integer (K := K)).le y.property⟩ : 𝒪[K]) =
      powerBoundedSubringEquivInteger y :=
    Subtype.ext (coe_powerBoundedSubringEquivInteger y).symm
  have hres :
      IsLocalRing.residue 𝒪[K]
          ⟨(y : K), (powerBoundedSubring_eq_integer (K := K)).le y.property⟩ =
        canonicalReductionRingEquivResidueField (Ideal.Quotient.mk _ y) :=
    (congrArg (IsLocalRing.residue 𝒪[K]) hy).trans
      (canonicalReductionRingEquivResidueField_mk y).symm
  rw [← residue_weightedEvalHom_eq_eval_polydiscReduction a ha hb f
      ((powerBoundedSubring_eq_integer (K := K)).le y.property),
    Ne, hres, map_eq_zero_iff _ canonicalReductionRingEquivResidueField.injective,
    Ideal.Quotient.eq_zero_iff_mem, mem_topologicallyNilpotentIdeal,
    IsTopologicallyNilpotent, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm hle h⟩

end EvalReduction

end TauCeti.Huber
