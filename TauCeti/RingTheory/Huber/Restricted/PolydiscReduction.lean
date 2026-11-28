/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.RingTheory.Huber.Restricted.Gauss.Valuation
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Subring
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

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

Under the unit-radius Gauss comparison, `K°⟨T₁, …, Tₙ⟩` is canonically isomorphic to the Gauss unit
ball `K⟨T₁, …, Tₙ⟩°` (`TauCeti.Huber.weightedSubringEquivUnitClosedBall`), and over a nontrivially
normed field `polydiscReduction` agrees with `TauCeti.MvPowerSeries.restrictedReduction` across this
comparison (`TauCeti.Huber.polydiscReduction_eq_restrictedReduction`).

A series reduces to zero exactly when every coefficient has norm strictly less than `1`, that is,
when `unitGaussValuation n K f.val < 1`; equivalently, its reduction is nonzero if and only if
`unitGaussValuation n K f.val = 1`. Over a complete field `K`, evaluating `f ∈ K°⟨T₁, …, Tₙ⟩` at
an integral tuple `a : Fin n → K°` gives a ring homomorphism
`TauCeti.Huber.weightedSubringEvalHom a : K°⟨T₁, …, Tₙ⟩ →+* K°` agreeing with `weightedEvalHom`
after coercion to `K` (`TauCeti.Huber.coe_weightedSubringEvalHom`) and forming a commuting square
with `polydiscReduction` and residue reduction
(`TauCeti.Huber.residue_comp_weightedSubringEvalHom`).

## Main definitions

* `TauCeti.Huber.polydiscReduction`: coefficientwise reduction
  `K°⟨T₁, …, Tₙ⟩ →+* 𝓀[K][T₁, …, Tₙ]`.
* `TauCeti.Huber.weightedSubringEquivUnitClosedBall`: canonical ring equivalence
  `K°⟨T₁, …, Tₙ⟩ ≃+* K⟨T₁, …, Tₙ⟩°`.
* `TauCeti.Huber.weightedSubringEvalHom`: evaluation `K°⟨T₁, …, Tₙ⟩ →+* K°` at an integral tuple
  `a : Fin n → K°`.

## Main results

* `TauCeti.Huber.polydiscReduction_def`: unfolding to `Ideal.restrictedReduction`,
  `weightedRestrictedSubringEquivWeightedSubring`, and `canonicalReductionRingEquivResidueField`.
* `TauCeti.Huber.coeff_polydiscReduction`, `TauCeti.Huber.polydiscReduction_weightedPolynomialHom`,
  `TauCeti.Huber.polydiscReduction_weightedC`, `TauCeti.Huber.polydiscReduction_weightedX`, and
  `TauCeti.Huber.polydiscReduction_surjective`: coefficient, generator, and surjectivity API.
* `TauCeti.Huber.polydiscReduction_eq_restrictedReduction` and
  `TauCeti.Huber.restrictedReduction_eq_polydiscReduction`: compatibility of `polydiscReduction`
  with `TauCeti.MvPowerSeries.restrictedReduction`.
* `TauCeti.Huber.polydiscReduction_eq_zero_iff` and
  `TauCeti.Huber.polydiscReduction_ne_zero_iff`: vanishing of the reduced polynomial is
  `unitGaussValuation n K f.val < 1`, and nonvanishing is `unitGaussValuation n K f.val = 1`.
* `TauCeti.Huber.coe_weightedSubringEvalHom`,
  `TauCeti.Huber.residue_comp_weightedSubringEvalHom`, and
  `TauCeti.Huber.residue_weightedSubringEvalHom`: coercion to `weightedEvalHom` and commuting
  square with residue reduction.
* `TauCeti.Huber.norm_weightedSubringEvalHom_eq_one_iff_eval_polydiscReduction_ne_zero`:
  `‖(weightedSubringEvalHom a f : K)‖ = 1` iff the reduced polynomial does not vanish at `ā`.
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

/-- **Unit-ball comparison for integral series.** The Gauss comparison restricts to a ring
equivalence between the integral subring `K°⟨T₁, …, Tₙ⟩` and the Gauss unit ball
`K⟨T₁, …, Tₙ⟩°`. -/
noncomputable def weightedSubringEquivUnitClosedBall :
    weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) ≃+*
      Subring.unitClosedBall (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
  RingEquiv.ofRingHom
    ((restrictedMvPowerSeriesGaussEquiv.toRingHom.comp
        (weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
          (powerBoundedSubring K)).subtype).codRestrict _ fun f ↦
      TauCeti.MvPowerSeries.mem_unitClosedBall_iff.mpr fun t ↦ by
        simpa [weightMul_one_weight, mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one] using
          mem_weightedNhd.mp (mem_weightedSubring.mp f.property) t)
    ((restrictedMvPowerSeriesGaussEquiv.symm.toRingHom.comp
        (Subring.unitClosedBall (MvPowerSeries.IsRestricted.subring (R := K)
          (fun _ : Fin n ↦ 1))).subtype).codRestrict _ fun g ↦
      mem_weightedSubring.mpr <| mem_weightedNhd.mpr fun t ↦ by
        simpa [weightMul_one_weight, mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one] using
          TauCeti.MvPowerSeries.mem_unitClosedBall_iff.mp g.property t)
    (RingHom.ext fun g ↦ Subtype.ext (restrictedMvPowerSeriesGaussEquiv.apply_symm_apply g.val))
    (RingHom.ext fun f ↦ Subtype.ext (restrictedMvPowerSeriesGaussEquiv.symm_apply_apply f.val))

/-- `weightedSubringEquivUnitClosedBall` acts on the underlying restricted series via
`restrictedMvPowerSeriesGaussEquiv`. -/
@[simp]
theorem coe_weightedSubringEquivUnitClosedBall
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    (weightedSubringEquivUnitClosedBall f :
        MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) =
      restrictedMvPowerSeriesGaussEquiv f.val :=
  (rfl)

/-- `weightedSubringEquivUnitClosedBall.symm` acts on the underlying restricted series via
`restrictedMvPowerSeriesGaussEquiv.symm`. -/
@[simp]
theorem coe_weightedSubringEquivUnitClosedBall_symm
    (g : Subring.unitClosedBall (MvPowerSeries.IsRestricted.subring (R := K)
      (fun _ : Fin n ↦ 1))) :
    ((weightedSubringEquivUnitClosedBall.symm g :
        weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
          (powerBoundedSubring K)) :
        weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) =
      restrictedMvPowerSeriesGaussEquiv.symm g.val :=
  (rfl)

end Basic

/-- Compatibility of `polydiscReduction` with `TauCeti.MvPowerSeries.restrictedReduction` under
the integral-series/unit-ball comparison `weightedSubringEquivUnitClosedBall`. -/
theorem polydiscReduction_eq_restrictedReduction
    {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    polydiscReduction n K f =
      TauCeti.MvPowerSeries.restrictedReduction (weightedSubringEquivUnitClosedBall f) := by
  refine MvPolynomial.ext _ _ fun ν ↦ ?_
  rw [coeff_polydiscReduction, TauCeti.MvPowerSeries.coeff_restrictedReduction]
  refine congrArg (IsLocalRing.residue 𝒪[K]) (Subtype.ext ?_)
  simp

/-- Compatibility of `TauCeti.MvPowerSeries.restrictedReduction` with `polydiscReduction` under
`weightedSubringEquivUnitClosedBall.symm`. -/
theorem restrictedReduction_eq_polydiscReduction
    {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (g : Subring.unitClosedBall (MvPowerSeries.IsRestricted.subring (R := K)
      (fun _ : Fin n ↦ 1))) :
    TauCeti.MvPowerSeries.restrictedReduction g =
      polydiscReduction n K (weightedSubringEquivUnitClosedBall.symm g) := by
  rw [polydiscReduction_eq_restrictedReduction, RingEquiv.apply_symm_apply]

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
      coe_weightedSubringEquivUnitClosedBall, coe_restrictedMvPowerSeriesGaussEquiv,
      ← coe_unitGaussValuation, ← NNReal.coe_one]
    exact NNReal.coe_lt_coe

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

private lemma isWeightBounded_powerBoundedSubring (a : Fin n → powerBoundedSubring K) :
    IsWeightBounded (RingHom.id (powerBoundedSubring K))
      (fun _ : Fin n ↦ ({1} : Set (powerBoundedSubring K))) a :=
  (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun _ ↦
    isPowerBounded_iff.mpr
      ((Subring.isBounded_preimage_subtype (powerBoundedSubring K)
        (IsUniform.isBounded_powerBoundedSubring (A := K))).subset fun _ _ ↦ SetLike.coe_mem _)

variable [CompleteSpace K]

/-- **Evaluation of integral series at integral tuples** as a ring homomorphism
`K°⟨T₁, …, Tₙ⟩ →+* K°`. -/
noncomputable def weightedSubringEvalHom (a : Fin n → powerBoundedSubring K) :
    weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) →+*
      powerBoundedSubring K :=
  (weightedEvalHom isWeightFamily_one_weight continuousAt_id
      (isWeightBounded_powerBoundedSubring a)).comp
    (weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm.toRingHom

/-- Evaluating an integral series `f ∈ K°⟨T₁, …, Tₙ⟩` at an integral tuple `a : Fin n → K°`
via `weightedSubringEvalHom` agrees after coercion to `K` with `weightedEvalHom` on `f.val`. -/
theorem coe_weightedSubringEvalHom (a : Fin n → powerBoundedSubring K)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    ((weightedSubringEvalHom a f : powerBoundedSubring K) : K) =
      weightedEvalHom isWeightFamily_one_weight continuousAt_id
        ((isWeightBounded_one_weight_iff_forall_isPowerBounded (RingHom.id K) _).mpr fun i ↦
          mem_powerBoundedSubring.mp (a i).property)
        f.val := by
  have hb : IsWeightBounded (RingHom.id K) (fun _ : Fin n ↦ ({1} : Set K))
      (fun i ↦ (a i : K)) :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded (RingHom.id K) _).mpr fun i ↦
      mem_powerBoundedSubring.mp (a i).property
  have hcont : Continuous (powerBoundedSubring K).subtype := continuous_subtypeVal
  let toSub := weightedMap (k := n) (φ := (powerBoundedSubring K).subtype) hcont
    isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp)
  have hExt := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := (powerBoundedSubring K).subtype.comp (weightedEvalHom isWeightFamily_one_weight
      continuousAt_id (isWeightBounded_powerBoundedSubring a)))
    (g := (weightedEvalHom isWeightFamily_one_weight continuousAt_id hb).comp toSub)
    (hcont.comp (continuous_weightedEvalHom _ _ _))
    ((continuous_weightedEvalHom _ _ _).comp (continuous_weightedMap _ _ _ _))
    (fun c ↦ by
      dsimp only [toSub, RingHom.comp_apply]
      rw [weightedEvalHom_weightedC, weightedMap_weightedC, weightedEvalHom_weightedC]
      simp)
    (fun i ↦ by
      dsimp only [toSub, RingHom.comp_apply]
      rw [weightedEvalHom_weightedX, weightedMap_weightedX, weightedEvalHom_weightedX]
      simp)
  have htoSub : ∀ g, toSub g = (weightedRestrictedSubringEquivWeightedSubring
      (powerBoundedSubring K) g).val := fun g ↦ Subtype.ext (by
    dsimp only [toSub]
    rw [coe_weightedMap, coe_weightedRestrictedSubringEquivWeightedSubring])
  have hval : toSub ((weightedRestrictedSubringEquivWeightedSubring
      (powerBoundedSubring K)).symm f) = f.val := by
    rw [htoSub, (weightedRestrictedSubringEquivWeightedSubring _).apply_symm_apply]
  simpa only [weightedSubringEvalHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Subring.coe_subtype, hval]
    using RingHom.congr_fun hExt
      ((weightedRestrictedSubringEquivWeightedSubring (powerBoundedSubring K)).symm f)

/-- `weightedSubringEvalHom a` fixes integral constants. -/
@[simp]
theorem weightedSubringEvalHom_weightedC (a : Fin n → powerBoundedSubring K)
    (c : powerBoundedSubring K) :
    weightedSubringEvalHom a
        ⟨weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight (c : K),
          (weightedC_mem_weightedSubring isWeightFamily_one_weight).mpr c.property⟩ = c := by
  simp [weightedSubringEvalHom]

/-- `weightedSubringEvalHom a` sends the coordinate variable `Tᵢ` to `a i`. -/
@[simp]
theorem weightedSubringEvalHom_weightedX (a : Fin n → powerBoundedSubring K) (i : Fin n) :
    weightedSubringEvalHom a
        ⟨weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i,
          weightedX_mem_weightedSubring_one_weight (powerBoundedSubring K) i⟩ = a i := by
  simp [weightedSubringEvalHom]

/-- **Reduction commutes with evaluation at integral tuples.** For `a : Fin n → K°`, the residue
homomorphism `K° →+* 𝓀[K]` composed with `weightedSubringEvalHom a` equals polynomial evaluation
at `ā` composed with `polydiscReduction n K`. -/
theorem residue_comp_weightedSubringEvalHom (a : Fin n → powerBoundedSubring K) :
    ((IsLocalRing.residue 𝒪[K]).comp powerBoundedSubringEquivInteger.toRingHom).comp
        (weightedSubringEvalHom a) =
      (MvPolynomial.eval fun i ↦
          IsLocalRing.residue 𝒪[K] (powerBoundedSubringEquivInteger (a i))).comp
        (polydiscReduction n K) := by
  ext f
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    weightedSubringEvalHom]
  rw [← canonicalReductionRingEquivResidueField_mk,
    mk_weightedEvalHom_eq_eval₂_restrictedReduction continuousAt_id
      (isWeightBounded_powerBoundedSubring a) isOpen_topologicallyNilpotentIdeal
      isOpen_topologicallyNilpotentIdeal (by simp)]
  have hid : Ideal.quotientMap (topologicallyNilpotentIdeal K)
        (RingHom.id (powerBoundedSubring K)) (by simp) =
      RingHom.id (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) :=
    RingHom.ext fun q ↦ by obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q; rfl
  rw [hid, ← RingEquiv.coe_toRingHom, MvPolynomial.hom_eval₂, RingHom.comp_id,
    ← MvPolynomial.eval_map]
  simp [polydiscReduction_def]

/-- Pointwise form of `residue_comp_weightedSubringEvalHom`: for `f ∈ K°⟨T₁, …, Tₙ⟩` and
`a : Fin n → K°`, the residue of `weightedSubringEvalHom a f` equals the evaluation of
`polydiscReduction n K f` at `ā`. -/
theorem residue_weightedSubringEvalHom (a : Fin n → powerBoundedSubring K)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    IsLocalRing.residue 𝒪[K] (powerBoundedSubringEquivInteger (weightedSubringEvalHom a f)) =
      MvPolynomial.eval
        (fun i ↦ IsLocalRing.residue 𝒪[K] (powerBoundedSubringEquivInteger (a i)))
        (polydiscReduction n K f) :=
  RingHom.congr_fun (residue_comp_weightedSubringEvalHom a) f

/-- A unit-bounded series `f ∈ K°⟨T₁, …, Tₙ⟩` evaluates to an element of norm `1` at an integral
tuple `a : Fin n → K°` if and only if its reduction does not vanish at the residue tuple `ā`. -/
theorem norm_weightedSubringEvalHom_eq_one_iff_eval_polydiscReduction_ne_zero
    (a : Fin n → powerBoundedSubring K)
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    ‖(weightedSubringEvalHom a f : K)‖ = 1 ↔
      MvPolynomial.eval
        (fun i ↦ IsLocalRing.residue 𝒪[K] (powerBoundedSubringEquivInteger (a i)))
        (polydiscReduction n K f) ≠ 0 := by
  let y := weightedSubringEvalHom a f
  have hle : ‖(y : K)‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp y.property)
  have hres :
      IsLocalRing.residue 𝒪[K] (powerBoundedSubringEquivInteger y) =
        canonicalReductionRingEquivResidueField (Ideal.Quotient.mk _ y) :=
    (canonicalReductionRingEquivResidueField_mk y).symm
  rw [← residue_weightedSubringEvalHom a f, Ne, hres,
    map_eq_zero_iff _ canonicalReductionRingEquivResidueField.injective,
    Ideal.Quotient.eq_zero_iff_mem, mem_topologicallyNilpotentIdeal,
    IsTopologicallyNilpotent, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm hle h⟩

end EvalReduction

end TauCeti.Huber
