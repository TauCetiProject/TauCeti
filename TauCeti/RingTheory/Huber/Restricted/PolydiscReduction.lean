/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.Restricted.UnitGaussValuation

/-!
# Residue reduction on the integral Tate algebra of a normed field

For an ultrametric normed field `K`, the maximal ideal `K°° = topologicallyNilpotentIdeal K` of the
power-bounded subring `K°` is open (`TauCeti.Huber.isOpen_topologicallyNilpotentIdeal`). Reducing
unit-bounded restricted series `f ∈ K°⟨T₁, …, Tₙ⟩` coefficientwise modulo `K°°` via
`Ideal.weightedSubringReduction` yields a surjective polynomial reduction homomorphism
`TauCeti.Huber.polydiscReduction n K : K°⟨T₁, …, Tₙ⟩ →+* (K° ⧸ K°°)[T₁, …, Tₙ]`.

A series reduces to zero exactly when every coefficient has norm strictly less than `1`, that is,
when `unitGaussValuation n K f.val < 1`; equivalently, its reduction is nonzero if and only if
`unitGaussValuation n K f.val = 1`.

## Main definitions

* `TauCeti.Huber.polydiscReduction`: coefficientwise reduction
  `K°⟨T₁, …, Tₙ⟩ →+* (K° ⧸ K°°)[T₁, …, Tₙ]`.

## Main results

* `TauCeti.Huber.polydiscReduction_def`, `TauCeti.Huber.coeff_polydiscReduction`,
  `TauCeti.Huber.polydiscReduction_surjective`: unfolding, coefficient computation, and
  surjectivity of residue reduction.
* `TauCeti.Huber.polydiscReduction_eq_zero_iff` and
  `TauCeti.Huber.polydiscReduction_ne_zero_iff`: vanishing of the reduced polynomial is
  `unitGaussValuation n K f.val < 1`, and nonvanishing is `unitGaussValuation n K f.val = 1`.
* `TauCeti.Huber.polydiscReduction_weightedPolynomialHom`,
  `TauCeti.Huber.polydiscReduction_weightedC`, and
  `TauCeti.Huber.polydiscReduction_weightedX`: `[simp]` behavior on polynomials, constants, and
  variables.
-/

public section

namespace TauCeti.Huber

open scoped NNReal

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **Coefficientwise reduction on `K°⟨T₁, …, Tₙ⟩`**, sending a unit-bounded restricted power
series to the polynomial over the canonical residue field `K° ⧸ K°°` obtained by reducing each
coefficient. -/
noncomputable def polydiscReduction (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) →+*
      MvPolynomial (Fin n) (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) :=
  Ideal.weightedSubringReduction (powerBoundedSubring K) (topologicallyNilpotentIdeal K)
    isOpen_topologicallyNilpotentIdeal

/-- Unfolding equation bridging `polydiscReduction` to `Ideal.weightedSubringReduction`. -/
theorem polydiscReduction_def :
    polydiscReduction n K =
      Ideal.weightedSubringReduction (powerBoundedSubring K) (topologicallyNilpotentIdeal K)
        isOpen_topologicallyNilpotentIdeal :=
  (rfl)

/-- Each coefficient of `polydiscReduction n K f` is the residue class of the corresponding
coefficient of `f`. -/
@[simp]
theorem coeff_polydiscReduction
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) (ν : Fin n →₀ ℕ) :
    (polydiscReduction n K f).coeff ν =
      Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
        ⟨MvPowerSeries.coeff ν ((f.val : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
            isWeightFamily_one_weight) : MvPowerSeries (Fin n) K),
          by simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
            mem_weightedNhd.mp (mem_weightedSubring.mp f.property) ν⟩ :=
  Ideal.coeff_weightedSubringReduction (powerBoundedSubring K) (topologicallyNilpotentIdeal K)
    isOpen_topologicallyNilpotentIdeal f ν

/-- A coefficient of `polydiscReduction n K f` vanishes if and only if the corresponding
coefficient of `f` has norm strictly less than `1`. -/
theorem coeff_polydiscReduction_eq_zero_iff
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) (ν : Fin n →₀ ℕ) :
    (polydiscReduction n K f).coeff ν = 0 ↔
      ‖MvPowerSeries.coeff ν ((f.val : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
          isWeightFamily_one_weight) : MvPowerSeries (Fin n) K)‖ < 1 := by
  rw [coeff_polydiscReduction, Ideal.Quotient.eq_zero_iff_mem, mem_topologicallyNilpotentIdeal,
    IsTopologicallyNilpotent, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]

/-- The reduction of a unit-bounded series vanishes if and only if its unit Gauss valuation is
strictly less than `1`. -/
theorem polydiscReduction_eq_zero_iff
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    polydiscReduction n K f = 0 ↔ unitGaussValuation n K f.val < 1 := by
  rw [MvPolynomial.ext_iff, unitGaussValuation_def, weightedGaussValuation_lt_iff]
  refine forall_congr' fun ν ↦ ?_
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
    coeff_polydiscReduction_eq_zero_iff, NormedField.valuation_apply, ← NNReal.coe_lt_coe,
    coe_nnNorm, NNReal.coe_one]

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

/-- Every polynomial over the residue field `K° ⧸ K°°` lifts to `K°⟨T₁, …, Tₙ⟩`. -/
theorem polydiscReduction_surjective :
    Function.Surjective (polydiscReduction (n := n) (K := K)) :=
  Ideal.weightedSubringReduction_surjective (powerBoundedSubring K) (topologicallyNilpotentIdeal K)
    isOpen_topologicallyNilpotentIdeal

/-- On embedded polynomials with coefficients in `K°`, `polydiscReduction` reduces coefficients
modulo `K°°`. -/
@[simp]
theorem polydiscReduction_weightedPolynomialHom
    (p : MvPolynomial (Fin n) (powerBoundedSubring K)) :
    polydiscReduction n K
        ⟨weightedPolynomialHom (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
            (MvPolynomial.map (powerBoundedSubring K).subtype p),
          weightedPolynomialHom_map_mem_weightedSubring_one_weight (powerBoundedSubring K) p⟩ =
      MvPolynomial.map (Ideal.Quotient.mk (topologicallyNilpotentIdeal K)) p :=
  Ideal.weightedSubringReduction_weightedPolynomialHom (powerBoundedSubring K)
    (topologicallyNilpotentIdeal K) isOpen_topologicallyNilpotentIdeal p

/-- `polydiscReduction` sends constant series in `K°` to constant polynomials over `K° ⧸ K°°`. -/
@[simp]
theorem polydiscReduction_weightedC (a : powerBoundedSubring K) :
    polydiscReduction n K
        ⟨weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight (a : K),
          (weightedC_mem_weightedSubring isWeightFamily_one_weight).mpr a.property⟩ =
      MvPolynomial.C (Ideal.Quotient.mk (topologicallyNilpotentIdeal K) a) :=
  Ideal.weightedSubringReduction_weightedC (powerBoundedSubring K)
    (topologicallyNilpotentIdeal K) isOpen_topologicallyNilpotentIdeal a

/-- `polydiscReduction` preserves the coordinate variables. -/
@[simp]
theorem polydiscReduction_weightedX (i : Fin n) :
    polydiscReduction n K
        ⟨weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i,
          weightedX_mem_weightedSubring_one_weight (powerBoundedSubring K) i⟩ =
      MvPolynomial.X i :=
  Ideal.weightedSubringReduction_weightedX (powerBoundedSubring K)
    (topologicallyNilpotentIdeal K) isOpen_topologicallyNilpotentIdeal i

end TauCeti.Huber
