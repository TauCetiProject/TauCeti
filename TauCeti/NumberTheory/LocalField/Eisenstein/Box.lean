/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.PowerBasis
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Valuation balls in Eisenstein power-basis coordinates

For an Eisenstein generator `ξ` of a finite extension `L/K`, the normalized valuation of the
`i`-th power-basis term is congruent to `i` modulo the degree. Consequently, the coefficient
vectors whose power-basis linear combination lies in the valuation ball of radius `r` form a
box: the `i`-th coefficient belongs to the `ceil((r - i) / n)`-th power of the maximal ideal of
`O_K`. At radii divisible by `n`, this box is a cube.

These descriptions turn valuation-ball questions in a totally ramified extension into
coordinatewise ideal-membership questions over the base field. They are used in local change of
variables and root-counting arguments.

## Main results

* `TauCeti.Polynomial.le_addVal_sum_eisenstein_powerBasis_iff` identifies every valuation ball
  with its coordinate box.
* `TauCeti.Polynomial.natDegree_mul_le_addVal_sum_eisenstein_powerBasis_iff` gives the cube
  specialization at radii divisible by the degree.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §6, Proposition 17.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField
open scoped IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

namespace Polynomial

/-- At an Eisenstein generator, the power-basis coefficient vectors representing elements of a
valuation ball form the box whose `i`-th factor is the `ceil((r - i) / deg f)`-th power of the
base maximal ideal. -/
theorem le_addVal_sum_eisenstein_powerBasis_iff
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) (c : Fin f.natDegree → 𝒪[K]) (r : ℕ) :
    (r : ℕ∞) ≤ IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ξ ^ (i : ℕ)) ↔
      ∀ i : Fin f.natDegree, c i ∈ 𝓂[K] ^ ((r - (i : ℕ)) ⌈/⌉ f.natDegree) := by
  rw [addVal_sum_eisenstein_powerBasis f hf ξ hroot hgen c,
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen,
    le_iInf_iff]
  have hdeg : 0 < f.natDegree := by
    rw [← ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen]
    exact ramificationIndex_pos
  constructor
  · intro h i
    rw [IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
    cases hci : IsDiscreteValuationRing.addVal 𝒪[K] (c i) with
    | top => simp
    | coe v =>
        have hi := h i
        rw [hci, nsmul_eq_mul] at hi
        rw [ENat.natCast_le_natCast]
        rw [ceilDiv_le_iff_le_mul hdeg]
        have hri : r ≤ f.natDegree * v + (i : ℕ) := by
          exact_mod_cast hi
        omega
  · intro h i
    have hi := h i
    rw [IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at hi
    cases hci : IsDiscreteValuationRing.addVal 𝒪[K] (c i) with
    | top => simp [hdeg.ne']
    | coe v =>
        rw [hci, ENat.natCast_le_natCast] at hi
        simp only [nsmul_eq_mul, ← ENat.natCast_mul, ← ENat.natCast_add,
          ENat.natCast_le_natCast]
        have hsub : r - (i : ℕ) ≤ f.natDegree * v :=
          (ceilDiv_le_iff_le_mul hdeg).mp hi
        have hri : r ≤ f.natDegree * v + (i : ℕ) := by omega
        exact_mod_cast hri

/-- At a radius divisible by the degree, the power-basis coordinate box is the cube in which
every coefficient belongs to the same power of the base maximal ideal. -/
theorem natDegree_mul_le_addVal_sum_eisenstein_powerBasis_iff
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) (c : Fin f.natDegree → 𝒪[K]) (ρ : ℕ) :
    (f.natDegree * ρ : ℕ) ≤ IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ξ ^ (i : ℕ)) ↔
      ∀ i : Fin f.natDegree, c i ∈ 𝓂[K] ^ ρ := by
  rw [le_addVal_sum_eisenstein_powerBasis_iff f hf ξ hroot hgen c]
  have hdeg : 0 < f.natDegree := by
    rw [← ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen]
    exact ramificationIndex_pos
  apply forall_congr'
  intro i
  have hceil : (f.natDegree * ρ - (i : ℕ)) ⌈/⌉ f.natDegree = ρ := by
    cases ρ with
    | zero => simp
    | succ ρ =>
        apply le_antisymm
        · rw [ceilDiv_le_iff_le_mul hdeg]
          omega
        · have hlt : ρ < (f.natDegree * (ρ + 1) - (i : ℕ)) ⌈/⌉ f.natDegree := by
            rw [(gc_mul_ceilDiv hdeg).lt_iff_lt, Nat.lt_sub_iff_add_lt]
            nlinarith [i.isLt]
          omega
  simp only [hceil]

end Polynomial

end TauCeti
