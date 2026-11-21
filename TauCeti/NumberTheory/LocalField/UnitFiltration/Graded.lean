/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import TauCeti.RingTheory.DiscreteValuationRing.UnitFiltration

/-!
# Positive graded pieces of the unit filtration

For a nonarchimedean local field `K`, each positive successive quotient `U(K,n+1) / U(K,n+2)`
of the unit filtration is identified, via `TauCeti.unitFiltrationGradedEquivInteger` and the
general discrete-valuation-ring isomorphism
`TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField`, with the additive
group of the residue field `𝓀[K]`. This file records the resulting cardinalities, relative
indices, powering congruence, and strictness of the unit filtration.

## Main results

* `TauCeti.natCard_unitFiltrationGraded_succ` and
  `TauCeti.relIndex_unitFiltration_succ_succ`: the positive graded pieces and relative indices
  have cardinality `#𝓀[K]`.
* `TauCeti.unitFiltration_isFiniteRelIndex_zero`: every step of the unit filtration has finite
  index in `U(K,0) = 𝒪[K]ˣ`; precisely, `TauCeti.relIndex_unitFiltration_succ_zero`:
  `[U(K,0) : U(K,n+1)] = (#𝓀[K] - 1) * #𝓀[K] ^ n`, so that
  `TauCeti.pow_natCard_sub_one_mul_pow_mem_unitFiltration_succ`: every unit `x` has
  `x ^ ((#𝓀[K] - 1) * #𝓀[K] ^ n) ∈ U(K,n+1)`.
* `TauCeti.relIndex_unitFiltration_add_succ_succ` and
  `TauCeti.natCard_unitFiltration_succ_quotient_add_succ`: more generally,
  `U(K,m+1) / U(K,m+n+1)` has `#𝓀[K] ^ n` elements.
* `TauCeti.unitFiltration_le_unitFiltration_iff`: the steps of the unit filtration are distinct,
  except that `U(K,1) = U(K,0)` when `#𝓀[K] = 2`
  (`TauCeti.unitFiltration_one_eq_unitFiltration_zero_iff`).

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The positive graded piece `U(K,n+1) / U(K,n+2)` is finite. -/
noncomputable instance finite_unitFiltrationGraded_succ (n : ℕ) :
    Finite (UnitFiltrationGraded K (n + 1)) :=
  have ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  Finite.of_equiv 𝓀[K]
    ((unitFiltrationGradedEquivInteger (K := K) (n + 1)).toAdditive.trans
      (TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField
        n π hπ)).symm.toEquiv

/-- Every positive graded piece has the cardinality of the residue field. -/
theorem natCard_unitFiltrationGraded_succ (n : ℕ) :
    Nat.card (UnitFiltrationGraded K (n + 1)) = Nat.card 𝓀[K] := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  exact Nat.card_congr
    ((unitFiltrationGradedEquivInteger (K := K) (n + 1)).toAdditive.trans
      (TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField n π hπ)).toEquiv

/-- Every positive step has relative index equal to the cardinality of the residue field:
`[U(K,n+1) : U(K,n+2)] = #𝓀[K]`. -/
theorem relIndex_unitFiltration_succ_succ (n : ℕ) :
    (unitFiltration K (n + 2)).relIndex (unitFiltration K (n + 1)) = Nat.card 𝓀[K] := by
  rw [Subgroup.relIndex, Subgroup.index]
  simpa only [UnitFiltrationGraded] using natCard_unitFiltrationGraded_succ (K := K) n

/-- The index of `U(K,m+n+1)` in `U(K,m+1)` is `q ^ n`, where `q = #𝓀[K]`. -/
theorem relIndex_unitFiltration_add_succ_succ (m n : ℕ) :
    (unitFiltration K (m + n + 1)).relIndex (unitFiltration K (m + 1)) =
      (Nat.card 𝓀[K]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ]
      calc
        (unitFiltration K (m + n + 2)).relIndex (unitFiltration K (m + 1)) =
            (unitFiltration K (m + n + 2)).relIndex (unitFiltration K (m + n + 1)) *
              (unitFiltration K (m + n + 1)).relIndex (unitFiltration K (m + 1)) :=
          (Subgroup.relIndex_mul_relIndex _ _ _
            (unitFiltration_antitone (K := K) (by omega : m + n + 1 ≤ m + n + 2))
            (unitFiltration_antitone (K := K) (by omega : m + 1 ≤ m + n + 1))).symm
        _ = (Nat.card 𝓀[K]) ^ (n + 1) := by
          rw [relIndex_unitFiltration_succ_succ, ih, pow_succ']

/-- Every `U(K,m)` has finite relative index in each positive-depth subgroup `U(K,n+1)`: the
index is `1` when `m ≤ n + 1`, and a power of `#𝓀[K]` otherwise. -/
noncomputable instance unitFiltration_isFiniteRelIndex_succ (m n : ℕ) :
    (unitFiltration K m).IsFiniteRelIndex (unitFiltration K (n + 1)) := by
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  rcases le_or_gt m (n + 1) with h | h
  · rw [Subgroup.relIndex_eq_one.mpr (unitFiltration_antitone h)]
    exact one_ne_zero
  · obtain ⟨k, rfl⟩ : ∃ k, m = n + k + 1 := ⟨m - n - 1, by omega⟩
    rw [relIndex_unitFiltration_add_succ_succ]
    exact pow_ne_zero k Nat.card_pos.ne'

/-- Every `U(K,m)` has finite index in the unit group `U(K,0) = 𝒪[K]ˣ`. -/
noncomputable instance unitFiltration_isFiniteRelIndex_zero (m : ℕ) :
    (unitFiltration K m).IsFiniteRelIndex (unitFiltration K 0) := by
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Subgroup.relIndex_self]
    exact one_ne_zero
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (unitFiltration_antitone hm)
    (unitFiltration_antitone (Nat.zero_le 1)), relIndex_unitFiltration_one_zero]
  have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  exact mul_ne_zero Subgroup.relIndex_ne_zero (by omega)

/-- The index of `U(K,n+1)` in the unit group `U(K,0) = 𝒪[K]ˣ` is `(q - 1) * q ^ n`, where
`q = #𝓀[K]`. -/
theorem relIndex_unitFiltration_succ_zero (n : ℕ) :
    (unitFiltration K (n + 1)).relIndex (unitFiltration K 0) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  have h := relIndex_unitFiltration_add_succ_succ (K := K) 0 n
  rw [zero_add, zero_add] at h
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (unitFiltration_antitone (by omega : 1 ≤ n + 1))
    (unitFiltration_antitone (Nat.zero_le 1)), h, relIndex_unitFiltration_one_zero, mul_comm]

/-- **Powering a unit into a deep step.** For every unit `x ∈ U(K,0)` and every `n`, the power
`x ^ ((q - 1) * q ^ n)` lies in `U(K,n+1)`, where `q = #𝓀[K]`: the exponent is the index of
`U(K,n+1)` in `U(K,0)`. -/
theorem pow_natCard_sub_one_mul_pow_mem_unitFiltration_succ {x : Kˣ}
    (hx : x ∈ unitFiltration K 0) (n : ℕ) :
    x ^ ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n) ∈ unitFiltration K (n + 1) := by
  rw [← relIndex_unitFiltration_succ_zero]
  exact Subgroup.pow_relIndex_mem _ hx

/-- The positive-depth finite-level quotient `U(K,m+1) / U(K,m+n+1)` has `q ^ n` elements,
where `q = #𝓀[K]`. -/
theorem natCard_unitFiltration_succ_quotient_add_succ (m n : ℕ) :
    Nat.card (unitFiltration K (m + 1) ⧸
      (unitFiltration K (m + n + 1)).subgroupOf (unitFiltration K (m + 1))) =
        (Nat.card 𝓀[K]) ^ n := by
  rw [← Subgroup.index_eq_card]
  exact relIndex_unitFiltration_add_succ_succ m n

/-- The first two steps of the unit filtration coincide, `U(K,1) = U(K,0)`, exactly when the
residue field has two elements. -/
theorem unitFiltration_one_eq_unitFiltration_zero_iff :
    unitFiltration K 1 = unitFiltration K 0 ↔ Nat.card 𝓀[K] = 2 := by
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  rw [le_antisymm_iff, and_iff_right (unitFiltration_antitone (Nat.zero_le 1)),
    ← Subgroup.relIndex_eq_one, relIndex_unitFiltration_one_zero]
  omega

/-- **The steps of the unit filtration are distinct**, apart from the coincidence
`U(K,1) = U(K,0)` when the residue field has two elements
(`unitFiltration_one_eq_unitFiltration_zero_iff`): away from it, `U(K,j) ⊆ U(K,i)` exactly
when `i ≤ j`. -/
theorem unitFiltration_le_unitFiltration_iff {i j : ℕ} (h : i ≠ 1 ∨ Nat.card 𝓀[K] ≠ 2) :
    unitFiltration K j ≤ unitFiltration K i ↔ i ≤ j := by
  refine ⟨fun hji ↦ ?_, fun hij ↦ unitFiltration_antitone hij⟩
  by_contra! hlt
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  -- Otherwise `U(K,i-1) ⊆ U(K,j) ⊆ U(K,i)`, so the step from depth `i - 1` to `i` is trivial.
  obtain _ | _ | k := i
  · omega
  · have hstep : (unitFiltration K 1).relIndex (unitFiltration K 0) = 1 :=
      Subgroup.relIndex_eq_one.mpr ((unitFiltration_antitone (by omega)).trans hji)
    rw [relIndex_unitFiltration_one_zero] at hstep
    omega
  · have hstep : (unitFiltration K (k + 2)).relIndex (unitFiltration K (k + 1)) = 1 :=
      Subgroup.relIndex_eq_one.mpr ((unitFiltration_antitone (by omega)).trans hji)
    rw [relIndex_unitFiltration_succ_succ] at hstep
    omega

end TauCeti
