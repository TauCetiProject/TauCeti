/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.RingTheory.Polynomial.Gauss.Valuation.Basic
import TauCeti.RingTheory.LocalRing.ResidueField.Polynomial
import TauCeti.RingTheory.Valuation.Polynomial

/-!
# Primitive factorization and generic evaluation for Gauss valuations

Over a valued field `(K, v)` with value group `Γ₀`, every polynomial `p : K[X]` factors as
`C c * q.map _` where `v c = p.gaussValuation v 1`, `q` has coefficients in `v.valuationSubring`
with `q.natDegree ≤ p.natDegree`, and `q` has nonzero reduction modulo the maximal ideal
(`Polynomial.exists_eq_C_mul_map_residue_ne_zero`). When `1 + ∑ j ∈ s, (p j).natDegree` is
strictly less than the cardinality of the residue field of `v.valuationSubring` (in particular,
whenever the residue field is infinite), the family `p` simultaneously attains its Gauss valuations
at a single point of prescribed valuation `v c`.

## Main results

* `Polynomial.exists_eq_C_mul_map_residue_ne_zero`: primitive factorization of any polynomial over
  a valued field.
* `Polynomial.exists_forall_valuation_eval_eq_gaussValuation_of_sum_natDegree_lt`: simultaneous
  attainment of the Gauss valuation at a point of prescribed valuation `v c` under a residue-field
  cardinality bound.
* `Polynomial.exists_forall_valuation_eval_eq_gaussValuation`: the infinite-residue-field corollary.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1.
* L. Alpöge, `New.Selmer.gaussVal` in `src/Lib/General/NumberTheory/GaussValuation.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

namespace Polynomial

section GenericEvaluation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- Every polynomial `p` over a valued field `K` factors as `C c * q.map _` where
`v c = p.gaussValuation v 1`, `q.natDegree ≤ p.natDegree`, and `q` has coefficients in
`v.valuationSubring` with nonzero reduction modulo the maximal ideal. -/
theorem exists_eq_C_mul_map_residue_ne_zero (p : K[X]) :
    ∃ (c : K) (q : v.valuationSubring[X]),
      v c = p.gaussValuation v 1 ∧
      p = C c * q.map (algebraMap v.valuationSubring K) ∧
      q.natDegree ≤ p.natDegree ∧
      q.map (IsLocalRing.residue v.valuationSubring) ≠ 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, 1, by simp, by simp, by simp, by simp⟩
  obtain ⟨d, D, hD, hle, -⟩ := v.exists_C_mul_coeff_eq_one hp
  have hd_ne : d ≠ 0 := fun h ↦ by simp [h] at hD
  have hnorm : (C d * p).gaussValuation v 1 = 1 :=
    le_antisymm ((gaussValuation_le_iff v 1).mpr fun n ↦ by simpa using hle n)
      (by simpa [hD] using le_gaussValuation v 1 (C d * p) D)
  have hlifts : C d * p ∈ lifts (algebraMap v.valuationSubring K) :=
    (lifts_iff_coeff_lifts _).mpr fun n ↦
      ⟨⟨(C d * p).coeff n, (Valuation.mem_valuationSubring_iff v _).mpr (hle n)⟩,
        ValuationSubring.algebraMap_apply v.valuationSubring _⟩
  obtain ⟨q, hq⟩ := (mem_lifts _).mp hlifts
  refine ⟨d⁻¹, q, ?_, ?_, ?_, fun hzero ↦ ?_⟩
  · simp only [gaussValuation_mul, gaussValuation_C] at hnorm
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hnorm]
  · rw [hq, ← mul_assoc, ← C_mul]
    simp [hd_ne]
  · rw [← natDegree_map_eq_of_injective (Valuation.valuationSubring.integers v).hom_inj, hq]
    exact natDegree_C_mul_le d p
  · have hcoeff : (q.map (IsLocalRing.residue v.valuationSubring)).coeff D = 0 := by simp [hzero]
    rw [coeff_map] at hcoeff
    have hqD : q.coeff D = 1 := (Valuation.valuationSubring.integers v).hom_inj <| by
      have hmap := congrArg (fun f ↦ f.coeff D) hq
      rw [coeff_map] at hmap
      simpa [map_one] using hmap.trans hD
    exact one_ne_zero (by rwa [hqD, map_one] at hcoeff)

/-- Over a valued field whose residue field has cardinality strictly greater than
`1 + ∑ j ∈ s, (p j).natDegree`, finitely many polynomials simultaneously attain their Gauss
valuations at a point of prescribed valuation `v c`. -/
theorem exists_forall_valuation_eval_eq_gaussValuation_of_sum_natDegree_lt {ι : Type*}
    (s : Finset ι) (p : ι → K[X]) (c : K)
    (hcard : ((1 + ∑ j ∈ s, (p j).natDegree : ℕ) : ENat) <
      ENat.card (IsLocalRing.ResidueField v.valuationSubring)) :
    ∃ x : K, v x = v c ∧ ∀ j ∈ s, v ((p j).eval x) = (p j).gaussValuation v (v c) := by
  classical
  choose a q ha hfac hdeg hres using fun j : ι ↦
    exists_eq_C_mul_map_residue_ne_zero v ((p j).comp (C c * X))
  have hF : ∀ o ∈ s.insertNone,
      (Option.elim' X q o).map (IsLocalRing.residue v.valuationSubring) ≠ 0 :=
    Finset.forall_mem_insertNone.mpr ⟨by simp, fun j _ ↦ hres j⟩
  have hdeg_sum : (∑ o ∈ s.insertNone,
      ((Option.elim' X q o).map (IsLocalRing.residue v.valuationSubring)).natDegree) ≤
      1 + ∑ j ∈ s, (p j).natDegree := by
    rw [Finset.sum_insertNone]
    refine Nat.add_le_add (by simp) (Finset.sum_le_sum fun j _ ↦ ?_)
    have hcX : (C c * X).natDegree ≤ 1 := (natDegree_C_mul_le c X).trans (by simp)
    exact natDegree_map_le.trans ((hdeg j).trans <|
      natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left (p j).natDegree hcX))
  obtain ⟨u, hu⟩ := exists_forall_isUnit_eval_of_sum_natDegree_lt s.insertNone (Option.elim' X q) hF
    ((Nat.cast_le.mpr hdeg_sum).trans_lt hcard)
  have hu_unit : IsUnit u := by simpa using hu none Finset.none_mem_insertNone
  have hu_val : v (algebraMap v.valuationSubring K u) = 1 :=
    (Valuation.valuationSubring.integers v).one_of_isUnit hu_unit
  refine ⟨c * algebraMap v.valuationSubring K u, by simp only [map_mul, hu_val, mul_one],
    fun j hj ↦ ?_⟩
  have hqu_unit : IsUnit ((q j).eval u) := by
    simpa using hu (some j) (Finset.some_mem_insertNone.mpr hj)
  have hqu_val : v (algebraMap v.valuationSubring K ((q j).eval u)) = 1 :=
    (Valuation.valuationSubring.integers v).one_of_isUnit hqu_unit
  have heval : (p j).eval (c * algebraMap v.valuationSubring K u) =
      a j * algebraMap v.valuationSubring K ((q j).eval u) := by
    have h1 : (p j).eval (c * algebraMap v.valuationSubring K u) =
        ((p j).comp (C c * X)).eval (algebraMap v.valuationSubring K u) := by simp [eval_comp]
    rw [h1, hfac j]
    simp only [eval_C_mul, eval_map_apply]
  simp only [heval, map_mul, hqu_val, mul_one, ha j, gaussValuation_comp_C_mul_X]

/-- Over a valued field with infinite residue field, finitely many polynomials simultaneously
attain their Gauss valuations at a point of prescribed valuation `v c`. -/
theorem exists_forall_valuation_eval_eq_gaussValuation
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] {ι : Type*}
    (s : Finset ι) (p : ι → K[X]) (c : K) :
    ∃ x : K, v x = v c ∧ ∀ j ∈ s, v ((p j).eval x) = (p j).gaussValuation v (v c) :=
  exists_forall_valuation_eval_eq_gaussValuation_of_sum_natDegree_lt v s p c
    (by rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top _)

end GenericEvaluation

end Polynomial
