/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationIndex
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Evaluating derivatives at a uniformizer

For a polynomial of degree less than the ramification index, differentiation lowers the order
of its value at a uniformizer by at most one. Orthogonality of the powers of a uniformizer
makes this hold without any cancellation hypothesis on the coefficients. This estimate controls
derivatives when counting roots in small valuation balls.

No separability, total ramification, or completeness hypothesis on the extension is needed beyond
the local-field structures used to define its ramification index.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Lemma 1.
-/

public section

open ValuativeRel Polynomial IsDiscreteValuationRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- Below the ramification index, differentiation can lower the order of evaluation at a
uniformizer by at most one. -/
theorem addVal_aeval_le_addVal_aeval_derivative_add_one {ξ : 𝒪[L]} (hξ : Irreducible ξ)
    {P : 𝒪[K][X]} (hP : P.natDegree < ramificationIndex K L) :
    addVal 𝒪[L] (aeval ξ P) ≤ addVal 𝒪[L] (aeval ξ P.derivative) + 1 := by
  classical
  have hexp : aeval ξ P =
      ∑ i : Fin (ramificationIndex K L), algebraMap 𝒪[K] 𝒪[L] (P.coeff i) * ξ ^ (i : ℕ) := by
    rw [aeval_eq_sum_range' hP]
    simp only [← Fin.sum_univ_eq_sum_range, Algebra.smul_def]
  have hterm (j : ℕ) : addVal 𝒪[L] (aeval ξ P) ≤
      addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (P.coeff j) * ξ ^ j) := by
    by_cases hj : j < ramificationIndex K L
    · rw [hexp, addVal_sum_algebraMap_mul_pow_of_irreducible hξ le_rfl,
        addVal_mul, addVal_algebraMap, addVal_pow, addVal_uniformizer hξ, nsmul_one]
      exact iInf_le (fun i : Fin (ramificationIndex K L) ↦
        ramificationIndex K L • addVal 𝒪[K] (P.coeff i) + (i : ℕ)) ⟨j, hj⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hP.trans_le (Nat.le_of_not_gt hj)), map_zero, zero_mul,
        addVal_zero]
      exact le_top
  have hder : aeval ξ P.derivative * ξ =
      ∑ i : Fin (ramificationIndex K L),
        algebraMap 𝒪[K] 𝒪[L] (P.coeff (i + 1) * (i + 1)) * ξ ^ ((i : ℕ) + 1) := by
    rw [aeval_eq_sum_range' ((P.natDegree_derivative_le.trans (Nat.sub_le _ _)).trans_lt hP),
      Finset.sum_mul]
    simp only [← Fin.sum_univ_eq_sum_range, coeff_derivative, Algebra.smul_def,
      pow_succ, mul_assoc]
  rw [← addVal_uniformizer hξ, ← addVal_mul, hder]
  refine (addVal 𝒪[L]).map_le_sum fun i _ ↦ (hterm (i + 1)).trans ?_
  rw [map_mul (algebraMap 𝒪[K] 𝒪[L]), mul_right_comm]
  exact addVal_le_iff_dvd.2 (dvd_mul_right _ _)

end TauCeti
