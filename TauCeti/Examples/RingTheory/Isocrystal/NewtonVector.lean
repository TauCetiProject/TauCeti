/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Isocrystal.NewtonVector
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Examples of Newton vectors and admissible sets

These examples test `TauCeti.twoRhoPairing`, `TauCeti.IsNewtonVector` and
`TauCeti.admissibleNewtonVectors`:

* for `GL₄` and `μ = (1, 1, 0, 0)`, the ordinary vector pairs to `4` with `2ρ` and the basic vector
  `(1/2, 1/2, 1/2, 1/2)` pairs to `0`;
* in the negative normalization of Shimura varieties, the ordinary `GL₂` vector `(0, -1)` pairs to
  `1`, while the unsorted vector `(-1, 0)` pairs to `-1` and is not a Newton vector;
* `(1/2, 0)` is not a Newton vector, since the slope `1/2` occurs only once;
* in `B(GL₂, (1, 0))` the basic vector is strictly below the ordinary one;
* vectors with different totals, such as `(0)` and `(1)`, are not comparable for dominance;
* for `GL₀`, the empty vector is admissible for the empty cocharacter and pairs to `0`.

## References

* A. Caraiani and P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), §3.1.
-/

open Finset TauCeti

/-! ### Pairings with `2ρ` -/

-- `⟨2ρ, (1, 1, 0, 0)⟩ = 4` for `GL₄`, the dimension of the ordinary stratum.
example : twoRhoPairing (![1, 1, 0, 0] : Fin 4 → ℚ) = 4 := by
  rw [twoRhoPairing_eq_sum_zsmul, Fin.sum_univ_four]
  norm_num

-- The same value from the minuscule formula `a (n - a) = 2 · 2`.
example : twoRhoPairing (fun i : Fin 4 ↦ if (i : ℕ) < 2 then (1 : ℚ) else 0) = 4 := by
  rw [twoRhoPairing_indicator]
  norm_num

-- The basic vector of slope `1/2` is central and pairs to `0`.
example : twoRhoPairing (fun _ : Fin 4 ↦ (1 / 2 : ℚ)) = 0 :=
  twoRhoPairing_const _

-- In the negative normalization, the dominant ordinary `GL₂` vector is `(0, -1)`.
example : twoRhoPairing (![0, -1] : Fin 2 → ℚ) = 1 := by
  rw [twoRhoPairing_eq_sum_zsmul, Fin.sum_univ_two]
  norm_num

-- The unsorted vector `(-1, 0)` pairs to `-1`, and is not a Newton vector.
example : twoRhoPairing (![-1, 0] : Fin 2 → ℚ) = -1 := by
  rw [twoRhoPairing_eq_sum_zsmul, Fin.sum_univ_two]
  norm_num

example : ¬ IsNewtonVector (![-1, 0] : Fin 2 → ℚ) := fun h ↦ by
  have := h.antitone (Fin.zero_le 1)
  norm_num at this

/-! ### Newton vectors and the admissible set -/

-- The slope `1/2` needs even multiplicity, so `(1/2, 0)` is not a Newton vector.
example : ¬ IsNewtonVector (![1 / 2, 0] : Fin 2 → ℚ) := fun h ↦ by
  obtain ⟨z, hz⟩ := h.exists_int_card_mul_eq 0
  have hcard : #{j | (![1 / 2, 0] : Fin 2 → ℚ) j = ![1 / 2, 0] 0} = 1 :=
    card_eq_one.mpr ⟨0, by ext j; fin_cases j <;> norm_num⟩
  rw [hcard] at hz
  have h₀ : (0 : ℚ) < z := by norm_num at hz; rw [← hz]; norm_num
  have h₁ : (z : ℚ) < 1 := by norm_num at hz; rw [← hz]; norm_num
  have : (0 : ℤ) < z := by exact_mod_cast h₀
  have : z < (1 : ℤ) := by exact_mod_cast h₁
  omega

-- In `B(GL₂, (1, 0))` the basic vector lies strictly below the ordinary one.
example : twoRhoPairing (![1 / 2, 1 / 2] : Fin 2 → ℚ) < twoRhoPairing (![1, 0] : Fin 2 → ℚ) := by
  have hν : (![1 / 2, 1 / 2] : Fin 2 → ℚ) ∈ admissibleNewtonVectors ![1, 0] := by
    rw [admissibleNewtonVectors_one_zero]
    exact Set.mem_insert_of_mem _ rfl
  have hμ : (fun i ↦ ((![1, 0] : Fin 2 → ℤ) i : ℚ)) = ![1, 0] := by
    ext i; fin_cases i <;> norm_num
  rw [← hμ]
  refine (mem_admissibleNewtonVectors.mp hν).2.twoRhoPairing_lt ?_
  rw [hμ]
  intro h
  simpa using congrFun h 1

-- Dominance requires equal totals: `(0)` and `(1)` are not comparable.
example : ¬ Dominates (![0] : Fin 1 → ℚ) ![1] := by
  rw [dominates_iff_eq_fin_one]
  intro h
  simpa using congrFun h 0

-- For `GL₀`, the empty vector is admissible for the empty cocharacter and pairs to `0`.
example : (![] : Fin 0 → ℚ) ∈ admissibleNewtonVectors ![] :=
  mem_admissibleNewtonVectors.mpr ⟨⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩,
    Subsingleton.elim (α := Fin 0 → ℚ) ![] (fun i ↦ ((![] : Fin 0 → ℤ) i : ℚ)) ▸
      Dominates.refl _⟩

example : twoRhoPairing (![] : Fin 0 → ℚ) = 0 := by
  simp [twoRhoPairing_def]
