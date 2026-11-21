/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Complete

/-!
# Layers 6.2 and 6.3: multiples of four, and the witnesses at `k = 5, …, 8`

`h1_complete_movedNorm_fin_three` already gives `h1 (complete V) (movedNorm (Fin 3)) = card V / 3`
for every `3 ≤ card V`. This file names the two specializations asked for by Layer 6:

* `h1_complete_movedNorm_fin_three_of_four_dvd` (6.2): the same identity under the hypotheses
  `4 ∣ card V` and `4 ≤ card V`;
* `h1_complete_fin_five`, `h1_complete_fin_six`, `h1_complete_fin_seven` and
  `h1_complete_fin_eight` (6.3): the values `5 / 3`, `6 / 3`, `7 / 3` and `8 / 3`.

The four cochains `witness5`, `witness6`, `witness7` and `witness8` are the explicit Appendix A
data: each is `Cochain.ofLt` of the listed non-identity edges, in the one-line notation of the
roadmap table. `witness*_defect` and `witness*_cost_one` check the table's defect column and the
identity-gauge cost by `decide`. The gauge-distance lower bound is not re-proved here; the ratios
are the corollaries above.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792, Corollary 7 (6.2) and Theorem 4 with
  Appendix A (6.3).
* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136, Definition 3.2.
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: `w5`, `w6`, `w7` and `w8` in `CoboundaryK3/Basic.lean`.
-/

public section

open Finset Equiv Equiv.Perm

namespace TauCeti

open TwoComplex

/-! ## 6.2 Every multiple of four -/

/-- Whenever `4 ∣ Fintype.card V` and `4 ≤ Fintype.card V`,
`h1 (complete V) (movedNorm (Fin 3)) = card V / 3` (Beasley, Corollary 7). This is the
`4 ∣ card V` case of `h1_complete_movedNorm_fin_three`. -/
theorem h1_complete_movedNorm_fin_three_of_four_dvd {V : Type*} [Fintype V] [LinearOrder V]
    (h4 : 4 ∣ Fintype.card V) (hV : 4 ≤ Fintype.card V) :
    h1 (complete V) (movedNorm (Fin 3)) = (Fintype.card V : ℝ) / 3 := by
  obtain ⟨q, hq⟩ := h4
  rw [h1_complete_movedNorm_fin_three (by omega), hq]

/-! ## 6.3 Explicit witnesses for `k = 5, …, 8` -/

/- The one-line notation `(1 2 0)`: `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 0`. -/
private def cyc120 : Perm (Fin 3) := swap 0 1 * swap 1 2

/- The one-line notation `(2 0 1)`: `0 ↦ 2`, `1 ↦ 0`, `2 ↦ 1`. -/
private def cyc201 : Perm (Fin 3) := swap 1 2 * swap 0 1

/-- Non-identity edges of the `k = 5` witness: `(0, 1)`, `(1, 2)`, `(2, 3) ↦ (1 0 2)`. -/
private def edge5 (u v : Fin 5) : Perm (Fin 3) :=
  if u = 0 ∧ v = 1 then swap 0 1 else if u = 1 ∧ v = 2 then swap 0 1
  else if u = 2 ∧ v = 3 then swap 0 1 else 1

/-- Non-identity edges of the `k = 6` witness: `(0, 1)`, `(1, 3) ↦ (1 2 0)` and
`(0, 3)`, `(0, 4)`, `(1, 5)`, `(4, 5) ↦ (2 0 1)`. -/
private def edge6 (u v : Fin 6) : Perm (Fin 3) :=
  if u = 0 ∧ v = 1 then cyc120 else if u = 1 ∧ v = 3 then cyc120
  else if u = 0 ∧ v = 3 then cyc201 else if u = 0 ∧ v = 4 then cyc201
  else if u = 1 ∧ v = 5 then cyc201 else if u = 4 ∧ v = 5 then cyc201 else 1

/-- Non-identity edges of the `k = 7` witness: the six pairs
`(0, 1)`, `(0, 3)`, `(0, 4)`, `(1, 2)`, `(1, 5)`, `(2, 3) ↦ (1 0 2)`. -/
private def edge7 (u v : Fin 7) : Perm (Fin 3) :=
  if u = 0 ∧ v = 1 then swap 0 1 else if u = 0 ∧ v = 3 then swap 0 1
  else if u = 0 ∧ v = 4 then swap 0 1 else if u = 1 ∧ v = 2 then swap 0 1
  else if u = 1 ∧ v = 5 then swap 0 1 else if u = 2 ∧ v = 3 then swap 0 1 else 1

/-- Non-identity edges of the `k = 8` witness, in the four blocks of the roadmap table:
`(0, 1)`, `(0, 7)`, `(1, 2)`, `(2, 5)`, `(2, 7) ↦ (0 2 1)`;
`(1, 3)`, `(1, 4)`, `(1, 6)`, `(3, 7) ↦ (1 0 2)`;
`(0, 4)`, `(2, 3)`, `(2, 4) ↦ (2 1 0)`; `(4, 7) ↦ (2 0 1)`. -/
private def edge8 (u v : Fin 8) : Perm (Fin 3) :=
  if u = 0 ∧ v = 1 then swap 1 2 else if u = 0 ∧ v = 7 then swap 1 2
  else if u = 1 ∧ v = 2 then swap 1 2 else if u = 2 ∧ v = 5 then swap 1 2
  else if u = 2 ∧ v = 7 then swap 1 2 else if u = 1 ∧ v = 3 then swap 0 1
  else if u = 1 ∧ v = 4 then swap 0 1 else if u = 1 ∧ v = 6 then swap 0 1
  else if u = 3 ∧ v = 7 then swap 0 1 else if u = 0 ∧ v = 4 then swap 0 2
  else if u = 2 ∧ v = 3 then swap 0 2 else if u = 2 ∧ v = 4 then swap 0 2
  else if u = 4 ∧ v = 7 then cyc201 else 1

private theorem defect_eq {k : ℕ} (f : Fin k → Fin k → Perm (Fin 3)) :
    (Cochain.ofLt (complete (Fin k)) f).defect (movedNorm (Fin 3)) =
      (∑ p ∈ univ.filter fun p : Fin k × Fin k × Fin k => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
        (f p.1 p.2.1 * f p.2.1 p.2.2 * (f p.1 p.2.2)⁻¹).support.card : ℝ) := by
  rw [Cochain.defect_complete]
  have h :
      ∀ p ∈ univ.filter fun p : Fin k × Fin k × Fin k => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
        movedNorm (Fin 3)
            ((Cochain.ofLt (complete (Fin k)) f).holonomy p.1 p.2.1 p.2.2) =
          (((f p.1 p.2.1 * f p.2.1 p.2.2 * (f p.1 p.2.2)⁻¹).support.card : ℕ) : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    rw [Cochain.holonomy_ofLt_complete _ hp.2.1 hp.2.2, movedNorm_apply]
  rw [sum_congr rfl h, ← Nat.cast_sum]

private theorem cost_one_eq {k : ℕ} (f : Fin k → Fin k → Perm (Fin 3)) :
    (Cochain.ofLt (complete (Fin k)) f).cost (movedNorm (Fin 3)) (fun _ => 1) =
      (∑ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2,
        (f p.1 p.2).support.card : ℝ) := by
  rw [Cochain.cost_complete]
  have h : ∀ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2,
      movedNorm (Fin 3) ((1 : Perm (Fin 3))⁻¹ *
        (Cochain.ofLt (complete (Fin k)) f) p.1 p.2 * 1) =
        (((f p.1 p.2).support.card : ℕ) : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    rw [Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr hp.2.ne) hp.2, inv_one, one_mul,
      mul_one, movedNorm_apply]
  rw [sum_congr rfl h, ← Nat.cast_sum]

/-- The README 6.3 witness at `k = 5`: `(0, 1)`, `(1, 2)`, `(2, 3) ↦ (1 0 2)`, and `1` on every
other ordered pair `u < v`. -/
noncomputable def witness5 : Cochain (complete (Fin 5)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 5)) edge5

/-- The README 6.3 witness at `k = 6`. -/
noncomputable def witness6 : Cochain (complete (Fin 6)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 6)) edge6

/-- The README 6.3 witness at `k = 7`: the six edges of `edge7` carry `(1 0 2)`, and every other
ordered pair `u < v` carries `1`. -/
noncomputable def witness7 : Cochain (complete (Fin 7)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 7)) edge7

/-- The README 6.3 witness at `k = 8`, with the thirteen non-identity edges of `edge8`. -/
noncomputable def witness8 : Cochain (complete (Fin 8)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 8)) edge8

theorem witness5_defect : witness5.defect (movedNorm (Fin 3)) = 10 := by
  rw [witness5, defect_eq]
  have h10 : ∑ p ∈ univ.filter fun p : Fin 5 × Fin 5 × Fin 5 => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      (edge5 p.1 p.2.1 * edge5 p.2.1 p.2.2 * (edge5 p.1 p.2.2)⁻¹).support.card = 10 := by
    decide +kernel
  exact_mod_cast h10

theorem witness6_defect : witness6.defect (movedNorm (Fin 3)) = 36 := by
  rw [witness6, defect_eq]
  have h36 : ∑ p ∈ univ.filter fun p : Fin 6 × Fin 6 × Fin 6 => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      (edge6 p.1 p.2.1 * edge6 p.2.1 p.2.2 * (edge6 p.1 p.2.2)⁻¹).support.card = 36 := by
    decide +kernel
  exact_mod_cast h36

theorem witness7_defect : witness7.defect (movedNorm (Fin 3)) = 28 := by
  rw [witness7, defect_eq]
  have h28 : ∑ p ∈ univ.filter fun p : Fin 7 × Fin 7 × Fin 7 => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      (edge7 p.1 p.2.1 * edge7 p.2.1 p.2.2 * (edge7 p.1 p.2.2)⁻¹).support.card = 28 := by
    decide +kernel
  exact_mod_cast h28

theorem witness8_defect : witness8.defect (movedNorm (Fin 3)) = 72 := by
  rw [witness8, defect_eq]
  have h72 : ∑ p ∈ univ.filter fun p : Fin 8 × Fin 8 × Fin 8 => p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      (edge8 p.1 p.2.1 * edge8 p.2.1 p.2.2 * (edge8 p.1 p.2.2)⁻¹).support.card = 72 := by
    decide +kernel
  exact_mod_cast h72

/-- The identity gauge costs `6` against `witness5`. -/
theorem witness5_cost_one : witness5.cost (movedNorm (Fin 3)) (fun _ => 1) = 6 := by
  rw [witness5, cost_one_eq]
  have h6 : ∑ p ∈ univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2,
      (edge5 p.1 p.2).support.card = 6 := by decide +kernel
  exact_mod_cast h6

/-- The identity gauge costs `18` against `witness6`. -/
theorem witness6_cost_one : witness6.cost (movedNorm (Fin 3)) (fun _ => 1) = 18 := by
  rw [witness6, cost_one_eq]
  have h18 : ∑ p ∈ univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2,
      (edge6 p.1 p.2).support.card = 18 := by decide +kernel
  exact_mod_cast h18

/-- The identity gauge costs `12` against `witness7`. -/
theorem witness7_cost_one : witness7.cost (movedNorm (Fin 3)) (fun _ => 1) = 12 := by
  rw [witness7, cost_one_eq]
  have h12 : ∑ p ∈ univ.filter fun p : Fin 7 × Fin 7 => p.1 < p.2,
      (edge7 p.1 p.2).support.card = 12 := by decide +kernel
  exact_mod_cast h12

/-- The identity gauge costs `27` against `witness8`. -/
theorem witness8_cost_one : witness8.cost (movedNorm (Fin 3)) (fun _ => 1) = 27 := by
  rw [witness8, cost_one_eq]
  have h27 : ∑ p ∈ univ.filter fun p : Fin 8 × Fin 8 => p.1 < p.2,
      (edge8 p.1 p.2).support.card = 27 := by decide +kernel
  exact_mod_cast h27

/-- **README 6.3, `k = 5`.** `h1 (complete (Fin 5)) (movedNorm (Fin 3)) = 5 / 3`. -/
theorem h1_complete_fin_five : h1 (complete (Fin 5)) (movedNorm (Fin 3)) = 5 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 5) (by simp)

/-- **README 6.3, `k = 6`.** `h1 (complete (Fin 6)) (movedNorm (Fin 3)) = 6 / 3`. -/
theorem h1_complete_fin_six : h1 (complete (Fin 6)) (movedNorm (Fin 3)) = 6 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 6) (by simp)

/-- **README 6.3, `k = 7`.** `h1 (complete (Fin 7)) (movedNorm (Fin 3)) = 7 / 3`. -/
theorem h1_complete_fin_seven : h1 (complete (Fin 7)) (movedNorm (Fin 3)) = 7 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 7) (by simp)

/-- **README 6.3, `k = 8`.** `h1 (complete (Fin 8)) (movedNorm (Fin 3)) = 8 / 3`. -/
theorem h1_complete_fin_eight : h1 (complete (Fin 8)) (movedNorm (Fin 3)) = 8 / 3 := by
  simpa using h1_complete_movedNorm_fin_three (V := Fin 8) (by simp)

end TauCeti
