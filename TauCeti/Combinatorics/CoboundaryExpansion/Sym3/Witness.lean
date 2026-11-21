/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Complete
import TauCeti.GroupTheory.Perm.FinThree.Basic
import Mathlib.Data.List.GetD

/-!
# Layers 6.2 and 6.3: multiples of four, and the witnesses at `k = 5, …, 8`

`h1_complete_movedNorm_fin_three` already gives `h1 (complete V) (movedNorm (Fin 3)) = card V / 3`
for every `3 ≤ card V`. This file names the two specializations asked for by Layer 6:

* `Sym3.replicatedSeed` (6.2): the seed `Sym3.w4` replicated on `Fin 4 ×ₗ Fin q`, with
  defect `8 q ^ 3` and gauge distance `6 q ^ 2`, the identity gauge attaining that distance.
  `replicatedSeedOfCardEq` carries it to any `V` with `card V = 4 q`, and
  `replicatedSeedOfCardEq_attains` is `defect / gaugeDist = card V / 3 = h1`.
  `h1_complete_movedNorm_fin_three_of_four_dvd` is that identity under `4 ∣ card V` and
  `4 ≤ card V`;
* `h1_complete_fin_five`, `h1_complete_fin_six`, `h1_complete_fin_seven` and
  `h1_complete_fin_eight` (6.3): the values `5 / 3`, `6 / 3`, `7 / 3` and `8 / 3`.

The four cochains `witness5`, `witness6`, `witness7` and `witness8` are the explicit Appendix A
data: each is `Cochain.ofLt` of the listed non-identity edges, in the one-line notation of the
roadmap table. `witness*_defect` and `witness*_cost_one` check the table's defect and the
identity-gauge cost. `witness*_gaugeDist` is the lower bound from a branch-and-bound exhaustion
of the gauges pinned at `0`, and `witness*_attains` is `defect / gaugeDist = k / 3`, equal to `h1`.

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


/-! ## Gauge distance of the four witnesses -/

private def g0 : Perm (Fin 3) := 1
private def g1 : Perm (Fin 3) := swap 0 1
private def g2 : Perm (Fin 3) := swap 1 2
private def g3 : Perm (Fin 3) := swap 0 2
private def g4 : Perm (Fin 3) := finRotate 3
private def g5 : Perm (Fin 3) := (finRotate 3)⁻¹

private def movedFast (σ : Perm (Fin 3)) : ℕ :=
  (if σ 0 ≠ 0 then 1 else 0) + (if σ 1 ≠ 1 then 1 else 0) + (if σ 2 ≠ 2 then 1 else 0)

private theorem movedFast_eq (σ : Perm (Fin 3)) : movedFast σ = σ.support.card := by
  revert σ
  decide +kernel

private def sym3Elems : List (Perm (Fin 3)) :=
  [g0, g1, g2, g3, g4, g5]

private theorem mem_sym3Elems (a : Perm (Fin 3)) : a ∈ sym3Elems := by
  rcases fin_three_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def edgeList (k : ℕ) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap fun u =>
    ((List.finRange k).filter fun v => decide (u < v)).map fun v => (u, v)

private def term {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (l : List (Perm (Fin 3)))
    (e : Fin k × Fin k) : ℕ :=
  movedFast ((l.getD e.1.val 1)⁻¹ * α e.1 e.2 * l.getD e.2.val 1)

private def pcost {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (l : List (Perm (Fin 3))) : ℕ :=
  ((edgeList k).map fun e => if e.2.val < l.length then term α l e else 0).sum

private def search {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (D : ℕ) :
    ℕ → List (Perm (Fin 3)) → Bool
  | 0, l => decide (D ≤ pcost α l)
  | f + 1, l => decide (D ≤ pcost α l) || sym3Elems.all fun a => search α D f (l ++ [a])

private theorem sum_map_le {ι : Type*} (l : List ι) (f g : ι → ℕ) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

private theorem lt_of_mem_edgeList {k : ℕ} {e : Fin k × Fin k} (h : e ∈ edgeList k) :
    e.1.val < e.2.val := by
  simp only [edgeList, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨u, _, v, hv, rfl⟩ := h
  exact hv.2

private theorem pcost_mono {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3))
    (l rest : List (Perm (Fin 3))) :
    pcost α l ≤ pcost α (l ++ rest) := by
  apply sum_map_le
  intro e he
  have h12 : e.1.val < e.2.val := lt_of_mem_edgeList he
  by_cases h1 : e.2.val < l.length
  · have h1' : e.1.val < l.length := Nat.lt_trans h12 h1
    have h2 : e.2.val < (l ++ rest).length := by
      rw [List.length_append]
      exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
    rw [ite_eq_left h1, ite_eq_left h2]
    simp only [term, List.getD_append l rest 1 e.1.val h1', List.getD_append l rest 1 e.2.val h1]
    exact le_rfl
  · by_cases h2 : e.2.val < (l ++ rest).length
    · rw [ite_eq_right h1, ite_eq_left h2]
      exact Nat.zero_le _
    · rw [ite_eq_right h1, ite_eq_right h2]

private theorem search_sound {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (D : ℕ) :
    ∀ (fuel : ℕ) (l : List (Perm (Fin 3))), search α D fuel l = true →
      ∀ rest : List (Perm (Fin 3)), rest.length = fuel → D ≤ pcost α (l ++ rest)
  | 0, l, h, rest, hl => by
    rw [List.length_eq_zero_iff.mp hl, List.append_nil]
    simpa [search] using h
  | f + 1, l, h, rest, hl => by
    simp only [search, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    rcases h with h | h
    · exact h.trans (pcost_mono α l rest)
    · obtain ⟨a, tail, rfl⟩ : ∃ a tail, rest = a :: tail := by
        cases rest with
        | nil => simp at hl
        | cons a t => exact ⟨a, t, rfl⟩
      have := search_sound α D f (l ++ [a]) (h a (mem_sym3Elems a)) tail (by simpa using hl)
      simpa using this

private theorem search_step {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (D f : ℕ)
    (l : List (Perm (Fin 3)))
    (h : ∀ a ∈ sym3Elems, search α D f (l ++ [a]) = true) : search α D (f + 1) l = true := by
  simp only [search, Bool.or_eq_true, List.all_eq_true]
  exact Or.inr h

private theorem sum_map_flatMap {α β : Type*} (l : List α) (g : α → List β) (f : β → ℕ) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private theorem sum_map_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    split <;> simp [ih]

private theorem sum_map_finRange {k : ℕ} (g : Fin k → ℕ) :
    ((List.finRange k).map g).sum = ∑ i : Fin k, g i := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
    rw [ih]
    simp [Function.comp_apply, Fin.sum_univ_succ]

private theorem sum_edgeList {k : ℕ} (f : Fin k × Fin k → ℕ) :
    ((edgeList k).map f).sum =
      ∑ u : Fin k, ∑ v ∈ univ.filter fun v => u < v, f (u, v) := by
  have hflat : ((edgeList k).map f).sum =
      ((List.finRange k).map fun u =>
        ((((List.finRange k).filter fun v => decide (u < v)).map fun v => (u, v)).map
            f).sum).sum := by
    simpa [edgeList] using sum_map_flatMap (List.finRange k)
      (fun u => ((List.finRange k).filter fun v => decide (u < v)).map fun v => (u, v)) f
  rw [hflat, sum_map_finRange]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [List.map_map, sum_map_filter, sum_map_finRange, Finset.sum_filter]
  simp [decide_eq_true_eq]

private theorem sum_filter_prod {k : ℕ} (f : Fin k × Fin k → ℕ) :
    ∑ u : Fin k, ∑ v ∈ univ.filter fun v => u < v, f (u, v) =
      ∑ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2, f p := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_filter]

private theorem pcost_ofFn {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (β : Fin k → Perm (Fin 3)) :
    pcost α (List.ofFn β) =
      ∑ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2,
        movedFast ((β p.1)⁻¹ * α p.1 p.2 * β p.2) := by
  have hlen : ∀ i : Fin k, i.val < (List.ofFn β).length := by simp
  unfold pcost
  have hmap : (edgeList k).map (fun e =>
        if e.2.val < (List.ofFn β).length then term α (List.ofFn β) e else 0) =
      (edgeList k).map fun e => movedFast ((β e.1)⁻¹ * α e.1 e.2 * β e.2) := by
    apply List.map_congr_left
    intro e _
    rw [ite_eq_left (hlen e.2)]
    simp only [term, List.getD_eq_getElem (List.ofFn β) 1 (hlen e.1),
      List.getD_eq_getElem (List.ofFn β) 1 (hlen e.2), List.getElem_ofFn]
  rw [hmap, sum_edgeList]
  exact sum_filter_prod fun e => movedFast ((β e.1)⁻¹ * α e.1 e.2 * β e.2)

private theorem cost_eq_card {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (β : Fin k → Perm (Fin 3)) :
    (Cochain.ofLt (complete (Fin k)) α).cost (movedNorm (Fin 3)) β =
      (∑ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2,
        ((β p.1)⁻¹ * α p.1 p.2 * β p.2).support.card : ℝ) := by
  rw [Cochain.cost_complete]
  have h : ∀ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2,
      movedNorm (Fin 3) ((β p.1)⁻¹ *
        (Cochain.ofLt (complete (Fin k)) α) p.1 p.2 * β p.2) =
        (((β p.1)⁻¹ * α p.1 p.2 * β p.2).support.card : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    rw [Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr hp.2.ne) hp.2, movedNorm_apply]
  rw [sum_congr rfl h, ← Nat.cast_sum]

private theorem and6 {a b c d e f : Bool}
    (h : (a && b && c) && (d && e && f) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true ∧ f = true := by
  revert a b c d e f
  decide +kernel

private theorem search_and6 {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (D f : ℕ)
    (l : List (Perm (Fin 3)))
    (h : (search α D f (l ++ [g0]) && search α D f (l ++ [g1]) &&
          search α D f (l ++ [g2])) &&
        (search α D f (l ++ [g3]) && search α D f (l ++ [g4]) &&
          search α D f (l ++ [g5])) = true) :
    search α D (f + 1) l = true := by
  apply search_step α D f l
  intro a ha
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩ := and6 h
  simp only [sym3Elems, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha0
  · exact ha1
  · exact ha2
  · exact ha3
  · exact ha4
  · exact ha5

private theorem le_cost_of_search {m : ℕ}
    (α : Fin (m + 1) → Fin (m + 1) → Perm (Fin 3)) (D : ℕ)
    (h : search α D m [g0] = true) (β : Fin (m + 1) → Perm (Fin 3)) (hβ : β 0 = 1) :
    (D : ℝ) ≤ (Cochain.ofLt (complete (Fin (m + 1))) α).cost (movedNorm (Fin 3)) β := by
  have hs := search_sound α D m [g0] h (List.ofFn fun i : Fin m => β i.succ) (by simp)
  have he : List.ofFn β = [g0] ++ List.ofFn fun i : Fin m => β i.succ := by
    rw [List.ofFn_succ, hβ, g0, ← List.singleton_append]
  rw [← he] at hs
  rw [cost_eq_card]
  have hsum := pcost_ofFn α β
  simp only [movedFast_eq] at hsum
  exact_mod_cast hsum ▸ hs

private theorem search5_root : search edge5 6 4 [g0] = true := by
  decide +kernel

private theorem search6_leaves :
    (search edge6 18 4 [g0, g0] && search edge6 18 4 [g0, g1] && search edge6 18 4 [g0, g2]) &&
      (search edge6 18 4 [g0, g3] &&
        search edge6 18 4 [g0, g4] &&
        search edge6 18 4 [g0, g5]) = true := by
  decide +kernel

private theorem search6_root : search edge6 18 5 [g0] = true :=
  search_and6 edge6 18 4 [g0] search6_leaves

private theorem search7_0 :
    (search edge7 12 4 [g0, g0, g0] && search edge7 12 4 [g0, g0, g1] &&
      search edge7 12 4 [g0, g0, g2]) &&
      (search edge7 12 4 [g0, g0, g3] && search edge7 12 4 [g0, g0, g4] &&
        search edge7 12 4 [g0, g0, g5]) = true := by
  decide +kernel
private theorem search7_node_0 : search edge7 12 5 [g0, g0] = true :=
  search_and6 edge7 12 4 [g0, g0] search7_0

private theorem search7_1 :
    (search edge7 12 4 [g0, g1, g0] && search edge7 12 4 [g0, g1, g1] &&
      search edge7 12 4 [g0, g1, g2]) &&
      (search edge7 12 4 [g0, g1, g3] && search edge7 12 4 [g0, g1, g4] &&
        search edge7 12 4 [g0, g1, g5]) = true := by
  decide +kernel
private theorem search7_node_1 : search edge7 12 5 [g0, g1] = true :=
  search_and6 edge7 12 4 [g0, g1] search7_1

private theorem search7_2 :
    (search edge7 12 4 [g0, g2, g0] && search edge7 12 4 [g0, g2, g1] &&
      search edge7 12 4 [g0, g2, g2]) &&
      (search edge7 12 4 [g0, g2, g3] && search edge7 12 4 [g0, g2, g4] &&
        search edge7 12 4 [g0, g2, g5]) = true := by
  decide +kernel
private theorem search7_node_2 : search edge7 12 5 [g0, g2] = true :=
  search_and6 edge7 12 4 [g0, g2] search7_2

private theorem search7_3 :
    (search edge7 12 4 [g0, g3, g0] && search edge7 12 4 [g0, g3, g1] &&
      search edge7 12 4 [g0, g3, g2]) &&
      (search edge7 12 4 [g0, g3, g3] && search edge7 12 4 [g0, g3, g4] &&
        search edge7 12 4 [g0, g3, g5]) = true := by
  decide +kernel
private theorem search7_node_3 : search edge7 12 5 [g0, g3] = true :=
  search_and6 edge7 12 4 [g0, g3] search7_3

private theorem search7_4 :
    (search edge7 12 4 [g0, g4, g0] && search edge7 12 4 [g0, g4, g1] &&
      search edge7 12 4 [g0, g4, g2]) &&
      (search edge7 12 4 [g0, g4, g3] && search edge7 12 4 [g0, g4, g4] &&
        search edge7 12 4 [g0, g4, g5]) = true := by
  decide +kernel
private theorem search7_node_4 : search edge7 12 5 [g0, g4] = true :=
  search_and6 edge7 12 4 [g0, g4] search7_4

private theorem search7_5 :
    (search edge7 12 4 [g0, g5, g0] && search edge7 12 4 [g0, g5, g1] &&
      search edge7 12 4 [g0, g5, g2]) &&
      (search edge7 12 4 [g0, g5, g3] && search edge7 12 4 [g0, g5, g4] &&
        search edge7 12 4 [g0, g5, g5]) = true := by
  decide +kernel
private theorem search7_node_5 : search edge7 12 5 [g0, g5] = true :=
  search_and6 edge7 12 4 [g0, g5] search7_5

private theorem search7_root : search edge7 12 6 [g0] = true := by
  apply search_and6 edge7 12 5 [g0]
  simp [search7_node_0, search7_node_1, search7_node_2,
    search7_node_3, search7_node_4, search7_node_5]
private theorem search8_0_0 :
    (search edge8 27 4 [g0, g0, g0, g0] && search edge8 27 4 [g0, g0, g0, g1] &&
      search edge8 27 4 [g0, g0, g0, g2]) &&
      (search edge8 27 4 [g0, g0, g0, g3] && search edge8 27 4 [g0, g0, g0, g4] &&
        search edge8 27 4 [g0, g0, g0, g5]) = true := by
  decide +kernel
private theorem search8_node_0_0 :
    search edge8 27 5 [g0, g0, g0] = true :=
  search_and6 edge8 27 4 [g0, g0, g0] search8_0_0

private theorem search8_0_1 :
    (search edge8 27 4 [g0, g0, g1, g0] && search edge8 27 4 [g0, g0, g1, g1] &&
      search edge8 27 4 [g0, g0, g1, g2]) &&
      (search edge8 27 4 [g0, g0, g1, g3] && search edge8 27 4 [g0, g0, g1, g4] &&
        search edge8 27 4 [g0, g0, g1, g5]) = true := by
  decide +kernel
private theorem search8_node_0_1 :
    search edge8 27 5 [g0, g0, g1] = true :=
  search_and6 edge8 27 4 [g0, g0, g1] search8_0_1

private theorem search8_0_2 :
    (search edge8 27 4 [g0, g0, g2, g0] && search edge8 27 4 [g0, g0, g2, g1] &&
      search edge8 27 4 [g0, g0, g2, g2]) &&
      (search edge8 27 4 [g0, g0, g2, g3] && search edge8 27 4 [g0, g0, g2, g4] &&
        search edge8 27 4 [g0, g0, g2, g5]) = true := by
  decide +kernel
private theorem search8_node_0_2 :
    search edge8 27 5 [g0, g0, g2] = true :=
  search_and6 edge8 27 4 [g0, g0, g2] search8_0_2

private theorem search8_0_3 :
    (search edge8 27 4 [g0, g0, g3, g0] && search edge8 27 4 [g0, g0, g3, g1] &&
      search edge8 27 4 [g0, g0, g3, g2]) &&
      (search edge8 27 4 [g0, g0, g3, g3] && search edge8 27 4 [g0, g0, g3, g4] &&
        search edge8 27 4 [g0, g0, g3, g5]) = true := by
  decide +kernel
private theorem search8_node_0_3 :
    search edge8 27 5 [g0, g0, g3] = true :=
  search_and6 edge8 27 4 [g0, g0, g3] search8_0_3

private theorem search8_0_4 :
    (search edge8 27 4 [g0, g0, g4, g0] && search edge8 27 4 [g0, g0, g4, g1] &&
      search edge8 27 4 [g0, g0, g4, g2]) &&
      (search edge8 27 4 [g0, g0, g4, g3] && search edge8 27 4 [g0, g0, g4, g4] &&
        search edge8 27 4 [g0, g0, g4, g5]) = true := by
  decide +kernel
private theorem search8_node_0_4 :
    search edge8 27 5 [g0, g0, g4] = true :=
  search_and6 edge8 27 4 [g0, g0, g4] search8_0_4

private theorem search8_0_5 :
    (search edge8 27 4 [g0, g0, g5, g0] && search edge8 27 4 [g0, g0, g5, g1] &&
      search edge8 27 4 [g0, g0, g5, g2]) &&
      (search edge8 27 4 [g0, g0, g5, g3] && search edge8 27 4 [g0, g0, g5, g4] &&
        search edge8 27 4 [g0, g0, g5, g5]) = true := by
  decide +kernel
private theorem search8_node_0_5 :
    search edge8 27 5 [g0, g0, g5] = true :=
  search_and6 edge8 27 4 [g0, g0, g5] search8_0_5

private theorem search8_mid_0 : search edge8 27 6 [g0, g0] = true := by
  apply search_and6 edge8 27 5 [g0, g0]
  simp [search8_node_0_0, search8_node_0_1, search8_node_0_2,
    search8_node_0_3, search8_node_0_4, search8_node_0_5]
private theorem search8_1_0 :
    (search edge8 27 4 [g0, g1, g0, g0] && search edge8 27 4 [g0, g1, g0, g1] &&
      search edge8 27 4 [g0, g1, g0, g2]) &&
      (search edge8 27 4 [g0, g1, g0, g3] && search edge8 27 4 [g0, g1, g0, g4] &&
        search edge8 27 4 [g0, g1, g0, g5]) = true := by
  decide +kernel
private theorem search8_node_1_0 :
    search edge8 27 5 [g0, g1, g0] = true :=
  search_and6 edge8 27 4 [g0, g1, g0] search8_1_0

private theorem search8_1_1 :
    (search edge8 27 4 [g0, g1, g1, g0] && search edge8 27 4 [g0, g1, g1, g1] &&
      search edge8 27 4 [g0, g1, g1, g2]) &&
      (search edge8 27 4 [g0, g1, g1, g3] && search edge8 27 4 [g0, g1, g1, g4] &&
        search edge8 27 4 [g0, g1, g1, g5]) = true := by
  decide +kernel
private theorem search8_node_1_1 :
    search edge8 27 5 [g0, g1, g1] = true :=
  search_and6 edge8 27 4 [g0, g1, g1] search8_1_1

private theorem search8_1_2 :
    (search edge8 27 4 [g0, g1, g2, g0] && search edge8 27 4 [g0, g1, g2, g1] &&
      search edge8 27 4 [g0, g1, g2, g2]) &&
      (search edge8 27 4 [g0, g1, g2, g3] && search edge8 27 4 [g0, g1, g2, g4] &&
        search edge8 27 4 [g0, g1, g2, g5]) = true := by
  decide +kernel
private theorem search8_node_1_2 :
    search edge8 27 5 [g0, g1, g2] = true :=
  search_and6 edge8 27 4 [g0, g1, g2] search8_1_2

private theorem search8_1_3 :
    (search edge8 27 4 [g0, g1, g3, g0] && search edge8 27 4 [g0, g1, g3, g1] &&
      search edge8 27 4 [g0, g1, g3, g2]) &&
      (search edge8 27 4 [g0, g1, g3, g3] && search edge8 27 4 [g0, g1, g3, g4] &&
        search edge8 27 4 [g0, g1, g3, g5]) = true := by
  decide +kernel
private theorem search8_node_1_3 :
    search edge8 27 5 [g0, g1, g3] = true :=
  search_and6 edge8 27 4 [g0, g1, g3] search8_1_3

private theorem search8_1_4 :
    (search edge8 27 4 [g0, g1, g4, g0] && search edge8 27 4 [g0, g1, g4, g1] &&
      search edge8 27 4 [g0, g1, g4, g2]) &&
      (search edge8 27 4 [g0, g1, g4, g3] && search edge8 27 4 [g0, g1, g4, g4] &&
        search edge8 27 4 [g0, g1, g4, g5]) = true := by
  decide +kernel
private theorem search8_node_1_4 :
    search edge8 27 5 [g0, g1, g4] = true :=
  search_and6 edge8 27 4 [g0, g1, g4] search8_1_4

private theorem search8_1_5 :
    (search edge8 27 4 [g0, g1, g5, g0] && search edge8 27 4 [g0, g1, g5, g1] &&
      search edge8 27 4 [g0, g1, g5, g2]) &&
      (search edge8 27 4 [g0, g1, g5, g3] && search edge8 27 4 [g0, g1, g5, g4] &&
        search edge8 27 4 [g0, g1, g5, g5]) = true := by
  decide +kernel
private theorem search8_node_1_5 :
    search edge8 27 5 [g0, g1, g5] = true :=
  search_and6 edge8 27 4 [g0, g1, g5] search8_1_5

private theorem search8_mid_1 : search edge8 27 6 [g0, g1] = true := by
  apply search_and6 edge8 27 5 [g0, g1]
  simp [search8_node_1_0, search8_node_1_1, search8_node_1_2,
    search8_node_1_3, search8_node_1_4, search8_node_1_5]
private theorem search8_2_0 :
    (search edge8 27 4 [g0, g2, g0, g0] && search edge8 27 4 [g0, g2, g0, g1] &&
      search edge8 27 4 [g0, g2, g0, g2]) &&
      (search edge8 27 4 [g0, g2, g0, g3] && search edge8 27 4 [g0, g2, g0, g4] &&
        search edge8 27 4 [g0, g2, g0, g5]) = true := by
  decide +kernel
private theorem search8_node_2_0 :
    search edge8 27 5 [g0, g2, g0] = true :=
  search_and6 edge8 27 4 [g0, g2, g0] search8_2_0

private theorem search8_2_1 :
    (search edge8 27 4 [g0, g2, g1, g0] && search edge8 27 4 [g0, g2, g1, g1] &&
      search edge8 27 4 [g0, g2, g1, g2]) &&
      (search edge8 27 4 [g0, g2, g1, g3] && search edge8 27 4 [g0, g2, g1, g4] &&
        search edge8 27 4 [g0, g2, g1, g5]) = true := by
  decide +kernel
private theorem search8_node_2_1 :
    search edge8 27 5 [g0, g2, g1] = true :=
  search_and6 edge8 27 4 [g0, g2, g1] search8_2_1

private theorem search8_2_2 :
    (search edge8 27 4 [g0, g2, g2, g0] && search edge8 27 4 [g0, g2, g2, g1] &&
      search edge8 27 4 [g0, g2, g2, g2]) &&
      (search edge8 27 4 [g0, g2, g2, g3] && search edge8 27 4 [g0, g2, g2, g4] &&
        search edge8 27 4 [g0, g2, g2, g5]) = true := by
  decide +kernel
private theorem search8_node_2_2 :
    search edge8 27 5 [g0, g2, g2] = true :=
  search_and6 edge8 27 4 [g0, g2, g2] search8_2_2

private theorem search8_2_3 :
    (search edge8 27 4 [g0, g2, g3, g0] && search edge8 27 4 [g0, g2, g3, g1] &&
      search edge8 27 4 [g0, g2, g3, g2]) &&
      (search edge8 27 4 [g0, g2, g3, g3] && search edge8 27 4 [g0, g2, g3, g4] &&
        search edge8 27 4 [g0, g2, g3, g5]) = true := by
  decide +kernel
private theorem search8_node_2_3 :
    search edge8 27 5 [g0, g2, g3] = true :=
  search_and6 edge8 27 4 [g0, g2, g3] search8_2_3

private theorem search8_2_4 :
    (search edge8 27 4 [g0, g2, g4, g0] && search edge8 27 4 [g0, g2, g4, g1] &&
      search edge8 27 4 [g0, g2, g4, g2]) &&
      (search edge8 27 4 [g0, g2, g4, g3] && search edge8 27 4 [g0, g2, g4, g4] &&
        search edge8 27 4 [g0, g2, g4, g5]) = true := by
  decide +kernel
private theorem search8_node_2_4 :
    search edge8 27 5 [g0, g2, g4] = true :=
  search_and6 edge8 27 4 [g0, g2, g4] search8_2_4

private theorem search8_2_5 :
    (search edge8 27 4 [g0, g2, g5, g0] && search edge8 27 4 [g0, g2, g5, g1] &&
      search edge8 27 4 [g0, g2, g5, g2]) &&
      (search edge8 27 4 [g0, g2, g5, g3] && search edge8 27 4 [g0, g2, g5, g4] &&
        search edge8 27 4 [g0, g2, g5, g5]) = true := by
  decide +kernel
private theorem search8_node_2_5 :
    search edge8 27 5 [g0, g2, g5] = true :=
  search_and6 edge8 27 4 [g0, g2, g5] search8_2_5

private theorem search8_mid_2 : search edge8 27 6 [g0, g2] = true := by
  apply search_and6 edge8 27 5 [g0, g2]
  simp [search8_node_2_0, search8_node_2_1, search8_node_2_2,
    search8_node_2_3, search8_node_2_4, search8_node_2_5]
private theorem search8_3_0 :
    (search edge8 27 4 [g0, g3, g0, g0] && search edge8 27 4 [g0, g3, g0, g1] &&
      search edge8 27 4 [g0, g3, g0, g2]) &&
      (search edge8 27 4 [g0, g3, g0, g3] && search edge8 27 4 [g0, g3, g0, g4] &&
        search edge8 27 4 [g0, g3, g0, g5]) = true := by
  decide +kernel
private theorem search8_node_3_0 :
    search edge8 27 5 [g0, g3, g0] = true :=
  search_and6 edge8 27 4 [g0, g3, g0] search8_3_0

private theorem search8_3_1 :
    (search edge8 27 4 [g0, g3, g1, g0] && search edge8 27 4 [g0, g3, g1, g1] &&
      search edge8 27 4 [g0, g3, g1, g2]) &&
      (search edge8 27 4 [g0, g3, g1, g3] && search edge8 27 4 [g0, g3, g1, g4] &&
        search edge8 27 4 [g0, g3, g1, g5]) = true := by
  decide +kernel
private theorem search8_node_3_1 :
    search edge8 27 5 [g0, g3, g1] = true :=
  search_and6 edge8 27 4 [g0, g3, g1] search8_3_1

private theorem search8_3_2 :
    (search edge8 27 4 [g0, g3, g2, g0] && search edge8 27 4 [g0, g3, g2, g1] &&
      search edge8 27 4 [g0, g3, g2, g2]) &&
      (search edge8 27 4 [g0, g3, g2, g3] && search edge8 27 4 [g0, g3, g2, g4] &&
        search edge8 27 4 [g0, g3, g2, g5]) = true := by
  decide +kernel
private theorem search8_node_3_2 :
    search edge8 27 5 [g0, g3, g2] = true :=
  search_and6 edge8 27 4 [g0, g3, g2] search8_3_2

private theorem search8_3_3 :
    (search edge8 27 4 [g0, g3, g3, g0] && search edge8 27 4 [g0, g3, g3, g1] &&
      search edge8 27 4 [g0, g3, g3, g2]) &&
      (search edge8 27 4 [g0, g3, g3, g3] && search edge8 27 4 [g0, g3, g3, g4] &&
        search edge8 27 4 [g0, g3, g3, g5]) = true := by
  decide +kernel
private theorem search8_node_3_3 :
    search edge8 27 5 [g0, g3, g3] = true :=
  search_and6 edge8 27 4 [g0, g3, g3] search8_3_3

private theorem search8_3_4 :
    (search edge8 27 4 [g0, g3, g4, g0] && search edge8 27 4 [g0, g3, g4, g1] &&
      search edge8 27 4 [g0, g3, g4, g2]) &&
      (search edge8 27 4 [g0, g3, g4, g3] && search edge8 27 4 [g0, g3, g4, g4] &&
        search edge8 27 4 [g0, g3, g4, g5]) = true := by
  decide +kernel
private theorem search8_node_3_4 :
    search edge8 27 5 [g0, g3, g4] = true :=
  search_and6 edge8 27 4 [g0, g3, g4] search8_3_4

private theorem search8_3_5 :
    (search edge8 27 4 [g0, g3, g5, g0] && search edge8 27 4 [g0, g3, g5, g1] &&
      search edge8 27 4 [g0, g3, g5, g2]) &&
      (search edge8 27 4 [g0, g3, g5, g3] && search edge8 27 4 [g0, g3, g5, g4] &&
        search edge8 27 4 [g0, g3, g5, g5]) = true := by
  decide +kernel
private theorem search8_node_3_5 :
    search edge8 27 5 [g0, g3, g5] = true :=
  search_and6 edge8 27 4 [g0, g3, g5] search8_3_5

private theorem search8_mid_3 : search edge8 27 6 [g0, g3] = true := by
  apply search_and6 edge8 27 5 [g0, g3]
  simp [search8_node_3_0, search8_node_3_1, search8_node_3_2,
    search8_node_3_3, search8_node_3_4, search8_node_3_5]
private theorem search8_4_0 :
    (search edge8 27 4 [g0, g4, g0, g0] && search edge8 27 4 [g0, g4, g0, g1] &&
      search edge8 27 4 [g0, g4, g0, g2]) &&
      (search edge8 27 4 [g0, g4, g0, g3] && search edge8 27 4 [g0, g4, g0, g4] &&
        search edge8 27 4 [g0, g4, g0, g5]) = true := by
  decide +kernel
private theorem search8_node_4_0 :
    search edge8 27 5 [g0, g4, g0] = true :=
  search_and6 edge8 27 4 [g0, g4, g0] search8_4_0

private theorem search8_4_1 :
    (search edge8 27 4 [g0, g4, g1, g0] && search edge8 27 4 [g0, g4, g1, g1] &&
      search edge8 27 4 [g0, g4, g1, g2]) &&
      (search edge8 27 4 [g0, g4, g1, g3] && search edge8 27 4 [g0, g4, g1, g4] &&
        search edge8 27 4 [g0, g4, g1, g5]) = true := by
  decide +kernel
private theorem search8_node_4_1 :
    search edge8 27 5 [g0, g4, g1] = true :=
  search_and6 edge8 27 4 [g0, g4, g1] search8_4_1

private theorem search8_4_2 :
    (search edge8 27 4 [g0, g4, g2, g0] && search edge8 27 4 [g0, g4, g2, g1] &&
      search edge8 27 4 [g0, g4, g2, g2]) &&
      (search edge8 27 4 [g0, g4, g2, g3] && search edge8 27 4 [g0, g4, g2, g4] &&
        search edge8 27 4 [g0, g4, g2, g5]) = true := by
  decide +kernel
private theorem search8_node_4_2 :
    search edge8 27 5 [g0, g4, g2] = true :=
  search_and6 edge8 27 4 [g0, g4, g2] search8_4_2

private theorem search8_4_3 :
    (search edge8 27 4 [g0, g4, g3, g0] && search edge8 27 4 [g0, g4, g3, g1] &&
      search edge8 27 4 [g0, g4, g3, g2]) &&
      (search edge8 27 4 [g0, g4, g3, g3] && search edge8 27 4 [g0, g4, g3, g4] &&
        search edge8 27 4 [g0, g4, g3, g5]) = true := by
  decide +kernel
private theorem search8_node_4_3 :
    search edge8 27 5 [g0, g4, g3] = true :=
  search_and6 edge8 27 4 [g0, g4, g3] search8_4_3

private theorem search8_4_4 :
    (search edge8 27 4 [g0, g4, g4, g0] && search edge8 27 4 [g0, g4, g4, g1] &&
      search edge8 27 4 [g0, g4, g4, g2]) &&
      (search edge8 27 4 [g0, g4, g4, g3] && search edge8 27 4 [g0, g4, g4, g4] &&
        search edge8 27 4 [g0, g4, g4, g5]) = true := by
  decide +kernel
private theorem search8_node_4_4 :
    search edge8 27 5 [g0, g4, g4] = true :=
  search_and6 edge8 27 4 [g0, g4, g4] search8_4_4

private theorem search8_4_5 :
    (search edge8 27 4 [g0, g4, g5, g0] && search edge8 27 4 [g0, g4, g5, g1] &&
      search edge8 27 4 [g0, g4, g5, g2]) &&
      (search edge8 27 4 [g0, g4, g5, g3] && search edge8 27 4 [g0, g4, g5, g4] &&
        search edge8 27 4 [g0, g4, g5, g5]) = true := by
  decide +kernel
private theorem search8_node_4_5 :
    search edge8 27 5 [g0, g4, g5] = true :=
  search_and6 edge8 27 4 [g0, g4, g5] search8_4_5

private theorem search8_mid_4 : search edge8 27 6 [g0, g4] = true := by
  apply search_and6 edge8 27 5 [g0, g4]
  simp [search8_node_4_0, search8_node_4_1, search8_node_4_2,
    search8_node_4_3, search8_node_4_4, search8_node_4_5]
private theorem search8_5_0 :
    (search edge8 27 4 [g0, g5, g0, g0] && search edge8 27 4 [g0, g5, g0, g1] &&
      search edge8 27 4 [g0, g5, g0, g2]) &&
      (search edge8 27 4 [g0, g5, g0, g3] && search edge8 27 4 [g0, g5, g0, g4] &&
        search edge8 27 4 [g0, g5, g0, g5]) = true := by
  decide +kernel
private theorem search8_node_5_0 :
    search edge8 27 5 [g0, g5, g0] = true :=
  search_and6 edge8 27 4 [g0, g5, g0] search8_5_0

private theorem search8_5_1 :
    (search edge8 27 4 [g0, g5, g1, g0] && search edge8 27 4 [g0, g5, g1, g1] &&
      search edge8 27 4 [g0, g5, g1, g2]) &&
      (search edge8 27 4 [g0, g5, g1, g3] && search edge8 27 4 [g0, g5, g1, g4] &&
        search edge8 27 4 [g0, g5, g1, g5]) = true := by
  decide +kernel
private theorem search8_node_5_1 :
    search edge8 27 5 [g0, g5, g1] = true :=
  search_and6 edge8 27 4 [g0, g5, g1] search8_5_1

private theorem search8_5_2 :
    (search edge8 27 4 [g0, g5, g2, g0] && search edge8 27 4 [g0, g5, g2, g1] &&
      search edge8 27 4 [g0, g5, g2, g2]) &&
      (search edge8 27 4 [g0, g5, g2, g3] && search edge8 27 4 [g0, g5, g2, g4] &&
        search edge8 27 4 [g0, g5, g2, g5]) = true := by
  decide +kernel
private theorem search8_node_5_2 :
    search edge8 27 5 [g0, g5, g2] = true :=
  search_and6 edge8 27 4 [g0, g5, g2] search8_5_2

private theorem search8_5_3 :
    (search edge8 27 4 [g0, g5, g3, g0] && search edge8 27 4 [g0, g5, g3, g1] &&
      search edge8 27 4 [g0, g5, g3, g2]) &&
      (search edge8 27 4 [g0, g5, g3, g3] && search edge8 27 4 [g0, g5, g3, g4] &&
        search edge8 27 4 [g0, g5, g3, g5]) = true := by
  decide +kernel
private theorem search8_node_5_3 :
    search edge8 27 5 [g0, g5, g3] = true :=
  search_and6 edge8 27 4 [g0, g5, g3] search8_5_3

private theorem search8_5_4 :
    (search edge8 27 4 [g0, g5, g4, g0] && search edge8 27 4 [g0, g5, g4, g1] &&
      search edge8 27 4 [g0, g5, g4, g2]) &&
      (search edge8 27 4 [g0, g5, g4, g3] && search edge8 27 4 [g0, g5, g4, g4] &&
        search edge8 27 4 [g0, g5, g4, g5]) = true := by
  decide +kernel
private theorem search8_node_5_4 :
    search edge8 27 5 [g0, g5, g4] = true :=
  search_and6 edge8 27 4 [g0, g5, g4] search8_5_4

private theorem search8_5_5 :
    (search edge8 27 4 [g0, g5, g5, g0] && search edge8 27 4 [g0, g5, g5, g1] &&
      search edge8 27 4 [g0, g5, g5, g2]) &&
      (search edge8 27 4 [g0, g5, g5, g3] && search edge8 27 4 [g0, g5, g5, g4] &&
        search edge8 27 4 [g0, g5, g5, g5]) = true := by
  decide +kernel
private theorem search8_node_5_5 :
    search edge8 27 5 [g0, g5, g5] = true :=
  search_and6 edge8 27 4 [g0, g5, g5] search8_5_5

private theorem search8_mid_5 : search edge8 27 6 [g0, g5] = true := by
  apply search_and6 edge8 27 5 [g0, g5]
  simp [search8_node_5_0, search8_node_5_1, search8_node_5_2,
    search8_node_5_3, search8_node_5_4, search8_node_5_5]
private theorem search8_root : search edge8 27 7 [g0] = true := by
  apply search_and6 edge8 27 6 [g0]
  simp [search8_mid_0, search8_mid_1, search8_mid_2, search8_mid_3, search8_mid_4, search8_mid_5]

private theorem witness5_le_cost (β : Fin 5 → Perm (Fin 3)) (hβ : β 0 = 1) :
    (6 : ℝ) ≤ witness5.cost (movedNorm (Fin 3)) β := by
  rw [witness5]; exact le_cost_of_search edge5 6 search5_root β hβ

private theorem witness6_le_cost (β : Fin 6 → Perm (Fin 3)) (hβ : β 0 = 1) :
    (18 : ℝ) ≤ witness6.cost (movedNorm (Fin 3)) β := by
  rw [witness6]; exact le_cost_of_search edge6 18 search6_root β hβ

private theorem witness7_le_cost (β : Fin 7 → Perm (Fin 3)) (hβ : β 0 = 1) :
    (12 : ℝ) ≤ witness7.cost (movedNorm (Fin 3)) β := by
  rw [witness7]; exact le_cost_of_search edge7 12 search7_root β hβ

private theorem witness8_le_cost (β : Fin 8 → Perm (Fin 3)) (hβ : β 0 = 1) :
    (27 : ℝ) ≤ witness8.cost (movedNorm (Fin 3)) β := by
  rw [witness8]; exact le_cost_of_search edge8 27 search8_root β hβ

/-- Every gauge costs at least `6` against `witness5`, and the identity gauge costs `6`, so the
gauge distance is `6`. -/
theorem witness5_gaugeDist : witness5.gaugeDist (movedNorm (Fin 3)) = 6 := by
  refine le_antisymm ((witness5.gaugeDist_le_cost _ (fun _ => 1)).trans_eq witness5_cost_one) ?_
  rw [Cochain.le_gaugeDist_iff_apply_eq_one isConjInvariant_movedNorm witness5 0]
  intro β hβ
  exact witness5_le_cost β hβ

/-- Every gauge costs at least `18` against `witness6`, and the identity gauge costs `18`. -/
theorem witness6_gaugeDist : witness6.gaugeDist (movedNorm (Fin 3)) = 18 := by
  refine le_antisymm ((witness6.gaugeDist_le_cost _ (fun _ => 1)).trans_eq witness6_cost_one) ?_
  rw [Cochain.le_gaugeDist_iff_apply_eq_one isConjInvariant_movedNorm witness6 0]
  intro β hβ
  exact witness6_le_cost β hβ

/-- Every gauge costs at least `12` against `witness7`, and the identity gauge costs `12`. -/
theorem witness7_gaugeDist : witness7.gaugeDist (movedNorm (Fin 3)) = 12 := by
  refine le_antisymm ((witness7.gaugeDist_le_cost _ (fun _ => 1)).trans_eq witness7_cost_one) ?_
  rw [Cochain.le_gaugeDist_iff_apply_eq_one isConjInvariant_movedNorm witness7 0]
  intro β hβ
  exact witness7_le_cost β hβ

/-- Every gauge costs at least `27` against `witness8`, and the identity gauge costs `27`. -/
theorem witness8_gaugeDist : witness8.gaugeDist (movedNorm (Fin 3)) = 27 := by
  refine le_antisymm ((witness8.gaugeDist_le_cost _ (fun _ => 1)).trans_eq witness8_cost_one) ?_
  rw [Cochain.le_gaugeDist_iff_apply_eq_one isConjInvariant_movedNorm witness8 0]
  intro β hβ
  exact witness8_le_cost β hβ

/-- `witness5` attains the constant: `defect / gaugeDist = 5 / 3 = h1`. -/
theorem witness5_attains :
    witness5.defect (movedNorm (Fin 3)) / witness5.gaugeDist (movedNorm (Fin 3)) =
      h1 (complete (Fin 5)) (movedNorm (Fin 3)) := by
  rw [witness5_defect, witness5_gaugeDist, h1_complete_fin_five]
  norm_num

/-- `witness6` attains the constant: `defect / gaugeDist = 6 / 3 = h1`. -/
theorem witness6_attains :
    witness6.defect (movedNorm (Fin 3)) / witness6.gaugeDist (movedNorm (Fin 3)) =
      h1 (complete (Fin 6)) (movedNorm (Fin 3)) := by
  rw [witness6_defect, witness6_gaugeDist, h1_complete_fin_six]
  norm_num

/-- `witness7` attains the constant: `defect / gaugeDist = 7 / 3 = h1`. -/
theorem witness7_attains :
    witness7.defect (movedNorm (Fin 3)) / witness7.gaugeDist (movedNorm (Fin 3)) =
      h1 (complete (Fin 7)) (movedNorm (Fin 3)) := by
  rw [witness7_defect, witness7_gaugeDist, h1_complete_fin_seven]
  norm_num

/-- `witness8` attains the constant: `defect / gaugeDist = 8 / 3 = h1`. -/
theorem witness8_attains :
    witness8.defect (movedNorm (Fin 3)) / witness8.gaugeDist (movedNorm (Fin 3)) =
      h1 (complete (Fin 8)) (movedNorm (Fin 3)) := by
  rw [witness8_defect, witness8_gaugeDist, h1_complete_fin_eight]
  norm_num

/-- At eight vertices the replicated seed `(64, 24)` and `witness8` `(72, 27)` both have ratio
`8 / 3`. -/
theorem replicatedSeed_two_and_witness8 :
    (Sym3.replicatedSeed 2).defect (movedNorm (Fin 3)) = 64 ∧
      (Sym3.replicatedSeed 2).gaugeDist (movedNorm (Fin 3)) = 24 ∧
      witness8.defect (movedNorm (Fin 3)) = 72 ∧
      witness8.gaugeDist (movedNorm (Fin 3)) = 27 ∧
      (Sym3.replicatedSeed 2).defect (movedNorm (Fin 3)) /
          (Sym3.replicatedSeed 2).gaugeDist (movedNorm (Fin 3)) = 8 / 3 ∧
      witness8.defect (movedNorm (Fin 3)) / witness8.gaugeDist (movedNorm (Fin 3)) = 8 / 3 := by
  refine ⟨Sym3.replicatedSeed_defect_two, Sym3.replicatedSeed_gaugeDist_two, witness8_defect,
    witness8_gaugeDist, Sym3.replicatedSeed_ratio_two, ?_⟩
  rw [witness8_defect, witness8_gaugeDist]
  norm_num

end TauCeti
