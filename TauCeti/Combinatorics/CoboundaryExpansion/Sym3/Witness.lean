/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Complete
import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.MovedNorm
import TauCeti.GroupTheory.Perm.FinThree.Basic
import Mathlib.Data.List.GetD
import TauCeti.Algebra.BigOperators.Finset.Filter

/-!
# Explicit `Sym(3)` witnesses on five to eight vertices

`h1_complete_movedNorm_fin_three` in `Sym3/Complete.lean` gives
`h1 (complete V) (movedNorm (Fin 3)) = card V / 3` for every `3 ≤ card V`.
Beasley, Theorem 8 (the moved-point count, k/3 for every k ≥ 4) is that statement for
`4 ≤ card V`; the Lean theorem also covers `card V = 3`.
Beasley, Corollary 7, is the replicated-seed ratio in that module:
`defect_replicatedSeed`, `gaugeDist_replicatedSeed` and
`defect_div_gaugeDist_replicatedSeedOfCardEq`.

`Sym3.witness5`, `Sym3.witness6`, `Sym3.witness7` and `Sym3.witness8` are the Appendix A cochains,
each `Cochain.ofLt` of `Sym3.edge5` through `Sym3.edge8`. `defect_witness*` is the moved-point
defect and `cost_one_witness*` is the identity-gauge cost. `gaugeDist_witness*` is the gauge
distance, equal to that cost (`6`, `18`, `12` and `27`) and attained by the identity gauge.
`defect_div_gaugeDist_witness*_eq_h1` is `defect / gaugeDist = h1`.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792, Corollary 7, Theorem 4 and Theorem 8,
  with Appendix A.
* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136, Definition 3.2.
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: `w5`, `w6`, `w7` and `w8` in `CoboundaryK3/Basic.lean`.
-/

public section

open Finset Equiv Equiv.Perm

namespace TauCeti

open TwoComplex

namespace Sym3

/-! ## Explicit witnesses for `k = 5, …, 8` -/

/-- Non-identity edges of the `k = 5` witness: `(0, 1)`, `(1, 2)` and `(2, 3)` carry `swap 0 1`. -/
def edge5 (u v : Fin 5) : Perm (Fin 3) :=
  if u = 0 ∧ v = 1 then swap 0 1 else if u = 1 ∧ v = 2 then swap 0 1
  else if u = 2 ∧ v = 3 then swap 0 1 else 1

/-- `edge5` sends `(0, 1)`, `(1, 2)` and `(2, 3)` to `swap 0 1`, and every other pair to `1`. -/
theorem edge5_apply (u v : Fin 5) : edge5 u v =
    if u = 0 ∧ v = 1 then swap 0 1 else if u = 1 ∧ v = 2 then swap 0 1
    else if u = 2 ∧ v = 3 then swap 0 1 else 1 :=
  (rfl)

/-- Non-identity edges of the `k = 6` witness: `(0, 1)` and `(1, 3)` carry `finRotate 3`, and
`(0, 3)`, `(0, 4)`, `(1, 5)` and `(4, 5)` carry its inverse. -/
def edge6 (u v : Fin 6) : Perm (Fin 3) :=
  if u = 0 ∧ v = 1 then finRotate 3 else if u = 1 ∧ v = 3 then finRotate 3
  else if u = 0 ∧ v = 3 then (finRotate 3)⁻¹ else if u = 0 ∧ v = 4 then (finRotate 3)⁻¹
  else if u = 1 ∧ v = 5 then (finRotate 3)⁻¹ else if u = 4 ∧ v = 5 then (finRotate 3)⁻¹ else 1

/-- `edge6` is the Appendix A labelling on `Fin 6`: two edges carry `finRotate 3` and four carry
its inverse. -/
theorem edge6_apply (u v : Fin 6) : edge6 u v =
    if u = 0 ∧ v = 1 then finRotate 3 else if u = 1 ∧ v = 3 then finRotate 3
    else if u = 0 ∧ v = 3 then (finRotate 3)⁻¹ else if u = 0 ∧ v = 4 then (finRotate 3)⁻¹
    else if u = 1 ∧ v = 5 then (finRotate 3)⁻¹ else if u = 4 ∧ v = 5 then (finRotate 3)⁻¹
    else 1 :=
  (rfl)

/-- Non-identity edges of the `k = 7` witness: `(0, 1)`, `(0, 3)`, `(0, 4)`, `(1, 2)`, `(1, 5)`
and `(2, 3)` carry `swap 0 1`. -/
def edge7 (u v : Fin 7) : Perm (Fin 3) :=
  if u = 0 ∧ v = 1 then swap 0 1 else if u = 0 ∧ v = 3 then swap 0 1
  else if u = 0 ∧ v = 4 then swap 0 1 else if u = 1 ∧ v = 2 then swap 0 1
  else if u = 1 ∧ v = 5 then swap 0 1 else if u = 2 ∧ v = 3 then swap 0 1 else 1

/-- `edge7` sends the six listed pairs to `swap 0 1` and every other pair to `1`. -/
theorem edge7_apply (u v : Fin 7) : edge7 u v =
    if u = 0 ∧ v = 1 then swap 0 1 else if u = 0 ∧ v = 3 then swap 0 1
    else if u = 0 ∧ v = 4 then swap 0 1 else if u = 1 ∧ v = 2 then swap 0 1
    else if u = 1 ∧ v = 5 then swap 0 1 else if u = 2 ∧ v = 3 then swap 0 1 else 1 :=
  (rfl)

/-- Non-identity edges of the `k = 8` witness, in four blocks: `(0, 1)`, `(0, 7)`, `(1, 2)`,
`(2, 5)` and `(2, 7)` carry `swap 1 2`; `(1, 3)`, `(1, 4)`, `(1, 6)` and `(3, 7)` carry
`swap 0 1`; `(0, 4)`, `(2, 3)` and `(2, 4)` carry `swap 0 2`; `(4, 7)` carries `(finRotate 3)⁻¹`. -/
def edge8 (u v : Fin 8) : Perm (Fin 3) :=
  if u = 0 ∧ v = 1 then swap 1 2 else if u = 0 ∧ v = 7 then swap 1 2
  else if u = 1 ∧ v = 2 then swap 1 2 else if u = 2 ∧ v = 5 then swap 1 2
  else if u = 2 ∧ v = 7 then swap 1 2 else if u = 1 ∧ v = 3 then swap 0 1
  else if u = 1 ∧ v = 4 then swap 0 1 else if u = 1 ∧ v = 6 then swap 0 1
  else if u = 3 ∧ v = 7 then swap 0 1 else if u = 0 ∧ v = 4 then swap 0 2
  else if u = 2 ∧ v = 3 then swap 0 2 else if u = 2 ∧ v = 4 then swap 0 2
  else if u = 4 ∧ v = 7 then (finRotate 3)⁻¹ else 1

/-- `edge8` is the thirteen-edge Appendix A labelling on `Fin 8`. -/
theorem edge8_apply (u v : Fin 8) : edge8 u v =
    if u = 0 ∧ v = 1 then swap 1 2 else if u = 0 ∧ v = 7 then swap 1 2
    else if u = 1 ∧ v = 2 then swap 1 2 else if u = 2 ∧ v = 5 then swap 1 2
    else if u = 2 ∧ v = 7 then swap 1 2 else if u = 1 ∧ v = 3 then swap 0 1
    else if u = 1 ∧ v = 4 then swap 0 1 else if u = 1 ∧ v = 6 then swap 0 1
    else if u = 3 ∧ v = 7 then swap 0 1 else if u = 0 ∧ v = 4 then swap 0 2
    else if u = 2 ∧ v = 3 then swap 0 2 else if u = 2 ∧ v = 4 then swap 0 2
    else if u = 4 ∧ v = 7 then (finRotate 3)⁻¹ else 1 :=
  (rfl)


/-- The Beasley Appendix A witness on `Fin 5`: `(0, 1)`, `(1, 2)` and `(2, 3)` carry `swap 0 1`,
and every other `u < v` carries `1`. -/
noncomputable def witness5 : Cochain (complete (Fin 5)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 5)) edge5

/-- `witness5` is the `Cochain.ofLt` cochain of `edge5`. -/
theorem witness5_def : witness5 = Cochain.ofLt (complete (Fin 5)) edge5 := (rfl)

/-- The Beasley Appendix A witness on `Fin 6`: `(0, 1)` and `(1, 3)` carry `finRotate 3`,
`(0, 3)`, `(0, 4)`, `(1, 5)` and `(4, 5)` carry its inverse, and every other `u < v` carries `1`. -/
noncomputable def witness6 : Cochain (complete (Fin 6)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 6)) edge6

/-- `witness6` is the `Cochain.ofLt` cochain of `edge6`. -/
theorem witness6_def : witness6 = Cochain.ofLt (complete (Fin 6)) edge6 := (rfl)

/-- The Beasley Appendix A witness on `Fin 7`: `(0, 1)`, `(0, 3)`, `(0, 4)`, `(1, 2)`, `(1, 5)`
and `(2, 3)` carry `swap 0 1`, and every other `u < v` carries `1`. -/
noncomputable def witness7 : Cochain (complete (Fin 7)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 7)) edge7

/-- `witness7` is the `Cochain.ofLt` cochain of `edge7`. -/
theorem witness7_def : witness7 = Cochain.ofLt (complete (Fin 7)) edge7 := (rfl)

/-- The Beasley Appendix A witness on `Fin 8`: the thirteen non-identity edges of `edge8`, and `1`
on every other `u < v`. -/
noncomputable def witness8 : Cochain (complete (Fin 8)) (Perm (Fin 3)) :=
  Cochain.ofLt (complete (Fin 8)) edge8

/-- `witness8` is the `Cochain.ofLt` cochain of `edge8`. -/
theorem witness8_def : witness8 = Cochain.ofLt (complete (Fin 8)) edge8 := (rfl)

/-- `witness5` has moved-point defect `10`. -/
theorem defect_witness5 : witness5.defect (movedNorm (Fin 3)) = 10 := by
  rw [witness5, Cochain.defect_ofLt_complete_movedNorm]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 5 × Fin 5 × Fin 5 =>
        p.1 < p.2.1 ∧ p.2.1 < p.2.2),
      (edge5 p.1 p.2.1 * edge5 p.2.1 p.2.2 * (edge5 p.1 p.2.2)⁻¹).support.card = 10)

/-- `witness6` has moved-point defect `36`. -/
theorem defect_witness6 : witness6.defect (movedNorm (Fin 3)) = 36 := by
  rw [witness6, Cochain.defect_ofLt_complete_movedNorm]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 6 × Fin 6 × Fin 6 =>
        p.1 < p.2.1 ∧ p.2.1 < p.2.2),
      (edge6 p.1 p.2.1 * edge6 p.2.1 p.2.2 * (edge6 p.1 p.2.2)⁻¹).support.card = 36)

/-- `witness7` has moved-point defect `28`. -/
theorem defect_witness7 : witness7.defect (movedNorm (Fin 3)) = 28 := by
  rw [witness7, Cochain.defect_ofLt_complete_movedNorm]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 7 × Fin 7 × Fin 7 =>
        p.1 < p.2.1 ∧ p.2.1 < p.2.2),
      (edge7 p.1 p.2.1 * edge7 p.2.1 p.2.2 * (edge7 p.1 p.2.2)⁻¹).support.card = 28)

/-- `witness8` has moved-point defect `72`. -/
theorem defect_witness8 : witness8.defect (movedNorm (Fin 3)) = 72 := by
  rw [witness8, Cochain.defect_ofLt_complete_movedNorm]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 8 × Fin 8 × Fin 8 =>
        p.1 < p.2.1 ∧ p.2.1 < p.2.2),
      (edge8 p.1 p.2.1 * edge8 p.2.1 p.2.2 * (edge8 p.1 p.2.2)⁻¹).support.card = 72)

/-- The identity gauge costs `6` against `witness5`. -/
theorem cost_one_witness5 : witness5.cost (movedNorm (Fin 3)) (fun _ => 1) = 6 := by
  rw [witness5, Cochain.cost_ofLt_complete_movedNorm]
  simp only [inv_one, one_mul, mul_one]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 5 × Fin 5 => p.1 < p.2),
      (edge5 p.1 p.2).support.card = 6)

/-- The identity gauge costs `18` against `witness6`. -/
theorem cost_one_witness6 : witness6.cost (movedNorm (Fin 3)) (fun _ => 1) = 18 := by
  rw [witness6, Cochain.cost_ofLt_complete_movedNorm]
  simp only [inv_one, one_mul, mul_one]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2),
      (edge6 p.1 p.2).support.card = 18)

/-- The identity gauge costs `12` against `witness7`. -/
theorem cost_one_witness7 : witness7.cost (movedNorm (Fin 3)) (fun _ => 1) = 12 := by
  rw [witness7, Cochain.cost_ofLt_complete_movedNorm]
  simp only [inv_one, one_mul, mul_one]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 7 × Fin 7 => p.1 < p.2),
      (edge7 p.1 p.2).support.card = 12)

/-- The identity gauge costs `27` against `witness8`. -/
theorem cost_one_witness8 : witness8.cost (movedNorm (Fin 3)) (fun _ => 1) = 27 := by
  rw [witness8, Cochain.cost_ofLt_complete_movedNorm]
  simp only [inv_one, one_mul, mul_one]
  exact_mod_cast
    (by decide +kernel : ∑ p ∈ univ.filter (fun p : Fin 8 × Fin 8 => p.1 < p.2),
      (edge8 p.1 p.2).support.card = 27)

end Sym3

namespace Sym3

/-! ## Gauge distance of the four witnesses

`gaugeDist_witness*` equates the gauge distance with the identity-gauge cost. The matching lower
bound searches gauges pinned at `0`, one element of `sym3Elems` at a time. At `k = 8` one
declaration can afford only one six-leaf `decide` within the default heartbeat budget, so that
tree is checked node by node. -/

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


private theorem lt_of_mem_edgeList {k : ℕ} {e : Fin k × Fin k} (h : e ∈ edgeList k) :
    e.1.val < e.2.val := by
  simp only [edgeList, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨u, _, v, hv, rfl⟩ := h
  exact hv.2

private theorem pcost_mono {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3))
    (l rest : List (Perm (Fin 3))) :
    pcost α l ≤ pcost α (l ++ rest) := by
  apply List.sum_le_sum
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


private theorem sum_edgeList {k : ℕ} (f : Fin k × Fin k → ℕ) :
    ((edgeList k).map f).sum = ∑ p ∈ univ.filter fun p : Fin k × Fin k => p.1 < p.2, f p := by
  rw [← univ_product_univ, sum_filter_product univ univ (· < ·) fun u v => f (u, v)]
  have row (u : Fin k) :
      (((List.finRange k).filter fun v => decide (u < v)).map fun v => f (u, v)).sum =
        ∑ v ∈ univ.filter (u < ·), f (u, v) := by
    simpa [List.toFinset_filter] using
      (List.sum_toFinset (fun v => f (u, v)) ((List.nodup_finRange k).filter
        (fun v => decide (u < v)))).symm
  calc
    ((edgeList k).map f).sum =
        ((List.finRange k).map fun u => ∑ v ∈ univ.filter (u < ·), f (u, v)).sum := by
      simp [edgeList, List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def, row]
    _ = _ := by
      simpa using
        (List.sum_toFinset (fun u : Fin k => ∑ v ∈ univ.filter (u < ·), f (u, v))
          (List.nodup_finRange k)).symm

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


/-- The gauge prefixes of length `n` over `sym3Elems`. -/
private def prefixes : ℕ → List (List (Perm (Fin 3)))
  | 0 => [[]]
  | n + 1 => sym3Elems.flatMap fun a => (prefixes n).map (a :: ·)

/-- A search with fuel `f + n` succeeds once its extensions by every length-`n` prefix succeed with
fuel `f`. -/
private theorem search_of_prefixes {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (D f : ℕ) :
    ∀ (n : ℕ) (l : List (Perm (Fin 3))),
      ((prefixes n).all fun p => search α D f (l ++ p)) = true → search α D (f + n) l = true
  | 0, l, h => by simpa [prefixes] using h
  | n + 1, l, h => by
    apply search_step α D (f + n) l
    intro a ha
    apply search_of_prefixes α D f n (l ++ [a])
    simp only [prefixes, List.all_eq_true, List.mem_flatMap, List.mem_map] at h ⊢
    intro p hp
    simpa using h (a :: p) ⟨a, ha, p, hp, rfl⟩

private theorem le_cost_of_search {m : ℕ}
    (α : Fin (m + 1) → Fin (m + 1) → Perm (Fin 3)) (D : ℕ)
    (h : search α D m [g0] = true) (β : Fin (m + 1) → Perm (Fin 3)) (hβ : β 0 = 1) :
    (D : ℝ) ≤ (Cochain.ofLt (complete (Fin (m + 1))) α).cost (movedNorm (Fin 3)) β := by
  have hs := search_sound α D m [g0] h (List.ofFn fun i : Fin m => β i.succ) (by simp)
  have he : List.ofFn β = [g0] ++ List.ofFn fun i : Fin m => β i.succ := by
    rw [List.ofFn_succ, hβ, g0, ← List.singleton_append]
  rw [← he] at hs
  rw [Cochain.cost_ofLt_complete_movedNorm]
  have hsum := pcost_ofFn α β
  simp only [movedFast_eq] at hsum
  rw [hsum] at hs
  exact_mod_cast hs


private theorem search5_root : search edge5 6 4 [g0] = true := by
  decide +kernel

private theorem search6_root : search edge6 18 5 [g0] = true :=
  search_of_prefixes edge6 18 4 1 [g0] (by decide +kernel)

/-- One step of the gauge search: the six extensions by `sym3Elems` give fuel `f + 1`. -/
private theorem search_step_of_six {k : ℕ} (α : Fin k → Fin k → Perm (Fin 3)) (D f : ℕ)
    (l : List (Perm (Fin 3)))
    (h0 : search α D f (l ++ [g0]) = true) (h1 : search α D f (l ++ [g1]) = true)
    (h2 : search α D f (l ++ [g2]) = true) (h3 : search α D f (l ++ [g3]) = true)
    (h4 : search α D f (l ++ [g4]) = true) (h5 : search α D f (l ++ [g5]) = true) :
    search α D (f + 1) l = true := by
  refine search_step α D f l fun a ha => ?_
  simp only [sym3Elems, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

private theorem search7_root : search edge7 12 6 [g0] = true :=
  search_step_of_six edge7 12 5 [g0]
    (search_of_prefixes edge7 12 4 1 [g0, g0] (by decide +kernel))
    (search_of_prefixes edge7 12 4 1 [g0, g1] (by decide +kernel))
    (search_of_prefixes edge7 12 4 1 [g0, g2] (by decide +kernel))
    (search_of_prefixes edge7 12 4 1 [g0, g3] (by decide +kernel))
    (search_of_prefixes edge7 12 4 1 [g0, g4] (by decide +kernel))
    (search_of_prefixes edge7 12 4 1 [g0, g5] (by decide +kernel))

/-! At `k = 8` each node below is one `decide`. `search_step_of_six` assembles them. -/

private theorem search8_node_0_0 : search edge8 27 5 [g0, g0, g0] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_0_1 : search edge8 27 5 [g0, g0, g1] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_0_2 : search edge8 27 5 [g0, g0, g2] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_0_3 : search edge8 27 5 [g0, g0, g3] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_0_4 : search edge8 27 5 [g0, g0, g4] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_0_5 : search edge8 27 5 [g0, g0, g5] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_1_0 : search edge8 27 5 [g0, g1, g0] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_1_1 : search edge8 27 5 [g0, g1, g1] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_1_2 : search edge8 27 5 [g0, g1, g2] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_1_3 : search edge8 27 5 [g0, g1, g3] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_1_4 : search edge8 27 5 [g0, g1, g4] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_1_5 : search edge8 27 5 [g0, g1, g5] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_2_0 : search edge8 27 5 [g0, g2, g0] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_2_1 : search edge8 27 5 [g0, g2, g1] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_2_2 : search edge8 27 5 [g0, g2, g2] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_2_3 : search edge8 27 5 [g0, g2, g3] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_2_4 : search edge8 27 5 [g0, g2, g4] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_2_5 : search edge8 27 5 [g0, g2, g5] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_3_0 : search edge8 27 5 [g0, g3, g0] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_3_1 : search edge8 27 5 [g0, g3, g1] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_3_2 : search edge8 27 5 [g0, g3, g2] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_3_3 : search edge8 27 5 [g0, g3, g3] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_3_4 : search edge8 27 5 [g0, g3, g4] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_3_5 : search edge8 27 5 [g0, g3, g5] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_4_0 : search edge8 27 5 [g0, g4, g0] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_4_1 : search edge8 27 5 [g0, g4, g1] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_4_2 : search edge8 27 5 [g0, g4, g2] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_4_3 : search edge8 27 5 [g0, g4, g3] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_4_4 : search edge8 27 5 [g0, g4, g4] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_4_5 : search edge8 27 5 [g0, g4, g5] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_5_0 : search edge8 27 5 [g0, g5, g0] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_5_1 : search edge8 27 5 [g0, g5, g1] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_5_2 : search edge8 27 5 [g0, g5, g2] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_5_3 : search edge8 27 5 [g0, g5, g3] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_5_4 : search edge8 27 5 [g0, g5, g4] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_node_5_5 : search edge8 27 5 [g0, g5, g5] = true :=
  search_of_prefixes edge8 27 4 1 _ (by decide +kernel)

private theorem search8_mid_0 : search edge8 27 6 [g0, g0] = true :=
  search_step_of_six edge8 27 5 [g0, g0]
    search8_node_0_0 search8_node_0_1 search8_node_0_2
    search8_node_0_3 search8_node_0_4 search8_node_0_5

private theorem search8_mid_1 : search edge8 27 6 [g0, g1] = true :=
  search_step_of_six edge8 27 5 [g0, g1]
    search8_node_1_0 search8_node_1_1 search8_node_1_2
    search8_node_1_3 search8_node_1_4 search8_node_1_5

private theorem search8_mid_2 : search edge8 27 6 [g0, g2] = true :=
  search_step_of_six edge8 27 5 [g0, g2]
    search8_node_2_0 search8_node_2_1 search8_node_2_2
    search8_node_2_3 search8_node_2_4 search8_node_2_5

private theorem search8_mid_3 : search edge8 27 6 [g0, g3] = true :=
  search_step_of_six edge8 27 5 [g0, g3]
    search8_node_3_0 search8_node_3_1 search8_node_3_2
    search8_node_3_3 search8_node_3_4 search8_node_3_5

private theorem search8_mid_4 : search edge8 27 6 [g0, g4] = true :=
  search_step_of_six edge8 27 5 [g0, g4]
    search8_node_4_0 search8_node_4_1 search8_node_4_2
    search8_node_4_3 search8_node_4_4 search8_node_4_5

private theorem search8_mid_5 : search edge8 27 6 [g0, g5] = true :=
  search_step_of_six edge8 27 5 [g0, g5]
    search8_node_5_0 search8_node_5_1 search8_node_5_2
    search8_node_5_3 search8_node_5_4 search8_node_5_5

private theorem search8_root : search edge8 27 7 [g0] = true :=
  search_step_of_six edge8 27 6 [g0]
    search8_mid_0 search8_mid_1 search8_mid_2
    search8_mid_3 search8_mid_4 search8_mid_5

private theorem gaugeDist_ofLt_eq_of_search {m : ℕ}
    (α : Fin (m + 1) → Fin (m + 1) → Perm (Fin 3)) (D : ℕ)
    (hc : (Cochain.ofLt (complete _) α).cost (movedNorm (Fin 3)) (fun _ => 1) = D)
    (hs : search α D m [g0] = true) :
    (Cochain.ofLt (complete _) α).gaugeDist (movedNorm (Fin 3)) = D := by
  refine le_antisymm (((Cochain.ofLt (complete _) α).gaugeDist_le_cost _ _).trans_eq hc) ?_
  exact (Cochain.le_gaugeDist_iff_apply_eq_one isConjInvariant_movedNorm _ 0).mpr
    (le_cost_of_search α D hs)

/-- `witness5` has gauge distance `6`, attained by the identity gauge. -/
theorem gaugeDist_witness5 : witness5.gaugeDist (movedNorm (Fin 3)) = 6 :=
  gaugeDist_ofLt_eq_of_search edge5 6 cost_one_witness5 search5_root

/-- `witness6` has gauge distance `18`, attained by the identity gauge. -/
theorem gaugeDist_witness6 : witness6.gaugeDist (movedNorm (Fin 3)) = 18 :=
  gaugeDist_ofLt_eq_of_search edge6 18 cost_one_witness6 search6_root

/-- `witness7` has gauge distance `12`, attained by the identity gauge. -/
theorem gaugeDist_witness7 : witness7.gaugeDist (movedNorm (Fin 3)) = 12 :=
  gaugeDist_ofLt_eq_of_search edge7 12 cost_one_witness7 search7_root

/-- `witness8` has gauge distance `27`, attained by the identity gauge. -/
theorem gaugeDist_witness8 : witness8.gaugeDist (movedNorm (Fin 3)) = 27 :=
  gaugeDist_ofLt_eq_of_search edge8 27 cost_one_witness8 search8_root

/-- `defect / gaugeDist` for `witness5` equals `h1 (complete (Fin 5)) (movedNorm (Fin 3))`. -/
theorem defect_div_gaugeDist_witness5_eq_h1 :
    witness5.defect (movedNorm (Fin 3)) / witness5.gaugeDist (movedNorm (Fin 3)) =
      h1 (complete (Fin 5)) (movedNorm (Fin 3)) := by
  rw [defect_witness5, gaugeDist_witness5,
    h1_complete_movedNorm_fin_three (V := Fin 5) (by simp)]
  norm_num

/-- `defect / gaugeDist` for `witness6` equals `h1 (complete (Fin 6)) (movedNorm (Fin 3))`. -/
theorem defect_div_gaugeDist_witness6_eq_h1 :
    witness6.defect (movedNorm (Fin 3)) / witness6.gaugeDist (movedNorm (Fin 3)) =
      h1 (complete (Fin 6)) (movedNorm (Fin 3)) := by
  rw [defect_witness6, gaugeDist_witness6,
    h1_complete_movedNorm_fin_three (V := Fin 6) (by simp)]
  norm_num

/-- `defect / gaugeDist` for `witness7` equals `h1 (complete (Fin 7)) (movedNorm (Fin 3))`. -/
theorem defect_div_gaugeDist_witness7_eq_h1 :
    witness7.defect (movedNorm (Fin 3)) / witness7.gaugeDist (movedNorm (Fin 3)) =
      h1 (complete (Fin 7)) (movedNorm (Fin 3)) := by
  rw [defect_witness7, gaugeDist_witness7,
    h1_complete_movedNorm_fin_three (V := Fin 7) (by simp)]
  norm_num

/-- `defect / gaugeDist` for `witness8` equals `h1 (complete (Fin 8)) (movedNorm (Fin 3))`. -/
theorem defect_div_gaugeDist_witness8_eq_h1 :
    witness8.defect (movedNorm (Fin 3)) / witness8.gaugeDist (movedNorm (Fin 3)) =
      h1 (complete (Fin 8)) (movedNorm (Fin 3)) := by
  rw [defect_witness8, gaugeDist_witness8,
    h1_complete_movedNorm_fin_three (V := Fin 8) (by simp)]
  norm_num

end Sym3

/-! ## Checks at small sizes

The replicated seed at `q = 2` and `witness8` are different cochains on eight vertices, with
defects and gauge distances `(64, 24)` and `(72, 27)` and the same ratio `8 / 3`. -/

example : (Sym3.replicatedSeed 1).defect (movedNorm (Fin 3)) = 8 ∧
    (Sym3.replicatedSeed 1).gaugeDist (movedNorm (Fin 3)) = 6 := by
  rw [Sym3.defect_replicatedSeed, Sym3.gaugeDist_replicatedSeed]
  norm_num

example : (Sym3.replicatedSeed 2).defect (movedNorm (Fin 3)) = 64 ∧
    (Sym3.replicatedSeed 2).gaugeDist (movedNorm (Fin 3)) = 24 := by
  rw [Sym3.defect_replicatedSeed, Sym3.gaugeDist_replicatedSeed]
  norm_num

example : (Sym3.replicatedSeed 3).defect (movedNorm (Fin 3)) = 216 ∧
    (Sym3.replicatedSeed 3).gaugeDist (movedNorm (Fin 3)) = 54 := by
  rw [Sym3.defect_replicatedSeed, Sym3.gaugeDist_replicatedSeed]
  norm_num

example : (Sym3.replicatedSeed 2).defect (movedNorm (Fin 3)) /
      (Sym3.replicatedSeed 2).gaugeDist (movedNorm (Fin 3)) = 8 / 3 ∧
    Sym3.witness8.defect (movedNorm (Fin 3)) / Sym3.witness8.gaugeDist (movedNorm (Fin 3)) =
      8 / 3 := by
  rw [Sym3.defect_replicatedSeed, Sym3.gaugeDist_replicatedSeed, Sym3.defect_witness8,
    Sym3.gaugeDist_witness8]
  norm_num

end TauCeti
