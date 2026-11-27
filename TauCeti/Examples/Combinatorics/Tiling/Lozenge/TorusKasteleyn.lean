/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.TorusKasteleyn
public import TauCeti.Examples.Combinatorics.Tiling.Lozenge.Torus
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

/-!
# Checks: twisted Kasteleyn matrices and the torus partition function

For type weights `(w₁, w₂, w₃)`, giving every edge of direction `k` the weight `w_k`:

* `n₁ = n₂ = 1`: `K_{ab}` is the `1 × 1` matrix `w₃ + (−1)^b w₁ + (−1)^a w₂`, its single entry
  adding the three edge contributions, every lozenge of type 1 crossing the horizontal seam and
  every lozenge of type 2 the vertical one; at type weights `(1, 1, 2)`, `K₁₁ = 2 − 1 − 1 = 0`
  although its three summands are nonzero.
* `n₁ = n₂ = 1`: the torus partition function is `w₁ + w₂ + w₃`, one term for each of the three
  torus tilings, and at unit weights it counts them.
* `n₁ = n₂ = 2`, unit weights: `det K₀₀ = −3` and `det K₁₀ = det K₀₁ = det K₁₁ = 5`.
* `n₁ = 1`, `n₂ = 2`, unit weights: `det K₁₀ = −1` and `det K₀₁ = 5`, so exchanging the seams
  that carry `a` and `b` would exchange `K₁₀` and `K₀₁`; and `det K₀₀ = 3`, `det K₁₁ = 1`.
-/

public section

namespace TauCeti.Examples.TorusKasteleynChecks

open TauCeti TauCeti.Examples.LozengeTorusChecks Matrix

/-- The type weights `(w₁, w₂, w₃)`: every edge of direction `k` gets the weight `w_k`. -/
def typeWeight (w₁ w₂ w₃ : ℝ) (e : TriEdge) : ℝ :=
  ![w₁, w₂, w₃] e.k

/-! ### The `1 × 1` torus -/

/-- On the `1 × 1` torus, `K_{ab}` is the `1 × 1` matrix `w₃ + (−1)^b w₁ + (−1)^a w₂`. -/
theorem twistedKasteleyn_one_one (w₁ w₂ w₃ : ℝ) (a b : Fin 2) (u u' : Fin 1 × Fin 1) :
    twistedKasteleyn 1 1 (typeWeight w₁ w₂ w₃) a b u u' =
      w₃ + (-1) ^ (b : ℕ) * w₁ + (-1) ^ (a : ℕ) * w₂ := by
  rw [Subsingleton.elim u 0, Subsingleton.elim u' 0, twistedKasteleyn_apply]
  simp +decide [typeWeight]

/-- At type weights `(1, 1, 2)` the entry `K₁₁ = 2 − 1 − 1` vanishes, although its three summands
do not. -/
example (u u' : Fin 1 × Fin 1) : twistedKasteleyn 1 1 (typeWeight 1 1 2) 1 1 u u' = 0 := by
  rw [twistedKasteleyn_one_one]
  norm_num

/-- On the `1 × 1` torus the torus partition function is `w₁ + w₂ + w₃`. -/
theorem torusPartitionFunction_one_one (w : TriEdge → ℝ) :
    torusPartitionFunction 1 1 w = w ⟨0, 0⟩ + w ⟨0, 1⟩ + w ⟨0, 2⟩ := by
  have hset : {M : Set TriEdge | IsTorusTiling 1 1 M} = Set.range edgesOfDir := by
    ext M
    simp [isTorusTiling_one_one_iff, eq_comm]
  have hinj : Function.Injective edgesOfDir := fun j j' h => by
    simpa using congrArg ((⟨0, j⟩ : TriEdge) ∈ ·) h
  have hdom : ∀ j : Fin 3, edgesOfDir j ∩ {e | e.v ∈ torusDomain 1 1} = {⟨0, j⟩} := fun j => by
    ext ⟨⟨x, y⟩, k⟩
    simp only [Set.mem_inter_iff, mem_edgesOfDir, Set.mem_ofPred_eq, mem_torusDomain,
      Set.mem_singleton_iff, TriEdge.mk.injEq, Prod.mk_eq_zero]
    omega
  have h := torusPartitionFunction_def 1 1 w
  rw [show (∑ᶠ (M : Set TriEdge) (_ : IsTorusTiling 1 1 M),
      ∏ᶠ (e : TriEdge) (_ : e ∈ M ∩ {e | e.v ∈ torusDomain 1 1}), w e) =
      ∑ᶠ (M : Set TriEdge) (_ : M ∈ {M : Set TriEdge | IsTorusTiling 1 1 M}),
      ∏ᶠ (e : TriEdge) (_ : e ∈ M ∩ {e | e.v ∈ torusDomain 1 1}), w e from rfl, hset,
    finsum_mem_range hinj] at h
  simp only [hdom, finprod_mem_singleton] at h
  rw [h, finsum_eq_sum_of_fintype, Fin.sum_univ_three]

/-- At unit weights the `1 × 1` torus partition function counts its three torus tilings. -/
example : torusPartitionFunction 1 1 (fun _ => 1) = 3 := by
  rw [torusPartitionFunction_one_one]
  norm_num

/-! ### Determinants at unit weights -/

/-- On the `2 × 2` torus at unit weights, `det K₀₀ = −3`. -/
example : (twistedKasteleyn 2 2 (fun _ => 1) 0 0).det = -3 := by
  rw [← det_reindex_self (finProdFinEquiv.trans (finCongr (by norm_num : 2 * 2 = 4)))]
  simp +decide [det_succ_row_zero, Fin.sum_univ_succ, twistedKasteleyn_apply, finProdFinEquiv]
  norm_num

/-- On the `2 × 2` torus at unit weights, `det K₁₀ = det K₀₁ = det K₁₁ = 5`. -/
example : (twistedKasteleyn 2 2 (fun _ => 1) 1 0).det = 5 ∧
    (twistedKasteleyn 2 2 (fun _ => 1) 0 1).det = 5 ∧
    (twistedKasteleyn 2 2 (fun _ => 1) 1 1).det = 5 := by
  simp only [← det_reindex_self (finProdFinEquiv.trans (finCongr (by norm_num : 2 * 2 = 4)))]
  simp +decide [det_succ_row_zero, Fin.sum_univ_succ, twistedKasteleyn_apply, finProdFinEquiv]
  norm_num

/-- On the `1 × 2` torus at unit weights, `det K₁₀ = −1` while `det K₀₁ = 5`: the seam carrying
`a` is the vertical one, crossed by the type-2 lozenges. Also `det K₀₀ = 3` and `det K₁₁ = 1`. -/
example : (twistedKasteleyn 1 2 (fun _ => 1) 1 0).det = -1 ∧
    (twistedKasteleyn 1 2 (fun _ => 1) 0 1).det = 5 ∧
    (twistedKasteleyn 1 2 (fun _ => 1) 0 0).det = 3 ∧
    (twistedKasteleyn 1 2 (fun _ => 1) 1 1).det = 1 := by
  simp only [← det_reindex_self (finProdFinEquiv.trans (finCongr (by norm_num : 1 * 2 = 2))),
    det_fin_two]
  simp +decide [twistedKasteleyn_apply, finProdFinEquiv]
  norm_num

end TauCeti.Examples.TorusKasteleynChecks
