/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.PathModel
public import TauCeti.Combinatorics.SimpleGraph.Hasse
public import TauCeti.QuantumGroups.QuantumInteger.Real

import TauCeti.Combinatorics.SimpleGraph.PathGraph.Basic

/-!
# Type-`A` quantum-integer eigenvectors for Temperley–Lieb path models

On the Dynkin graph `A_(k+1)`, realized as `SimpleGraph.pathGraph (k + 1)`, assigning the quantum
integer `[t + 1]` (`TauCeti.qInt R δ (t + 1)`) to vertex `t : Fin (k + 1)` turns the three-term
Chebyshev recurrence `[t] + [t + 2] = δ * [t + 1]` into the adjacency recurrence at every non-top
vertex `t < k`, with boundary defect `[k + 2]` at the top vertex `k`.

Consequently, over any commutative ring `R`:
* if `[k + 2] = 0` and `r t ^ 2 = [t + 1]`, the weights `r` satisfy the global adjacency
  eigenvector equation on `pathGraph (k + 1)`, hence `TauCeti.TemperleyLieb.IsPathEigenvectorUpTo`
  at every base vertex and every strand depth (in particular over `ℝ` at the discrete cosine
  parameters `δ = 2 cos (π / (k + 2))` with `r t = √[t + 1]`);
* for arbitrary `δ`, walks of fewer than `n ≤ k` steps from vertex `0` stay strictly below the top
  vertex `k`, so any weights with `r t ^ 2 = [t + 1]` satisfy
  `IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ n` (in particular over `ℝ` with `r t = √[t + 1]`
  whenever `[1], …, [k + 1]` are nonnegative).

Together with `TauCeti.TemperleyLieb.IsPathEigenvectorUpTo.map`, these lemmas instantiate
`TauCeti.TemperleyLieb.pathRep` and `TauCeti.TemperleyLieb.pathTrace` on `pathGraph` over `ℝ` and
`ℂ`. Over `ℂ`, `discretePathWeight` and `genericPathWeight` package the square-root weights on
`A_(m-1)` and `A_∞` (`hasse ℕ`) together with their nonvanishing, self-adjointness, and
eigenvector identities.

## Main definitions

* `TauCeti.TemperleyLieb.discretePathWeight`, `TauCeti.TemperleyLieb.genericPathWeight`: complex
  square-root quantum-integer vertex weights on `A_(m-1)` and `A_∞`.

## Main results

* `TauCeti.TemperleyLieb.sum_neighborFinset_pathGraph_qInt_eq`,
  `TauCeti.TemperleyLieb.sum_neighborFinset_pathGraph_qInt_of_lt`,
  `TauCeti.TemperleyLieb.sum_neighborFinset_pathGraph_qInt_of_eq_zero`,
  `TauCeti.TemperleyLieb.sum_neighborFinset_pathGraph_qInt`,
  `TauCeti.TemperleyLieb.sum_neighborFinset_hasse_qInt`: quantum-integer neighbour sums on
  `SimpleGraph.pathGraph (k + 1)` and `SimpleGraph.hasse ℕ`.
* `TauCeti.TemperleyLieb.isPathEigenvectorUpTo_pathGraph_of_sq_eq_qInt`,
  `TauCeti.TemperleyLieb.isPathEigenvectorUpTo_pathGraph_of_qInt_eq_zero`: bounded-depth and
  vanishing-boundary `IsPathEigenvectorUpTo` criteria over any commutative ring.
* `TauCeti.TemperleyLieb.isPathEigenvectorUpTo_pathGraph_sqrt_qInt`,
  `TauCeti.TemperleyLieb.isPathEigenvectorUpTo_pathGraph_two_mul_cos`: real square-root weight
  specializations for nonnegative quantum integers and for `δ = 2 cos (π / (k + 2))`.
* `TauCeti.TemperleyLieb.discretePathWeight_ne_zero`,
  `TauCeti.TemperleyLieb.isSelfAdjoint_discretePathWeight`,
  `TauCeti.TemperleyLieb.sum_neighborFinset_discretePathWeight_sq`,
  `TauCeti.TemperleyLieb.genericPathWeight_ne_zero`,
  `TauCeti.TemperleyLieb.isSelfAdjoint_genericPathWeight`,
  `TauCeti.TemperleyLieb.sum_neighborFinset_genericPathWeight_sq`: nonvanishing, self-adjointness,
  and eigenvector identities for complex path weights on `A_(m-1)` and `A_∞`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* H. Wenzl, *Hecke algebras of type `A_n` and subfactors*, Invent. Math. 92 (1988), 349–383.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §§4.4–4.5.
-/

public section

namespace TauCeti.TemperleyLieb

open Real SimpleGraph

/-- Over any commutative ring `R` and loop value `δ : R`, summing the quantum integers `[u + 1]`
over the neighbours of `v` in `SimpleGraph.pathGraph (k + 1)` gives `δ * [v + 1]` except at the top
vertex `v = k`, where the missing upper neighbour subtracts `[k + 2]`. -/
theorem sum_neighborFinset_pathGraph_qInt_eq {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    (v : Fin (k + 1)) [Fintype ((pathGraph (k + 1)).neighborSet v)] :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) =
      δ * qInt R δ (v + 1) - if (v : ℕ) = k then qInt R δ (k + 2) else 0 := by
  rw [sum_neighborFinset_pathGraph]
  have hlo : (if h : 0 < (v : ℕ) then qInt R δ ((⟨(v : ℕ) - 1, by omega⟩ : Fin (k + 1)) + 1)
      else 0) = qInt R δ v := by
    split_ifs with hv
    · exact congrArg (qInt R δ) (Nat.sub_add_cancel hv)
    · have hv0 : (v : ℕ) = 0 := by omega
      simp [hv0]
  have hhi : (if h : (v : ℕ) + 1 < k + 1 then
      qInt R δ ((⟨(v : ℕ) + 1, h⟩ : Fin (k + 1)) + 1) else 0) =
      qInt R δ (v + 2) - if (v : ℕ) = k then qInt R δ (k + 2) else 0 := by
    split_ifs with hv hvk hvk
    · omega
    · ring
    · rw [hvk]; ring
    · omega
  rw [hlo, hhi, qInt_add_two]
  ring

/-- At any non-top vertex `v < k` of `SimpleGraph.pathGraph (k + 1)`, the quantum integers `[u + 1]`
satisfy the exact adjacency recurrence `∑ u, [u + 1] = δ * [v + 1]` for every loop parameter
`δ : R`. -/
theorem sum_neighborFinset_pathGraph_qInt_of_lt {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    {v : Fin (k + 1)} [Fintype ((pathGraph (k + 1)).neighborSet v)] (hv : (v : ℕ) < k) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq, ite_eq_right hv.ne, sub_zero]

/-- Whenever `[k + 2] = 0`, the quantum integers `[t + 1]` on the vertices `t` of
`SimpleGraph.pathGraph (k + 1)` satisfy the global adjacency eigenvector equation with eigenvalue
`δ`. -/
theorem sum_neighborFinset_pathGraph_qInt_of_eq_zero {R : Type*} [CommRing R] {δ : R} {k : ℕ}
    (hq : qInt R δ (k + 2) = 0) (v : Fin (k + 1))
    [Fintype ((pathGraph (k + 1)).neighborSet v)] :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq, hq, ite_self, sub_zero]

/-- At `δ = 2 cos (π / (k + 2))`, `[k + 2] = 0`, so the quantum integers `[t + 1]` on the vertices
`t` of `SimpleGraph.pathGraph (k + 1)` form a global eigenvector of its adjacency matrix with
eigenvalue `δ`. -/
theorem sum_neighborFinset_pathGraph_qInt {k : ℕ} (v : Fin (k + 1))
    [Fintype ((pathGraph (k + 1)).neighborSet v)] :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (u + 1) =
      2 * cos (π / (k + 2 : ℕ)) * qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (v + 1) :=
  sum_neighborFinset_pathGraph_qInt_of_eq_zero (qInt_two_mul_cos_pi_div_eq_zero (by omega)) v

/-- Over any commutative ring `R` and loop value `δ : R`, the quantum integers `[u + 1]` on the
vertices `u` of `SimpleGraph.hasse ℕ` (`A_∞`) form an eigenvector of its adjacency matrix with
eigenvalue `δ`. -/
theorem sum_neighborFinset_hasse_qInt {R : Type*} [CommRing R] (δ : R) :
    ∀ v : ℕ, ∑ u ∈ (hasse ℕ).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1)
  | 0 => by simp [qInt_two]
  | k + 1 => by
    rw [neighborFinset_hasse_nat_succ, Finset.sum_pair (by omega), qInt_add_two (R := R) δ (k + 1)]
    ring

/-- Over any commutative ring `R`, vertex weights `r` on `SimpleGraph.pathGraph (k + 1)` with
`r t ^ 2 = [t + 1]` satisfy the bounded-depth eigenvector equation from base vertex `0` up to any
`n ≤ k`: walks of fewer than `n` steps from `0` never reach the top vertex `k`. -/
theorem isPathEigenvectorUpTo_pathGraph_of_sq_eq_qInt {R : Type*} [CommRing R] {δ : R}
    {k n : ℕ} (hnk : n ≤ k) {r : Fin (k + 1) → R}
    (hr : ∀ t : Fin (k + 1), r t ^ 2 = qInt R δ (t + 1)) :
    IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ n := by
  refine isPathEigenvectorUpTo_iff.2 fun m hm s hs ↦ ?_
  have hle := hs.le_add_of_adj_le_succ Fin.val
    (fun u v huv ↦ by simp [pathGraph_adj] at huv; omega) (Fin.last m)
  have hlt : (s (Fin.last m) : ℕ) < k := by
    simp only [Fin.val_zero, zero_add, Fin.val_last] at hle
    omega
  simp_rw [hr]
  exact sum_neighborFinset_pathGraph_qInt_of_lt δ hlt

/-- Over any commutative ring `R`, if `r t ^ 2 = [t + 1]` on `SimpleGraph.pathGraph (k + 1)` and
`[k + 2] = 0`, then `r` satisfies `IsPathEigenvectorUpTo` at every base vertex `v₀` and every
strand depth `n`. -/
theorem isPathEigenvectorUpTo_pathGraph_of_qInt_eq_zero {R : Type*} [CommRing R] {δ : R}
    {k : ℕ} (v₀ : Fin (k + 1)) {r : Fin (k + 1) → R}
    (hr : ∀ t : Fin (k + 1), r t ^ 2 = qInt R δ (t + 1))
    (hq : qInt R δ (k + 2) = 0) (n : ℕ) :
    IsPathEigenvectorUpTo (pathGraph (k + 1)) v₀ r δ n := by
  refine .of_forall (fun v ↦ ?_) n
  simp_rw [hr]
  exact sum_neighborFinset_pathGraph_qInt_of_eq_zero hq v

/-- Whenever the quantum integers `[1], …, [k + 1]` at `δ : ℝ` are nonnegative, the square-root
weights `t ↦ √[t + 1]` on `SimpleGraph.pathGraph (k + 1)` satisfy `IsPathEigenvectorUpTo` from base
vertex `0` up to any `n ≤ k`. -/
theorem isPathEigenvectorUpTo_pathGraph_sqrt_qInt {δ : ℝ} {k n : ℕ} (hnk : n ≤ k)
    (hq : ∀ t : Fin (k + 1), 0 ≤ qInt ℝ δ (t + 1)) :
    IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 (fun t ↦ √(qInt ℝ δ (t + 1))) δ n :=
  isPathEigenvectorUpTo_pathGraph_of_sq_eq_qInt hnk fun t ↦ Real.sq_sqrt (hq t)

/-- At `δ = 2 cos (π / (k + 2))`, the positive square-root weights `t ↦ √[t + 1]` on
`SimpleGraph.pathGraph (k + 1)` satisfy `IsPathEigenvectorUpTo` at every base vertex `v₀` and every
strand depth `n`. -/
theorem isPathEigenvectorUpTo_pathGraph_two_mul_cos {k : ℕ} (v₀ : Fin (k + 1)) (n : ℕ) :
    IsPathEigenvectorUpTo (pathGraph (k + 1)) v₀
      (fun t ↦ √(qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t + 1)))
      (2 * cos (π / (k + 2 : ℕ))) n :=
  isPathEigenvectorUpTo_pathGraph_of_qInt_eq_zero v₀
    (fun _ ↦ Real.sq_sqrt (qInt_two_mul_cos_pi_div_pos (by omega) (by omega)).le)
    (qInt_two_mul_cos_pi_div_eq_zero (by omega)) n

/-- Quantum-integer vertex weight `√[t + 1]` on `A_(m-1)` (`pathGraph (m - 1)`). -/
noncomputable def discretePathWeight (m : ℕ) (t : Fin (m - 1)) : ℂ :=
  ((√(qInt ℝ (2 * cos (π / m)) (t.val + 1)) : ℝ) : ℂ)

/-- Quantum-integer vertex weight `√[t + 1]` on `A_∞` (`hasse ℕ`). -/
noncomputable def genericPathWeight (δ : ℝ) (t : ℕ) : ℂ := ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ)

/-- Every vertex weight `discretePathWeight m t` on `A_(m-1)` is nonzero. -/
theorem discretePathWeight_ne_zero {m : ℕ} (t : Fin (m - 1)) : discretePathWeight m t ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (qInt_two_mul_cos_pi_div_pos (by omega) (by omega))).ne'

/-- Every vertex weight `discretePathWeight m t` is real (self-adjoint). -/
theorem isSelfAdjoint_discretePathWeight (m : ℕ) (t : Fin (m - 1)) :
    IsSelfAdjoint (discretePathWeight m t) := Complex.conj_ofReal _

/-- On `A_(m-1)`, the square of `discretePathWeight m t` equals the quantum integer `[t + 1]` at
`δ = 2 cos (π / m)`. -/
@[simp] theorem discretePathWeight_sq {m : ℕ} (t : Fin (m - 1)) :
    discretePathWeight m t ^ 2 = (qInt ℝ (2 * cos (π / m)) (t.val + 1) : ℂ) := by
  have hm : 2 ≤ m := by have := t.isLt; omega
  rw [discretePathWeight, ← Complex.ofReal_pow,
    Real.sq_sqrt (qInt_two_mul_cos_pi_div_pos (by omega) (by omega)).le]

/-- `discretePathWeight m ^ 2` is a `2 cos (π / m)`-eigenvector of `pathGraph (m - 1)`. -/
theorem sum_neighborFinset_discretePathWeight_sq {m : ℕ} (v : Fin (m - 1)) :
    ∑ u ∈ (pathGraph (m - 1)).neighborFinset v, discretePathWeight m u ^ 2 =
      ((2 * cos (π / m) : ℝ) : ℂ) * discretePathWeight m v ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by have := v.isLt; omega⟩
  simp_rw [discretePathWeight_sq]; exact_mod_cast sum_neighborFinset_pathGraph_qInt (k := k) v

/-- For `δ ≥ 2`, every vertex weight `genericPathWeight δ t` on `A_∞` is nonzero. -/
theorem genericPathWeight_ne_zero {δ : ℝ} (hδ : 2 ≤ δ) (t : ℕ) : genericPathWeight δ t ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (qInt_pos_of_two_le hδ (Nat.succ_pos t))).ne'

/-- Every vertex weight `genericPathWeight δ t` is real (self-adjoint). -/
theorem isSelfAdjoint_genericPathWeight (δ : ℝ) (t : ℕ) :
    IsSelfAdjoint (genericPathWeight δ t) := Complex.conj_ofReal _

/-- For `δ ≥ 2`, the square of `genericPathWeight δ t` equals the quantum integer `[t + 1]`. -/
@[simp] theorem genericPathWeight_sq {δ : ℝ} (hδ : 2 ≤ δ) (t : ℕ) :
    genericPathWeight δ t ^ 2 = (qInt ℝ δ (t + 1) : ℂ) := by
  rw [genericPathWeight, ← Complex.ofReal_pow,
    Real.sq_sqrt (qInt_pos_of_two_le hδ (Nat.succ_pos t)).le]

/-- For `δ ≥ 2`, `genericPathWeight δ ^ 2` is a `δ`-eigenvector of `hasse ℕ`. -/
theorem sum_neighborFinset_genericPathWeight_sq {δ : ℝ} (hδ : 2 ≤ δ) (v : ℕ) :
    ∑ u ∈ (hasse ℕ).neighborFinset v, genericPathWeight δ u ^ 2 =
      (δ : ℂ) * genericPathWeight δ v ^ 2 := by
  simp_rw [genericPathWeight_sq hδ]; exact_mod_cast sum_neighborFinset_hasse_qInt δ v

end TauCeti.TemperleyLieb
