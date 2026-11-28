/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Torus.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Set.Card

/-!
# Twisted Kasteleyn matrices and the torus partition function

For `n₁, n₂ ≥ 1` the torus tilings are the plane tilings invariant under `L = n₁ℤ × n₂ℤ`
(`TauCeti.IsTorusTiling`). A torus lozenge is an `L`-orbit of plane edges; the three torus lozenges
at the white face `W(v)` are the orbits of `(v, 3)`, `(v, 1)` and `(v + e₁, 2)`, joining `W(v)` to
`B(v)`, `B(v − e₂)` and `B(v + e₁)` modulo `L`.

For an edge weight `w` and `a, b ∈ {0, 1}`, the twisted Kasteleyn matrix `K_{ab}` has rows the
white faces and columns the black faces of the fundamental domain `[0, n₁) × [0, n₂)`, both indexed
by `Fin n₁ × Fin n₂`. Its entry at `(W(u), B(u'))` is the sum of the signed weights of the torus
lozenges joining `W(u)` to `B(u')`: the weight `w(u, 3)` of the type-3 lozenge at the column `u`,
the weight `w(u, 1)` of the type-1 lozenge at the column `u − e₂`, multiplied by `(−1)^b` when it
crosses the horizontal seam (`u` in the first row), and the weight `w(u + e₁, 2)` of the type-2
lozenge at the column `u + e₁`, multiplied by `(−1)^a` when it crosses the vertical seam (`u` in
the last column). For `n₁ = 1` or `n₂ = 1` different lozenges share an entry, and on the `1 × 1`
torus all three do.

The definitions accept any `w : TriEdge → ℝ`, but `w` is meant to be `L`-periodic, so that it is a
weight on torus lozenges: only then is the entry `w(u + e₁, 2)` for `u` in the last column the
weight `w(u + e₁ − (n₁, 0), 2)` that the partition function gives the same lozenge at its
representative in the fundamental domain.

The torus partition function is the sum, over the torus tilings, of the product of `w` over their
edges `(v, k)` with `v` in the fundamental domain. A torus tiling is determined by those edges
(`TauCeti.IsTorusTiling.eq_of_inter_eq`), so there are finitely many torus tilings, the sum is
finite, and at `w ≡ 1` it counts the torus tilings.

## Main definitions

* `TauCeti.torusPoint u`: the point of the fundamental domain with coordinates
  `u : Fin n₁ × Fin n₂`.
* `TauCeti.twistedKasteleyn n₁ n₂ w a b`: the twisted Kasteleyn matrix `K_{ab}`.
* `TauCeti.torusPartitionFunction n₁ n₂ w`: the torus partition function.

## Main statements

* `TauCeti.torusPartitionFunction_eq_sum`: the torus partition function is a finite sum of
  finite products of values of `w` on edges with initial vertex in the fundamental domain.
* `TauCeti.torusPartitionFunction_one`: at `w ≡ 1` it is the number of torus tilings.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Definition 3.9.
* R. Kenyon, *Local statistics of lattice dimers*, Ann. Inst. H. Poincaré Probab. Statist. 33
  (1997), Section 4.1.
-/

public section

namespace TauCeti

variable {n₁ n₂ : ℕ}

/-- The point of the fundamental domain `[0, n₁) × [0, n₂)` with coordinates `u`. -/
def torusPoint (u : Fin n₁ × Fin n₂) : ℤ × ℤ :=
  (((u.1 : ℕ) : ℤ), ((u.2 : ℕ) : ℤ))

theorem torusPoint_def (u : Fin n₁ × Fin n₂) :
    torusPoint u = (((u.1 : ℕ) : ℤ), ((u.2 : ℕ) : ℤ)) :=
  (rfl)

theorem torusPoint_mem_torusDomain (u : Fin n₁ × Fin n₂) :
    torusPoint u ∈ torusDomain n₁ n₂ := by
  simp [torusPoint_def]

/-- The twisted Kasteleyn matrix `K_{ab}` of the `n₁ × n₂` torus for the edge weight `w`: rows the
white faces, columns the black faces of the fundamental domain, both indexed by
`Fin n₁ × Fin n₂`. The row of `W(u)` receives the weight `w(u, 3)` at the column `u`, the weight
`w(u, 1)` at the column `u − e₂`, multiplied by `(−1)^b` for `u` in the first row, and the weight
`w(u + e₁, 2)` at the column `u + e₁`, multiplied by `(−1)^a` for `u` in the last column;
contributions at the same column are added. The weight `w` is meant to be `L`-periodic: for `u` in
the last column, `w(u + e₁, 2)` is then the weight of the torus lozenge `(u + e₁ − (n₁, 0), 2)`
that `torusPartitionFunction` uses; for other `w` the entry is `w` at the plane edge
`(u + e₁, 2)`. -/
def twistedKasteleyn (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (w : TriEdge → ℝ) (a b : Fin 2) :
    Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  Matrix.of fun u u' =>
    (if u' = u then w ⟨torusPoint u, 2⟩ else 0) +
    (if u' = (u.1, u.2 - 1) then
      (if (u.2 : ℕ) = 0 then (-1) ^ (b : ℕ) else 1) * w ⟨torusPoint u, 0⟩ else 0) +
    (if u' = (u.1 + 1, u.2) then
      (if (u.1 : ℕ) + 1 = n₁ then (-1) ^ (a : ℕ) else 1) * w ⟨torusPoint u + (1, 0), 1⟩ else 0)

theorem twistedKasteleyn_apply [NeZero n₁] [NeZero n₂] (w : TriEdge → ℝ) (a b : Fin 2)
    (u u' : Fin n₁ × Fin n₂) :
    twistedKasteleyn n₁ n₂ w a b u u' =
      (if u' = u then w ⟨torusPoint u, 2⟩ else 0) +
      (if u' = (u.1, u.2 - 1) then
        (if (u.2 : ℕ) = 0 then (-1) ^ (b : ℕ) else 1) * w ⟨torusPoint u, 0⟩ else 0) +
      (if u' = (u.1 + 1, u.2) then
        (if (u.1 : ℕ) + 1 = n₁ then (-1) ^ (a : ℕ) else 1) * w ⟨torusPoint u + (1, 0), 1⟩
        else 0) :=
  (rfl)

/-- The entry of `K_{ab}` at a column that is none of `u`, `u − e₂`, `u + e₁` is `0`. -/
theorem twistedKasteleyn_apply_eq_zero [NeZero n₁] [NeZero n₂] (w : TriEdge → ℝ) (a b : Fin 2)
    {u u' : Fin n₁ × Fin n₂} (h₃ : u' ≠ u) (h₁ : u' ≠ (u.1, u.2 - 1))
    (h₂ : u' ≠ (u.1 + 1, u.2)) : twistedKasteleyn n₁ n₂ w a b u u' = 0 := by
  simp [twistedKasteleyn_apply, h₁, h₂, h₃]

open Classical in
/-- The torus partition function of the `n₁ × n₂` torus for the edge weight `w`: the sum, over the
torus tilings `M`, of the product of `w` over the edges of `M` with initial vertex in the
fundamental domain `[0, n₁) × [0, n₂)`. -/
noncomputable def torusPartitionFunction (n₁ n₂ : ℕ) (w : TriEdge → ℝ) : ℝ :=
  ∑ᶠ M ∈ {M : Set TriEdge | IsTorusTiling n₁ n₂ M}, ∏ᶠ e ∈ M ∩ {e | e.v ∈ torusDomain n₁ n₂}, w e

open Classical in
theorem torusPartitionFunction_def (n₁ n₂ : ℕ) (w : TriEdge → ℝ) :
    torusPartitionFunction n₁ n₂ w =
      ∑ᶠ M ∈ {M : Set TriEdge | IsTorusTiling n₁ n₂ M},
        ∏ᶠ e ∈ M ∩ {e | e.v ∈ torusDomain n₁ n₂}, w e :=
  (rfl)

open Classical in
/-- **The torus partition function is a finite sum**, over the finitely many torus tilings, of
finite products of values of `w` on edges with initial vertex in the fundamental domain; in
particular it is a polynomial in those values. -/
theorem torusPartitionFunction_eq_sum (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (w : TriEdge → ℝ) :
    torusPartitionFunction n₁ n₂ w =
      ∑ M ∈ (finite_setOf_isTorusTiling hn₁ hn₂).toFinset,
        ∏ e ∈ (finite_setOf_v_mem_torusDomain n₁ n₂).toFinset.filter (· ∈ M), w e := by
  rw [torusPartitionFunction_def, ← finsum_mem_finset_eq_sum]
  refine finsum_congr fun M => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  refine finsum_congr fun _ => ?_
  rw [← finprod_mem_finset_eq_prod]
  congr 1
  ext e
  simp [and_comm]

/-- **At `w ≡ 1` the torus partition function is the number of torus tilings.** -/
theorem torusPartitionFunction_one (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    torusPartitionFunction n₁ n₂ (fun _ => 1) =
      {M : Set TriEdge | IsTorusTiling n₁ n₂ M}.ncard := by
  rw [torusPartitionFunction_eq_sum hn₁ hn₂]
  simp [Set.ncard_eq_toFinset_card _ (finite_setOf_isTorusTiling hn₁ hn₂)]

end TauCeti
