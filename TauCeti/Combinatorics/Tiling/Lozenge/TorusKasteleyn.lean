/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Torus
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Int.Interval
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

The torus partition function is the sum, over the torus tilings, of the product of `w` over their
edges `(v, k)` with `v` in the fundamental domain. A torus tiling is determined by those edges, so
there are finitely many torus tilings, the sum is finite, and at `w ≡ 1` it counts the torus
tilings.

## Main definitions

* `TauCeti.torusDomain n₁ n₂`: the fundamental domain `[0, n₁) × [0, n₂)` in `ℤ²`.
* `TauCeti.twistedKasteleyn n₁ n₂ w a b`: the twisted Kasteleyn matrix `K_{ab}`.
* `TauCeti.torusPartitionFunction n₁ n₂ w`: the torus partition function.

## Main statements

* `TauCeti.IsTorusTiling.vadd_mem_iff`: torus tilings are invariant under all of `L`.
* `TauCeti.IsTorusTiling.eq_of_inter_eq`: a torus tiling is determined by its edges with initial
  vertex in the fundamental domain.
* `TauCeti.finite_setOf_isTorusTiling`: for `n₁, n₂ ≥ 1` there are finitely many torus tilings.
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

open Pointwise

namespace TauCeti

variable {M M' : Set TriEdge} {n₁ n₂ : ℕ}

/-- The fundamental domain `[0, n₁) × [0, n₂)` of the torus `ℤ² / (n₁ℤ × n₂ℤ)`. -/
def torusDomain (n₁ n₂ : ℕ) : Set (ℤ × ℤ) :=
  Set.Ico 0 (n₁ : ℤ) ×ˢ Set.Ico 0 (n₂ : ℤ)

theorem mem_torusDomain {v : ℤ × ℤ} :
    v ∈ torusDomain n₁ n₂ ↔ (0 ≤ v.1 ∧ v.1 < n₁) ∧ 0 ≤ v.2 ∧ v.2 < n₂ :=
  Iff.rfl

theorem finite_torusDomain (n₁ n₂ : ℕ) : (torusDomain n₁ n₂).Finite :=
  (Set.finite_Ico _ _).prod (Set.finite_Ico _ _)

/-- The edges with initial vertex in the fundamental domain are finitely many. -/
theorem finite_setOf_v_mem_torusDomain (n₁ n₂ : ℕ) :
    {e : TriEdge | e.v ∈ torusDomain n₁ n₂}.Finite := by
  have : {e : TriEdge | e.v ∈ torusDomain n₁ n₂} =
      (fun p : (ℤ × ℤ) × Fin 3 => (⟨p.1, p.2⟩ : TriEdge)) '' (torusDomain n₁ n₂ ×ˢ Set.univ) := by
    ext ⟨v, k⟩
    simp
  rw [this]
  exact ((finite_torusDomain n₁ n₂).prod Set.finite_univ).image _

/-- The point of the fundamental domain `[0, n₁) × [0, n₂)` with coordinates `u`. -/
def torusPoint (u : Fin n₁ × Fin n₂) : ℤ × ℤ :=
  (((u.1 : ℕ) : ℤ), ((u.2 : ℕ) : ℤ))

theorem torusPoint_def (u : Fin n₁ × Fin n₂) :
    torusPoint u = (((u.1 : ℕ) : ℤ), ((u.2 : ℕ) : ℤ)) :=
  (rfl)

theorem torusPoint_mem_torusDomain (u : Fin n₁ × Fin n₂) : torusPoint u ∈ torusDomain n₁ n₂ := by
  simp [torusPoint, mem_torusDomain]

/-- The twisted Kasteleyn matrix `K_{ab}` of the `n₁ × n₂` torus for the edge weight `w`: rows the
white faces, columns the black faces of the fundamental domain, both indexed by
`Fin n₁ × Fin n₂`. The row of `W(u)` receives the weight `w(u, 3)` at the column `u`, the weight
`w(u, 1)` at the column `u − e₂`, multiplied by `(−1)^b` for `u` in the first row, and the weight
`w(u + e₁, 2)` at the column `u + e₁`, multiplied by `(−1)^a` for `u` in the last column;
contributions at the same column are added. -/
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
  ∑ᶠ (M : Set TriEdge) (_ : IsTorusTiling n₁ n₂ M),
    ∏ᶠ (e : TriEdge) (_ : e ∈ M ∩ {e | e.v ∈ torusDomain n₁ n₂}), w e

open Classical in
theorem torusPartitionFunction_def (n₁ n₂ : ℕ) (w : TriEdge → ℝ) :
    torusPartitionFunction n₁ n₂ w =
      ∑ᶠ (M : Set TriEdge) (_ : IsTorusTiling n₁ n₂ M),
        ∏ᶠ (e : TriEdge) (_ : e ∈ M ∩ {e | e.v ∈ torusDomain n₁ n₂}), w e :=
  (rfl)

namespace IsTorusTiling

/-- **Torus tilings are invariant under all of `L = n₁ℤ × n₂ℤ`.** -/
theorem vadd_mem_iff (h : IsTorusTiling n₁ n₂ M) (m₁ m₂ : ℤ) (e : TriEdge) :
    ((m₁ * n₁, m₂ * n₂) +ᵥ e) ∈ M ↔ e ∈ M := by
  have h₁ : ((n₁ : ℤ), (0 : ℤ)) ∈ AddAction.stabilizer (ℤ × ℤ) M := h.vadd_fst
  have h₂ : ((0 : ℤ), (n₂ : ℤ)) ∈ AddAction.stabilizer (ℤ × ℤ) M := h.vadd_snd
  have hm : (m₁ * n₁, m₂ * n₂) ∈ AddAction.stabilizer (ℤ × ℤ) M := by
    have := add_mem (zsmul_mem h₁ m₁) (zsmul_mem h₂ m₂)
    simpa using this
  have hneg := neg_mem hm
  rw [AddAction.mem_stabilizer_iff] at hneg
  conv_rhs => rw [← hneg]
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg]

/-- **A torus tiling is determined by its edges with initial vertex in the fundamental domain.**
For `n₁, n₂ ≥ 1` two torus tilings with the same such edges are equal. -/
theorem eq_of_inter_eq (h : IsTorusTiling n₁ n₂ M) (h' : IsTorusTiling n₁ n₂ M') (hn₁ : 0 < n₁)
    (hn₂ : 0 < n₂) (hMM' : M ∩ {e | e.v ∈ torusDomain n₁ n₂} = M' ∩ {e | e.v ∈ torusDomain n₁ n₂}) :
    M = M' := by
  ext ⟨⟨x, y⟩, k⟩
  set e₀ : TriEdge := ⟨(x % n₁, y % n₂), k⟩
  have he : (⟨(x, y), k⟩ : TriEdge) = ((x / n₁) * n₁, (y / n₂) * n₂) +ᵥ e₀ := by
    simp only [e₀, TriEdge.vadd_mk, Prod.mk_add_mk, TriEdge.mk.injEq, Prod.mk.injEq, and_true]
    exact ⟨(Int.ediv_mul_add_emod _ _).symm, (Int.ediv_mul_add_emod _ _).symm⟩
  have hd : e₀.v ∈ torusDomain n₁ n₂ := by
    simp only [e₀, mem_torusDomain]
    refine ⟨⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩,
      Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  rw [he, h.vadd_mem_iff, h'.vadd_mem_iff]
  have := congrArg (e₀ ∈ ·) hMM'
  simpa [hd] using this

end IsTorusTiling

/-- **There are finitely many torus tilings** of the `n₁ × n₂` torus for `n₁, n₂ ≥ 1`. -/
theorem finite_setOf_isTorusTiling (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    {M : Set TriEdge | IsTorusTiling n₁ n₂ M}.Finite := by
  refine Set.Finite.of_finite_image (f := fun M => M ∩ {e | e.v ∈ torusDomain n₁ n₂}) ?_
    fun M hM M' hM' hMM' => IsTorusTiling.eq_of_inter_eq hM hM' hn₁ hn₂ hMM'
  refine ((finite_setOf_v_mem_torusDomain n₁ n₂).finite_subsets).subset ?_
  rintro _ ⟨M, -, rfl⟩
  exact Set.inter_subset_right

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
