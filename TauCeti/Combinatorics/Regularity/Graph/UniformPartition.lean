/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import TauCeti.Order.Partition.Pi
import TauCeti.Data.Fintype.BigOperators

/-!
# Irregular-pair volume in uniform equipartitions

An irregular pair of roles occupies at most four times the uniformity parameter of the space
of all vertex maps, for any finite set of roles. The estimate transfers Mathlib's irregular-pair
mass bound through the partition boxes and sums over the remaining coordinates.
-/

public section

open Finset SimpleGraph

namespace TauCeti

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In an equitable `τ`-uniform partition, boxes whose cells at two distinct roles form an
irregular pair occupy at most `4 * τ * card V ^ card ι` of the vertex-map space. -/
theorem sum_volume_nonUniform_pair_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finpartition (univ : Finset V))
    {τ : ℝ} (hτ : 0 < τ) (hP : P.IsEquipartition) (hG : P.IsUniform G τ)
    {i j : ι} (hij : i ≠ j) :
    (∑ φ : ι → P.parts, (∏ k, (#(φ k : Finset V) : ℝ)) *
      if ((φ i : Finset V), (φ j : Finset V)) ∈ P.nonUniforms G τ then 1 else 0) ≤
        4 * τ * (Fintype.card V : ℝ) ^ Fintype.card ι := by
  classical
  let B := (P.nonUniforms G τ).biUnion fun q ↦ q.1 ×ˢ q.2
  have hmem (x y : V) :
      (P.part x, P.part y) ∈ P.nonUniforms G τ ↔ (x, y) ∈ B := by
    constructor
    · intro h
      exact mem_biUnion.2 ⟨_, h, mem_product.2 ⟨P.mem_part (mem_univ _), P.mem_part (mem_univ _)⟩⟩
    · intro h
      obtain ⟨⟨A, C⟩, hAC, hxy⟩ := mem_biUnion.1 h
      obtain ⟨hA, hC, _, _⟩ := (P.mk_mem_nonUniforms G).1 hAC
      rw [mem_product] at hxy
      rwa [P.part_eq_of_mem hA hxy.1, P.part_eq_of_mem hC hxy.2]
  have hsum : (∑ x : V, ∑ y : V,
      if (P.part x, P.part y) ∈ P.nonUniforms G τ then (1 : ℝ) else 0) = #B := by
    simp_rw [hmem]
    rw [← Fintype.sum_prod_type (fun q : V × V ↦ if q ∈ B then (1 : ℝ) else 0)]
    simp
  have htransfer := P.sum_piFinset_apply_part (ι := ι)
    (fun A ↦ if (A i, A j) ∈ P.nonUniforms G τ then (1 : ℝ) else 0)
  simp only [Fintype.piFinset_univ, nsmul_eq_mul, Nat.cast_prod] at htransfer
  rw [← htransfer]
  have hpairs := Fintype.sum_piFinset_apply_apply hij (univ : Finset V)
    (fun x y ↦ if (P.part x, P.part y) ∈ P.nonUniforms G τ then (1 : ℝ) else 0)
  simp only [Fintype.piFinset_univ, card_univ, nsmul_eq_mul, Nat.cast_pow, hsum] at hpairs
  rw [hpairs]
  have hι : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  rcases isEmpty_or_nonempty V with hV | hV
  · have hB : B = ∅ := eq_empty_of_isEmpty _
    have hι₀ : Fintype.card ι ≠ 0 := by omega
    simp [hB, hι₀]
  · have hB := hP.sum_nonUniforms_lt (G := G) (univ_nonempty : (univ : Finset V).Nonempty) hτ hG
    simp only [card_univ] at hB
    calc (Fintype.card V : ℝ) ^ (Fintype.card ι - 2) * #B
        ≤ (Fintype.card V : ℝ) ^ (Fintype.card ι - 2) *
            (4 * τ * Fintype.card V ^ 2) :=
          mul_le_mul_of_nonneg_left hB.le (by positivity)
      _ = _ := by
        rw [mul_left_comm, mul_assoc, ← pow_add, Nat.sub_add_cancel hι, ← mul_assoc]

end TauCeti
