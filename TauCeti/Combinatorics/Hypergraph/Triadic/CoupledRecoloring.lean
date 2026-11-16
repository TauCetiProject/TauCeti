/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.CoupledRecoloring
import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Gap
import TauCeti.Combinatorics.Hypergraph.Polyad.Permute
import TauCeti.Combinatorics.Hypergraph.Polyad.Rank
import TauCeti.Order.Partition.Pi

/-!
# Coupled recoloring over fine polyads

Given a coarse triadic complex `C` with equitable vertex cells and a same-cell palette refinement
`D` along a projection `π`, suppose a coloring `H : Colored3Graph κ V` is `(η, 1)`-top-regular
over most polyads of `D` and has small polyad energy gap from `C` to `D`. This file constructs an
approximating coloring `H'` that is close to `H` in edit discrepancy and rank-one top-regular over
most polyads of `C`.

On each canonical `S₃`-representative of a large, distinct-cell, rank-one top-regular fine polyad
`Q` over `D`, we apply `exists_recoloring_abs_card_filter_sub_mul_card_le` to shift the triple
coloring toward the coarse density `H.relativeDensity · (Q.coarsen _ π)` while preserving small
discrepancy on every `Subpolyad3 Q`. Because distinct `S₃`-orbits of distinct-cell polyads have
pairwise disjoint unordered supports (`Polyad3.disjoint_unorderedSupport_of_forall_ne_permute`),
these local recolorings glue into a single global coloring `H'`. Summing the local edit bounds over
the `S₃`-orbits yields `H.Approximates3 H' ε` from the polyad energy gap, and aggregating
subpolyad discrepancies across fine children yields `H'.TopRegularOverMostPolyads C δ₁ ε 1`
(`Colored3Graph.exists_recoloring_topRegularOverMostPolyads`).

We also lift rank amplification (`Colored3Graph.IsTopRegularOverPolyad.of_rank_one`) from single
polyads to triadic complexes (`Colored3Graph.exceptionalPolyadMass_le_of_rank_one` and
`Colored3Graph.TopRegularOverMostPolyads.of_rank_one`).

## Main results

* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_rank_one` and
  `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_rank_one`: rank amplification on a triadic
  complex.
* `TauCeti.Colored3Graph.exists_recoloring_topRegularOverMostPolyads`: coupled recoloring from a
  fine rank-one top-regular refinement with small polyad energy gap.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3.
-/

public section

open Finset Finpartition Real

namespace TauCeti

section Helpers

/-- For `n ≥ 6`, `n³ ≤ 2 * n.descFactorial 3`. -/
private theorem pow_three_le_two_mul_descFactorial {n : ℕ} (hn : 6 ≤ n) :
    n ^ 3 ≤ 2 * n.descFactorial 3 := by
  have hdesc : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
    simp [Nat.descFactorial_succ, mul_assoc]
    ring
  rw [hdesc]
  have h1 : n ^ 2 ≤ 2 * (n - 1) * (n - 2) := by
    zify [show 1 ≤ n by omega, show 2 ≤ n by omega]
    nlinarith
  calc n ^ 3 = n * n ^ 2 := by ring
    _ ≤ n * (2 * (n - 1) * (n - 2)) := Nat.mul_le_mul_left n h1
    _ = 2 * (n * (n - 1) * (n - 2)) := by ring

open Classical in
/-- Repeated-cell injective triples over an equipartition into `t` cells of size at least `1`
carry at most `6 * |V|³ / t` triples. -/
private theorem sum_card_support_not_hasDistinctCells_le {κ₂ V : Type*}
    [Fintype V] [DecidableEq V] [Fintype κ₂] (S : PairSkeleton3 κ₂ V)
    (hEq : S.vertexPart.IsEquipartition) (ht : 0 < #S.vertexPart.parts)
    (hs : 1 ≤ Fintype.card V / #S.vertexPart.parts) :
    ∑ P : Polyad3 S with ¬P.HasDistinctCells, (#P.support : ℝ) ≤
      6 * (Fintype.card V : ℝ) ^ 3 / #S.vertexPart.parts := by
  set t := #S.vertexPart.parts
  set s := Fintype.card V / t
  have hm : ∀ A ∈ S.vertexPart.parts, #A ≤ 2 * s := fun A hA ↦ by
    have hle := hEq.card_part_le_average_add_one hA
    rw [card_univ] at hle
    dsimp only [s, t] at *
    omega
  have hsum_nat : ∑ P : Polyad3 S with ¬P.HasDistinctCells, #P.support ≤
      3 * (2 * s) * Fintype.card V ^ 2 := by
    rw [← card_biUnion fun P _ Q _ hne ↦ Polyad3.pairwise_disjoint_support hne]
    calc #((univ.filter fun P : Polyad3 S ↦ ¬P.HasDistinctCells).biUnion Polyad3.support)
        ≤ #{g ∈ Fintype.piFinset (fun _ : Fin 3 ↦ (univ : Finset V)) |
            ¬Function.Injective fun i ↦ S.vertexPart.part (g i)} := by
          refine card_le_card_of_injOn (fun x ↦ x.1) (fun x hx ↦ ?_)
            (fun _ _ _ _ h ↦ Subtype.ext h)
          obtain ⟨P, hP, hxP⟩ := mem_biUnion.1 hx
          rw [mem_coe, mem_filter]
          refine ⟨Fintype.mem_piFinset.2 fun _ ↦ mem_univ _, fun hinj ↦ (mem_filter.1 hP).2 ?_⟩
          rw [Polyad3.hasDistinctCells_iff_injective_cell]
          intro i j hij
          apply hinj
          dsimp only
          have hci := ((Polyad3.mem_support_iff_cell_pairColor P x).1 hxP).1
          rw [S.vertexPart.part_eq_of_mem (P.cell_mem i) (hci i),
            S.vertexPart.part_eq_of_mem (P.cell_mem j) (hci j), hij]
      _ ≤ (Fintype.card (Fin 3)).choose 2 * (2 * s) *
            #(univ : Finset V) ^ (Fintype.card (Fin 3) - 1) :=
          S.vertexPart.card_filter_not_injective_part_le_of_card_le hm
      _ = 3 * (2 * s) * Fintype.card V ^ 2 := by simp [card_univ]
  have hst : (s : ℝ) * t ≤ Fintype.card V := by
    exact_mod_cast Nat.div_mul_le_self (Fintype.card V) t
  rw [le_div_iff₀ (Nat.cast_pos.2 ht)]
  calc (∑ P : Polyad3 S with ¬P.HasDistinctCells, (#P.support : ℝ)) * t
      ≤ (3 * (2 * (s : ℝ)) * (Fintype.card V : ℝ) ^ 2) * t := by gcongr; exact_mod_cast hsum_nat
    _ = 6 * ((s : ℝ) * t) * (Fintype.card V : ℝ) ^ 2 := by ring
    _ ≤ 6 * (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ 2 := by gcongr
    _ = 6 * (Fintype.card V : ℝ) ^ 3 := by ring

/-- Elementary exponential union bound for coupled recoloring over `Subpolyad3 Q`. -/
private theorem union_bound_subpolyad3 {q₃ s I_card N : ℕ} {η γ : ℝ}
    (hq : 1 ≤ q₃) (hs : 1 ≤ s) (hη : 0 < η) (hγ : 0 < γ)
    (hI : I_card ≤ 2 ^ (12 * s ^ 2))
    (hs_req : ((q₃ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤ s)
    (hN : γ * (s : ℝ) ^ 3 ≤ N) :
    2 * ((I_card : ℝ) + 1) * q₃ * exp (-2 * (η * N) ^ 2 / N) < 1 := by
  have hs1 : (1 : ℝ) ≤ s := Nat.one_le_cast.2 hs
  have hs2 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hpow2 : (2 : ℝ) ^ (12 * s ^ 2 + 2) ≤ exp ((12 * s ^ 2 + 2 : ℕ) : ℝ) := by
    calc (2 : ℝ) ^ (12 * s ^ 2 + 2)
        ≤ (exp 1) ^ (12 * s ^ 2 + 2) :=
          pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (1 : ℝ)]) _
      _ = exp ((12 * s ^ 2 + 2 : ℕ) : ℝ) := by rw [← exp_nat_mul, mul_one]
  have hI1 : 2 * ((I_card : ℝ) + 1) ≤ (2 : ℝ) ^ (12 * s ^ 2 + 2) := by
    have h1 : (1 : ℕ) ≤ 2 ^ (12 * s ^ 2) := Nat.one_le_pow _ _ two_pos
    exact_mod_cast (show 2 * (I_card + 1) ≤ 2 ^ (12 * s ^ 2 + 2) by
      calc 2 * (I_card + 1) ≤ 2 * (2 ^ (12 * s ^ 2) + 2 ^ (12 * s ^ 2)) := by omega
        _ = 2 ^ (12 * s ^ 2 + 2) := by ring)
  have hqexp : (q₃ : ℝ) < exp (q₃ : ℝ) :=
    lt_of_lt_of_le (by linarith) (add_one_le_exp (q₃ : ℝ))
  have hreq' : ((q₃ : ℝ) + 14) ≤ 2 * η ^ 2 * γ * s := by
    rwa [div_le_iff₀' (by positivity)] at hs_req
  have hexp_arg : ((12 * s ^ 2 + 2 : ℕ) : ℝ) + q₃ ≤ 2 * η ^ 2 * N := by
    have h1 : ((12 * s ^ 2 + 2 : ℕ) : ℝ) + q₃ ≤ ((q₃ : ℝ) + 14) * (s : ℝ) ^ 2 := by
      push_cast; have : (0 : ℝ) ≤ q₃ := Nat.cast_nonneg _; nlinarith
    have h2 : ((q₃ : ℝ) + 14) * (s : ℝ) ^ 2 ≤ 2 * η ^ 2 * (γ * (s : ℝ) ^ 3) := by
      calc _ ≤ (2 * η ^ 2 * γ * s) * (s : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hreq' (sq_nonneg _)
        _ = 2 * η ^ 2 * (γ * (s : ℝ) ^ 3) := by ring
    linarith [mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 2 * η ^ 2)]
  rw [show -2 * (η * N) ^ 2 / N = -(2 * η ^ 2 * N) by field_simp [hNpos.ne']]
  calc 2 * ((I_card : ℝ) + 1) * q₃ * exp (-(2 * η ^ 2 * N))
      ≤ exp ((12 * s ^ 2 + 2 : ℕ) : ℝ) * q₃ * exp (-(2 * η ^ 2 * N)) := by
        gcongr; exact hI1.trans hpow2
    _ < exp ((12 * s ^ 2 + 2 : ℕ) : ℝ) * exp (q₃ : ℝ) * exp (-(2 * η ^ 2 * N)) := by gcongr
    _ = exp (((12 * s ^ 2 + 2 : ℕ) : ℝ) + q₃ - 2 * η ^ 2 * N) := by
        rw [← exp_add, ← exp_add, sub_eq_add_neg]
    _ ≤ exp 0 := exp_le_exp.2 (by linarith)
    _ = 1 := exp_zero

/-- Summing a nonnegative `S₃`-invariant function over a set of distinct-cell polyads in pairwise
distinct `S₃`-orbits is at most one-sixth of the total sum over all polyads. -/
private theorem six_mul_sum_le_of_permute_invariant {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ₂] {S : PairSkeleton3 κ₂ V} (G : Finset (Polyad3 S)) (Φ : Polyad3 S → ℝ)
    (hΦ0 : ∀ Q, 0 ≤ Φ Q) (hΦperm : ∀ Q σ, Φ (Q.permute σ) = Φ Q)
    (horbit : ∀ Q₁ ∈ G, ∀ Q₂ ∈ G, ∀ σ : Equiv.Perm (Fin 3),
      Q₂ = Q₁.permute σ → Q₁ = Q₂ ∧ σ = 1) :
    6 * ∑ Q ∈ G, Φ Q ≤ ∑ Q : Polyad3 S, Φ Q := by
  classical
  have hcardS3 : (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]; norm_num
  have hinj : Set.InjOn (fun p : Polyad3 S × Equiv.Perm (Fin 3) ↦ p.1.permute p.2)
      ((G ×ˢ (univ : Finset (Equiv.Perm (Fin 3))) : Finset _) : Set _) := by
    intro p₁ hp₁ p₂ hp₂ heq
    rw [mem_coe, mem_product] at hp₁ hp₂
    dsimp only at heq
    have hrel : p₂.1 = p₁.1.permute (p₁.2 * p₂.2⁻¹) := by
      rw [← Polyad3.permute_permute, heq, Polyad3.permute_permute, mul_inv_cancel,
        Polyad3.permute_one]
    obtain ⟨hQ, hσ⟩ := horbit p₁.1 hp₁.1 p₂.1 hp₂.1 _ hrel
    exact Prod.ext hQ (mul_inv_eq_one.1 hσ)
  calc 6 * ∑ Q ∈ G, Φ Q
      = ∑ Q ∈ G, ∑ σ : Equiv.Perm (Fin 3), Φ (Q.permute σ) := by
        rw [mul_sum]
        refine sum_congr rfl fun Q _ ↦ ?_
        simp_rw [hΦperm]
        rw [sum_const, card_univ, nsmul_eq_mul, hcardS3]
    _ = ∑ p ∈ G ×ˢ (univ : Finset (Equiv.Perm (Fin 3))), Φ (p.1.permute p.2) :=
        (sum_product' _ _ _).symm
    _ = ∑ Q ∈ (G ×ˢ (univ : Finset (Equiv.Perm (Fin 3)))).image
          (fun p ↦ p.1.permute p.2), Φ Q := (sum_image hinj).symm
    _ ≤ ∑ Q : Polyad3 S, Φ Q :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun Q _ _ ↦ hΦ0 Q

end Helpers

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- **Rank amplification for exceptional polyad mass.** Every polyad that is rank-one top-regular
at tolerance `δ₁` is rank-`r` top-regular at tolerance `δ` whenever `0 < δ` and
`2 ^ r * δ₁ ≤ δ ^ 2`, so the rank-`r` exceptional mass is at most the rank-one exceptional
mass. -/
theorem exceptionalPolyadMass_le_of_rank_one [DecidableEq κ] (H : Colored3Graph κ V)
    (C : TriadicComplex3 V) {δ₁ δ : ℝ} {r : ℕ}
    (hδ : 0 < δ) (hδε : (2 : ℝ) ^ r * δ₁ ≤ δ ^ 2) :
    H.exceptionalPolyadMass C δ r ≤ H.exceptionalPolyadMass C δ₁ 1 := by
  classical
  rw [exceptionalPolyadMass_def, exceptionalPolyadMass_def]
  refine div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg ?_
    fun _ _ _ ↦ Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  intro P
  simp only [mem_filter]
  exact fun ⟨hP, hreg⟩ ↦ ⟨hP, fun h1 ↦ hreg (h1.of_rank_one hδ hδε)⟩

/-- **Rank amplification on a triadic complex.** Rank-one top regularity over most polyads at
tolerance `δ₁` implies rank-`r` top regularity over most polyads at tolerance `δ` whenever `0 < δ`
and `2 ^ r * δ₁ ≤ δ ^ 2`. -/
theorem TopRegularOverMostPolyads.of_rank_one [DecidableEq κ] {H : Colored3Graph κ V}
    {C : TriadicComplex3 V} {δ₁ δ ε : ℝ} {r : ℕ}
    (h : H.TopRegularOverMostPolyads C δ₁ ε 1) (hδ : 0 < δ) (hδε : (2 : ℝ) ^ r * δ₁ ≤ δ ^ 2) :
    H.TopRegularOverMostPolyads C δ ε r :=
  topRegularOverMostPolyads_iff.2
    ((H.exceptionalPolyadMass_le_of_rank_one C hδ hδε).trans (topRegularOverMostPolyads_iff.1 h))

section Internal

variable [Fintype κ] [DecidableEq κ]

/-- Large, distinct-cell, rank-one top-regular fine polyads recolored in the gluing step. -/
private def IsGoodFinePolyad (H : Colored3Graph κ V) {D : TriadicComplex3 V} (η γ : ℝ) (s : ℕ)
    (Q : Polyad3 D.skeleton) : Prop :=
  Q.HasDistinctCells ∧ γ * (s : ℝ) ^ 3 ≤ #Q.support ∧ H.IsTopRegularOverPolyad Q η 1

omit [Fintype κ] in
private theorem isGoodFinePolyad_permute_iff (H : Colored3Graph κ V) {D : TriadicComplex3 V}
    (η γ : ℝ) (s : ℕ) (Q : Polyad3 D.skeleton) (σ : Equiv.Perm (Fin 3)) :
    IsGoodFinePolyad H η γ s (Q.permute σ) ↔ IsGoodFinePolyad H η γ s Q := by
  simp [IsGoodFinePolyad, Colored3Graph.isTopRegularOverPolyad_permute_iff]

/-- Local coupled recoloring on the unordered support of a single good fine polyad `Q`. -/
private theorem exists_local_coupled_recoloring (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η γ : ℝ} {s : ℕ} (hq : 1 ≤ Fintype.card κ) (hs : 1 ≤ s) (hη : 0 < η) (hγ : 0 < γ)
    (hcells : ∀ A ∈ D.skeleton.vertexPart.parts, #A ≤ 2 * s)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤ s)
    (Q : Polyad3 D.skeleton) (hQ : IsGoodFinePolyad H η γ s Q) :
    ∃ x : Set.powersetCard V 3 → κ,
      (∀ e ∉ Q.unorderedSupport, x e = H.color e) ∧
      (#{e ∈ Q.unorderedSupport | x e ≠ H.color e} : ℝ) ≤
        (∑ c : κ, #Q.support *
          |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
          Fintype.card κ * η * #Q.support ∧
      ∀ (S : Subpolyad3 Q) (d : κ),
        |(#{e ∈ S.unorderedSupport | x e = d} : ℝ) -
            H.relativeDensity d (Q.coarsen hVeq.le π) * #S.unorderedSupport| ≤
          2 * Fintype.card κ * η * #Q.support := by
  classical
  obtain ⟨hdist, hsize, hreg⟩ := hQ
  have hQpos : (0 : ℝ) < #Q.support := lt_of_lt_of_le (by positivity) hsize
  have hPne : (Q.coarsen hVeq.le π).support.Nonempty :=
    (card_pos.1 (Nat.cast_pos.1 hQpos)).mono
      (Polyad3.support_subset_coarsen hVeq.le π (fun p ↦ (hπ p).symm) Q)
  have hcardΩ : #Q.unorderedSupport = #Q.support := hdist.card_unorderedSupport
  have hIcard : Fintype.card (Subpolyad3 Q) ≤ 2 ^ (12 * s ^ 2) := by
    refine (card_subpolyad3_le Q).trans (Nat.pow_le_pow_right two_pos ?_)
    have h0 := hcells Q.c₀ Q.hc₀; have h1 := hcells Q.c₁ Q.hc₁; have h2 := hcells Q.c₂ Q.hc₂
    calc #Q.c₀ * #Q.c₁ + #Q.c₀ * #Q.c₂ + #Q.c₁ * #Q.c₂
        ≤ (2 * s) * (2 * s) + (2 * s) * (2 * s) + (2 * s) * (2 * s) := by gcongr
      _ = 12 * s ^ 2 := by ring
  have hub : 2 * (Fintype.card (Subpolyad3 Q) + 1 : ℝ) * Fintype.card κ *
      exp (-2 * (η * #Q.support) ^ 2 / #Q.unorderedSupport) < 1 := by
    rw [hcardΩ]; exact union_bound_subpolyad3 hq hs hη hγ hIcard hs_req hsize
  have hQcount (c : κ) : (#{e ∈ Q.unorderedSupport | H.color e = c} : ℝ) =
      (H.relativeDensity c Q : ℝ) * #Q.support := by
    rw [hdist.card_filter_unorderedSupport H c, relativeDensity_def]
    exact_mod_cast (H.relDensityOn_mul_card c Q.support).symm
  have hx₀ (S : Subpolyad3 Q) (c : κ) :
      |(#{e ∈ S.unorderedSupport | H.color e = c} : ℝ) -
        (#{e ∈ Q.unorderedSupport | H.color e = c} : ℝ) / #Q.unorderedSupport *
          #S.unorderedSupport| ≤ η * #Q.support := by
    have hScount : (#{e ∈ S.unorderedSupport | H.color e = c} : ℝ) =
        (H.relDensityOn c S.support : ℝ) * #S.support := by
      rw [S.card_filter_unorderedSupport hdist H c]
      exact_mod_cast (H.relDensityOn_mul_card c S.support).symm
    rw [hScount, hQcount, hcardΩ, S.card_unorderedSupport hdist,
      mul_div_cancel_right₀ _ hQpos.ne', ← sub_mul, abs_mul, Nat.abs_cast]
    exact hreg.abs_relDensityOn_sub_mul_card_le c S
  have hp0 (c : κ) : 0 ≤ (H.relativeDensity c (Q.coarsen hVeq.le π) : ℝ) :=
    mod_cast H.relativeDensity_nonneg c _
  have hp1 : ∑ c : κ, (H.relativeDensity c (Q.coarsen hVeq.le π) : ℝ) = 1 :=
    mod_cast H.sum_relativeDensity hPne
  obtain ⟨x, hxout, hxedit, hxdisc⟩ := exists_recoloring_abs_card_filter_sub_mul_card_le
    Q.unorderedSupport H.color hp0 hp1 (fun S : Subpolyad3 Q ↦ S.unorderedSupport)
    (fun S ↦ S.unorderedSupport_subset) (mul_pos hη hQpos) (mul_nonneg hη.le hQpos.le) hx₀ hub
  refine ⟨x, hxout, hxedit.trans_eq ?_, fun S d ↦ (hxdisc S d).trans_eq (by ring)⟩
  congr 1
  · congr 1
    refine sum_congr rfl fun c _ ↦ ?_
    rw [hQcount, hcardΩ, ← sub_mul, abs_mul, Nat.abs_cast, mul_comm]
  · ring

omit [Fintype κ] in
/-- Piecewise gluing of local recolorings across a family of polyads with pairwise disjoint
unordered supports, together with the exact count of modified triples. -/
private theorem exists_piecewise_coloring_on_disjoint (H : Colored3Graph κ V)
    {κ₂ : Type*} {S : PairSkeleton3 κ₂ V} (G : Finset (Polyad3 S))
    (hdisj : (G : Set (Polyad3 S)).PairwiseDisjoint Polyad3.unorderedSupport)
    (xQ : Polyad3 S → Set.powersetCard V 3 → κ) :
    ∃ H' : Colored3Graph κ V,
      (∀ {Q}, Q ∈ G → ∀ {e}, e ∈ Q.unorderedSupport → H'.color e = xQ Q e) ∧
      ({e | H.color e ≠ H'.color e}.ncard : ℝ) =
        ∑ Q ∈ G, (#{e ∈ Q.unorderedSupport | xQ Q e ≠ H.color e} : ℝ) := by
  classical
  let H' : Colored3Graph κ V := ⟨fun e ↦
    if h : ∃ Q ∈ G, e ∈ Q.unorderedSupport then xQ h.choose e else H.color e⟩
  have hH'_eq {Q : Polyad3 S} (hQ : Q ∈ G) {e : Set.powersetCard V 3}
      (he : e ∈ Q.unorderedSupport) : H'.color e = xQ Q e := by
    have hex : ∃ Q' ∈ G, e ∈ Q'.unorderedSupport := ⟨Q, hQ, he⟩
    have hch : hex.choose = Q := by
      by_contra hne
      exact disjoint_left.1 (hdisj hex.choose_spec.1 hQ hne) hex.choose_spec.2 he
    change (if h : ∃ Q' ∈ G, e ∈ Q'.unorderedSupport then xQ h.choose e else H.color e) = _
    rw [dite_eq_left hex, hch]
  have hH'_out {e : Set.powersetCard V 3} (he : ∀ Q ∈ G, e ∉ Q.unorderedSupport) :
      H'.color e = H.color e := by
    change (if h : ∃ Q' ∈ G, e ∈ Q'.unorderedSupport then xQ h.choose e else H.color e) = _
    exact dite_eq_right fun ⟨Q, hQ, hm⟩ ↦ he Q hQ hm
  refine ⟨H', hH'_eq, ?_⟩
  have hedit_set : {e | H.color e ≠ H'.color e} =
      ((G.biUnion fun Q ↦ {e ∈ Q.unorderedSupport | H'.color e ≠ H.color e} :
        Finset (Set.powersetCard V 3)) : Set _) := by
    ext e
    simp only [Set.mem_ofPred_eq, mem_coe, mem_biUnion, mem_filter]
    refine ⟨fun hne ↦ ?_, fun ⟨_, _, _, hne⟩ ↦ hne.symm⟩
    by_cases hex : ∃ Q ∈ G, e ∈ Q.unorderedSupport
    · obtain ⟨Q, hQ, hm⟩ := hex; exact ⟨Q, hQ, hm, hne.symm⟩
    · exact absurd (hH'_out fun Q hQ hm ↦ hex ⟨Q, hQ, hm⟩).symm hne
  rw [hedit_set, Set.ncard_coe_finset, card_biUnion (fun Q₁ hQ₁ Q₂ hQ₂ hne ↦
    (hdisj hQ₁ hQ₂ hne).mono (filter_subset _ _) (filter_subset _ _)), Nat.cast_sum]
  exact sum_congr rfl fun Q hQ ↦
    congrArg Nat.cast (congrArg card (filter_congr fun e he ↦ by rw [hH'_eq hQ he]))

omit [Fintype κ] in
/-- Transfer a local subpolyad discrepancy bound on a permuted representative `Q.permute σ` back to
`Q` when `H'` agrees with the local coloring `x` on `(Q.permute σ).unorderedSupport`. -/
private theorem abs_relDensityOn_sub_of_permute_recoloring (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {Q : Polyad3 D.skeleton} (hdist : Q.HasDistinctCells) (hQne : Q.support.Nonempty)
    (σ : Equiv.Perm (Fin 3)) (x : Set.powersetCard V 3 → κ) (S : Subpolyad3 Q) (d : κ) {B : ℝ}
    (hH'_eq : ∀ {e}, e ∈ (Q.permute σ).unorderedSupport → H'.color e = x e)
    (hdisc : |(#{e ∈ (S.permute σ).unorderedSupport | x e = d} : ℝ) -
        H.relativeDensity d ((Q.permute σ).coarsen hVeq.le π) *
          #(S.permute σ).unorderedSupport| ≤ B) :
    |((H'.relDensityOn d S.support : ℝ) -
        H.relativeDensity d (Q.coarsen hVeq.le π)) * #S.support| ≤ B := by
  have hcount : (#{e ∈ (S.permute σ).unorderedSupport | x e = d} : ℝ) =
      (H'.relDensityOn d S.support : ℝ) * #S.support := by
    have hfilt : {e ∈ (S.permute σ).unorderedSupport | x e = d} =
        {e ∈ S.unorderedSupport | H'.color e = d} := by
      rw [Subpolyad3.unorderedSupport_permute]
      refine filter_congr fun e he ↦ ?_
      have heQ : e ∈ (Q.permute σ).unorderedSupport := by
        rw [Polyad3.unorderedSupport_permute]; exact S.unorderedSupport_subset he
      rw [hH'_eq heQ]
    rw [hfilt, S.card_filter_unorderedSupport hdist H' d]
    exact_mod_cast (H'.relDensityOn_mul_card d S.support).symm
  rw [hcount, Subpolyad3.unorderedSupport_permute, S.card_unorderedSupport hdist,
    Polyad3.coarsen_permute_of_support_nonempty Q σ hVeq.le π (fun p ↦ (hπ p).symm) hQne,
    relativeDensity_permute] at hdisc
  rwa [sub_mul]

/-- Summing the local coupled-recoloring edit budget over canonical `S₃`-representatives is at most
one-sixth of the total polyad-density deviation plus `|κ| η |V| (|V| - 1) (|V| - 2)`. -/
private theorem six_mul_sum_local_budget_le (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η : ℝ} (hη : 0 < η) (G : Finset (Polyad3 D.skeleton))
    (horbit : ∀ Q₁ ∈ G, ∀ Q₂ ∈ G, ∀ σ : Equiv.Perm (Fin 3),
      Q₂ = Q₁.permute σ → Q₁ = Q₂ ∧ σ = 1) :
    6 * ∑ Q ∈ G,
        ((∑ c : κ, #Q.support *
            |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
          Fintype.card κ * η * #Q.support) ≤
      (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
          #Q.support * |(H.relativeDensity c Q : ℝ) -
            H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3 := by
  let Φ : Polyad3 D.skeleton → ℝ := fun Q ↦
    (∑ c : κ, #Q.support *
      |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
      Fintype.card κ * η * #Q.support
  have htotalD : ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) =
      (Fintype.card V).descFactorial 3 := by
    have hdec :
        (⟨D.pairColorCount, D.skeleton, univ⟩ : TriadicComplex3 V).IsPolyadDecomposition :=
      (TriadicComplex3.isPolyadDecomposition_iff_ofTriple_mem _).2 fun _ ↦ mem_univ _
    exact_mod_cast hdec.sum_card_support
  have hΦperm (Q : Polyad3 D.skeleton) (σ : Equiv.Perm (Fin 3)) : Φ (Q.permute σ) = Φ Q := by
    obtain hQ0 | hQne := Q.support.eq_empty_or_nonempty
    · simp [Φ, hQ0]
    · simp only [Φ, Polyad3.card_support_permute, relativeDensity_permute,
        Polyad3.coarsen_permute_of_support_nonempty Q σ hVeq.le π (fun p ↦ (hπ p).symm) hQne]
  have hΦ0 (Q : Polyad3 D.skeleton) : 0 ≤ Φ Q :=
    add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (abs_nonneg _)) (by norm_num)) (by positivity)
  calc 6 * ∑ Q ∈ G, Φ Q
      ≤ ∑ Q : Polyad3 D.skeleton, Φ Q :=
        six_mul_sum_le_of_permute_invariant G Φ hΦ0 hΦperm horbit
    _ = (∑ c : κ, ∑ Q : Polyad3 D.skeleton, #Q.support *
          |(H.relativeDensity c Q : ℝ) - H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3 := by
        dsimp only [Φ]; rw [sum_add_distrib, ← sum_div, sum_comm, ← mul_sum, htotalD]

/-- Coupled recoloring on each canonical `S₃`-representative of a good fine polyad, glued across
their pairwise disjoint unordered supports into a global coloring `H'`. -/
private theorem exists_glued_coupled_recoloring (H : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {η γ : ℝ} {s : ℕ} (hq : 1 ≤ Fintype.card κ) (hs : 1 ≤ s) (hη : 0 < η) (hγ : 0 < γ)
    (hcells : ∀ A ∈ D.skeleton.vertexPart.parts, #A ≤ 2 * s)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤ s) :
    ∃ H' : Colored3Graph κ V,
      (6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
        (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
          #Q.support * |(H.relativeDensity c Q : ℝ) -
            H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
        Fintype.card κ * η * (Fintype.card V).descFactorial 3) ∧
      (∀ Q : Polyad3 D.skeleton, IsGoodFinePolyad H η γ s Q →
        ∀ (S : Subpolyad3 Q) (d : κ),
          |((H'.relDensityOn d S.support : ℝ) -
              H.relativeDensity d (Q.coarsen hVeq.le π)) * #S.support| ≤
            2 * Fintype.card κ * η * #Q.support) := by
  classical
  let eP : D.skeleton.vertexPart.parts ≃ Fin (Fintype.card D.skeleton.vertexPart.parts) :=
    Fintype.equivFin _
  let GoodCanon : Finset (Polyad3 D.skeleton) := univ.filter fun Q ↦
    IsGoodFinePolyad H η γ s Q ∧ StrictMono fun i : Fin 3 ↦ eP ⟨Q.cell i, Q.cell_mem i⟩
  have hcanon_orbit : ∀ Q₁ ∈ GoodCanon, ∀ Q₂ ∈ GoodCanon, ∀ σ : Equiv.Perm (Fin 3),
      Q₂ = Q₁.permute σ → Q₁ = Q₂ ∧ σ = 1 := by
    intro Q₁ hQ₁ Q₂ hQ₂ σ h
    obtain ⟨τ, -, huniq⟩ := (mem_filter.1 hQ₁).2.1.1.existsUnique_permute_strictMono eP eP.injective
    have hσ1 : σ = 1 := (huniq σ (by simpa [← h] using (mem_filter.1 hQ₂).2.2)).trans
      (huniq 1 (by simpa using (mem_filter.1 hQ₁).2.2)).symm
    exact ⟨by simpa [hσ1] using h.symm, hσ1⟩
  have hdisj : (GoodCanon : Set (Polyad3 D.skeleton)).PairwiseDisjoint Polyad3.unorderedSupport :=
    fun Q₁ hQ₁ Q₂ hQ₂ hne ↦ Polyad3.disjoint_unorderedSupport_of_forall_ne_permute fun σ h ↦
      hne (hcanon_orbit Q₁ hQ₁ Q₂ hQ₂ σ h).1
  let xQ (Q : Polyad3 D.skeleton) : Set.powersetCard V 3 → κ :=
    if h : IsGoodFinePolyad H η γ s Q then
      (exists_local_coupled_recoloring H π hVeq hπ hq hs hη hγ hcells hs_req Q h).choose
    else H.color
  have hxQ_spec {Q : Polyad3 D.skeleton} (hQ : IsGoodFinePolyad H η γ s Q) :=
    (exists_local_coupled_recoloring H π hVeq hπ hq hs hη hγ hcells hs_req Q hQ).choose_spec
  obtain ⟨H', hH'_eq, hncard⟩ := exists_piecewise_coloring_on_disjoint H GoodCanon hdisj xQ
  refine ⟨H', ?_, ?_⟩
  · refine (le_trans ?_ (six_mul_sum_local_budget_le H π hVeq hπ hη GoodCanon hcanon_orbit))
    rw [hncard]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun Q hQ ↦ ?_) (by norm_num)
    have hQg := (mem_filter.1 hQ).2.1
    simpa only [xQ, dite_eq_left hQg] using (hxQ_spec hQg).2.1
  · intro Q hQ S d
    have hQne : Q.support.Nonempty := card_pos.1 (Nat.cast_pos.1
      (lt_of_lt_of_le (by positivity : (0 : ℝ) < γ * (s : ℝ) ^ 3) hQ.2.1))
    obtain ⟨σ, hσ, -⟩ := hQ.1.existsUnique_permute_strictMono eP eP.injective
    have hQ'good : IsGoodFinePolyad H η γ s (Q.permute σ) :=
      (isGoodFinePolyad_permute_iff H η γ s Q σ).2 hQ
    have hQ'mem : Q.permute σ ∈ GoodCanon := mem_filter.2 ⟨mem_univ _, hQ'good, hσ⟩
    have hdisc := (hxQ_spec hQ'good).2.2 (S.permute σ) d
    exact (abs_relDensityOn_sub_of_permute_recoloring H H' π hVeq hπ hQ.1 hQne σ
      (xQ (Q.permute σ)) S d (hH'_eq hQ'mem)
      (by simpa only [xQ, dite_eq_left hQ'good] using hdisc)).trans_eq
      (by rw [Polyad3.card_support_permute])

omit [Fintype κ] in
open Classical in
/-- Aggregating subpolyad discrepancy of `H'` against `H.relativeDensity d P` across fine children
of `P` gives discrepancy at most `(δ₁² / 2) * #P.support`. -/
private theorem abs_relDensityOn_sub_coarse_mul_card_le_of_good_children (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {P : Polyad3 C.skeleton} {Good : Polyad3 D.skeleton → Prop} {δ₁ τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ δ₁ ^ 2 / 4)
    (hgood : ∀ Q : Polyad3 D.skeleton, Q.coarsen hVeq.le π = P → Good Q →
      ∀ (S : Subpolyad3 Q) (d : κ),
        |((H'.relDensityOn d S.support : ℝ) - H.relativeDensity d P) * #S.support| ≤
          τ * #Q.support)
    (hbad : ∑ Q : Polyad3 D.skeleton with Q.coarsen hVeq.le π = P ∧ ¬Good Q,
        (#Q.support : ℝ) ≤ (δ₁ ^ 2 / 4) * #P.support)
    (S : Subpolyad3 P) (d : κ) :
    |((H'.relDensityOn d S.support : ℝ) - H.relativeDensity d P) * #S.support| ≤
      (δ₁ ^ 2 / 2) * #P.support := by
  have hπ' : ∀ p, C.skeleton.pairColors.color p = π (D.skeleton.pairColors.color p) :=
    fun p ↦ (hπ p).symm
  have hmiss (Q : Polyad3 D.skeleton) (hQ : Q.coarsen hVeq.le π ≠ P) :
      S.support ∩ Q.support = ∅ :=
    disjoint_iff_inter_eq_empty.1 ((Polyad3.pairwise_disjoint_support hQ.symm).mono
      S.support_subset (Polyad3.support_subset_coarsen hVeq.le π hπ' Q))
  have hsumP : ∑ Q : Polyad3 D.skeleton with Q.coarsen hVeq.le π = P, (#Q.support : ℝ) =
      #P.support := by
    have h := Polyad3.sum_card_support_coarsen hVeq.le π hπ' P
    rw [← Finset.filter_congr_decidable] at h
    exact_mod_cast h
  rw [H'.relDensityOn_sub_mul_card_eq_sum_inter_support D.skeleton d S.support]
  calc |∑ Q : Polyad3 D.skeleton,
          ((H'.relDensityOn d (S.support ∩ Q.support) : ℝ) - H.relativeDensity d P) *
            #(S.support ∩ Q.support)|
      ≤ ∑ Q : Polyad3 D.skeleton,
          |((H'.relDensityOn d (S.support ∩ Q.support) : ℝ) - H.relativeDensity d P) *
            #(S.support ∩ Q.support)| := abs_sum_le_sum_abs _ _
    _ = ∑ Q : Polyad3 D.skeleton with Q.coarsen hVeq.le π = P,
          |((H'.relDensityOn d (S.support ∩ Q.support) : ℝ) - H.relativeDensity d P) *
            #(S.support ∩ Q.support)| := by
        rw [sum_filter]
        refine sum_congr rfl fun Q _ ↦ ?_
        split_ifs with hQ <;> [rfl; simp [hmiss Q hQ]]
    _ ≤ ∑ Q : Polyad3 D.skeleton with Q.coarsen hVeq.le π = P,
          (τ * #Q.support + if ¬Good Q then (#Q.support : ℝ) else 0) := by
        refine sum_le_sum fun Q hQ ↦ ?_
        by_cases hG : Good Q
        · simp only [hG, not_true_eq_false, ↓reduceIte, add_zero]
          simpa only [Subpolyad3.support_restrict] using
            hgood Q (mem_filter.1 hQ).2 hG (S.restrict Q) d
        · simp only [hG, not_false_eq_true, ↓reduceIte]
          have habs : |(H'.relDensityOn d (S.support ∩ Q.support) : ℝ) -
              H.relativeDensity d P| ≤ 1 :=
            abs_sub_le_of_nonneg_of_le (mod_cast H'.relDensityOn_nonneg d _)
              (mod_cast H'.relDensityOn_le_one d _) (mod_cast H.relativeDensity_nonneg d P)
              (mod_cast H.relativeDensity_le_one d P)
          have hcard : (#(S.support ∩ Q.support) : ℝ) ≤ #Q.support := by
            exact_mod_cast card_le_card inter_subset_right
          rw [abs_mul, Nat.abs_cast]
          have h1 := mul_le_mul habs hcard (Nat.cast_nonneg _) zero_le_one
          linarith [mul_nonneg hτ0 (Nat.cast_nonneg (α := ℝ) #Q.support)]
    _ = τ * #P.support +
          ∑ Q : Polyad3 D.skeleton with Q.coarsen hVeq.le π = P ∧ ¬Good Q,
            (#Q.support : ℝ) := by
        rw [sum_add_distrib, ← mul_sum, hsumP, ← sum_filter, filter_filter]
    _ ≤ (δ₁ ^ 2 / 2) * #P.support := by
        have : (0 : ℝ) ≤ #P.support := Nat.cast_nonneg _
        nlinarith

omit [Fintype κ] in
open Classical in
/-- A coarse polyad `P` over `C` is `(δ₁, 1)`-top-regular for `H'` whenever every good fine child
has subpolyad discrepancy at most `τ |Q|` against `H`'s density over `P`, the bad fine children
carry at most `(δ₁² / 4) |P|` triples, and `τ ≤ δ₁² / 4`. -/
private theorem isTopRegularOverPolyad_of_good_children (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    {P : Polyad3 C.skeleton} {Good : Polyad3 D.skeleton → Prop} {δ₁ τ : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₁1 : δ₁ ≤ 1) (hτ0 : 0 ≤ τ) (hτ : τ ≤ δ₁ ^ 2 / 4)
    (hgood : ∀ Q : Polyad3 D.skeleton, Q.coarsen hVeq.le π = P → Good Q →
      ∀ (S : Subpolyad3 Q) (d : κ),
        |((H'.relDensityOn d S.support : ℝ) - H.relativeDensity d P) * #S.support| ≤
          τ * #Q.support)
    (hbad : ∑ Q : Polyad3 D.skeleton with Q.coarsen hVeq.le π = P ∧ ¬Good Q,
        (#Q.support : ℝ) ≤ (δ₁ ^ 2 / 4) * #P.support) :
    H'.IsTopRegularOverPolyad P δ₁ 1 := by
  have hsub := abs_relDensityOn_sub_coarse_mul_card_le_of_good_children H H' π hVeq hπ hτ0 hτ
    hgood hbad
  rw [isTopRegularOverPolyad_one_iff]
  intro d S hS
  obtain hP0 | hPpos := P.support.eq_empty_or_nonempty
  · have hS0 : S.support = ∅ := subset_empty.1 (hP0 ▸ S.support_subset)
    rw [hS0, relDensityOn_empty, H'.relativeDensity_of_support_eq_empty d hP0]
    simpa using hδ₁.le
  · have hPposR : (0 : ℝ) < #P.support := Nat.cast_pos.2 hPpos.card_pos
    have hSposR : (0 : ℝ) < #S.support := (mul_pos hδ₁ hPposR).trans_le hS
    have h1 : |(H'.relDensityOn d S.support : ℝ) - H.relativeDensity d P| ≤ δ₁ / 2 := by
      refine le_of_mul_le_mul_right ?_ hSposR
      have h := hsub S d
      rw [abs_mul, Nat.abs_cast] at h
      calc |(H'.relDensityOn d S.support : ℝ) - H.relativeDensity d P| * #S.support
          ≤ (δ₁ ^ 2 / 2) * #P.support := h
        _ = (δ₁ / 2) * (δ₁ * #P.support) := by ring
        _ ≤ (δ₁ / 2) * #S.support := by gcongr
    have h2 : |(H'.relativeDensity d P : ℝ) - H.relativeDensity d P| ≤ δ₁ / 2 := by
      refine le_of_mul_le_mul_right ?_ hPposR
      have h := hsub (Subpolyad3.ofSubcells P P.c₀ P.c₁ P.c₂) d
      rw [Subpolyad3.support_ofSubcells_cells, ← relativeDensity_def, abs_mul,
        Nat.abs_cast] at h
      exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith) hPposR.le)
    calc |(H'.relDensityOn d S.support : ℝ) - H'.relativeDensity d P|
        ≤ |(H'.relDensityOn d S.support : ℝ) - H.relativeDensity d P| +
            |(H.relativeDensity d P : ℝ) - (H'.relativeDensity d P : ℝ)| := abs_sub_le _ _ _
      _ ≤ δ₁ := by rw [abs_sub_comm (H.relativeDensity d P : ℝ)]; linarith

/-- Derive `H.Approximates3 H' ε` from the glued global edit bound and the polyad energy gap. -/
private theorem approximates3_of_glued_edit_bound (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    {ε η g : ℝ} (hε : 0 < ε) (hV6 : 6 ≤ Fintype.card V)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη_eps : (Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η ≤ ε)
    (hedit : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
      (∑ c : κ, ∑ Q : Polyad3 D.skeleton,
        #Q.support * |(H.relativeDensity c Q : ℝ) -
          H.relativeDensity c (Q.coarsen hVeq.le π)|) / 2 +
      Fintype.card κ * η * (Fintype.card V).descFactorial 3) :
    H.Approximates3 H' ε := by
  have hdev : ∑ c : κ, ∑ Q : Polyad3 D.skeleton,
        #Q.support * |(H.relativeDensity c Q : ℝ) -
          H.relativeDensity c (Q.coarsen hVeq.le π)| ≤
      (Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3 := by
    calc _ ≤ ∑ _c : κ, (√g * (Fintype.card V).descFactorial 3) :=
          sum_le_sum fun c _ ↦ H.sum_card_support_mul_abs_relativeDensity_coarsen_le
            hVeq.le π (fun p ↦ (hπ p).symm) hgap c
      _ = (Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3 := by
          rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]
  have hdesc_le : ((Fintype.card V).descFactorial 3 : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card V) 3
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) ^ 3 := by
    have : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
    positivity
  have h6 : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (Fintype.card V).descFactorial 3 := Nat.cast_nonneg _
    have h1 : 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ) ≤
        ε * (Fintype.card V).descFactorial 3 := by
      calc 6 * ({e | H.color e ≠ H'.color e}.ncard : ℝ)
          ≤ ((Fintype.card κ : ℝ) * √g * (Fintype.card V).descFactorial 3) / 2 +
              (Fintype.card κ : ℝ) * η * (Fintype.card V).descFactorial 3 := by linarith
        _ = ((Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η) *
              (Fintype.card V).descFactorial 3 := by ring
        _ ≤ ε * (Fintype.card V).descFactorial 3 := by gcongr
    nlinarith
  rw [approximates3_iff, editDiscrepancy3_def]
  push_cast
  rw [Nat.card_eq_fintype_card, div_le_iff₀ hVpos]
  exact h6

omit [Fintype κ] in
open Classical in
/-- Total bad fine polyad mass over distinct-cell coarse polyads is bounded by the irregular fine
mass plus the tiny fine polyad mass. -/
private theorem sum_card_support_bad_fine_le (H : Colored3Graph κ V) {C D : TriadicComplex3 V}
    (π : Fin D.pairColorCount → Fin C.pairColorCount) {η μ γ : ℝ} (hγ : 0 < γ)
    (hV6 : 6 ≤ Fintype.card V) (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hpolyD : D.polyads = univ) (htopD : H.TopRegularOverMostPolyads D η μ 1) :
    ∑ P : Polyad3 C.skeleton with P.HasDistinctCells,
        ∑ Q : Polyad3 D.skeleton with
          Q.coarsen hVeq.le π = P ∧
            ¬IsGoodFinePolyad H η γ (Fintype.card V / #C.skeleton.vertexPart.parts) Q,
          (#Q.support : ℝ) ≤
      (μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ) * (Fintype.card V).descFactorial 3 := by
  set t := #C.skeleton.vertexPart.parts
  set s := Fintype.card V / t
  have hfiber : ∑ P : Polyad3 C.skeleton with P.HasDistinctCells,
        ∑ Q : Polyad3 D.skeleton with
          Q.coarsen hVeq.le π = P ∧ ¬IsGoodFinePolyad H η γ s Q, (#Q.support : ℝ) =
      ∑ Q : Polyad3 D.skeleton with
        (Q.coarsen hVeq.le π).HasDistinctCells ∧ ¬IsGoodFinePolyad H η γ s Q, (#Q.support : ℝ) := by
    rw [← sum_fiberwise_of_maps_to (g := fun Q : Polyad3 D.skeleton ↦ Q.coarsen hVeq.le π)
      (fun Q hQ ↦ mem_filter.2 ⟨mem_univ _, (mem_filter.1 hQ).2.1⟩)]
    refine sum_congr rfl fun P hP ↦ sum_congr ?_ fun _ _ ↦ rfl
    ext Q; simp only [mem_filter, mem_univ, true_and]
    have hPd : P.HasDistinctCells := (mem_filter.1 hP).2
    exact ⟨by rintro ⟨rfl, hng⟩; exact ⟨⟨hPd, hng⟩, rfl⟩,
      by rintro ⟨⟨_, hng⟩, rfl⟩; exact ⟨rfl, hng⟩⟩
  have hsplit : ∑ Q : Polyad3 D.skeleton with
        (Q.coarsen hVeq.le π).HasDistinctCells ∧ ¬IsGoodFinePolyad H η γ s Q, (#Q.support : ℝ) ≤
      (∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η 1, (#Q.support : ℝ)) +
      (∑ Q : Polyad3 D.skeleton with (#Q.support : ℝ) < γ * (s : ℝ) ^ 3, (#Q.support : ℝ)) := by
    rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun Q _ ↦ ?_
    have : (0 : ℝ) ≤ #Q.support := Nat.cast_nonneg _
    split_ifs with hQ hirr htiny <;> try linarith
    exact absurd ⟨(Polyad3.hasDistinctCells_coarsen_iff Q hVeq π).1 hQ.1,
      not_lt.1 htiny, hirr⟩ hQ.2
  have hirrD : ∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η 1, (#Q.support : ℝ) ≤
      μ * (Fintype.card V).descFactorial 3 := by
    simpa only [hpolyD] using htopD.sum_card_support_le
  have htinyD : ∑ Q : Polyad3 D.skeleton with (#Q.support : ℝ) < γ * (s : ℝ) ^ 3,
        (#Q.support : ℝ) ≤
      2 * (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V).descFactorial 3 := by
    have hcardD : (Fintype.card (Polyad3 D.skeleton) : ℝ) ≤
        (t : ℝ) ^ 3 * (D.pairColorCount : ℝ) ^ 3 := by
      have h1 := card_polyad3_le D.skeleton; rw [hVeq, Fintype.card_fin] at h1; exact_mod_cast h1
    have hts : (t : ℝ) * s ≤ Fintype.card V := by exact_mod_cast Nat.mul_div_le (Fintype.card V) t
    have hpow : (Fintype.card V : ℝ) ^ 3 ≤ 2 * (Fintype.card V).descFactorial 3 := by
      exact_mod_cast pow_three_le_two_mul_descFactorial hV6
    calc _ ≤ ∑ _Q : Polyad3 D.skeleton, (γ * (s : ℝ) ^ 3) := by
          rw [sum_filter]
          refine sum_le_sum fun Q _ ↦ ?_
          split_ifs with hlt <;> [exact hlt.le; positivity]
      _ = (Fintype.card (Polyad3 D.skeleton) : ℝ) * (γ * (s : ℝ) ^ 3) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ ((t : ℝ) ^ 3 * (D.pairColorCount : ℝ) ^ 3) * (γ * (s : ℝ) ^ 3) := by gcongr
      _ = (D.pairColorCount : ℝ) ^ 3 * γ * ((t : ℝ) * s) ^ 3 := by ring
      _ ≤ (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V : ℝ) ^ 3 := by gcongr
      _ ≤ (D.pairColorCount : ℝ) ^ 3 * γ * (2 * (Fintype.card V).descFactorial 3) := by gcongr
      _ = 2 * (D.pairColorCount : ℝ) ^ 3 * γ * (Fintype.card V).descFactorial 3 := by ring
  rw [hfiber]; linarith

omit [Fintype κ] in
open Classical in
/-- Split irregular coarse polyad mass into repeated-cell polyads and distinct-cell polyads whose
bad-child mass exceeds `(δ₁² / 4) |P|`. -/
private theorem sum_card_support_not_isTopRegularOverPolyad_le_of_bad (H' : Colored3Graph κ V)
    {C : TriadicComplex3 V} {δ₁ : ℝ} (hδ₁ : 0 < δ₁) (bad : Polyad3 C.skeleton → ℝ)
    (hbad0 : ∀ P, 0 ≤ bad P)
    (hbad_gt : ∀ P, P.HasDistinctCells → ¬H'.IsTopRegularOverPolyad P δ₁ 1 →
      (δ₁ ^ 2 / 4) * #P.support < bad P) :
    ∑ P : Polyad3 C.skeleton with ¬H'.IsTopRegularOverPolyad P δ₁ 1, (#P.support : ℝ) ≤
      (∑ P : Polyad3 C.skeleton with ¬P.HasDistinctCells, (#P.support : ℝ)) +
      (4 / δ₁ ^ 2) * ∑ P : Polyad3 C.skeleton with P.HasDistinctCells, bad P := by
  have h1 : ∑ P : Polyad3 C.skeleton with ¬H'.IsTopRegularOverPolyad P δ₁ 1, (#P.support : ℝ) ≤
      ∑ P : Polyad3 C.skeleton,
        ((if ¬P.HasDistinctCells then (#P.support : ℝ) else 0) +
          (if P.HasDistinctCells then (4 / δ₁ ^ 2) * bad P else 0)) := by
    rw [sum_filter]
    refine sum_le_sum fun P _ ↦ ?_
    have : (0 : ℝ) ≤ #P.support := Nat.cast_nonneg _
    have hb : 0 ≤ (4 / δ₁ ^ 2) * bad P := mul_nonneg (by positivity) (hbad0 P)
    by_cases hd : P.HasDistinctCells
    · simp only [hd, not_true_eq_false, ↓reduceIte, zero_add]
      split_ifs with hreg
      · exact hb
      · have hgt := mul_lt_mul_of_pos_left (hbad_gt P hd hreg)
          (by positivity : (0 : ℝ) < 4 / δ₁ ^ 2)
        have hmul : (4 / δ₁ ^ 2) * ((δ₁ ^ 2 / 4) * #P.support) = #P.support := by
          field_simp [hδ₁.ne']
        linarith
    · simp only [hd, not_false_eq_true, ↓reduceIte, add_zero]
      split_ifs <;> linarith
  refine h1.trans_eq ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter, ← mul_sum]

open Classical in
/-- Derive coarse rank-one top regularity off an `ε`-proportion from good-child discrepancies. -/
private theorem topRegularOverMostPolyads_of_glued (H H' : Colored3Graph κ V)
    {C D : TriadicComplex3 V} (π : Fin D.pairColorCount → Fin C.pairColorCount)
    {ε δ₁ η μ γ : ℝ} (hε : 0 < ε) (hδ₁ : 0 < δ₁) (hδ₁1 : δ₁ ≤ 1) (hη : 0 < η) (hγ : 0 < γ)
    (hV6 : 6 ≤ Fintype.card V) (hCeq : C.skeleton.vertexPart.IsEquipartition)
    (ht : 48 / ε ≤ #C.skeleton.vertexPart.parts) (hpolyC : C.polyads = univ)
    (hpolyD : D.polyads = univ) (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    (htopD : H.TopRegularOverMostPolyads D η μ 1)
    (hη_reg : 2 * (Fintype.card κ : ℝ) * η ≤ δ₁ ^ 2 / 4)
    (hμ_γ : μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ ≤ 3 * ε * δ₁ ^ 2 / 16)
    (hs1 : 1 ≤ Fintype.card V / #C.skeleton.vertexPart.parts)
    (hdisc : ∀ Q : Polyad3 D.skeleton,
      IsGoodFinePolyad H η γ (Fintype.card V / #C.skeleton.vertexPart.parts) Q →
      ∀ (S : Subpolyad3 Q) (d : κ),
        |((H'.relDensityOn d S.support : ℝ) -
            H.relativeDensity d (Q.coarsen hVeq.le π)) * #S.support| ≤
          2 * Fintype.card κ * η * #Q.support) :
    H'.TopRegularOverMostPolyads C δ₁ ε 1 := by
  have ht_pos : 0 < #C.skeleton.vertexPart.parts :=
    Nat.cast_pos.1 (lt_of_lt_of_le (by positivity) ht)
  have hsplit := sum_card_support_not_isTopRegularOverPolyad_le_of_bad H' hδ₁
    (fun P ↦ ∑ Q : Polyad3 D.skeleton with Q.coarsen hVeq.le π = P ∧
      ¬IsGoodFinePolyad H η γ (Fintype.card V / #C.skeleton.vertexPart.parts) Q, (#Q.support : ℝ))
    (fun _ ↦ sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    (fun P _ hirr ↦ by
      by_contra hle; push Not at hle
      exact hirr (isTopRegularOverPolyad_of_good_children H H' π hVeq hπ hδ₁ hδ₁1
        (by positivity) hη_reg (fun Q hQP hGQ S d ↦ hQP ▸ hdisc Q hGQ S d) hle))
  have hrep : ∑ P : Polyad3 C.skeleton with ¬P.HasDistinctCells, (#P.support : ℝ) ≤
      (ε / 4) * (Fintype.card V).descFactorial 3 := by
    have hpow : (Fintype.card V : ℝ) ^ 3 ≤ 2 * (Fintype.card V).descFactorial 3 := by
      exact_mod_cast pow_three_le_two_mul_descFactorial hV6
    have hdiv : 6 / (#C.skeleton.vertexPart.parts : ℝ) ≤ ε / 8 := by
      rw [div_le_iff₀ (Nat.cast_pos.2 ht_pos)]; rw [div_le_iff₀ hε] at ht; linarith
    calc _ ≤ 6 * (Fintype.card V : ℝ) ^ 3 / #C.skeleton.vertexPart.parts :=
          sum_card_support_not_hasDistinctCells_le C.skeleton hCeq ht_pos hs1
      _ = (6 / #C.skeleton.vertexPart.parts) * (Fintype.card V : ℝ) ^ 3 := by ring
      _ ≤ (ε / 8) * (2 * (Fintype.card V).descFactorial 3) := by gcongr
      _ = (ε / 4) * (Fintype.card V).descFactorial 3 := by ring
  have hbad_bound : (4 / δ₁ ^ 2) * ∑ P : Polyad3 C.skeleton with P.HasDistinctCells,
        ∑ Q : Polyad3 D.skeleton with Q.coarsen hVeq.le π = P ∧
          ¬IsGoodFinePolyad H η γ (Fintype.card V / #C.skeleton.vertexPart.parts) Q,
          (#Q.support : ℝ) ≤
      (3 * ε / 4) * (Fintype.card V).descFactorial 3 := by
    have hdesc0 : (0 : ℝ) ≤ (Fintype.card V).descFactorial 3 := Nat.cast_nonneg _
    have hsum_le := (sum_card_support_bad_fine_le H π hγ hV6 hVeq hpolyD htopD).trans
      (mul_le_mul_of_nonneg_right hμ_γ hdesc0)
    calc _ ≤ (4 / δ₁ ^ 2) * ((3 * ε * δ₁ ^ 2 / 16) * (Fintype.card V).descFactorial 3) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (3 * ε / 4) * (Fintype.card V).descFactorial 3 := by field_simp [hδ₁.ne']; ring
  have hdecC : C.IsPolyadDecomposition :=
    C.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ hpolyC.symm ▸ mem_univ _
  have htotalC : ∑ P ∈ C.polyads, (#P.support : ℝ) = (Fintype.card V).descFactorial 3 := by
    exact_mod_cast hdecC.sum_card_support
  rw [topRegularOverMostPolyads_iff_sum_card_support_le hε.le, htotalC, hpolyC]
  linarith

end Internal

/-- **Coupled recoloring from a fine rank-one top-regular refinement.** Given a coarse triadic
complex `C` with at least `48 / ε` equitable vertex cells and a same-cell palette refinement `D`
over which `H` is `(η, 1)`-top-regular outside a `μ`-proportion and has polyad energy gap at most
`g`, if the cell size `s = |V| / #C.skeleton.vertexPart.parts` and parameters satisfy the coupled
recoloring budgets, then there exists a recoloring `H'` with `H.Approximates3 H' ε` and
`H'.TopRegularOverMostPolyads C δ₁ ε 1`. -/
theorem exists_recoloring_topRegularOverMostPolyads [Fintype κ] [DecidableEq κ]
    (H : Colored3Graph κ V) {C D : TriadicComplex3 V}
    (π : Fin D.pairColorCount → Fin C.pairColorCount) {ε δ₁ η μ γ g : ℝ}
    (hε : 0 < ε) (hδ₁ : 0 < δ₁) (hδ₁1 : δ₁ ≤ 1) (hη : 0 < η) (hγ : 0 < γ)
    (hV6 : 6 ≤ Fintype.card V)
    (hCeq : C.skeleton.vertexPart.IsEquipartition)
    (ht : 48 / ε ≤ #C.skeleton.vertexPart.parts)
    (hpolyC : C.polyads = univ) (hpolyD : D.polyads = univ)
    (hVeq : D.skeleton.vertexPart = C.skeleton.vertexPart)
    (hπ : ∀ p, π (D.skeleton.pairColors.color p) = C.skeleton.pairColors.color p)
    (htopD : H.TopRegularOverMostPolyads D η μ 1)
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη_eps : (Fintype.card κ : ℝ) * √g / 2 + (Fintype.card κ : ℝ) * η ≤ ε)
    (hη_reg : 2 * (Fintype.card κ : ℝ) * η ≤ δ₁ ^ 2 / 4)
    (hμ_γ : μ + 2 * (D.pairColorCount : ℝ) ^ 3 * γ ≤ 3 * ε * δ₁ ^ 2 / 16)
    (hs1 : 1 ≤ Fintype.card V / #C.skeleton.vertexPart.parts)
    (hs_req : ((Fintype.card κ : ℝ) + 14) / (2 * η ^ 2 * γ) ≤
      ((Fintype.card V / #C.skeleton.vertexPart.parts : ℕ) : ℝ)) :
    ∃ H' : Colored3Graph κ V,
      H.Approximates3 H' ε ∧ H'.TopRegularOverMostPolyads C δ₁ ε 1 := by
  have hq : 1 ≤ Fintype.card κ := by
    let e := (Fintype.equivFin V).symm
    let emb : Fin 3 ↪ V :=
      (Fin.castLEEmb (by omega : 3 ≤ Fintype.card V)).trans e.toEmbedding
    have : Nonempty κ := ⟨H.color (Set.powersetCard.ofFinEmb 3 V emb)⟩
    exact Fintype.card_pos
  have hcell_ub : ∀ A ∈ D.skeleton.vertexPart.parts,
      #A ≤ 2 * (Fintype.card V / #C.skeleton.vertexPart.parts) := fun A hA ↦ by
    have hle := hCeq.card_part_le_average_add_one (hVeq ▸ hA)
    rw [card_univ] at hle
    omega
  obtain ⟨H', hedit, hdisc⟩ := exists_glued_coupled_recoloring H π hVeq hπ hq hs1 hη hγ
    hcell_ub hs_req
  exact ⟨H',
    approximates3_of_glued_edit_bound H H' π hε hV6 hVeq hπ hgap hη_eps hedit,
    topRegularOverMostPolyads_of_glued H H' π hε hδ₁ hδ₁1 hη hγ hV6 hCeq ht hpolyC hpolyD
      hVeq hπ htopD hη_reg hμ_γ hs1 hdisc⟩

end Colored3Graph

end TauCeti
