/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Gap
import TauCeti.Combinatorics.Hypergraph.Polyad.Perm
import TauCeti.Combinatorics.Hypergraph.Polyad.Rank
import TauCeti.Data.Fintype.EmbeddingFiber
import TauCeti.Data.Set.PowersetCard
import TauCeti.LinearAlgebra.Matrix.Stochastic

/-!
# Orbit-glued coupled recoloring across a polyad energy gap

Given a coarse triadic complex `C` and a palette refinement `D` with polyad energy gap at most `g`
(`H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g`),
`TauCeti.Colored3Graph.exists_coupled_recoloring_of_polyadEnergy_sub_le` constructs a coloring `H'`
within edit discrepancy `|κ| (√g + β)` of `H` such that on every fine polyad `Q` of size at least
`N₀`, every `(η, 1)`-top-regular fine polyad `Q` has all of its subpolyad densities pushed to the
coarse density `H.relativeDensity c (Q.coarsen hV f)` within `|κ| (η + β) #Q.support`.

The construction selects one canonical representative per `(Equiv.Perm (Fin 3))ᵐᵒᵖ`-orbit of fine
polyads, finds a row-stochastic transition matrix pushing its densities to the coarse parent via
`Matrix.exists_mem_rowStochastic_vecMul_eq`, samples each color fiber independently on unordered
triples via `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`, and stratifies ordered-fiber
multiplicities `k + 1 ∈ {1, …, 6}` via `Finset.card_filter_ofFinEmb_eq_sum_factorial`.

## Main results

* `TauCeti.Colored3Graph.exists_coupled_recoloring_of_polyadEnergy_sub_le`: orbit-glued coupled
  recoloring preserving coarse parent densities on large fine polyads across a polyad energy gap.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3.
-/

public section

open Finset
open scoped Matrix

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]

/-- Index type for the discrepancy tests attached to a canonical orbit representative `Q₀`: a
role permutation `σ`, a subpolyad of `Q₀.perm σ`, and an ordered-fiber multiplicity `k + 1` in
`{1, …, 6}`. -/
private abbrev TestIdx {κ₂ : Type*} {T : PairSkeleton3 κ₂ V} (Q₀ : Polyad3 T) : Type _ :=
  Σ σ : Equiv.Perm (Fin 3), Subpolyad3 (Q₀.perm σ) × Fin (Nat.factorial 3)

private theorem card_testIdx_le {κ₂ : Type*} {T : PairSkeleton3 κ₂ V} (Q₀ : Polyad3 T) :
    Fintype.card (TestIdx Q₀) ≤ 36 * 2 ^ (3 * Fintype.card V ^ 2) := by
  classical
  dsimp only [TestIdx]
  rw [Fintype.card_sigma]
  calc ∑ σ : Equiv.Perm (Fin 3), Fintype.card (Subpolyad3 (Q₀.perm σ) × Fin (Nat.factorial 3))
      ≤ ∑ _σ : Equiv.Perm (Fin 3), 2 ^ (3 * Fintype.card V ^ 2) * Nat.factorial 3 := by
        refine sum_le_sum fun σ _ ↦ ?_
        rw [Fintype.card_prod, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (card_subpolyad3_le (Q₀.perm σ))
    _ = 36 * 2 ^ (3 * Fintype.card V ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
        norm_num [Nat.factorial]
        ring

private theorem pos_of_support_lower_bound {n q : ℕ} {β N₀ : ℝ}
    (hN₀ : 221 * (3 * (n : ℝ) ^ 2 + q + 7) ≤ β ^ 2 * N₀) : 0 < N₀ := by
  by_contra! hle
  have : β ^ 2 * N₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
  have hpos : (0 : ℝ) < 221 * (3 * (n : ℝ) ^ 2 + q + 7) := by positivity
  linarith

omit [DecidableEq κ] in
open Real in
/-- The polynomial support lower bound `221 * (3 |V|² + |κ| + 7) ≤ β² N₀` ensures both positivity
of `N₀` and the Hoeffding union-bound inequality for `TestIdx Q₀` at deviation `(β / 21) #Q₀`. -/
private theorem testIdx_union_bound {κ₂ : Type*} {T : PairSkeleton3 κ₂ V} {β N₀ : ℝ}
    (hβ : 0 < β)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀)
    (Q₀ : Polyad3 T) (hQ₀ : N₀ ≤ (#Q₀.support : ℝ)) :
    0 < (β / 21) * (#Q₀.support : ℝ) ∧
      2 * Fintype.card (TestIdx Q₀) * Fintype.card κ *
        exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ)) < 1 := by
  set n := Fintype.card V
  set B : ℝ := 3 * (n : ℝ) ^ 2 + Fintype.card κ + 7
  have hQpos : (0 : ℝ) < #Q₀.support := (pos_of_support_lower_bound hN₀).trans_le hQ₀
  refine ⟨by positivity, ?_⟩
  have hcard2 : 2 * Fintype.card (TestIdx Q₀) ≤ 2 ^ (3 * n ^ 2 + 7) := by
    have h1 := Nat.mul_le_mul_left 2 (card_testIdx_le Q₀)
    have h27 : (2 : ℕ) ^ 7 = 128 := by norm_num
    rw [pow_add, h27]
    linarith
  have hIexp : (2 : ℝ) * Fintype.card (TestIdx Q₀) ≤ exp (3 * (n : ℝ) ^ 2 + 7) := by
    have h2e : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) * Fintype.card (TestIdx Q₀)
        ≤ (2 : ℝ) ^ (3 * n ^ 2 + 7) := by exact_mod_cast hcard2
      _ ≤ exp 1 ^ (3 * n ^ 2 + 7) := pow_le_pow_left₀ (by norm_num) h2e _
      _ = exp (3 * (n : ℝ) ^ 2 + 7) := by rw [← exp_natCast_mul, mul_one]; push_cast; rfl
  have hKexp : (Fintype.card κ : ℝ) ≤ exp (Fintype.card κ) := by
    linarith [add_one_le_exp (Fintype.card κ : ℝ)]
  have hexp_eq : -2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ) =
      -(2 / 441) * (β ^ 2 * (#Q₀.support : ℝ)) := by field_simp [hQpos.ne']; ring
  have hBN : 221 * B ≤ β ^ 2 * (#Q₀.support : ℝ) :=
    hN₀.trans (mul_le_mul_of_nonneg_left hQ₀ (by positivity))
  have hexp_lt : -2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ) < -B := by
    have hBpos : 0 < B := by positivity
    rw [hexp_eq]; linarith
  calc 2 * (Fintype.card (TestIdx Q₀) : ℝ) * Fintype.card κ *
          exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ))
      ≤ exp (3 * (n : ℝ) ^ 2 + 7) * exp (Fintype.card κ) *
          exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ)) := by gcongr
    _ < exp (3 * (n : ℝ) ^ 2 + 7) * exp (Fintype.card κ) * exp (-B) := by gcongr
    _ = 1 := by rw [← exp_add, ← exp_add]; convert exp_zero; dsimp only [B]; ring

/-- Canonical representative of the `(Equiv.Perm (Fin 3))ᵐᵒᵖ`-orbit of a fine polyad `Q`. -/
private noncomputable def canonPolyad {κ₂ : Type*} {T : PairSkeleton3 κ₂ V} (Q : Polyad3 T) :
    Polyad3 T :=
  (Quotient.mk (MulAction.orbitRel (Equiv.Perm (Fin 3))ᵐᵒᵖ (Polyad3 T)) Q).out

private theorem exists_perm_canonPolyad {κ₂ : Type*} {T : PairSkeleton3 κ₂ V} (Q : Polyad3 T) :
    ∃ σ : Equiv.Perm (Fin 3), (canonPolyad Q).perm σ = Q := by
  have hq : canonPolyad Q ∈ MulAction.orbit (Equiv.Perm (Fin 3))ᵐᵒᵖ Q :=
    Quotient.exact (Quotient.out_eq
      (Quotient.mk (MulAction.orbitRel (Equiv.Perm (Fin 3))ᵐᵒᵖ (Polyad3 T)) Q))
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_symm.1 hq
  exact ⟨g.unop, hg⟩

private theorem canonPolyad_perm {κ₂ : Type*} {T : PairSkeleton3 κ₂ V} (Q : Polyad3 T)
    (σ : Equiv.Perm (Fin 3)) : canonPolyad (Q.perm σ) = canonPolyad Q :=
  congrArg Quotient.out (Quotient.sound ⟨MulOpposite.op σ, rfl⟩)

private theorem card_support_canonPolyad {κ₂ : Type*} {T : PairSkeleton3 κ₂ V} (Q : Polyad3 T) :
    #(canonPolyad Q).support = #Q.support := by
  obtain ⟨σ, hσ⟩ := exists_perm_canonPolyad Q
  conv_rhs => rw [← hσ]
  exact ((canonPolyad Q).card_support_perm σ).symm

/-- Canonical fine-polyad orbit representative assigned to an unordered `3`-subset `s`. -/
private noncomputable def canonTriple {κ₂ : Type*} (T : PairSkeleton3 κ₂ V)
    (s : Set.powersetCard V 3) : Polyad3 T :=
  let e := (Set.powersetCard.ofFinEmb_surjective 3 V s).choose
  canonPolyad (Polyad3.ofTriple T ⟨e.toFun, e.inj'⟩)

private theorem canonTriple_ofFinEmb_eq {κ₂ : Type*} {T : PairSkeleton3 κ₂ V} {Q : Polyad3 T}
    {x : {x : Fin 3 → V // Function.Injective x}} (hx : x ∈ Q.support) :
    canonTriple T (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = canonPolyad Q := by
  set s := Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩
  let e := (Set.powersetCard.ofFinEmb_surjective 3 V s).choose
  have he : Set.powersetCard.ofFinEmb 3 V e = s :=
    (Set.powersetCard.ofFinEmb_surjective 3 V s).choose_spec
  obtain ⟨σ, hσ⟩ := (Set.powersetCard.ofFinEmb_eq_iff_exists_perm ⟨x.val, x.property⟩ e).1 he.symm
  let x₀ : {x : Fin 3 → V // Function.Injective x} := ⟨e.toFun, e.inj'⟩
  have hx_eq : x = ⟨x₀.val ∘ σ, x₀.property.comp σ.injective⟩ := Subtype.ext hσ
  have hQ_eq : Q = (Polyad3.ofTriple T x₀).perm σ := by
    rw [Polyad3.mem_support_iff_eq_ofTriple.1 hx, hx_eq, Polyad3.ofTriple_comp_perm]
  dsimp only [canonTriple]
  rw [hQ_eq, canonPolyad_perm]

omit [Fintype V] [DecidableEq V] in
private theorem card_filter_color_fiberwise (H : Colored3Graph κ V)
    (W : Finset {x : Fin 3 → V // Function.Injective x}) (P : Set.powersetCard V 3 → Prop)
    [DecidablePred P] :
    #{x ∈ W | P (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩)} =
      ∑ c₀ : κ, #{x ∈ W | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
        P (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩)} := by
  classical
  rw [card_eq_sum_card_fiberwise
    (f := fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩))
    (t := univ) (fun _ _ ↦ mem_univ _)]
  exact sum_congr rfl fun c₀ _ ↦ congrArg card (ext fun x ↦ by simp only [mem_filter]; tauto)

omit [Fintype κ] in
private theorem relativeDensity_canonPolyad {κ₂ : Type*} {T : PairSkeleton3 κ₂ V}
    (H : Colored3Graph κ V) (Q : Polyad3 T) (c : κ) :
    H.relativeDensity c (canonPolyad Q) = H.relativeDensity c Q := by
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_canonPolyad Q
  conv_rhs => rw [← hσ₀]
  exact (H.relativeDensity_perm c (canonPolyad Q) σ₀).symm

omit [Fintype κ] in
private theorem relativeDensity_coarsen_canonPolyad {κ₁ κ₂ : Type*} {S : PairSkeleton3 κ₁ V}
    {T : PairSkeleton3 κ₂ V} (hV : T.vertexPart ≤ S.vertexPart) (f : κ₂ → κ₁)
    (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p))
    (H : Colored3Graph κ V) {Q : Polyad3 T} (hQ : Q.support.Nonempty) (c : κ) :
    H.relativeDensity c ((canonPolyad Q).coarsen hV f) = H.relativeDensity c (Q.coarsen hV f) := by
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_canonPolyad Q
  have hcan_ne : (canonPolyad Q).support.Nonempty := by
    rw [← card_pos, card_support_canonPolyad]
    exact hQ.card_pos
  conv_rhs => rw [← hσ₀]
  rw [Polyad3.coarsen_perm_of_support_nonempty _ hcan_ne σ₀ hV f hf, H.relativeDensity_perm]

/-- Orbit-glued coupled recoloring: produces a coloring `H'` and row-stochastic transition
matrices `M Q₀` pushing fine densities to coarse parent densities on every fine polyad `Q` with
`N₀ ≤ #Q.support`, tracking `M` within `β * #Q.support` on every subpolyad while leaving smaller
fine polyads untouched. -/
private theorem exists_coupled_recoloring
    {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {β N₀ : ℝ}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hβ : 0 < β)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀) :
    ∃ (H' : Colored3Graph κ V) (M : Polyad3 D.skeleton → Matrix κ κ ℝ),
      (∀ Q : Polyad3 D.skeleton, N₀ ≤ (#Q.support : ℝ) →
        M (canonPolyad Q) ∈ Matrix.rowStochastic ℝ κ ∧
        (fun c₀ ↦ (H.relativeDensity c₀ (canonPolyad Q) : ℝ)) ᵥ* M (canonPolyad Q) =
          (fun c ↦ (H.relativeDensity c ((canonPolyad Q).coarsen hV f) : ℝ)) ∧
        (∀ c₀, (H.relativeDensity c₀ (canonPolyad Q) : ℝ) * (1 - M (canonPolyad Q) c₀ c₀) =
          max ((H.relativeDensity c₀ (canonPolyad Q) : ℝ) -
            H.relativeDensity c₀ ((canonPolyad Q).coarsen hV f)) 0) ∧
        ∀ (S' : Subpolyad3 Q) (c₀ c : κ),
          |(#{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
              H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) -
            M (canonPolyad Q) c₀ c *
              #{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val,
                  x.property⟩) = c₀}| ≤
            β * #Q.support) ∧
      (∀ Q : Polyad3 D.skeleton, ¬N₀ ≤ (#Q.support : ℝ) → H.editedOn H' Q.support = ∅) := by
  classical
  have hN₀_pos : 0 < N₀ := pos_of_support_lower_bound hN₀
  let L (Q₀ : Polyad3 D.skeleton) (c₀ : κ) (idx : TestIdx Q₀) : Finset (Set.powersetCard V 3) :=
    univ.filter fun s ↦ H.color s = c₀ ∧
      #{x ∈ idx.2.1.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} =
        idx.2.2.val + 1
  have hL_card (Q₀ : Polyad3 D.skeleton) (c₀ : κ) (idx : TestIdx Q₀) :
      #(L Q₀ c₀ idx) ≤ #Q₀.support := by
    obtain ⟨σ, S', k⟩ := idx
    calc #(L Q₀ c₀ ⟨σ, S', k⟩)
        = ∑ _s ∈ L Q₀ c₀ ⟨σ, S', k⟩, 1 := by simp
      _ ≤ ∑ s ∈ L Q₀ c₀ ⟨σ, S', k⟩,
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} :=
          sum_le_sum fun s hs ↦ by rw [(mem_filter.1 hs).2.2]; omega
      _ ≤ ∑ s : Set.powersetCard V 3,
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ Nat.zero_le _
      _ = #S'.support := (card_eq_sum_card_fiberwise fun _ _ ↦ mem_univ _).symm
      _ ≤ #(Q₀.perm σ).support := card_le_card S'.support_subset
      _ = #Q₀.support := Q₀.card_support_perm σ
  have hcouple (Q₀ : Polyad3 D.skeleton) :
      ∃ (M : Matrix κ κ ℝ) (φ : κ → Set.powersetCard V 3 → κ),
        N₀ ≤ (#Q₀.support : ℝ) →
          M ∈ Matrix.rowStochastic ℝ κ ∧
          (fun c₀ ↦ (H.relativeDensity c₀ Q₀ : ℝ)) ᵥ* M =
            (fun c ↦ (H.relativeDensity c (Q₀.coarsen hV f) : ℝ)) ∧
          (∀ c₀, (H.relativeDensity c₀ Q₀ : ℝ) * (1 - M c₀ c₀) =
            max ((H.relativeDensity c₀ Q₀ : ℝ) - H.relativeDensity c₀ (Q₀.coarsen hV f)) 0) ∧
          ∀ c₀ (idx : TestIdx Q₀) c,
            |(#{s ∈ L Q₀ c₀ idx | φ c₀ s = c} : ℝ) - M c₀ c * #(L Q₀ c₀ idx)| <
              (β / 21) * #Q₀.support := by
    by_cases hQ₀ : N₀ ≤ (#Q₀.support : ℝ)
    · have hQ₀_ne : Q₀.support.Nonempty := card_pos.1 (by exact_mod_cast hN₀_pos.trans_le hQ₀)
      have hP₀_ne : (Q₀.coarsen hV f).support.Nonempty :=
        hQ₀_ne.mono (Polyad3.support_subset_coarsen hV f hf Q₀)
      have hsum : (∑ c, (H.relativeDensity c Q₀ : ℝ)) =
          ∑ c, (H.relativeDensity c (Q₀.coarsen hV f) : ℝ) := by
        exact_mod_cast (H.sum_relativeDensity hQ₀_ne).trans (H.sum_relativeDensity hP₀_ne).symm
      obtain ⟨M, hMmem, hMpush, hMdiag⟩ := Matrix.exists_mem_rowStochastic_vecMul_eq hsum
        (fun c ↦ mod_cast H.relativeDensity_nonneg c _)
      obtain ⟨ha, hub⟩ := testIdx_union_bound (κ := κ) hβ hN₀ Q₀ hQ₀
      have hφ (c₀ : κ) : ∃ φ₀ : Set.powersetCard V 3 → κ, ∀ (idx : TestIdx Q₀) c,
          |(#{s ∈ L Q₀ c₀ idx | φ₀ s = c} : ℝ) - M c₀ c * #(L Q₀ c₀ idx)| <
            (β / 21) * #Q₀.support :=
        exists_forall_abs_card_filter_sub_mul_card_lt
          (fun c ↦ Matrix.nonneg_of_mem_rowStochastic hMmem)
          (Matrix.sum_row_of_mem_rowStochastic hMmem c₀) (L Q₀ c₀) (hL_card Q₀ c₀) ha hub
      choose φ hφ using hφ
      exact ⟨M, φ, fun _ ↦ ⟨hMmem, hMpush, hMdiag, hφ⟩⟩
    · exact ⟨0, fun c₀ _ ↦ c₀, fun h' ↦ absurd h' hQ₀⟩
  choose M φ hMφ using hcouple
  let H' : Colored3Graph κ V :=
    ⟨fun s ↦ if N₀ ≤ (#(canonTriple D.skeleton s).support : ℝ) then
      φ (canonTriple D.skeleton s) (H.color s) s else H.color s⟩
  refine ⟨H', M, fun Q hQ ↦ ?_, fun Q hQ ↦ ?_⟩
  · set Q₀ := canonPolyad Q
    obtain ⟨σ₀, hσ₀⟩ := exists_perm_canonPolyad Q
    have hQ₀_card : #Q₀.support = #Q.support := card_support_canonPolyad Q
    have hQ₀ : N₀ ≤ (#Q₀.support : ℝ) := by rwa [hQ₀_card]
    obtain ⟨hMmem, hMpush, hMdiag, hφ_disc⟩ := hMφ Q₀ hQ₀
    refine ⟨hMmem, hMpush, hMdiag, fun S' c₀ c ↦ ?_⟩
    let S₀ : Subpolyad3 (Q₀.perm σ₀) :=
      S'.inclusion (hσ₀ ▸ Subset.rfl) (hσ₀ ▸ Subset.rfl) (hσ₀ ▸ Subset.rfl)
    have hS₀ : S₀.support = S'.support := Subpolyad3.support_inclusion _ _ _ S'
    have hH'_on_L (k : Fin (Nat.factorial 3)) :
        #{s : Set.powersetCard V 3 | (H.color s = c₀ ∧ H'.color s = c) ∧
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} =
              k.val + 1} =
          #{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} := by
      refine congrArg card (ext fun s ↦ ?_)
      simp only [L, mem_filter, mem_univ, true_and, hS₀]
      by_cases hm : #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val,
          x.property⟩ = s} = k.val + 1
      · obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < #{x ∈ S'.support |
          Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s})
        obtain ⟨hxS, hxs⟩ := mem_filter.1 hx
        have hcan : canonTriple D.skeleton s = Q₀ :=
          hxs ▸ canonTriple_ofFinEmb_eq (S'.support_subset hxS)
        by_cases hc₀ : H.color s = c₀ <;> simp [H', hcan, hQ₀, hc₀, hm]
      · simp [hm]
    rw [S'.support.card_filter_ofFinEmb_eq_sum_factorial fun s ↦ H.color s = c₀,
      S'.support.card_filter_ofFinEmb_eq_sum_factorial fun s ↦ H.color s = c₀ ∧ H'.color s = c]
    simp_rw [hH'_on_L]
    have h1' (k : Fin (Nat.factorial 3)) :
        #{s : Set.powersetCard V 3 | H.color s = c₀ ∧
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩ = s} =
              k.val + 1} =
          #(L Q₀ c₀ ⟨σ₀, S₀, k⟩) := by simp only [L, hS₀]
    simp_rw [h1']
    push_cast
    rw [mul_sum, ← sum_sub_distrib]
    let d (k : Fin (Nat.factorial 3)) : ℝ :=
      (#{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} : ℝ) - M Q₀ c₀ c * #(L Q₀ c₀ ⟨σ₀, S₀, k⟩)
    calc |∑ k : Fin (Nat.factorial 3), ((k.val + 1 : ℝ) *
            #{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} -
            M Q₀ c₀ c * ((k.val + 1 : ℝ) * #(L Q₀ c₀ ⟨σ₀, S₀, k⟩)))|
        = |∑ k, (k.val + 1 : ℝ) * d k| := congrArg abs (sum_congr rfl fun k _ ↦ by dsimp [d]; ring)
      _ ≤ ∑ k, |(k.val + 1 : ℝ) * d k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin (Nat.factorial 3), (k.val + 1 : ℝ) * ((β / 21) * #Q₀.support) := by
          refine sum_le_sum fun k _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (hφ_disc c₀ ⟨σ₀, S₀, k⟩ c).le (by positivity)
      _ = β * #Q.support := by
          rw [← sum_mul, hQ₀_card]
          have hsum21 : ∑ k : Fin (Nat.factorial 3), ((k : ℕ) + 1 : ℝ) = 21 := by
            exact_mod_cast (by decide : ∑ k : Fin (Nat.factorial 3), ((k : ℕ) + 1) = 21)
          rw [hsum21]; ring
  · rw [eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxQ, hne⟩ := (H.mem_editedOn H' Q.support x).1 hx
    have hnot : ¬N₀ ≤
        (#(canonTriple D.skeleton (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩)).support : ℝ)
            := by
      rwa [canonTriple_ofFinEmb_eq hxQ, card_support_canonPolyad Q]
    exact hne (by simp [H', hnot])

/-- Deterministic global edit-discrepancy bound for any coupled recoloring witnessing `M`. -/
private theorem approximates3_of_coupled_recoloring
    {H H' : Colored3Graph κ V} {C D : TriadicComplex3 V}
    {M : Polyad3 D.skeleton → Matrix κ κ ℝ} {β N₀ g : ℝ}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hβ : 0 < β) (hN₀_pos : 0 < N₀)
    (hdiag : ∀ Q : Polyad3 D.skeleton, N₀ ≤ (#Q.support : ℝ) →
      ∀ c₀, (H.relativeDensity c₀ (canonPolyad Q) : ℝ) * (1 - M (canonPolyad Q) c₀ c₀) =
        max ((H.relativeDensity c₀ (canonPolyad Q) : ℝ) -
          H.relativeDensity c₀ ((canonPolyad Q).coarsen hV f)) 0)
    (hkeep : ∀ Q : Polyad3 D.skeleton, N₀ ≤ (#Q.support : ℝ) →
      ∀ (S' : Subpolyad3 Q) (c₀ c : κ),
        |(#{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
            H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) -
          M (canonPolyad Q) c₀ c *
            #{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀}| ≤
          β * #Q.support)
    (hsmall : ∀ Q : Polyad3 D.skeleton, ¬N₀ ≤ (#Q.support : ℝ) → H.editedOn H' Q.support = ∅) :
    H.Approximates3 H' (Fintype.card κ * (√g + β)) := by
  let e₃ : {x : Fin 3 → V // Function.Injective x} → Set.powersetCard V 3 :=
    fun x ↦ Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩
  have hedit_Q (Q : Polyad3 D.skeleton) :
      (#(H.editedOn H' Q.support) : ℝ) ≤
        (∑ c₀, #Q.support *
          |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
          Fintype.card κ * β * #Q.support := by
    by_cases hQ : N₀ ≤ (#Q.support : ℝ)
    · have hQ_ne : Q.support.Nonempty := card_pos.1 (by exact_mod_cast hN₀_pos.trans_le hQ)
      set Q₀ := canonPolyad Q
      have hpart : #(H.editedOn H' Q.support) =
          ∑ c₀ : κ, #{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H.color (e₃ x) ≠ H'.color (e₃ x)} := by
        rw [editedOn_def]
        exact card_filter_color_fiberwise H Q.support fun s ↦ H.color s ≠ H'.color s
      rw [hpart, Nat.cast_sum]
      have hbound_c₀ (c₀ : κ) :
          (#{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H.color (e₃ x) ≠ H'.color (e₃ x)} : ℝ) ≤
            #Q.support *
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| +
              β * #Q.support := by
        have hkeep_c₀ := hkeep Q hQ (Subpolyad3.ofSubcells Q Q.c₀ Q.c₁ Q.c₂) c₀ c₀
        rw [Subpolyad3.support_ofSubcells_cells] at hkeep_c₀
        let s₀ := {x ∈ Q.support | H.color (e₃ x) = c₀}
        have hsplit : #{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H.color (e₃ x) ≠ H'.color (e₃ x)} +
            #{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H'.color (e₃ x) = c₀} = #s₀ := by
          rw [← card_filter_add_card_filter_not (s := s₀) (p := fun x ↦ H'.color (e₃ x) = c₀),
            add_comm]
          congr 1 <;> refine congrArg card (ext fun x ↦ ?_) <;> simp only [s₀, mem_filter]
          · exact and_assoc.symm
          · exact ⟨fun ⟨hx, hc₀, hne⟩ ↦ ⟨⟨hx, hc₀⟩, fun hc' ↦ hne (hc₀.trans hc'.symm)⟩,
              fun ⟨⟨hx, hc₀⟩, hne⟩ ↦ ⟨hx, hc₀, fun hc' ↦ hne (hc'.symm.trans hc₀)⟩⟩
        have hdens : (#s₀ : ℝ) = (H.relativeDensity c₀ Q₀ : ℝ) * #Q.support := by
          rw [relativeDensity_canonPolyad H Q c₀, H.relativeDensity_def]
          exact_mod_cast (H.relDensityOn_mul_card c₀ Q.support).symm
        have hkeep_lo : M Q₀ c₀ c₀ * ((H.relativeDensity c₀ Q₀ : ℝ) * #Q.support) -
            β * #Q.support ≤
            (#{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H'.color (e₃ x) = c₀} : ℝ) := by
          dsimp only [Q₀, s₀, e₃] at hdens ⊢
          rw [hdens] at hkeep_c₀
          linarith [(abs_le.1 hkeep_c₀).1]
        have hsplitR :
            (#{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H.color (e₃ x) ≠ H'.color (e₃ x)} : ℝ) +
            (#{x ∈ Q.support | H.color (e₃ x) = c₀ ∧ H'.color (e₃ x) = c₀} : ℝ) =
            (H.relativeDensity c₀ Q₀ : ℝ) * #Q.support := by
          rw [← Nat.cast_add, hsplit, hdens]
        have hdiag_le : (H.relativeDensity c₀ Q₀ : ℝ) * (1 - M Q₀ c₀ c₀) ≤
            |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| := by
          rw [hdiag Q hQ c₀, relativeDensity_canonPolyad H Q c₀,
            relativeDensity_coarsen_canonPolyad hV f hf H hQ_ne c₀]
          exact max_le (le_abs_self _) (abs_nonneg _)
        have hdiag_Q := mul_le_mul_of_nonneg_right hdiag_le (Nat.cast_nonneg (α := ℝ) #Q.support)
        nlinarith
      calc _ ≤ ∑ c₀ : κ, (#Q.support *
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| +
              β * #Q.support) := sum_le_sum fun c₀ _ ↦ hbound_c₀ c₀
        _ = (∑ c₀, #Q.support *
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
              Fintype.card κ * β * #Q.support := by
            rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]; ring
    · rw [hsmall Q hQ, card_empty, Nat.cast_zero]
      exact add_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
        (by positivity)
  have hbi : #(H.editedOn H' univ) = ∑ Q : Polyad3 D.skeleton, #(H.editedOn H' Q.support) := by
    rw [← Polyad3.sum_card_inter_support (S := D.skeleton) (H.editedOn H' univ)]
    refine sum_congr rfl fun Q _ ↦ congrArg card (ext fun x ↦ ?_)
    simp only [mem_inter, mem_editedOn, mem_univ, true_and, and_comm]
  have hsumQ : ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) = (Fintype.card V).descFactorial 3 := by
    simpa [Fintype.card_subtype_injective] using
      (Polyad3.sum_comp_ofTriple (S := D.skeleton) (fun _ ↦ (1 : ℝ))).symm
  refine approximates3_of_card_editedOn_univ_le (by positivity) ?_
  calc (#(H.editedOn H' univ) : ℝ)
      = ∑ Q : Polyad3 D.skeleton, (#(H.editedOn H' Q.support) : ℝ) := by exact_mod_cast hbi
    _ ≤ ∑ Q : Polyad3 D.skeleton, ((∑ c₀, #Q.support *
          |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
          Fintype.card κ * β * #Q.support) := sum_le_sum fun Q _ ↦ hedit_Q Q
    _ = (∑ c₀, ∑ Q : Polyad3 D.skeleton, #Q.support *
          |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
          Fintype.card κ * β * (Fintype.card V).descFactorial 3 := by
        rw [sum_add_distrib, sum_comm, ← mul_sum, hsumQ]
    _ ≤ (∑ _c₀ : κ, √g * (Fintype.card V).descFactorial 3) +
          Fintype.card κ * β * (Fintype.card V).descFactorial 3 := by
        gcongr with c₀
        exact H.sum_card_support_mul_abs_relativeDensity_coarsen_le hV f hf hgap c₀
    _ = Fintype.card κ * (√g + β) * (Fintype.card V).descFactorial 3 := by
        rw [sum_const, card_univ, nsmul_eq_mul]; ring
    _ ≤ Fintype.card κ * (√g + β) * (Fintype.card V : ℝ) ^ 3 := by
        gcongr; exact_mod_cast Nat.descFactorial_le_pow (Fintype.card V) 3

/-- On a large `(η, 1)`-top-regular fine child `Q` of `P`, a coupled recoloring pushes fine
subpolyad counts onto `H.relativeDensity c P` within `|κ| * (η + β) * #Q.support`. -/
private theorem recolored_child_dev_le
    {H H' : Colored3Graph κ V} {C D : TriadicComplex3 V}
    {M : Polyad3 D.skeleton → Matrix κ κ ℝ} {η β : ℝ}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    {P : Polyad3 C.skeleton} {Q : Polyad3 D.skeleton} (hQP : Q.coarsen hV f = P)
    (hQ_ne : Q.support.Nonempty) (hQreg : H.IsTopRegularOverPolyad Q η 1)
    (hMmem : M (canonPolyad Q) ∈ Matrix.rowStochastic ℝ κ)
    (hMpush : (fun c₀ ↦ (H.relativeDensity c₀ (canonPolyad Q) : ℝ)) ᵥ* M (canonPolyad Q) =
      (fun c ↦ (H.relativeDensity c ((canonPolyad Q).coarsen hV f) : ℝ)))
    (hsub : ∀ (S' : Subpolyad3 Q) (c₀ c : κ),
      |(#{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
          H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ) -
        M (canonPolyad Q) c₀ c *
          #{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀}| ≤
        β * #Q.support)
    (c : κ) (S' : Subpolyad3 Q) :
    |(H'.relDensityOn c S'.support : ℝ) - H.relativeDensity c P| * #S'.support ≤
      Fintype.card κ * (η + β) * #Q.support := by
  set Q₀ := canonPolyad Q
  let a (c₀ : κ) : ℝ := #{x ∈ S'.support |
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀ ∧
    H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c}
  let b (c₀ : κ) : ℝ := #{x ∈ S'.support |
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c₀}
  have hnew : (H'.relDensityOn c S'.support : ℝ) * #S'.support = ∑ c₀, a c₀ := by
    have hmul : (H'.relDensityOn c S'.support : ℝ) * #S'.support =
        (#{x ∈ S'.support | H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c} : ℝ)
            := by
      exact_mod_cast H'.relDensityOn_mul_card c S'.support
    rw [hmul, card_filter_color_fiberwise H S'.support fun s ↦ H'.color s = c, Nat.cast_sum]
  have hpush_c : ∑ c₀, (H.relativeDensity c₀ Q₀ : ℝ) * M Q₀ c₀ c =
      H.relativeDensity c (Q₀.coarsen hV f) := by
    simpa [Matrix.vecMul, dotProduct] using congrFun hMpush c
  have htarget : (H.relativeDensity c P : ℝ) * #S'.support =
      ∑ c₀, M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support) := by
    rw [← hQP, ← relativeDensity_coarsen_canonPolyad hV f hf H hQ_ne c, ← hpush_c, sum_mul]
    exact sum_congr rfl fun c₀ _ ↦ by rw [relativeDensity_canonPolyad H Q c₀]; ring
  rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℝ) #S'.support), ← abs_mul, sub_mul,
    hnew, htarget, ← sum_sub_distrib]
  calc |∑ c₀, (a c₀ - M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support))|
      ≤ ∑ c₀, |a c₀ - M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c₀ : κ, (η + β) * #Q.support := by
        refine sum_le_sum fun c₀ _ ↦ ?_
        have hb : b c₀ = (H.relDensityOn c₀ S'.support : ℝ) * #S'.support := by
          dsimp only [b]; exact_mod_cast (H.relDensityOn_mul_card c₀ S'.support).symm
        have hM0 : 0 ≤ M Q₀ c₀ c := Matrix.nonneg_of_mem_rowStochastic hMmem
        have hM1 : M Q₀ c₀ c ≤ 1 := Matrix.le_one_of_mem_rowStochastic hMmem
        have hreg_c₀ : |(H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q| *
            #S'.support ≤ η * #Q.support := by
          simpa only [Subpolyad3.unionSupport_unique] using
            hQreg.abs_relDensityOn_unionSupport_sub_mul_card_le_of_card_le c₀ (by simp)
              (fun _ : Fin 1 ↦ S')
        have hdiff : a c₀ - M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support) =
            (a c₀ - M Q₀ c₀ c * b c₀) +
            M Q₀ c₀ c * (((H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q) *
              #S'.support) := by rw [hb]; ring
        have htri : |a c₀ - M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support)| ≤
            |a c₀ - M Q₀ c₀ c * b c₀| +
            M Q₀ c₀ c * (|(H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q| *
              #S'.support) := by
          rw [hdiff]
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_nonneg hM0, abs_mul, Nat.abs_cast]
        have hM_term := (mul_le_mul hM1 hreg_c₀
          (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (by norm_num)).trans_eq (one_mul _)
        linarith [hsub S' c₀ c]
    _ = Fintype.card κ * (η + β) * #Q.support := by
        rw [sum_const, card_univ, nsmul_eq_mul]; ring

/-- **Orbit-glued coupled recoloring across a polyad energy gap.** Given a coarse complex `C` and
a fine refinement `D` with polyad energy gap at most `g`, for any `β > 0` and size threshold `N₀`
satisfying `221 (3 |V|² + |κ| + 7) ≤ β² N₀`, there exists an `|κ| (√g + β)`-close recoloring `H'`
such that every `(η, 1)`-top-regular fine polyad `Q` of size at least `N₀` has subpolyad
discrepancy against `H.relativeDensity c (Q.coarsen hV f)` bounded by `|κ| (η + β) #Q.support`. -/
theorem exists_coupled_recoloring_of_polyadEnergy_sub_le
    {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {β N₀ g : ℝ}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hβ : 0 < β)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀) :
    ∃ H' : Colored3Graph κ V,
      H.Approximates3 H' (Fintype.card κ * (√g + β)) ∧
      ∀ {P : Polyad3 C.skeleton} {Q : Polyad3 D.skeleton} {η : ℝ},
        Q.coarsen hV f = P → N₀ ≤ (#Q.support : ℝ) → H.IsTopRegularOverPolyad Q η 1 →
          ∀ (c : κ) (S' : Subpolyad3 Q),
            |((H'.relDensityOn c S'.support : ℝ) - H.relativeDensity c P) * #S'.support| ≤
              Fintype.card κ * (η + β) * #Q.support := by
  have hN₀_pos : 0 < N₀ := pos_of_support_lower_bound hN₀
  obtain ⟨H', M, hbig, hsmall⟩ :=
    exists_coupled_recoloring (H := H) (C := C) (D := D) hV f hf hβ hN₀
  refine ⟨H', approximates3_of_coupled_recoloring hV f hf hgap hβ hN₀_pos
    (fun Q hQ ↦ (hbig Q hQ).2.2.1) (fun Q hQ ↦ (hbig Q hQ).2.2.2) hsmall, ?_⟩
  intro P Q η hQP hQ hQreg c S'
  have hQ_ne : Q.support.Nonempty := card_pos.1 (by exact_mod_cast hN₀_pos.trans_le hQ)
  obtain ⟨hMmem, hMpush, -, hsub⟩ := hbig Q hQ
  simpa only [abs_mul, Nat.abs_cast] using
    recolored_child_dev_le hV f hf hQP hQ_ne hQreg hMmem hMpush hsub c S'

end Colored3Graph

end TauCeti
