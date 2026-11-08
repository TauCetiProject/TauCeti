/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Partition.Equipartition
public import TauCeti.Data.Nat.RoundUp
public import TauCeti.Order.Partition.Finpartition
import Mathlib.Tactic.Linarith

/-!
# Padding finite equipartitions to divisible equal cells

An equipartition can be embedded, without splitting or merging any original cell, into a
partition with exactly equal cell sizes divisible by a prescribed positive integer `q`.
If there are `t` original cells, fewer than `q * t` vertices need to be added. The padded host
is a rectangle `P.parts × Fin m`: its first coordinate names the original cell, and every
padded cell is a full fiber of that coordinate.

This removes divisibility restrictions in finite regularity arguments. The embedding preserves
cell membership exactly; it is not merely an almost-refinement. No finiteness assumption on the
ambient type is needed, only on the set being partitioned.

The embedding uses Mathlib's `Finpartition.equivSigmaParts` and `Fin.castLEEmb` on each fiber.
The padded partition is Mathlib's `Finpartition.ofSetoid` for equality of first coordinates.
-/

public section

open Finset

namespace Finpartition

variable {V : Type*} [DecidableEq V] {s : Finset V} {P : Finpartition s}

/-- The largest cell of a nonempty equipartition exceeds the mean cell size by less than one.
This integral form also covers equipartitions whose cells already have equal sizes. -/
theorem IsEquipartition.card_parts_mul_sup_card_lt (hP : P.IsEquipartition)
    (hs : s.Nonempty) : #P.parts * P.parts.sup card < #s + #P.parts := by
  obtain ⟨A, hA, hmax⟩ := exists_mem_eq_sup P.parts (P.parts_nonempty hs.ne_empty) card
  have hle (B) (hB : B ∈ P.parts) : P.parts.sup card ≤ #B + 1 := by
    rw [hmax]
    exact hP hA hB
  have hlt : (∑ _B ∈ P.parts, P.parts.sup card) < ∑ B ∈ P.parts, (#B + 1) := by
    apply sum_lt_sum (fun B hB ↦ hle B hB)
    exact ⟨A, hA, by omega⟩
  simpa [sum_add_distrib, P.sum_card_parts, mul_comm] using hlt

/-- A partition whose cells have size at most `m` embeds into a rectangle with one fiber per
cell. The first coordinate of the embedding records cell membership exactly. -/
theorem exists_embedding_prod_fin (P : Finpartition s) {m : ℕ}
    (hm : ∀ A ∈ P.parts, #A ≤ m) :
    ∃ e : s ↪ P.parts × Fin m, ∀ (A : P.parts) (x : s), (e x).1 = A ↔ x.1 ∈ A.1 := by
  let f (A : P.parts) : A.1 ↪ Fin m :=
    A.1.equivFin.toEmbedding.trans (Fin.castLEEmb (hm A.1 A.2))
  let e := P.equivSigmaParts.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl _) f).trans
      (Equiv.sigmaEquivProd P.parts (Fin m)).toEmbedding)
  refine ⟨e, fun A x ↦ ?_⟩
  -- The sigma enumeration and its fiberwise embeddings leave the cell index unchanged.
  have hfst (x : s) : (e x).1 = ⟨P.part x.1, P.part_mem.2 x.2⟩ := by
    simp [e, equivSigmaParts, Function.Embedding.sigmaMap, Equiv.sigmaEquivProd, Sigma.map]
  rw [hfst, Subtype.ext_iff]
  exact P.part_eq_iff_mem A.2

/-- **Divisible padding of an equipartition.** A nonempty equipartition admits a cell-preserving
embedding into a rectangle with common positive cell size `m` divisible by `q`. The fibers
form an equipartition with exactly as many cells as the original partition, and fewer than
`q * #P.parts` vertices lie outside the embedded original set. -/
theorem IsEquipartition.exists_divisible_padding (hP : P.IsEquipartition) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q) :
    ∃ (m : ℕ) (e : s ↪ P.parts × Fin m)
      (Q : Finpartition (univ : Finset (P.parts × Fin m))),
      0 < m ∧ q ∣ m ∧ Q.IsEquipartition ∧ #Q.parts = #P.parts ∧
      Q.parts = univ.image (fun A : P.parts ↦ {A} ×ˢ (univ : Finset (Fin m))) ∧
      (∀ B ∈ Q.parts, #B = m) ∧
      (∀ (A : P.parts) (x : s), e x ∈ {A} ×ˢ (univ : Finset (Fin m)) ↔ x.1 ∈ A.1) ∧
      Fintype.card (P.parts × Fin m) < #s + q * #P.parts := by
  classical
  -- Round the largest cell size up to a multiple of `q`.
  obtain ⟨m, hqm, hmlo, hmhi⟩ := Nat.exists_dvd_between_of_pos hq (P.parts.sup card)
  have hM : 0 < P.parts.sup card := by
    obtain ⟨A, hA⟩ := P.parts_nonempty hs.ne_empty
    exact (card_pos.2 (P.nonempty_of_mem_parts hA)).trans_le (le_sup hA)
  have hmpos := hM.trans_le hmlo
  obtain ⟨e, he⟩ := P.exists_embedding_prod_fin (m := m)
    (fun A hA ↦ (le_sup hA).trans hmlo)
  have : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
  obtain ⟨Q, hparts, hcard⟩ :=
    TauCeti.exists_parts_eq_image_singleton_prod (α := P.parts) (β := Fin m)
  simp only [Fintype.card_fin] at hcard
  have hinj : Function.Injective
      (fun A : P.parts ↦ {A} ×ˢ (univ : Finset (Fin m))) := by
    intro A B h
    have hmem : (A, (⟨0, hmpos⟩ : Fin m)) ∈ {A} ×ˢ (univ : Finset (Fin m)) := by simp
    simp only at h
    rw [h] at hmem
    simpa only [mem_product, mem_singleton, mem_univ, and_true] using hmem
  refine ⟨m, e, Q, hmpos, hqm, ?_, ?_, hparts, hcard, ?_, ?_⟩
  · intro A B hA hB
    simp only [hcard A hA, hcard B hB]
    omega
  · rw [hparts, card_image_of_injective _ hinj, card_univ, Fintype.card_coe]
  · intro A x
    simpa only [mem_product, mem_singleton, mem_univ, and_true] using he A x
  · -- Rounding costs at most `q - 1` per cell; equitability costs strictly less than one.
    have hgap := hP.card_parts_mul_sup_card_lt hs
    have hround := Nat.mul_le_mul_left #P.parts (by omega : m + 1 ≤ P.parts.sup card + q)
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    nlinarith

end Finpartition
