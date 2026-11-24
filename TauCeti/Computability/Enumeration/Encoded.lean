/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Serialization
import Mathlib.Data.Finset.Option
import TauCeti.Computability.Primrec.FiniteSet

/-!
# Serialization of coded finite-stage enumerations

Serialize a finite-stage enumeration of an encodable type by serializing its natural
codes. The construction adds at most one element and preserves the limit, even for
arbitrary batches or nonmonotone source stages. A pair enters as a single value, and
a left-tagged value remains distinct from the same value with a right tag.

For products and disjoint sums of enumerations of natural numbers, the input is just
the two binary finite-set codes at each stage. Pairing and parity provide the natural
codes for the resulting stages, and the stage table is effective uniformly in
parameters of the sources.
-/

public section

open Encodable

namespace TauCeti.Enumeration

variable {α : Type*}

/-- Serialize the natural codes of the elements of each stage, then decode the entries. -/
def serializedStageOf [Encodable α] [DecidableEq α] (A : ℕ → Finset α) (s : ℕ) : Finset α :=
  (serializedStage (fun t => (A t).map (encode' α)) s).biUnion
    (fun n => (decode₂ α n).toFinset)

/-- Serialization of coded entries agrees with natural-number serialization under the
encoding map. -/
theorem map_encode_serializedStageOf [Encodable α] [DecidableEq α] (A : ℕ → Finset α) (s : ℕ) :
    (serializedStageOf A s).map (encode' α) =
      serializedStage (fun t => (A t).map (encode' α)) s := by
  ext n
  constructor
  · intro hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hn
    obtain ⟨m, hm, hdec⟩ := Finset.mem_biUnion.mp hx
    rw [Option.mem_toFinset, mem_decode₂] at hdec
    simpa only [Encodable.encode', Function.Embedding.coeFn_mk, hdec] using hm
  · intro hn
    obtain ⟨t, _, ht⟩ := mem_serializedStage.mp hn
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ht
    exact Finset.mem_map.mpr ⟨x, Finset.mem_biUnion.mpr ⟨encode x, hn, by simp⟩, rfl⟩

/-- An element occurs by a serialized stage exactly when its code and some discovery
stage form a pair whose code has been inspected. -/
@[simp]
theorem mem_serializedStageOf [Encodable α] [DecidableEq α] {A : ℕ → Finset α} {s : ℕ} {x : α} :
    x ∈ serializedStageOf A s ↔ ∃ t, Nat.pair (encode x) t < s ∧ x ∈ A t := by
  rw [← Finset.mem_map' (encode' α), map_encode_serializedStageOf, mem_serializedStage]
  simp only [Finset.mem_map']
  simp only [Encodable.encode', Function.Embedding.coeFn_mk]

/-- The typed serialized enumeration starts empty. -/
@[simp]
theorem serializedStageOf_zero [Encodable α] [DecidableEq α] (A : ℕ → Finset α) :
    serializedStageOf A 0 = ∅ := by
  ext x
  simp

/-- The typed serialized stages are increasing. -/
theorem monotone_serializedStageOf [Encodable α] [DecidableEq α] (A : ℕ → Finset α) :
    Monotone (serializedStageOf A) := by
  intro s t h
  rw [← Finset.map_subset_map (f := encode' α), map_encode_serializedStageOf,
    map_encode_serializedStageOf]
  exact monotone_serializedStage _ h

/-- At most one typed entry is added in each transition. -/
theorem card_fresh_serializedStageOf_le_one [Encodable α] [DecidableEq α] (A : ℕ → Finset α)
    (s : ℕ) : (fresh (serializedStageOf A) s).card ≤ 1 := by
  rw [← Finset.card_map (f := encode' α), fresh_eq_sdiff, Finset.map_sdiff,
    map_encode_serializedStageOf, map_encode_serializedStageOf, ← fresh_eq_sdiff]
  exact card_fresh_serializedStage_le_one _ _

/-- Serialization never runs ahead of the original enumeration when it is increasing. -/
theorem serializedStageOf_subset [Encodable α] [DecidableEq α] {A : ℕ → Finset α}
    (hA : Monotone A) (s : ℕ) : serializedStageOf A s ⊆ A s := by
  rw [← Finset.map_subset_map (f := encode' α), map_encode_serializedStageOf]
  exact serializedStage_subset (fun _ _ h => Finset.map_subset_map.mpr (hA h)) s

/-- The binary code of a source stage bounds when all its entries have been serialized. -/
theorem subset_serializedStageOf [Encodable α] [DecidableEq α] (A : ℕ → Finset α) (s : ℕ) :
    A s ⊆ serializedStageOf A
      (Nat.pair (Finset.equivBitIndices.symm ((A s).map (encode' α))) s) := by
  rw [← Finset.map_subset_map (f := encode' α), map_encode_serializedStageOf]
  exact subset_serializedStage (fun t => (A t).map (encode' α)) s

/-- A coded enumeration and its serialization enumerate the same elements. -/
@[simp]
theorem stageLimit_serializedStageOf [Encodable α] [DecidableEq α] (A : ℕ → Finset α) :
    stageLimit (serializedStageOf A) = stageLimit A := by
  ext x
  simp only [mem_stageLimit, mem_serializedStageOf]
  exact ⟨fun ⟨_, t, _, hx⟩ => ⟨t, hx⟩,
    fun ⟨t, hx⟩ => ⟨Nat.pair (encode x) t + 1, t, Nat.lt_succ_self _, hx⟩⟩

/-- The serialized binary stage codes are computable uniformly in the parameters of an
effective family of coded stages. -/
theorem computable_serializedStageOf {ι : Type*} [Primcodable ι] [Encodable α] [DecidableEq α]
    {A : ι → ℕ → Finset α}
    (hA : Computable₂ fun i s => Finset.equivBitIndices.symm ((A i s).map (encode' α))) :
    Computable₂ fun i s =>
      Finset.equivBitIndices.symm ((serializedStageOf (A i) s).map (encode' α)) :=
  (computable_serializedStage (A := fun i s => (A i s).map (encode' α)) hA).of_eq fun ⟨_, _⟩ => by
    simp only [map_encode_serializedStageOf]

/-- Serialize products uniformly from the two effective tables of source stages. -/
theorem computable_serializedStageOf_product {ι : Type*} [Primcodable ι]
    {A B : ι → ℕ → Finset ℕ}
    (hA : Computable₂ fun i s => Finset.equivBitIndices.symm (A i s))
    (hB : Computable₂ fun i s => Finset.equivBitIndices.symm (B i s)) :
    Computable₂ fun i s => Finset.equivBitIndices.symm
      ((serializedStageOf (fun t => A i t ×ˢ B i t) s).map (encode' (ℕ × ℕ))) := by
  apply computable_serializedStageOf
  exact (Primrec.equivBitIndices_symm_product.to_comp.comp hA hB).of_eq fun _ => by simp

/-- Serialize tagged unions uniformly from the two effective tables of source stages. -/
theorem computable_serializedStageOf_disjSum {ι : Type*} [Primcodable ι]
    {A B : ι → ℕ → Finset ℕ}
    (hA : Computable₂ fun i s => Finset.equivBitIndices.symm (A i s))
    (hB : Computable₂ fun i s => Finset.equivBitIndices.symm (B i s)) :
    Computable₂ fun i s => Finset.equivBitIndices.symm
      ((serializedStageOf (fun t => (A i t).disjSum (B i t)) s).map (encode' (ℕ ⊕ ℕ))) := by
  apply computable_serializedStageOf
  exact (Primrec.equivBitIndices_symm_disjSum.to_comp.comp hA hB).of_eq fun _ => by simp

end TauCeti.Enumeration
