/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Multiset.Range
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Equiv.Fintype

/-!
# Multisets of values indexed by `Fin n`, and enumerations of finsets

The multiset of values of a family `i ↦ g i` indexed by `Fin n`, through the coercion to `ℕ`, is
the image of `Multiset.range n` under `g` (`Fin.univ_val_map_eq_map_range`). This is the multiset
analogue of `Fin.prod_univ_eq_prod_range`, and lets a statement about a family indexed by `Fin n`
be compared with one about an initial segment of `ℕ` without passing through lists. Also
`Fin.exists_embedding_image_univ_eq`: a finset with `m` elements is the image of an embedding of
`Fin m`.
-/

public section

namespace Fin

/-- The multiset of values `g i` for `i : Fin n` is the image of `Multiset.range n` under `g`. -/
theorem univ_val_map_eq_map_range {α : Type*} (g : ℕ → α) (n : ℕ) :
    Finset.univ.val.map (fun i : Fin n ↦ g i) = (Multiset.range n).map g := by
  rw [← Finset.range_val, ← Nat.Iio_eq_range, ← map_valEmbedding_univ, Finset.map_val,
    Multiset.map_map]
  simp only [Function.comp_def, Fin.valEmbedding_apply]

/-- A finset with `m` elements is the image of an embedding of `Fin m`. -/
theorem exists_embedding_image_univ_eq {ι : Type*} [DecidableEq ι] {V : Finset ι} {m : ℕ}
    (hV : V.card = m) : ∃ f : Fin m ↪ ι, (Finset.univ : Finset (Fin m)).image f = V := by
  let e := (Finset.equivFinOfCardEq hV).symm
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype (· ∈ V)), ?_⟩
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).2
  · intro hv
    exact ⟨e.symm ⟨v, hv⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩

end Fin
