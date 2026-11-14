/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.List

/-!
# Codes of lists

The code of a list over an encodable type depends only on the codes of its entries: it is the
code of the list of natural numbers obtained by encoding each entry, so mapping the entries along
a function that preserves their codes preserves the code of the list. Conversely, reading the code
of a list as a list of natural numbers returns the codes of its entries. Decoding lists along an
embedding of the entries keeps exactly the lists all of whose entries lie in its image
(`Encodable.map_listMap_decode`).
-/

public section

namespace Encodable

variable {α : Type*} [Encodable α]

/-- The code of a list is the code of the list of the codes of its entries. -/
@[simp]
theorem encode_list_map_encode (l : List α) : encode (l.map encode) = encode l := by
  induction l <;> simp [*]

/-- Mapping the entries of a list along a function that preserves their codes preserves the code
of the list. -/
theorem encode_list_map {β : Type*} [Encodable β] {f : α → β} {l : List α}
    (hf : ∀ a ∈ l, encode (f a) = encode a) : encode (l.map f) = encode l := by
  rw [← encode_list_map_encode (l.map f), List.map_map, ← encode_list_map_encode l]
  exact congrArg encode (List.map_congr_left hf)

/-- Decoding lists along an embedding of the entries: if decoding along `f` keeps exactly the
elements passing `p`, decoding lists along `List.map f` keeps exactly the lists all of whose
entries pass `p`. -/
theorem map_listMap_decode {β : Type*} [Encodable β] {f : α → β} {p : β → Bool}
    (h : ∀ n, (decode n).map f = (decode n).filter p) (n : ℕ) :
    (decode (α := List α) n).map (List.map f) =
      (decode (α := List β) n).filter fun l => l.all p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [Option.filter]
    | succ v =>
      have ih2 := ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le v))
      have h1 := h v.unpair.1
      clear ih
      simp only [decode_list_succ]
      revert h1 ih2
      rcases decode (α := α) v.unpair.1 with _ | a <;>
        rcases decode (α := List α) v.unpair.2 with _ | l <;>
        rcases decode (α := β) v.unpair.1 with _ | b <;>
        rcases decode (α := List β) v.unpair.2 with _ | l' <;>
        simp +contextual [Option.filter, Seq.seq]

end Encodable

namespace Denumerable

variable {α : Type*} [Encodable α]

/-- Reading the code of a list as a list of natural numbers gives the codes of its entries. -/
@[simp]
theorem ofNat_encode_list (l : List α) :
    ofNat (List ℕ) (Encodable.encode l) = l.map Encodable.encode := by
  rw [← Encodable.encode_list_map_encode, ofNat_encode]

end Denumerable
