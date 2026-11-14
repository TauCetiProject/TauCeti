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
code of the list of natural numbers obtained by encoding each entry. Conversely, reading the code
of a list as a list of natural numbers returns the codes of its entries.
-/

public section

namespace Encodable

variable {α : Type*} [Encodable α]

/-- The code of a list is the code of the list of the codes of its entries. -/
@[simp]
theorem encode_list_map_encode (l : List α) : encode (l.map encode) = encode l := by
  induction l <;> simp [*]

end Encodable

namespace Denumerable

variable {α : Type*} [Encodable α]

/-- Reading the code of a list as a list of natural numbers gives the codes of its entries. -/
@[simp]
theorem ofNat_encode_list (l : List α) :
    ofNat (List ℕ) (Encodable.encode l) = l.map Encodable.encode := by
  rw [← Encodable.encode_list_map_encode, ofNat_encode]

end Denumerable
