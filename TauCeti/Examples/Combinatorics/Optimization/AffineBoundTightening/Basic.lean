/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Optimization.AffineBoundTightening.Basic
import Mathlib.Tactic.NormNum

/-!
# Examples for joint raw boxes and public interval states

Checks for `TauCeti.AffineBoundTightening.pack`:

* **Invalid tuples (`pack_inverted_eq_bot`, `pack_inverted_row_eq_bot`):** the one-coordinate tuple
  with lower endpoint `1` and upper endpoint `0` packs to the global bottom, both as a variable
  coordinate (`n = 1`, `m = 0`) and as a row coordinate (`n = 0`, `m = 1`).
* **Unit boxes (`half_mem_pack_unit`, `half_mem_pack_unit_row`):** the box `[0, 1]` contains
  `1 / 2`, again with no rows and with no variables respectively.
* **Singletons:** the singleton tuple `(x, x)` contains exactly `x`.
* **No coordinates:** for `n = m = 0` the
  unique raw tuple packs to a state different from the global bottom that contains the unique
  empty function.
-/

public section

namespace TauCeti.AffineBoundTightening

/-- With one variable and no rows, lower endpoint `1` above upper endpoint `0` packs to `⊥`. -/
theorem pack_inverted_eq_bot : pack ((fun _ => 1, fun _ => 0) : Raw 1 0) = ⊥ :=
  pack_eq_bot_iff.2 fun h => absurd (h (.inl 0)) (by norm_num)

/-- With no variables and one row, lower endpoint `1` above upper endpoint `0` packs to `⊥`. -/
theorem pack_inverted_row_eq_bot : pack ((fun _ => 1, fun _ => 0) : Raw 0 1) = ⊥ :=
  pack_eq_bot_iff.2 fun h => absurd (h (.inr 0)) (by norm_num)

/-- With one variable and no rows, the box `[0, 1]` contains `1 / 2`. -/
theorem half_mem_pack_unit : (fun _ => 1 / 2) ∈ pack ((fun _ => 0, fun _ => 1) : Raw 1 0) :=
  mem_pack.2 ⟨fun _ => by norm_num, fun _ => by norm_num⟩

/-- With no variables and one row, the box `[0, 1]` contains `1 / 2`. -/
theorem half_mem_pack_unit_row :
    (fun _ => 1 / 2) ∈ pack ((fun _ => 0, fun _ => 1) : Raw 0 1) :=
  mem_pack.2 ⟨fun _ => by norm_num, fun _ => by norm_num⟩

/-- A singleton raw tuple contains exactly its endpoint. -/
example {n m : ℕ} {x y : Coord n m → ℝ} : y ∈ pack (x, x) ↔ y = x := by
  simp

/-- There is exactly one raw tuple with no variables and no rows. -/
example : Subsingleton (Raw 0 0) :=
  inferInstance

/-- With no variables and no rows, every raw tuple packs to a nonbottom state. -/
example (q : Raw 0 0) : pack q ≠ ⊥ :=
  pack_ne_bot_iff.2 fun c => isEmptyElim c

/-- With no variables and no rows, the packed state contains the empty function. -/
example (q : Raw 0 0) : (isEmptyElim : Coord 0 0 → ℝ) ∈ pack q :=
  mem_pack.2 ⟨fun c => isEmptyElim c, fun c => isEmptyElim c⟩

end TauCeti.AffineBoundTightening
