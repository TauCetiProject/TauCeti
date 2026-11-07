/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Fin

/-!
# The linearly oriented quiver of type A

`LineQuiver n` has vertices `0, …, n - 1` and one arrow from each vertex to its successor.
A directed path exists precisely when its source is at most its target. This characterization
allows constructions on intervals to use the order of the vertices without replacing the
successor quiver by the quiver with an arrow for every comparable pair.
-/

public section

namespace TauCeti

/-- The vertices of the linearly oriented quiver `0 → 1 → ⋯ → n - 1`. -/
@[expose] def LineQuiver (n : ℕ) := Fin n

namespace LineQuiver

variable {n : ℕ}

instance : LinearOrder (LineQuiver n) := inferInstanceAs (LinearOrder (Fin n))

instance : Fintype (LineQuiver n) := inferInstanceAs (Fintype (Fin n))

instance : Quiver (LineQuiver n) where
  Hom i j := PLift (i.val + 1 = j.val)

/-- The unique arrow between two consecutive vertices of the line quiver. -/
def arrow (i j : LineQuiver n) (h : i.val + 1 = j.val) : i ⟶ j := ⟨h⟩

/-- An arrow of the line quiver increases the vertex number by one. -/
theorem val_add_one_eq {i j : LineQuiver n} (e : i ⟶ j) : i.val + 1 = j.val := e.down

/-- Every directed path in the line quiver goes from a smaller vertex to a larger one. -/
theorem le_of_path {i j : LineQuiver n} (p : Quiver.Path i j) : i ≤ j := by
  induction p with
  | nil => exact le_rfl
  | @cons j l p e ih =>
    have he := val_add_one_eq e
    exact le_trans ih (by exact_mod_cast (by omega : j.val ≤ l.val))

/-- Two vertices of the line quiver are joined by a directed path exactly when they are
ordered in the direction of the arrows. -/
theorem nonempty_path_iff_le (i j : LineQuiver n) : Nonempty (Quiver.Path i j) ↔ i ≤ j := by
  refine ⟨fun ⟨p⟩ ↦ le_of_path p, fun hij ↦ ?_⟩
  have h : i.val ≤ j.val := hij
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction m generalizing j with
  | zero =>
    have he : i = j := Fin.ext (by omega)
    subst j
    exact ⟨Quiver.Path.nil⟩
  | succ m ih =>
    let l : LineQuiver n := ⟨j.val - 1, by omega⟩
    have hl : l.val = i.val + m := by dsimp [l]; omega
    obtain ⟨p⟩ := ih l (by exact_mod_cast (by omega : i.val ≤ l.val)) hl
    exact ⟨p.cons ⟨by dsimp [l]; omega⟩⟩

end LineQuiver
end TauCeti
