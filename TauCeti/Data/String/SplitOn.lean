/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-!
# Reassembling a string from its split at a character

Splitting the characters of a string at `c` and joining the pieces with `c` recovers the string.
-/

public section

namespace String

/-- A string is recovered from the pieces of its split at a character by joining them with that
character. -/
theorem toList_eq_intercalate_of_splitOn_eq {s : String} {c : Char} {parts : List String}
    (h : (s.toList.splitOn c).map String.ofList = parts) :
    s.toList = [c].intercalate (parts.map String.toList) := by
  rw [← h, List.map_map, Function.comp_def]
  simp only [String.toList_ofList, List.map_id']
  exact (List.intercalate_splitOn c).symm

end String
