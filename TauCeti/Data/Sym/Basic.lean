/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Sym.Basic

/-!
# Basic lemmas for symmetric powers

This file records small API extensions for Mathlib's symmetric powers.
-/

public section

namespace Sym

variable {X Y : Type*} {d e : ℕ}

/-- Mapping a function over an appended symmetric-power point is the append of the mapped
symmetric-power points. -/
@[simp]
theorem map_append (f : X → Y) (s : Sym X d) (t : Sym X e) :
    Sym.map f (s.append t) = (Sym.map f s).append (Sym.map f t) :=
  Subtype.ext <| by simp [Multiset.map_add]

end Sym
