/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sym

/-!
# Unordered pairs inside the image of an embedding

`Finset.map_sym2Map_sdiff_sym2_map` says that removing the unordered pairs inside a finite set `t`
commutes with pushing a finite set of unordered pairs forward along an embedding `g`, when the
pairs inside `t` are pushed forward along `g` as well.
-/

public section

namespace Finset

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- Removing the pairs inside a finite set `t` commutes with pushing a set of pairs forward along
an embedding `g`, when the pairs inside `t` are pushed forward along `g` as well. -/
theorem map_sym2Map_sdiff_sym2_map (E : Finset (Sym2 U)) (t : Finset U) (g : U ↪ V) :
    E.map g.sym2Map \ (t.map g).sym2 = (E \ t.sym2).map g.sym2Map := by
  rw [Finset.sym2_map, Finset.map_sdiff]

end Finset
