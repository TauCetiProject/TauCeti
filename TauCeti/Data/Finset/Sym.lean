/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sym

/-!
# Unordered pairs inside the image of an embedding

`Finset.map_sym2Map_sdiff_sym2_map` says that removing the unordered pairs inside the image of
an embedding `l` commutes with pushing a finite set of unordered pairs forward along a further
embedding `g`, when the image of `l` under `g` is the image of `l'`.
-/

public section

namespace Finset

variable {ι U V : Type*} [DecidableEq U] [DecidableEq V]

/-- Removing the pairs inside the image of an embedding `l` commutes with pushing a set of pairs
forward along a further embedding `g`, when the image of `l` under `g` is the image of `l'`. -/
theorem map_sym2Map_sdiff_sym2_map (E : Finset (Sym2 U)) (s : Finset ι) (l : ι ↪ U) (g : U ↪ V)
    {l' : ι ↪ V} (h : l.trans g = l') :
    E.map g.sym2Map \ (s.map l').sym2 = (E \ (s.map l).sym2).map g.sym2Map := by
  rw [← h, ← Finset.map_map, Finset.sym2_map, Finset.map_sdiff]

end Finset
