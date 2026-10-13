/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# The cartesian monoidal structure on topological spaces

The continuous map underlying the tensor product `f ⊗ₘ g` of two morphisms of `TopCat` is the
product map `f.hom.prodMap g.hom`.

## Main results

* `TopCat.hom_tensorHom`: `(f ⊗ₘ g).hom = f.hom.prodMap g.hom`.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace TopCat

/-- The continuous map underlying `f ⊗ₘ g`, for the cartesian monoidal structure on spaces, is the
product map. -/
theorem hom_tensorHom {X X' Y Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g).hom = f.hom.prodMap g.hom :=
  ContinuousMap.ext fun p ↦ tensor_apply f g p

end TopCat
