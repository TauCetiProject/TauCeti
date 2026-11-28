/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

/-!
# Modules over the double opposite

Restriction along the double-opposite equivalence identifies modules over `C` with
modules over `Cᵒᵖᵒᵖ`. This lets a left module over `C` serve as a right module over
`Cᵒᵖ` when interchanging the factors of a tensor product. The equivalence is the
specialization of `CategoryTheory.Equivalence.additiveCongrLeft` to this reindexing.
-/

public section

open CategoryTheory Opposite

universe w v u

namespace TauCeti.ModCat

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Restriction along `unopUnop` identifies left modules over `C` with
left modules over `Cᵒᵖᵒᵖ`. The underlying groups compute by restriction, so an element
of a module can be used directly as an element of the reindexed module. -/
abbrev opOpEquiv : ModCat.{w} C ≌ ModCat.{w} Cᵒᵖᵒᵖ :=
  letI : (opOpEquivalence Cᵒᵖ).symm.functor.Additive := ⟨by intros; rfl⟩
  (opOpEquivalence Cᵒᵖ).symm.additiveCongrLeft

end TauCeti.ModCat
