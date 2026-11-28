/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Bimod
public import TauCeti.CategoryTheory.Preadditive.ModCat.Submodule

/-!
# One-sided submodules of a bimodule

For a bimodule, forgetting one action gives a family of one-sided modules. A choice of
submodule for each member of this family forms a one-sided submodule of the bimodule.
Inclusion, infima and suprema are computed slice by slice.
-/

public section

open CategoryTheory

universe w

namespace TauCeti

namespace ModCat.Bimod

variable {D : Type*} [Category* D] [Preadditive D]
  {C : Type*} [Category* C] [Preadditive C]

/-- A submodule of each left slice of a bimodule, with the right action forgotten. -/
abbrev LeftSubmodule (M : ModCat.Bimod.{w} D C) :=
  ∀ Y : C, ModCat.Submodule (M.sliceLeft Y)

/-- A submodule of each right slice of a bimodule, with the left action forgotten. -/
abbrev RightSubmodule (M : ModCat.Bimod.{w} D C) :=
  ∀ X : D, ModCat.Submodule (M.sliceRight X)

end ModCat.Bimod

end TauCeti
