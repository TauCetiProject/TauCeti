/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Generator.Preadditive

/-!
# The regular module is a separator of finitely generated modules

The regular module detects morphisms of finitely generated modules: a morphism vanishes when its
composite with every morphism out of the regular module does. This is the analogue for
`FGModuleCat R` of Mathlib's `ModuleCat.isSeparator`.

## Main results

* `FGModuleCat.isSeparator`: the regular module is a separator of `FGModuleCat R`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable (R : Type u) [Ring R]

/-- The regular module is a separator of the finitely generated modules, the analogue of Mathlib's
`ModuleCat.isSeparator`: a morphism vanishes when its composite with every morphism out of the
regular module does. -/
theorem _root_.FGModuleCat.isSeparator : IsSeparator (FGModuleCat.of R R) :=
  (Preadditive.isSeparator_iff _).mpr fun M N f h ↦ by
    ext x
    -- `ofHom` and composition unfold by definition, so the composite at `1` is `f (1 • x)`.
    have hx : f.hom.hom ((1 : R) • x) = 0 :=
      congrArg (fun g : FGModuleCat.of R R ⟶ N ↦ g.hom.hom 1)
        (h (FGModuleCat.ofHom (LinearMap.toSpanSingleton R M x)))
    simpa using hx

end TauCeti
