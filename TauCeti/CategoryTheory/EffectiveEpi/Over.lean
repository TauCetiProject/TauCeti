/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Effective epimorphisms in a slice category

An effective epimorphism remains effective when regarded as a morphism over a fixed base.
The forgetful functor creates colimits and preserves kernel pairs, so the coequalizer
description passes to the slice. This lets descent on carriers be used for group schemes.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C] {S : C}

/-- A morphism in a slice category is effective epi if its underlying morphism is. -/
instance effectiveEpi_of_effectiveEpi_left {X Y : Over S} (f : X ⟶ Y)
    [EffectiveEpi f.left] : EffectiveEpi f := by
  apply effectiveEpi_of_kernelPair
  apply isColimitOfIsColimitCoforkMap (forget S)
  exact isColimitCoforkOfEffectiveEpi f.left _
    ((IsPullback.of_hasPullback f f).map (forget S)).isLimit

end CategoryTheory.Over
