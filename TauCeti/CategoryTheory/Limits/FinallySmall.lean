/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FinallySmall
public import TauCeti.CategoryTheory.Elements

/-!
# Invariance of `InitiallySmall` on categories of elements under natural isomorphism

If `F ≅ G` is a natural isomorphism of functors `C ⥤ Type w`, their categories of elements are
equivalent (`CategoryTheory.NatIso.mapElementsEquiv`), so `InitiallySmall.{w'} G.Elements`
transfers to `InitiallySmall.{w'} F.Elements` (`CategoryTheory.initiallySmall_elements_of_iso`).
-/

public section

universe w w'

namespace CategoryTheory

open Limits

/-- An isomorphism of functors to types transports `InitiallySmall` across their categories of
elements. -/
lemma initiallySmall_elements_of_iso {C : Type*} [Category* C]
    {F G : C ⥤ Type w} (e : F ≅ G) [InitiallySmall.{w'} G.Elements] :
    InitiallySmall.{w'} F.Elements :=
  initiallySmall_of_initial_of_initiallySmall (NatIso.mapElementsEquiv e).inverse

end CategoryTheory
