/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Locally quasi-finite morphisms

Formal unramifiedness together with local finite type implies local quasi-finiteness.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A formally unramified morphism that is locally of finite type is locally quasi-finite. -/
instance (priority := low) LocallyQuasiFinite.of_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [hform : FormallyUnramified f] [htype : LocallyOfFiniteType f] :
    LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have hform := hform.formallyUnramified_appLE hU hV e
  have htype := htype.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

end AlgebraicGeometry
