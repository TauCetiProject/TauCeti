/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Projective representations and projective group-algebra modules

A representation `A` is a projective object of `Rep k G` exactly when its group-algebra module
`A.ρ.asModule` is a projective `k[G]`-module (`Rep.projective_iff_moduleProjective`). The proof
transports projectivity along Mathlib's equivalence `Rep.equivalenceModuleMonoidAlgebra`, whose
functor sends `A` to `ModuleCat.of k[G] A.ρ.asModule` by definition, and then compares the
categorical and module-theoretic notions with `IsProjective.iff_projective`.
-/

public section

universe w u v

namespace Rep

open CategoryTheory

/-- A representation is projective in `Rep k G` exactly when its `k[G]`-module is projective. -/
theorem projective_iff_moduleProjective {k : Type u} {G : Type v} [CommRing k] [Monoid G]
    [Small.{w} (MonoidAlgebra k G)] (A : Rep.{w} k G) :
    Projective A ↔ Module.Projective (MonoidAlgebra k G) A.ρ.asModule :=
  -- `equivalenceModuleMonoidAlgebra.functor.obj A` is `ModuleCat.of k[G] A.ρ.asModule` by
  -- definition, so the two equivalences compose.
  (equivalenceModuleMonoidAlgebra.map_projective_iff A).symm.trans
    (IsProjective.iff_projective A.ρ.asModule).symm

end Rep
