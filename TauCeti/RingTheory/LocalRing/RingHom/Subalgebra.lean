/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Local homomorphisms into subalgebras

Unit reflection (`IsLocalHom`) passes from an algebra `R → S` to every subalgebra `T` of `S`
(`Subalgebra.isLocalHom_algebraMap`).

## Main results

* `Subalgebra.isLocalHom_algebraMap`: if `R → S` is a local homomorphism, then `R → T` is a local
  homomorphism for every `T : Subalgebra R S`.
-/

public section

namespace Subalgebra

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- If `R → S` reflects units, then so does `R → T` for every subalgebra `T` of `S`. -/
instance isLocalHom_algebraMap [IsLocalHom (algebraMap R S)] (T : Subalgebra R S) :
    IsLocalHom (algebraMap R T) :=
  have : IsLocalHom ((T.val : T →+* S).comp (algebraMap R T)) := by
    rwa [T.val.comp_algebraMap]
  isLocalHom_of_comp _ (T.val : T →+* S)

end Subalgebra
