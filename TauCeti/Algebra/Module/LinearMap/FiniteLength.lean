/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.StdBasis

/-!
# Linear maps into a module of finite length

Over a commutative ring `R`, the linear maps from a finitely generated module `P` to a module `N`
of finite length form a module of finite length (`TauCeti.isFiniteLength_linearMap`): a surjection
`Rⁿ → P` embeds `Hom_R(P, N)` into `Hom_R(Rⁿ, N) ≅ Nⁿ`.
-/

public section

namespace TauCeti

/-- **Linear maps into a module of finite length.** Over a commutative ring, the linear maps from
a finitely generated module to a module of finite length form a module of finite length. -/
theorem isFiniteLength_linearMap {R : Type*} [CommRing R] (P N : Type*) [AddCommGroup P]
    [Module R P] [Module.Finite R P] [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    IsFiniteLength R (P →ₗ[R] N) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R P
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hN
  have : IsFiniteLength R ((Fin n → R) →ₗ[R] N) := (Module.piEquiv (Fin n) R N).isFiniteLength
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  exact this.of_injective (f := g.lcomp R N) fun _ _ h ↦ (LinearMap.cancel_right hg).mp h

end TauCeti
