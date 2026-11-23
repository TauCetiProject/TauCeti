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

Let `A` be a semiring and `R` a ring acting on an `A`-module `M` through `A`-linear maps. If `P` is
finitely generated over `A` and `M` has finite length over `R`, the `R`-module `Hom_A(P, M)` has
finite length (`TauCeti.isFiniteLength_linearMap`): a surjection `Aⁿ → P` embeds it in `Mⁿ`. This
is the finite-length counterpart of `TauCeti.isNoetherian_linearMap_of_finite`.
-/

public section

namespace TauCeti

/-- **Linear maps into a module of finite length.** Let `A` be a semiring and `R` a ring acting on
an `A`-module `M` through `A`-linear maps. If `P` is finitely generated over `A` and `M` has finite
length over `R`, then the `R`-module of `A`-linear maps `P → M` has finite length. -/
theorem isFiniteLength_linearMap {R A : Type*} [Ring R] [Semiring A] (P M : Type*)
    [AddCommMonoid P] [Module A P] [Module.Finite A P] [AddCommGroup M] [Module A M] [Module R M]
    [SMulCommClass A R M] (hM : IsFiniteLength R M) : IsFiniteLength R (P →ₗ[A] M) := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  -- Precomposition with a surjection `A ^ n → P` embeds the maps `P → M` into `M ^ n`.
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  have : IsFiniteLength R (Fin n → M) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact this.of_injective (f := (LinearEquiv.piRing A M (Fin n) R).toLinearMap ∘ₗ
    LinearMap.lcomp R M π) ((LinearEquiv.piRing A M (Fin n) R).injective.comp
      (LinearMap.lcomp_injective_of_surjective π hπ))

end TauCeti
