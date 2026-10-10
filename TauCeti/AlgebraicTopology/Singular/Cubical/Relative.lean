/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# Relative cubical chains

For a subspace `A ⊆ X`, the normalized cubical chains of `A` push forward to those of `X` along
the inclusion, and the **relative cubical chains** `C^□_n(X, A; R)` are the quotient of the chains
of `X` by this image.  The boundary descends, since it is natural, and the three complexes fit
into the short exact sequence `C^□_*(A) → C^□_*(X) → C^□_*(X, A)`, whose connecting map gives the
long exact sequence of the pair once the complexes are packaged as chain complexes.

## Main definitions

* `TauCeti.NormalizedCubicalChain.supportedIn R A n`: the chains of `X` supported in `A`, the image
  of the chains of `A`.
* `TauCeti.RelativeCubicalChain X A R n`: the relative chains, and their boundary
  `TauCeti.RelativeCubicalChain.boundary`.

## Main results

* `TauCeti.NormalizedCubicalChain.boundary_mem_supportedIn`: the chains supported in `A` form a
  subcomplex.
* `TauCeti.RelativeCubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0` on relative chains.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (R : Type*) [Ring R]

namespace NormalizedCubicalChain

/-- The normalized chains of `X` **supported in** the subspace `A`: the image of the chains of
`A` along the inclusion. -/
def supportedIn (A : Set X) (n : ℕ) : Submodule R (NormalizedCubicalChain X R n) :=
  LinearMap.range (map R (ContinuousMap.subtypeVal A) n)

theorem map_subtypeVal_mem_supportedIn {A : Set X} {n : ℕ} (g : NormalizedCubicalChain A R n) :
    map R (ContinuousMap.subtypeVal A) n g ∈ supportedIn R A n :=
  ⟨g, rfl⟩

/-- The chains supported in a subspace form a subcomplex. -/
theorem boundary_mem_supportedIn {A : Set X} {n : ℕ} {g : NormalizedCubicalChain X R (n + 1)}
    (hg : g ∈ supportedIn R A (n + 1)) : boundary X R n g ∈ supportedIn R A n := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨boundary A R n h, ?_⟩
  rw [← LinearMap.comp_apply, map_boundary, LinearMap.comp_apply]

theorem supportedIn_le_comap_boundary (A : Set X) (n : ℕ) :
    supportedIn R A (n + 1) ≤ (supportedIn R A n).comap (boundary X R n) :=
  fun _ hg ↦ boundary_mem_supportedIn R hg

end NormalizedCubicalChain

/-- The **relative normalized cubical chains** of the pair `(X, A)`: the chains of `X` modulo
those supported in `A`. -/
abbrev RelativeCubicalChain (X : Type*) [TopologicalSpace X] (A : Set X) (R : Type*) [Ring R]
    (n : ℕ) : Type _ :=
  NormalizedCubicalChain X R n ⧸ NormalizedCubicalChain.supportedIn R A n

namespace RelativeCubicalChain

variable (X) (A : Set X)

/-- The boundary of relative chains, induced by the boundary of the chains of `X`. -/
def boundary (n : ℕ) : RelativeCubicalChain X A R (n + 1) →ₗ[R] RelativeCubicalChain X A R n :=
  Submodule.mapQ _ _ (NormalizedCubicalChain.boundary X R n)
    (NormalizedCubicalChain.supportedIn_le_comap_boundary R A n)

@[simp]
theorem boundary_mk {n : ℕ} (g : NormalizedCubicalChain X R (n + 1)) :
    boundary X R A n (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (NormalizedCubicalChain.boundary X R n g) :=
  Submodule.mapQ_apply _ _ _ g

/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) : boundary X R A n ∘ₗ boundary X R A (n + 1) = 0 := by
  refine LinearMap.ext ((Submodule.Quotient.mk_surjective _).forall.2 fun g ↦ ?_)
  rw [LinearMap.comp_apply, boundary_mk, boundary_mk, LinearMap.zero_apply,
    ← LinearMap.comp_apply, NormalizedCubicalChain.boundary_boundary, LinearMap.zero_apply,
    Submodule.Quotient.mk_zero]

/-- The projection from the chains of `X` to the relative chains kills exactly the chains
supported in `A`: the short exact sequence of the pair. -/
theorem ker_mkQ (n : ℕ) :
    LinearMap.ker (NormalizedCubicalChain.supportedIn R A n).mkQ =
      LinearMap.range (NormalizedCubicalChain.map R (ContinuousMap.subtypeVal A) n) :=
  Submodule.ker_mkQ _

end RelativeCubicalChain

end TauCeti

end
