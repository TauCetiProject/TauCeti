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
into the short exact sequence `C^□_*(A) → C^□_*(X) → C^□_*(X, A)`: the projection kills exactly
the chains supported in `A` (`Submodule.ker_mkQ`), and the connecting map gives the long exact
sequence of the pair once the complexes are packaged as chain complexes.

## Main definitions

* `TauCeti.NormalizedCubicalChain.supportedIn R A n`: the chains of `X` supported in `A`, the image
  of the chains of `A`.
* `TauCeti.RelativeCubicalChain X A R n`: the relative chains, their boundary
  `TauCeti.RelativeCubicalChain.boundary` and their push-forward `TauCeti.RelativeCubicalChain.map`
  along a map of pairs.

## Main results

* `TauCeti.NormalizedCubicalChain.boundary_mem_supportedIn`: the chains supported in `A` form a
  subcomplex.
* `TauCeti.RelativeCubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0` on relative chains.
* `TauCeti.RelativeCubicalChain.map_boundary`: the relative boundary is natural.

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

theorem supportedIn_def (A : Set X) (n : ℕ) :
    supportedIn R A n = LinearMap.range (map R (ContinuousMap.subtypeVal A) n) := by
  rw [supportedIn]

/-- The chains supported in a subspace form a subcomplex. -/
theorem boundary_mem_supportedIn {A : Set X} {n : ℕ} {g : NormalizedCubicalChain X R (n + 1)}
    (hg : g ∈ supportedIn R A (n + 1)) : boundary X R n g ∈ supportedIn R A n := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨boundary A R n h, ?_⟩
  rw [← LinearMap.comp_apply, map_boundary, LinearMap.comp_apply]

private theorem supportedIn_le_comap_boundary (A : Set X) (n : ℕ) :
    supportedIn R A (n + 1) ≤ (supportedIn R A n).comap (boundary X R n) :=
  fun _ hg ↦ boundary_mem_supportedIn R hg

/-- A map of pairs `f : (X, A) → (Y, B)` carries the chains supported in `A` to chains supported
in `B`. -/
theorem map_mem_supportedIn {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} {f : C(X, Y)}
    (hf : Set.MapsTo f A B) {n : ℕ} {g : NormalizedCubicalChain X R n}
    (hg : g ∈ supportedIn R A n) : map R f n g ∈ supportedIn R B n := by
  obtain ⟨h, rfl⟩ := hg
  -- `f` restricted to `A`, with values in `B`.
  let f' : C(A, B) :=
    ⟨fun a ↦ ⟨f a, hf a.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hres : (ContinuousMap.subtypeVal B).comp f' = f.comp (ContinuousMap.subtypeVal A) :=
    ContinuousMap.ext fun _ ↦ rfl
  refine ⟨map R f' n h, ?_⟩
  rw [← LinearMap.comp_apply, ← map_comp, hres, map_comp, LinearMap.comp_apply]

private theorem supportedIn_le_comap_map {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y}
    {f : C(X, Y)} (hf : Set.MapsTo f A B) (n : ℕ) :
    supportedIn R A n ≤ (supportedIn R B n).comap (map R f n) :=
  fun _ hg ↦ map_mem_supportedIn R hf hg

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
  rw [boundary, boundary,
    ← Submodule.mapQ_comp (hf := NormalizedCubicalChain.supportedIn_le_comap_boundary R A (n + 1))
      (hg := NormalizedCubicalChain.supportedIn_le_comap_boundary R A n)]
  simp only [NormalizedCubicalChain.boundary_boundary, Submodule.mapQ_zero]

section Map

variable {X A} {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {B : Set Y} {C : Set Z}

/-- The relative chains pushed forward along a map of pairs `f : (X, A) → (Y, B)`. -/
def map (f : C(X, Y)) (hf : Set.MapsTo f A B) (n : ℕ) :
    RelativeCubicalChain X A R n →ₗ[R] RelativeCubicalChain Y B R n :=
  Submodule.mapQ _ _ (NormalizedCubicalChain.map R f n)
    (NormalizedCubicalChain.supportedIn_le_comap_map R hf n)

@[simp]
theorem map_mk (f : C(X, Y)) (hf : Set.MapsTo f A B) {n : ℕ} (g : NormalizedCubicalChain X R n) :
    map R f hf n (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (NormalizedCubicalChain.map R f n g) :=
  Submodule.mapQ_apply _ _ _ g

@[simp]
theorem map_id (n : ℕ) : map R (ContinuousMap.id X) (Set.mapsTo_id A) n = LinearMap.id := by
  unfold map
  simp only [NormalizedCubicalChain.map_id, Submodule.mapQ_id]

theorem map_comp (g : C(Y, Z)) (hg : Set.MapsTo g B C) (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (n : ℕ) : map R (g.comp f) (hg.comp hf) n = map R g hg n ∘ₗ map R f hf n := by
  unfold map
  simp only [NormalizedCubicalChain.map_comp]
  exact Submodule.mapQ_comp _ _ _ _ _ (NormalizedCubicalChain.supportedIn_le_comap_map R hf n)
    (NormalizedCubicalChain.supportedIn_le_comap_map R hg n)

/-- The relative boundary is natural. -/
theorem map_boundary (f : C(X, Y)) (hf : Set.MapsTo f A B) (n : ℕ) :
    map R f hf n ∘ₗ boundary X R A n = boundary Y R B n ∘ₗ map R f hf (n + 1) := by
  unfold map boundary
  rw [← Submodule.mapQ_comp (hf := NormalizedCubicalChain.supportedIn_le_comap_boundary R A n)
      (hg := NormalizedCubicalChain.supportedIn_le_comap_map R hf n),
    ← Submodule.mapQ_comp (hf := NormalizedCubicalChain.supportedIn_le_comap_map R hf (n + 1))
      (hg := NormalizedCubicalChain.supportedIn_le_comap_boundary R B n)]
  simp only [NormalizedCubicalChain.map_boundary]

end Map

end RelativeCubicalChain

end TauCeti

end
