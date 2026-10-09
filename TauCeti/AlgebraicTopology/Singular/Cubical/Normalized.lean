/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Chains

/-!
# Normalized cubical chains

The **degenerate chains** `D_n(X; R)` are the span of the degenerate singular `n`-cubes inside the
unnormalized cubical chains.  They form a subcomplex: on a cube `c` degenerate at the coordinate
`i`, the two `i`-terms of `∂ c` cancel, because the two `i`-faces of `c` coincide
(`face_eq_of_isDegenerateAt`), and every other term is a degenerate cube
(`isDegenerate_face_of_ne`).  The **normalized cubical chains** `C^□_n(X; R)` are the quotient
`CubicalChain X R n ⧸ D_n`, with the induced boundary, and they are the cubical singular chains of
Massey, *Singular Homology Theory*, Chapter II.

Degenerate cubes are preserved by composition with a continuous map, so the push-forward descends
to the quotient and the normalized chains are functorial.

## Main definitions

* `TauCeti.CubicalChain.degenerate X R n`: the submodule spanned by the degenerate `n`-cubes.
* `TauCeti.NormalizedCubicalChain X R n`: the normalized cubical `n`-chains.
* `TauCeti.NormalizedCubicalChain.boundary X R n`: the induced boundary.
* `TauCeti.NormalizedCubicalChain.map f n`: the push-forward along a continuous map.

## Main results

* `TauCeti.CubicalChain.boundary_mem_degenerate`: the boundary of a degenerate chain is degenerate.
* `TauCeti.CubicalChain.degenerate_zero`: there are no degenerate `0`-chains.
* `TauCeti.NormalizedCubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0` on normalized chains.
* `TauCeti.NormalizedCubicalChain.map_boundary`: the boundary is natural.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (R : Type*) [CommRing R]

namespace CubicalChain

open SingularCube

variable (X) in
/-- The **degenerate `n`-chains**: the span of the degenerate singular `n`-cubes. -/
def degenerate (n : ℕ) : Submodule R (CubicalChain X R n) :=
  Submodule.span R {f | ∃ c : SingularCube X n, IsDegenerate c ∧ f = single c 1}

theorem single_mem_degenerate {n : ℕ} {c : SingularCube X n} (hc : IsDegenerate c) (a : R) :
    single c a ∈ degenerate X R n := by
  rw [← smul_single_one]
  exact Submodule.smul_mem _ a (Submodule.subset_span ⟨c, hc, rfl⟩)

/-- The boundary of a degenerate cube is a degenerate chain: the two terms of the degenerate
coordinate cancel, and every other face is degenerate. -/
theorem boundary_single_mem_degenerate {n : ℕ} {c : SingularCube X (n + 1)}
    (hc : IsDegenerate c) : boundary X R n (single c 1) ∈ degenerate X R n := by
  obtain ⟨i, hi⟩ := isDegenerate_iff.1 hc
  rw [boundary_single]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
  by_cases hij : i = j
  · subst hij
    rw [face_eq_of_isDegenerateAt hi 0 1, sub_self]
    exact Submodule.zero_mem _
  · exact Submodule.sub_mem _ (single_mem_degenerate R (isDegenerate_face_of_ne hi hij 0) 1)
      (single_mem_degenerate R (isDegenerate_face_of_ne hi hij 1) 1)

/-- The degenerate chains form a subcomplex. -/
theorem boundary_mem_degenerate {n : ℕ} {f : CubicalChain X R (n + 1)}
    (hf : f ∈ degenerate X R (n + 1)) : boundary X R n f ∈ degenerate X R n := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hc, rfl⟩ := hf
    exact boundary_single_mem_degenerate R hc
  | zero => simp
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [map_smul]; exact Submodule.smul_mem _ a hf

/-- There are no degenerate `0`-chains: a `0`-cube is a point. -/
theorem degenerate_zero : degenerate X R 0 = ⊥ := by
  rw [degenerate, Submodule.span_eq_bot]
  rintro f ⟨c, hc, rfl⟩
  exact (not_isDegenerate_zero c hc).elim

theorem degenerate_le_comap_boundary (n : ℕ) :
    degenerate X R (n + 1) ≤ (degenerate X R n).comap (boundary X R n) :=
  fun _ hf ↦ boundary_mem_degenerate R hf

/-- The push-forward of a degenerate chain is degenerate. -/
theorem map_mem_degenerate (f : C(X, Y)) {n : ℕ} {g : CubicalChain X R n}
    (hg : g ∈ degenerate X R n) : map R f n g ∈ degenerate Y R n := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c, hc, rfl⟩ := hg
    rw [map_single]
    exact single_mem_degenerate R (hc.comp f) 1
  | zero => simp
  | add g h _ _ hg hh => rw [map_add]; exact Submodule.add_mem _ hg hh
  | smul a g _ hg => rw [map_smul]; exact Submodule.smul_mem _ a hg

theorem degenerate_le_comap_map (f : C(X, Y)) (n : ℕ) :
    degenerate X R n ≤ (degenerate Y R n).comap (map R f n) :=
  fun _ hg ↦ map_mem_degenerate R f hg

end CubicalChain

/-- The **normalized cubical `n`-chains** of `X` with coefficients in `R`: the unnormalized chains
modulo the degenerate ones. -/
abbrev NormalizedCubicalChain (X : Type*) [TopologicalSpace X] (R : Type*) [CommRing R]
    (n : ℕ) : Type _ :=
  CubicalChain X R n ⧸ CubicalChain.degenerate X R n

namespace NormalizedCubicalChain

open CubicalChain

variable (X) in
/-- The class of a singular cube in the normalized chains. -/
def ofCube {n : ℕ} (c : SingularCube X n) : NormalizedCubicalChain X R n :=
  Submodule.Quotient.mk (single c 1)

theorem ofCube_eq_mk {n : ℕ} (c : SingularCube X n) :
    ofCube X R c = Submodule.Quotient.mk (single c 1) := by
  rw [ofCube]

theorem ofCube_eq_zero {n : ℕ} {c : SingularCube X n} (hc : SingularCube.IsDegenerate c) :
    ofCube X R c = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (single_mem_degenerate R hc 1)

variable (X) in
/-- The boundary of normalized cubical chains, induced by the boundary of the unnormalized ones. -/
def boundary (n : ℕ) : NormalizedCubicalChain X R (n + 1) →ₗ[R] NormalizedCubicalChain X R n :=
  Submodule.mapQ _ _ (CubicalChain.boundary X R n) (degenerate_le_comap_boundary R n)

@[simp]
theorem boundary_mk {n : ℕ} (f : CubicalChain X R (n + 1)) :
    boundary X R n (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (CubicalChain.boundary X R n f) :=
  Submodule.mapQ_apply _ _ _ f

/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) : boundary X R n ∘ₗ boundary X R (n + 1) = 0 := by
  refine LinearMap.ext ((Submodule.Quotient.mk_surjective _).forall.2 fun f ↦ ?_)
  rw [LinearMap.comp_apply, boundary_mk, boundary_mk, LinearMap.zero_apply,
    Submodule.Quotient.mk_eq_zero]
  rw [← LinearMap.comp_apply, CubicalChain.boundary_boundary, LinearMap.zero_apply]
  exact Submodule.zero_mem _

/-- Normalized cubical chains pushed forward along a continuous map. -/
def map (f : C(X, Y)) (n : ℕ) : NormalizedCubicalChain X R n →ₗ[R] NormalizedCubicalChain Y R n :=
  Submodule.mapQ _ _ (CubicalChain.map R f n) (degenerate_le_comap_map R f n)

@[simp]
theorem map_mk (f : C(X, Y)) {n : ℕ} (g : CubicalChain X R n) :
    map R f n (Submodule.Quotient.mk g) = Submodule.Quotient.mk (CubicalChain.map R f n g) :=
  Submodule.mapQ_apply _ _ _ g

theorem map_id (n : ℕ) : map R (ContinuousMap.id X) n = LinearMap.id := by
  refine LinearMap.ext ((Submodule.Quotient.mk_surjective _).forall.2 fun g ↦ ?_)
  rw [map_mk, CubicalChain.map_id, LinearMap.id_apply, LinearMap.id_apply]

theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) (n : ℕ) :
    map R (g.comp f) n = map R g n ∘ₗ map R f n := by
  refine LinearMap.ext ((Submodule.Quotient.mk_surjective _).forall.2 fun h ↦ ?_)
  rw [map_mk, LinearMap.comp_apply, map_mk, map_mk, CubicalChain.map_comp, LinearMap.comp_apply]

/-- The boundary is natural. -/
theorem map_boundary (f : C(X, Y)) (n : ℕ) :
    map R f n ∘ₗ boundary X R n = boundary Y R n ∘ₗ map R f (n + 1) := by
  refine LinearMap.ext ((Submodule.Quotient.mk_surjective _).forall.2 fun g ↦ ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, boundary_mk, map_mk, map_mk, boundary_mk,
    ← LinearMap.comp_apply, CubicalChain.map_boundary, LinearMap.comp_apply]

end NormalizedCubicalChain

end TauCeti

end
