/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# A deformation starting at a map, as a homotopy

A map `H : I × X → Y` which is `f` at time zero is a homotopy from `f` to its time-one map
`H.curry 1` (`ContinuousMap.Homotopy.ofApplyZero`). This packages a deformation, given as a bare
continuous map together with its value at time zero, for the results which take a homotopy.

A deformation of `Y` starting at the identity, keeping subsets `B` and `N` inside themselves and
pushing `N` into `B` at time one, is in particular a homotopy from the identity to a map carrying
`N` into `B` (`ContinuousMap.exists_homotopy_id_of_deformation`): these are the hypotheses under
which enlarging the subspace `B` of a pair to `N` induces isomorphisms on relative singular homology
and cohomology.
-/

public section

open scoped unitInterval

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}

/-- A map `H : I × X → Y` which is `f` at time zero, as a homotopy from `f` to its time-one map
`H.curry 1`. -/
def ofApplyZero (H : C(I × X, Y)) (hH : ∀ x, H (0, x) = f x) : f.Homotopy (H.curry 1) where
  toContinuousMap := H
  map_zero_left := hH
  map_one_left x := (H.curry_apply 1 x).symm

@[simp]
theorem ofApplyZero_apply (H : C(I × X, Y)) (hH : ∀ x, H (0, x) = f x) (p : I × X) :
    ofApplyZero H hH p = H p :=
  (rfl)

end ContinuousMap.Homotopy

namespace ContinuousMap

open Homotopy Set

/-- **A deformation as a homotopy from the identity.** A deformation `H` of `Y` which starts at the
identity, keeps `B` and `N` inside themselves and pushes `N` into `B` at time one is a homotopy from
the identity of `Y` to a map carrying `N` into `B`, keeping `B` and `N` inside themselves. These are
the hypotheses of `TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy` and of its
cohomology form. -/
theorem exists_homotopy_id_of_deformation {Y : Type*} [TopologicalSpace Y] {B N : Set Y}
    (H : C(I × Y, Y)) (hH₀ : ∀ y, H (0, y) = y) (hHB : ∀ t, ∀ y ∈ B, H (t, y) ∈ B)
    (hHN : ∀ t, ∀ y ∈ N, H (t, y) ∈ N) (hH₁ : ∀ y ∈ N, H (1, y) ∈ B) :
    ∃ (ρ : C(Y, Y)) (G : (ContinuousMap.id Y).Homotopy ρ),
      (∀ (τ : I) (y : Y), y ∈ B → G (τ, y) ∈ B) ∧ (∀ (τ : I) (y : Y), y ∈ N → G (τ, y) ∈ N) ∧
        MapsTo ρ N B := by
  have hH₀' (y : Y) : H (0, y) = ContinuousMap.id Y y :=
    (hH₀ y).trans (ContinuousMap.id_apply y).symm
  refine ⟨H.curry 1, ofApplyZero H hH₀', fun τ y hy ↦ ?_, fun τ y hy ↦ ?_, fun y hy ↦ ?_⟩
  · rw [ofApplyZero_apply]
    exact hHB τ y hy
  · rw [ofApplyZero_apply]
    exact hHN τ y hy
  · rw [ContinuousMap.curry_apply]
    exact hH₁ y hy

end ContinuousMap
