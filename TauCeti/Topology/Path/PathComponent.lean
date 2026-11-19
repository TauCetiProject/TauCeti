/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Path

/-!
# Paths in a subspace containing a path component

Every path starting at `a` stays in the path component of `a` (`Path.mem_pathComponent`). So for a
subspace `S` containing that path component, mapping along the inclusion is a homeomorphism from
the paths in `S` to the paths in the ambient space with the same endpoints
(`Path.subtypeHomeomorphOfPathComponentSubset`), with inverse the corestriction `Path.codRestrict`.
In particular the loop space of a path component, at any of its points, is the loop space of the
ambient space at that point.

## Main declarations

* `Path.subtypeHomeomorphOfPathComponentSubset`: paths in a subspace containing the path component
  of their source are the paths in the ambient space.
-/

public section

open scoped unitInterval
open Topology

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- **Paths in a subspace containing a path component.** If a subspace `S` contains the path
component of `a ∈ S`, mapping along the inclusion identifies the paths in `S` from `a` to `b` with
the paths in the ambient space with the same endpoints. The inverse corestricts a path to `S`,
which it never leaves (`Path.mem_pathComponent`). -/
def subtypeHomeomorphOfPathComponentSubset {S : Set X} {a b : S}
    (hS : pathComponent (a : X) ⊆ S) : Path a b ≃ₜ Path (a : X) (b : X) where
  toFun γ := γ.map continuous_subtype_val
  invFun γ := γ.codRestrict fun t ↦ hS (γ.mem_pathComponent t)
  left_inv γ := by
    ext t
    simp
  right_inv γ := map_codRestrict γ _
  continuous_toFun := continuous_induced_rng.2 <|
    (ContinuousMap.continuous_postcomp ⟨Subtype.val, continuous_subtype_val⟩).comp
      continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 <|
    (ContinuousMap.isInducing_postcomp ⟨Subtype.val, continuous_subtype_val⟩
      IsInducing.subtypeVal).continuous_iff.2 <| continuous_induced_dom.congr fun γ ↦ by
        ext t
        simp

@[simp]
theorem subtypeHomeomorphOfPathComponentSubset_apply {S : Set X} {a b : S}
    (hS : pathComponent (a : X) ⊆ S) (γ : Path a b) (t : I) :
    subtypeHomeomorphOfPathComponentSubset hS γ t = γ t :=
  (rfl)

@[simp]
theorem coe_subtypeHomeomorphOfPathComponentSubset_symm_apply {S : Set X} {a b : S}
    (hS : pathComponent (a : X) ⊆ S) (γ : Path (a : X) (b : X)) (t : I) :
    ((subtypeHomeomorphOfPathComponentSubset hS).symm γ t : X) = γ t :=
  codRestrict_coe γ _ t

end Path
