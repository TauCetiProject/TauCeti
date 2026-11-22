/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Subpath

/-!
# Homotopies inside a union of path components

Let `t` be a union of path components of a space `Y`: with every point it contains its whole path
component (`∀ y ∈ t, pathComponent y ⊆ t`). A homotopy `F` from `f₀` to `f₁` moves each point
`f₀ x` along the path `τ ↦ F (τ, x)` (`ContinuousMap.Homotopy.evalAt`), so it never leaves the path
component of `f₀ x`. Hence if `f₀ x` lies in `t`, so does every `F (τ, x)`
(`ContinuousMap.Homotopy.apply_mem`), and in particular `f₁ x`
(`ContinuousMap.Homotopic.apply_mem`). So homotopic maps with values in `t` are homotopic as maps
into `t` (`ContinuousMap.Homotopic.codRestrict`): the homotopy itself takes values in `t`.

Unions of path components are stable under preimages by continuous maps
(`Continuous.pathComponent_subset_preimage`), since continuous maps send path components into path
components. Examples are a single path component, such as the free loops that are contractible, or
a free homotopy class of loops.

## Main results

* `ContinuousMap.Homotopy.apply_mem`: a homotopy starting in a union of path components stays in it.
* `ContinuousMap.Homotopic.apply_mem`: a map homotopic to a map with values in a union of path
  components takes its values there as well.
* `ContinuousMap.Homotopic.codRestrict`: homotopic maps into a union of path components are
  homotopic as maps into it.
* `Continuous.pathComponent_subset_preimage`: the preimage of a union of path components under a
  continuous map is a union of path components.
-/

public section

open Set unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {t : Set Y}

/-- **The preimage of a union of path components is a union of path components.** A continuous map
sends the path component of `x` into the path component of its image. -/
theorem Continuous.pathComponent_subset_preimage {f : X → Y} (hf : Continuous f)
    (ht : ∀ y ∈ t, pathComponent y ⊆ t) {x : X} (hx : x ∈ f ⁻¹' t) :
    pathComponent x ⊆ f ⁻¹' t :=
  fun _ hz ↦ ht _ hx (hf.mapsTo_pathComponent x hz)

namespace ContinuousMap

variable {f₀ f₁ : C(X, Y)}

/-- **A homotopy starting in a union of path components stays in it.** If `f₀ x` lies in a union
`t` of path components, then so does `F (τ, x)` at every time `τ` of a homotopy `F` from `f₀`. -/
theorem Homotopy.apply_mem (F : f₀.Homotopy f₁) (ht : ∀ y ∈ t, pathComponent y ⊆ t) {x : X}
    (hx : f₀ x ∈ t) (τ : I) : F (τ, x) ∈ t := by
  -- The path traced by `x` under `F`, up to time `τ`, joins `f₀ x = F (0, x)` to `F (τ, x)`.
  have hj : Nonempty (Path (f₀ x) (F (τ, x))) := by
    simpa using (⟨(F.evalAt x).subpath 0 τ⟩ : Nonempty (Path _ _))
  exact ht _ hx (mem_pathComponent_iff.2 hj)

/-- **Homotopic maps take values in the same unions of path components.** If `f₀` is homotopic to
`f₁` and `f₀ x` lies in a union `t` of path components, then so does `f₁ x`. -/
theorem Homotopic.apply_mem (h : f₀.Homotopic f₁) (ht : ∀ y ∈ t, pathComponent y ⊆ t) {x : X}
    (hx : f₀ x ∈ t) : f₁ x ∈ t := by
  obtain ⟨F⟩ := h
  simpa using F.apply_mem ht hx 1

/-- **Homotopic maps into a union of path components are homotopic as maps into it.** If `f₀` and
`f₁` are homotopic and take their values in a union `t` of path components, then their
corestrictions to `t` are homotopic: the homotopy between them never leaves `t`. -/
theorem Homotopic.codRestrict (h : f₀.Homotopic f₁) (ht : ∀ y ∈ t, pathComponent y ⊆ t)
    (h₀ : ∀ x, f₀ x ∈ t) (h₁ : ∀ x, f₁ x ∈ t) :
    (⟨t.codRestrict f₀ h₀, f₀.continuous.codRestrict h₀⟩ : C(X, t)).Homotopic
      ⟨t.codRestrict f₁ h₁, f₁.continuous.codRestrict h₁⟩ := by
  obtain ⟨F⟩ := h
  exact ⟨{ toFun := t.codRestrict F fun p ↦ F.apply_mem ht (h₀ p.2) p.1
           continuous_toFun := F.continuous.codRestrict _
           map_zero_left := fun x ↦ Subtype.ext (F.apply_zero x)
           map_one_left := fun x ↦ Subtype.ext (F.apply_one x) }⟩

end ContinuousMap
