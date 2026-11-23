/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import TauCeti.Topology.Homotopy.Path

/-!
# Point-set topology of path components

Paths and path homotopies based in `pathComponent x₀` remain in that component, without any
local path-connectedness assumption. This gives path connectedness of the component as a
subspace; under local path connectedness of the ambient space, openness of path components also
gives local path connectedness of the subspace.

## Main declarations

* `TauCeti.homotopic_pathComponent_of_map_subtypeVal_homotopic`: path homotopies reflect along
  the inclusion of a path component.
* Instances making `↥(pathComponent x₀)` path connected and locally path connected.
* `TauCeti.pathComponentSelf`: a point viewed in its own path component.
* `ZerothHomotopy.mk_eq_mk_iff`: two points have the same path component exactly when they are
  joined by a path.
* `Joined.eq_of_totallyDisconnectedSpace` and
  `ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace`: in a totally disconnected space,
  the path components are the points.
* `Homeomorph.joined_iff` and `Homeomorph.zerothHomotopyCongr`: a homeomorphism preserves and
  reflects being joined by a path, so it induces a bijection of path components.
* `TauCeti.PathComponentBasepoints`: a choice of a basepoint in each path component, with
  `TauCeti.PathComponentBasepoints.choose` giving one. Each chosen basepoint is joined to the
  points of its component (`TauCeti.PathComponentBasepoints.joined_point_mk`).
* `Path.subtypeHomeomorphOfPathComponentSubset`: paths in a subspace containing the path component
  of their source are the paths in the ambient space. In particular the loop space of a path
  component, at any of its points, is the loop space of the ambient space at that point.
-/

public section

open scoped unitInterval
open Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- Two paths in a path component which are homotopic in the ambient space are already
homotopic in the path component. -/
theorem homotopic_pathComponent_of_map_subtypeVal_homotopic
    {a b : pathComponent x₀} {γ δ : Path a b}
    (h : (γ.map continuous_subtypeVal).Homotopic
      (δ.map continuous_subtypeVal)) :
    γ.Homotopic δ := by
  obtain ⟨H⟩ := h
  have hγmem : ∀ t, (γ.map continuous_subtypeVal) t ∈ pathComponent x₀ := fun t =>
    (γ t).property
  have hmem : ∀ p : I × I, H p ∈ pathComponent x₀ := fun p =>
    Joined.mem_pathComponent
      ((H.evalAt p.2).mem_pathComponent p.1)
      (H.map_zero_left p.2 ▸ hγmem p.2)
  exact Path.homotopic_of_continuous_square (fun p => ⟨H p, hmem p⟩)
    (H.continuous.subtype_mk hmem) (fun t => Subtype.ext (H.map_zero_left t))
    (fun t => Subtype.ext (H.map_one_left t)) (fun t => Subtype.ext (H.source t))
    (fun t => Subtype.ext (H.target t))

/-- The path component of a point, as a subspace, is path connected. -/
instance instPathConnectedSpaceSubtypePathComponent :
    PathConnectedSpace (pathComponent x₀) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

/-- In a locally path connected space the path components are open, hence locally path connected
as subspaces. -/
instance instLocallyPathConnectedSpaceSubtypePathComponent [LocallyPathConnectedSpace X] :
    LocallyPathConnectedSpace (pathComponent x₀) :=
  (IsOpen.pathComponent x₀).locallyPathConnectedSpace

/-- The basepoint of `X`, viewed as a point of its own path component. -/
abbrev pathComponentSelf : (pathComponent x₀ : Set X) :=
  ⟨x₀, mem_pathComponent_self x₀⟩

/-- Two points lie in the same path component exactly when they are joined by a path. -/
@[simp]
theorem _root_.ZerothHomotopy.mk_eq_mk_iff {x y : X} :
    ZerothHomotopy.mk x = ZerothHomotopy.mk y ↔ Joined x y :=
  ⟨Quotient.exact, fun h ↦ ZerothHomotopy.sound h.somePath⟩

/-- In a totally disconnected space, points joined by a path are equal. -/
theorem _root_.Joined.eq_of_totallyDisconnectedSpace [TotallyDisconnectedSpace X] {x y : X}
    (h : Joined x y) : x = y := by
  obtain ⟨γ⟩ := h
  simpa using (isPreconnected_range γ.continuous).subsingleton
    (Set.mem_range_self 0) (Set.mem_range_self 1)

/-- In a totally disconnected space, distinct points lie in distinct path components. -/
theorem _root_.ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace
    [TotallyDisconnectedSpace X] : Function.Injective (ZerothHomotopy.mk (X := X)) :=
  fun _ _ h ↦ Joined.eq_of_totallyDisconnectedSpace (Quotient.exact h)

section Homeomorph

variable {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y)

/-- Two points are joined by a path exactly when their images under a homeomorphism are. -/
@[simp]
theorem _root_.Homeomorph.joined_iff {a b : X} : Joined (e a) (e b) ↔ Joined a b :=
  ⟨fun h ↦ by simpa using h.map e.symm.continuous, fun h ↦ h.map e.continuous⟩

/-- A homeomorphism induces a bijection of the sets of path components. -/
def _root_.Homeomorph.zerothHomotopyCongr : ZerothHomotopy X ≃ ZerothHomotopy Y :=
  Quotient.congr e.toEquiv fun _ _ ↦ e.joined_iff.symm

@[simp]
theorem _root_.Homeomorph.zerothHomotopyCongr_mk (a : X) :
    e.zerothHomotopyCongr (.mk a) = .mk (e a) := by
  rw [Homeomorph.zerothHomotopyCongr.eq_1]
  -- `Quotient.congr` computes on the class `ZerothHomotopy.mk a = Quotient.mk _ a`
  rfl

@[simp]
theorem _root_.Homeomorph.zerothHomotopyCongr_symm_mk (b : Y) :
    e.zerothHomotopyCongr.symm (.mk b) = .mk (e.symm b) := by
  rw [Equiv.symm_apply_eq, Homeomorph.zerothHomotopyCongr_mk, Homeomorph.apply_symm_apply]

end Homeomorph

/-- A choice of a basepoint in each path component of a space: a section of the projection
`ZerothHomotopy.mk` to the set of path components. -/
@[ext]
structure PathComponentBasepoints (X : Type*) [TopologicalSpace X] where
  /-- The chosen basepoint of a path component. -/
  point : ZerothHomotopy X → X
  /-- The chosen basepoint of a path component lies in that component. -/
  mk_point : ∀ c, ZerothHomotopy.mk (point c) = c

attribute [simp] PathComponentBasepoints.mk_point

/-- Some choice of a basepoint in each path component, through a right inverse of the surjection
`ZerothHomotopy.mk`. -/
noncomputable def PathComponentBasepoints.choose (X : Type*) [TopologicalSpace X] :
    PathComponentBasepoints X :=
  ⟨Function.surjInv ZerothHomotopy.mk_surjective, Function.surjInv_eq _⟩

instance (X : Type*) [TopologicalSpace X] : Nonempty (PathComponentBasepoints X) :=
  ⟨PathComponentBasepoints.choose X⟩

/-- The chosen basepoint of the path component of `x` is joined to `x`. -/
theorem PathComponentBasepoints.joined_point_mk (β : PathComponentBasepoints X) (x : X) :
    Joined (β.point (ZerothHomotopy.mk x)) x :=
  Quotient.exact (β.mk_point (ZerothHomotopy.mk x))

/-- A continuous map `f` sends the chosen basepoint of the path component of `y` into the path
component of `f y`. -/
theorem PathComponentBasepoints.mk_apply_point_mk {Y : Type*} [TopologicalSpace Y]
    (β : PathComponentBasepoints Y) {f : Y → X} (hf : Continuous f) (y : Y) :
    ZerothHomotopy.mk (f (β.point (ZerothHomotopy.mk y))) = ZerothHomotopy.mk (f y) :=
  Quotient.sound ((β.joined_point_mk y).map hf)

end TauCeti

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- **Paths in a subspace containing a path component.** If a subspace `S` contains the path
component of `a ∈ S`, mapping along the inclusion identifies the paths in `S` from `a` to `b` with
the paths in the ambient space with the same endpoints. The inverse corestricts a path to `S`,
which it never leaves (`Path.mem_pathComponent`). -/
def subtypeHomeomorphOfPathComponentSubset {S : Set X} {a b : S}
    (hS : pathComponent (a : X) ⊆ S) : Path a b ≃ₜ Path (a : X) (b : X) where
  toFun γ := γ.map continuous_subtypeVal
  invFun γ := γ.codRestrict fun t ↦ hS (γ.mem_pathComponent t)
  left_inv γ := by
    ext t
    simp
  right_inv γ := map_codRestrict γ _
  continuous_toFun := continuous_induced_rng.2 <|
    (ContinuousMap.continuous_postcomp ⟨Subtype.val, continuous_subtypeVal⟩).comp
      continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 <|
    (ContinuousMap.isInducing_postcomp ⟨Subtype.val, continuous_subtypeVal⟩
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
