/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Path

/-!
# Homotopies inside a union of path components

Let `S` be a union of path components of a space `Y`: with every point it contains its path
component. A homotopy `F` whose initial map lands in `S` runs inside `S` at all times, since each
point `F (t, x)` is joined to `F (0, x)` by the track of `x`
(`ContinuousMap.Homotopy.apply_mem_of_pathComponent_subset`). So two maps into `S` that are
homotopic as maps into `Y` are homotopic as maps into `S`
(`ContinuousMap.Homotopic.codRestrict`). For instance, the contractible free loops of a space are
the union of the path components of the constant loops, and a homotopy of families of free loops
starting at contractible loops is a homotopy of families of contractible loops. The analogue for
homotopies of paths in a single path component is
`TauCeti.homotopic_pathComponent_of_map_subtypeVal_homotopic`.

## Main definitions

* `ContinuousMap.Homotopy.codRestrict`: a homotopy between maps into `S`, read in `S`.

## Main results

* `ContinuousMap.Homotopy.apply_mem_of_pathComponent_subset`: a homotopy starting in `S` stays
  in `S`.
* `ContinuousMap.Homotopic.codRestrict`: homotopic maps into `Y` with values in `S` are homotopic
  as maps into `S`.
-/

public section

open unitInterval

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set Y}

namespace Homotopy

/-- **A homotopy starting in a union of path components stays there.** If `S` contains the path
component of each of its points and the initial map of a homotopy `F` lands in `S`, then so does
every `F (t, x)`. -/
theorem apply_mem_of_pathComponent_subset (hS : ∀ y ∈ S, pathComponent y ⊆ S) {f₀ f₁ : C(X, Y)}
    (F : f₀.Homotopy f₁) (h₀ : ∀ x, f₀ x ∈ S) (t : I) (x : X) : F (t, x) ∈ S :=
  hS _ (h₀ x) ((F.evalAt x).mem_pathComponent t)

/-- **A homotopy between maps into a union of path components, read in it.** For `S` containing
the path component of each of its points, a homotopy between the composites of `f₀, f₁ : X → S`
with the inclusion of `S` is a homotopy from `f₀` to `f₁`. -/
def codRestrict (hS : ∀ y ∈ S, pathComponent y ⊆ S) {f₀ f₁ : C(X, S)}
    (F : ((ContinuousMap.subtypeVal S).comp f₀).Homotopy ((ContinuousMap.subtypeVal S).comp f₁)) :
    f₀.Homotopy f₁ where
  toFun p := ⟨F p, F.apply_mem_of_pathComponent_subset hS (fun x ↦ (f₀ x).property) p.1 p.2⟩
  continuous_toFun := F.continuous.subtype_mk _
  map_zero_left x := Subtype.ext (F.apply_zero x)
  map_one_left x := Subtype.ext (F.apply_one x)

@[simp]
theorem coe_codRestrict_apply (hS : ∀ y ∈ S, pathComponent y ⊆ S) {f₀ f₁ : C(X, S)}
    (F : ((ContinuousMap.subtypeVal S).comp f₀).Homotopy ((ContinuousMap.subtypeVal S).comp f₁))
    (p : I × X) : (F.codRestrict hS p : Y) = F p :=
  (rfl)

end Homotopy

/-- **Homotopic maps into a union of path components are homotopic in it.** For `S` containing the
path component of each of its points, two maps `X → S` whose composites with the inclusion of `S`
are homotopic are homotopic. -/
theorem Homotopic.codRestrict (hS : ∀ y ∈ S, pathComponent y ⊆ S) {f₀ f₁ : C(X, S)}
    (h : ((ContinuousMap.subtypeVal S).comp f₀).Homotopic ((ContinuousMap.subtypeVal S).comp f₁)) :
    f₀.Homotopic f₁ :=
  h.map fun F ↦ F.codRestrict hS

end ContinuousMap
