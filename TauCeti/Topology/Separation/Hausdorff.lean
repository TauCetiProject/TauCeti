/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Closed equalizers and relatively compact images in Hausdorff spaces

Mathlib's `isClosed_eq` shows that the locus `{ x : X | f x = g x }` where two continuous maps into
a Hausdorff space agree is closed. Intersecting over one or two arbitrary index types (possibly
propositions, for bounded quantifiers) shows that the simultaneous agreement locus of a singly or
doubly indexed family of pairs of continuous maps into Hausdorff spaces is closed.

Mathlib's `image_closure_of_isCompact` identifies the image of a compact closure with the closure
of the image; consequently a map into a Hausdorff space that is continuous on the closure of a
relatively compact set sends it to a relatively compact set (`IsCompact.closure_image`).

## Main results

* `TauCeti.isClosed_forall_eq`: `{ x : X | ∀ i, f i x = g i x }` is closed for continuous maps
  into Hausdorff spaces.
* `TauCeti.isClosed_forall₂_eq`: `{ x : X | ∀ i j, f i j x = g i j x }` is closed for doubly
  indexed continuous maps into Hausdorff spaces.
* `IsCompact.closure_image`: a map into a Hausdorff space, continuous on the closure of `s`, sends
  a set `s` with compact closure to a set with compact closure.
-/

public section

namespace TauCeti

/-- The locus where an indexed family of pairs of continuous maps into Hausdorff spaces agree is
closed. -/
theorem isClosed_forall_eq {X : Type*} [TopologicalSpace X] {ι : Sort*} {α : ι → Type*}
    [∀ i, TopologicalSpace (α i)] [∀ i, T2Space (α i)] {f g : ∀ i, X → α i}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i)) :
    IsClosed { x : X | ∀ i, f i x = g i x } := by
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_eq (hf i) (hg i)

/-- The locus where a doubly indexed family of pairs of continuous maps into Hausdorff spaces agree
is closed. -/
theorem isClosed_forall₂_eq {X : Type*} [TopologicalSpace X] {ι : Sort*} {κ : ι → Sort*}
    {α : ∀ i, κ i → Type*} [∀ i j, TopologicalSpace (α i j)] [∀ i j, T2Space (α i j)]
    {f g : ∀ i j, X → α i j} (hf : ∀ i j, Continuous (f i j))
    (hg : ∀ i j, Continuous (g i j)) :
    IsClosed { x : X | ∀ i j, f i j x = g i j x } := by
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_forall_eq (hf i) (hg i)

end TauCeti

/-- A map into a Hausdorff space that is continuous on the closure of `s` sends a set `s` with
compact closure to a set with compact closure. -/
theorem IsCompact.closure_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {s : Set X} (hs : IsCompact (closure s)) {f : X → Y}
    (hf : ContinuousOn f (closure s)) : IsCompact (closure (f '' s)) := by
  rw [← image_closure_of_isCompact hs hf]
  exact hs.image_of_continuousOn hf
