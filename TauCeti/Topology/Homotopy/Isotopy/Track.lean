/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Tracks of isotopies with compact source

The track of an isotopy retains time as its first coordinate. For a compact source
and Hausdorff target it is a closed embedding, so points of the moving image have
continuous source coordinates. Compactness matters here: slice-wise embeddings alone
do not guarantee that the track of a noncompact isotopy is an embedding.

Reference: M. Hirsch, *Differential Topology*, Chapter 8, §1, the track construction
in the proof of the isotopy extension theorem.
-/

public section

namespace TauCeti.Isotopy

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ : C(X, Y)}

/-- The time-preserving track of an isotopy. -/
def track (F : Isotopy f₀ f₁) : C(unitInterval × X, unitInterval × Y) :=
  ⟨fun p => (p.1, F p), continuous_fst.prodMk F.continuous⟩

/-- The track records both time and the moving point. -/
@[simp] theorem track_apply (F : Isotopy f₀ f₁) (p : unitInterval × X) :
    F.track p = (p.1, F p) := (rfl)

/-- Distinct points of the space-time source have distinct track images. -/
theorem track_injective (F : Isotopy f₀ f₁) : Function.Injective F.track := by
  rintro ⟨t, x⟩ ⟨s, y⟩ h
  have ht : t = s := congrArg Prod.fst h
  subst s
  exact Prod.ext rfl ((F.isEmbedding_apply t).injective (congrArg Prod.snd h))

/-- The track of a compact-source isotopy into a Hausdorff space is a closed embedding. -/
theorem isClosedEmbedding_track [CompactSpace X] [T2Space Y] (F : Isotopy f₀ f₁) :
    IsClosedEmbedding F.track :=
  F.track.continuous.isClosedEmbedding F.track_injective

/-- A space-time point lies on the track exactly when its spatial coordinate lies on
the image of the corresponding time slice. This is an explicit rewrite lemma, since
`Set.mem_range` already expands its left-hand side in the simplifier. -/
theorem mem_range_track (F : Isotopy f₀ f₁) (q : unitInterval × Y) :
    q ∈ range F.track ↔ q.2 ∈ range (fun x => F (q.1, x)) := by
  constructor
  · rintro ⟨⟨t, x⟩, h⟩
    have ht : t = q.1 := congrArg Prod.fst h
    exact ⟨x, ht ▸ congrArg Prod.snd h⟩
  · rintro ⟨x, hx⟩
    exact ⟨(q.1, x), Prod.ext rfl hx⟩

end TauCeti.Isotopy
