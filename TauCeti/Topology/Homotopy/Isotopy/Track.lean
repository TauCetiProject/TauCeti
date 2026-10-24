/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Tracks of isotopies with compact source

The track of an isotopy retains time as its first coordinate. For a compact source
and Hausdorff target it is a closed embedding, so points of the moving image have
continuous source coordinates. Compactness matters here: slice-wise embeddings alone
do not guarantee that the track of a noncompact isotopy is an embedding.

The same holds for a motion over any parameter space, such as an isotopy run over the
whole real line: a parameter-preserving map `(p, x) ↦ (p, G (p, x))` with injective
slices, compact source and Hausdorff target is a closed embedding
(`Continuous.isClosedEmbedding_fst_prod`). Its image is the projection of a closed set
along the compact factor, so it is closed by the tube lemma.

Reference: M. Hirsch, *Differential Topology*, Chapter 8, §1, the track construction
in the proof of the isotopy extension theorem.
-/

public section

open Set Topology in
/-- A parameter-preserving map `(p, x) ↦ (p, G (p, x))` whose slices are injective, from a
product with a compact second factor to a Hausdorff space, is a closed embedding. -/
theorem Continuous.isClosedEmbedding_fst_prod {P X Y : Type*} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {G : P × X → Y}
    (hG : Continuous G) (hinj : ∀ p, Function.Injective fun x => G (p, x)) :
    IsClosedEmbedding fun q : P × X => (q.1, G q) := by
  refine .of_continuous_injective_isClosedMap (continuous_fst.prodMk hG) ?_ ?_
  · rintro ⟨p, x⟩ ⟨p', x'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact Prod.ext rfl (hinj p h)
  · intro C hC
    -- The image is the projection along `X` of a closed subset of `(P × Y) × X`.
    have himage : (fun q : P × X => (q.1, G q)) '' C =
        Prod.fst '' {r : (P × Y) × X | (r.1.1, r.2) ∈ C ∧ G (r.1.1, r.2) = r.1.2} := by
      ext ⟨p, y⟩
      constructor
      · rintro ⟨⟨p', x⟩, hx, h⟩
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨((p', G (p', x)), x), ⟨hx, rfl⟩, rfl⟩
      · rintro ⟨⟨⟨p', y'⟩, x⟩, ⟨hx, hy⟩, h⟩
        simp only [Prod.mk.injEq] at h hy
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨(p', x), hx, by simp [hy]⟩
    rw [himage]
    exact isClosedMap_fst_of_compactSpace _
      ((hC.preimage (by fun_prop)).inter (isClosed_eq (by fun_prop) (by fun_prop)))

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
