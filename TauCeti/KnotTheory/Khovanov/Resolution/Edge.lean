/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Resolution.Face
public import TauCeti.KnotTheory.Khovanov.Transport

/-!
# Edge maps of the cube of resolutions

Let `s` and `t` be states of a PD-code differing exactly at the crossing `c`. The edge from `s` to
`t` is a *saddle* when two circles pass through `c` in one of the two smoothings; then exactly one
circle passes through `c` in the other, and the edge merges two circles or splits one. The map
`TauCeti.PDCode.resolutionEdgeMap` is the merge `TauCeti.PDCode.resolutionMergeMap` in the first
case and the split `TauCeti.PDCode.resolutionSplitMap` in the second. These are the unsigned
blocks of the Khovanov differential; the cube signs are supplied by the signed totalization
`CategoryTheory.Functor.cubeComplex`.

Every edge of the cube of a planar code is a saddle, while a nonplanar code may have an edge
replacing one circle through `c` by another, on which no map is defined here.

## Main results

All in the namespace `TauCeti.PDCode`:

* `resolutionEdgeMap_eq_resolutionMergeMap`, `resolutionEdgeMap_eq_resolutionSplitMap`: the edge
  map is the merge or the split, according to the smoothing with two circles through `c`.
* `isHomogeneous_resolutionEdgeMap`: every edge map has quantum degree `-1`.
* `SmoothingEquiv.reindex_resolutionEdgeMap`: edge maps commute with transport of the smoothed
  diagrams.
* `resolutionEdgeMap_comp_resolutionEdgeMap_comm`: **the faces of the cube commute.** If all four
  edges of a face are saddles, the two composites around it agree.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

open Finset PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

section Edge

variable {n : ℕ} (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
  (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)

section Semiring

variable (R : Type u) [CommSemiring R]

/-- The map on resolved-circle tensors along a saddle edge of the cube of resolutions: the merge
at `c` when two circles of `s` pass through `c`, and the split at `c` when two circles of `t` do.
Every other factor, including each crossing-free circle, is transported unchanged. -/
noncomputable def resolutionEdgeMap :
    Khovanov.CircleTensor R (D.ResolvedCircle s) →ₗ[R]
      Khovanov.CircleTensor R (D.ResolvedCircle t) :=
  if hs : #(D.circlesAt s c) = 2 then (D.resolutionMergeMap hst hc hs R).toLinearMap
  else D.resolutionSplitMap hst hc (h.resolve_left hs) R

/-- The edge map merges when two circles of the source pass through `c`, and splits otherwise. -/
theorem resolutionEdgeMap_def :
    D.resolutionEdgeMap hst hc h R =
      if hs : #(D.circlesAt s c) = 2 then (D.resolutionMergeMap hst hc hs R).toLinearMap
      else D.resolutionSplitMap hst hc (h.resolve_left hs) R := (rfl)

/-- An edge along which two circles merge carries the resolution merge. -/
@[simp]
theorem resolutionEdgeMap_eq_resolutionMergeMap (hs : #(D.circlesAt s c) = 2) :
    D.resolutionEdgeMap hst hc h R = (D.resolutionMergeMap hst hc hs R).toLinearMap :=
  dite_eq_left hs

/-- An edge along which a circle splits carries the resolution split. -/
@[simp]
theorem resolutionEdgeMap_eq_resolutionSplitMap (ht : #(D.circlesAt t c) = 2) :
    D.resolutionEdgeMap hst hc h R = D.resolutionSplitMap hst hc ht R := by
  have hs := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm)
    hc.symm ht
  exact dite_eq_right (by omega)

end Semiring

/-- An actual resolution edge map has quantum degree `-1`. -/
theorem isHomogeneous_resolutionEdgeMap (R : Type u) [CommRing R] :
    TauCeti.LinearMap.IsHomogeneous (D.resolutionEdgeMap hst hc h R)
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle s)).piece
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle t)).piece (-1) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · rw [D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs]
    exact D.isHomogeneous_resolutionMergeMap hst hc hs R
  · rw [D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R (h.resolve_left hs)]
    exact D.isHomogeneous_resolutionSplitMap hst hc (h.resolve_left hs) R

end Edge

section Face

variable {n : ℕ} (D : PDCode n) {s t₁ t₂ u : Fin n → Bool} {c c' : Fin n}
  (hst₁ : ∀ j, j ≠ c → s j = t₁ j) (hc₁ : s c ≠ t₁ c)
  (ht₁u : ∀ j, j ≠ c' → t₁ j = u j) (hc₁' : t₁ c' ≠ u c')
  (hst₂ : ∀ j, j ≠ c' → s j = t₂ j) (hc₂ : s c' ≠ t₂ c')
  (ht₂u : ∀ j, j ≠ c → t₂ j = u j) (hc₂' : t₂ c ≠ u c)
  (h₁ : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t₁ c) = 2)
  (h₁' : #(D.circlesAt t₁ c') = 2 ∨ #(D.circlesAt u c') = 2)
  (h₂ : #(D.circlesAt s c') = 2 ∨ #(D.circlesAt t₂ c') = 2)
  (h₂' : #(D.circlesAt t₂ c) = 2 ∨ #(D.circlesAt u c) = 2)
  (R : Type u) [CommSemiring R]

/-- **The faces of the cube of resolutions commute.** Let `s`, `t₁`, `t₂`, `u` be the states of a
face, where `t₁` changes `s` at `c`, `t₂` changes `s` at `c'`, and `u` changes both. If all four
edges are saddles, the composite of the edge maps through `t₁` equals the composite through
`t₂`. -/
theorem resolutionEdgeMap_comp_resolutionEdgeMap_comm :
    D.resolutionEdgeMap ht₁u hc₁' h₁' R ∘ₗ D.resolutionEdgeMap hst₁ hc₁ h₁ R =
      D.resolutionEdgeMap ht₂u hc₂' h₂' R ∘ₗ D.resolutionEdgeMap hst₂ hc₂ h₂ R := by
  -- Each edge merges or splits, changing the circle count by one. The two routes change it by
  -- the same total, which leaves the six configurations treated in
  -- `TauCeti.KnotTheory.Khovanov.Resolution.Face`, listed with each route as merge (`M`) or
  -- split (`S`): `MM = MM`, `MS = MS`, `MS = SM`, `SM = MS`, `SM = SM` and `SS = SS`.
  rcases D.card_resolvedCircle_of_saddle hst₁ hc₁ h₁ with ⟨a₁, n₁⟩ | ⟨a₁, n₁⟩ <;>
    rcases D.card_resolvedCircle_of_saddle ht₁u hc₁' h₁' with ⟨a₁', n₁'⟩ | ⟨a₁', n₁'⟩ <;>
    rcases D.card_resolvedCircle_of_saddle hst₂ hc₂ h₂ with ⟨a₂, n₂⟩ | ⟨a₂, n₂⟩ <;>
    rcases D.card_resolvedCircle_of_saddle ht₂u hc₂' h₂' with ⟨a₂', n₂'⟩ | ⟨a₂', n₂'⟩ <;>
    try omega
  · rw [D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₁,
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₁',
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₂,
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₂', ← AlgHom.comp_toLinearMap,
      ← AlgHom.comp_toLinearMap,
      D.resolutionMergeMap_comp_resolutionMergeMap_comm hst₁ hc₁ ht₁u hc₁' hst₂ hc₂ ht₂u hc₂' R
        a₁ a₁' a₂ a₂']
  · rw [D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₁,
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₁',
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₂,
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₂']
    exact D.resolutionSplitMap_comp_resolutionMergeMap_comm hst₁ hc₁ ht₁u hc₁' hst₂ hc₂ ht₂u hc₂'
      R a₁ a₁' a₂ a₂'
  · rw [D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₁,
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₁',
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₂,
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₂']
    exact D.resolutionSplitMap_comp_resolutionMergeMap_eq_resolutionMergeMap_comp_resolutionSplitMap
      hst₁ hc₁ ht₁u hc₁' hst₂ hc₂ ht₂u hc₂' R a₁ a₁' a₂ a₂'
  · rw [D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₁,
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₁',
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₂,
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₂']
    exact
      (D.resolutionSplitMap_comp_resolutionMergeMap_eq_resolutionMergeMap_comp_resolutionSplitMap
        hst₂ hc₂ ht₂u hc₂' hst₁ hc₁ ht₁u hc₁' R a₂ a₂' a₁ a₁').symm
  · rw [D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₁,
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₁',
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₂,
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ a₂']
    exact D.resolutionMergeMap_comp_resolutionSplitMap_comm hst₁ hc₁ ht₁u hc₁' hst₂ hc₂ ht₂u hc₂'
      R a₁ a₁' a₂ a₂'
  · rw [D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₁,
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₁',
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₂,
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ a₂']
    exact D.resolutionSplitMap_comp_resolutionSplitMap_comm hst₁ hc₁ ht₁u hc₁' hst₂ hc₂ ht₂u hc₂'
      R a₁ a₁' a₂ a₂'

end Face

namespace SmoothingEquiv

variable {n m : ℕ} {D : PDCode n} {D' : PDCode m}
  {s t : Fin n → Bool} {s' t' : Fin m → Bool} {c : Fin n} {c' : Fin m}
  (es : D.SmoothingEquiv s D' s') (et : D.SmoothingEquiv t D' t')
  (hhalf : es.halfEdgeEquiv = et.halfEdgeEquiv)
  (hisolated : es.crossinglessEquiv = et.crossinglessEquiv)
  (slots : Fin 4 ≃ Fin 4)
  (hcross : ∀ k, es.halfEdgeEquiv (D.crossing c k) = D'.crossing c' (slots k))
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
  (hst' : ∀ j, j ≠ c' → s' j = t' j) (hc' : s' c' ≠ t' c')
  (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
  (h' : #(D'.circlesAt s' c') = 2 ∨ #(D'.circlesAt t' c') = 2)
  (R : Type*) [CommSemiring R]

include hhalf hisolated hcross in
/-- Reindexing the source and target circles commutes with an actual resolution edge map, when
the transports at the two endpoints use the same half-edge and isolated-circle bijections and
carry the slots of `c` to those of `c'`. -/
theorem reindex_resolutionEdgeMap (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    reindex R (fun _ ↦ R[ε]) et.resolvedCircleCongr (D.resolutionEdgeMap hst hc h R x) =
      D'.resolutionEdgeMap hst' hc' h' R
        (reindex R (fun _ ↦ R[ε]) es.resolvedCircleCongr x) := by
  have hcs := es.card_circlesAt_eq slots hcross
  have hct := et.card_circlesAt_eq slots (hhalf ▸ hcross)
  by_cases hs : #(D.circlesAt s c) = 2
  · have hs' : #(D'.circlesAt s' c') = 2 := hcs ▸ hs
    rw [D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs,
      D'.resolutionEdgeMap_eq_resolutionMergeMap hst' hc' h' R hs', AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply]
    exact es.reindex_resolutionMergeMap et hhalf hisolated hst hc hst' hc' R hs hs' x
  · have ht := h.resolve_left hs
    have ht' : #(D'.circlesAt t' c') = 2 := hct ▸ ht
    rw [D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R ht,
      D'.resolutionEdgeMap_eq_resolutionSplitMap hst' hc' h' R ht']
    exact es.reindex_resolutionSplitMap et hhalf hisolated hst hc hst' hc' R ht ht' x

end SmoothingEquiv

end TauCeti.PDCode
