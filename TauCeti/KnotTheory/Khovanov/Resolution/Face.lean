/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Resolution.Split

/-!
# Commuting faces of the cube of resolutions

A face of the cube of resolutions of a PD-code consists of four states: `s`, the states `t₁` and
`t₂` obtained by changing `s` at the crossings `c` and `c'` respectively, and the state `u`
changed at both. Each edge carries the merge map `TauCeti.PDCode.resolutionMergeMap` when two
circles pass through its crossing in its source, and the split map
`TauCeti.PDCode.resolutionSplitMap` when two pass through it in its target. This file proves that
the two composites around a face agree whenever all four edges are merges or splits:

* both routes merge twice (associativity, including merges of disjoint pairs of circles);
* both routes split twice (coassociativity);
* one route merges and then splits while the other splits and then merges (the Frobenius
  relation);
* both routes merge and then split, as for two crossings joining the same two circles;
* both routes split and then merge, as for two interleaved crossings on one circle, where both
  composites multiply by `2X` on that circle.

Up to exchanging the two routes, these are all the faces in which every edge is a merge or a
split: each edge changes the number of circles by one, so the numbers of circles of `s` and `u`
determine whether the routes merge twice, split twice, or do one of each.
All identities are stated for the unsigned maps, with every crossing-free circle retained; the
cube signs are supplied separately.

The proofs are algebraic. Merges along successive saddles compose to the merge along the composite
circle correspondence, and dually for splits. The mixed faces follow from the projection formula
`TauCeti.Khovanov.fiberwiseSplit_fiberwiseMul_mul`, which reduces each composite to multiplication
by a merged image of the split `X ⊗ 1 + 1 ⊗ X` of the unit. The combinatorial input is that all
four smoothings are quotients of the same half-edges, so every circle correspondence sends the
circle of a half-edge to its circle; when one state has a single circle through each crossing at
which it differs from another, `TauCeti.PDCode.coarseningResolvedCircleMap` compares them directly.

## Main results

All in the namespace `TauCeti.PDCode`:

* `resolutionMergeMap_comp_resolutionMergeMap_comm`: faces of two merges.
* `resolutionSplitMap_comp_resolutionSplitMap_comm`: faces of two splits.
* `resolutionSplitMap_comp_resolutionMergeMap_eq_resolutionMergeMap_comp_resolutionSplitMap`:
  a merge followed by a split equals a split followed by a merge.
* `resolutionSplitMap_comp_resolutionMergeMap_comm`: faces in which both routes merge and then
  split.
* `resolutionMergeMap_comp_resolutionSplitMap_comm`: faces in which both routes split and then
  merge.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

open Finset PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n) {s t₁ t₂ u : Fin n → Bool} {c c' : Fin n}
  (hst₁ : ∀ j, j ≠ c → s j = t₁ j) (hc₁ : s c ≠ t₁ c)
  (ht₁u : ∀ j, j ≠ c' → t₁ j = u j) (hc₁' : t₁ c' ≠ u c')
  (hst₂ : ∀ j, j ≠ c' → s j = t₂ j) (hc₂ : s c' ≠ t₂ c')
  (ht₂u : ∀ j, j ≠ c → t₂ j = u j) (hc₂' : t₂ c ≠ u c)
  (R : Type u) [CommSemiring R]

/-- Two correspondences of resolved circles that send the circle of every half-edge to its circle
and retain every crossing-free label are equal. -/
private theorem resolvedCircle_funext {s t : Fin n → Bool}
    {φ ψ : D.ResolvedCircle s → D.ResolvedCircle t}
    (hφ : ∀ x : Fin (4 * n), φ (.inl ⟦x⟧) = .inl ⟦x⟧)
    (hψ : ∀ x : Fin (4 * n), ψ (.inl ⟦x⟧) = .inl ⟦x⟧)
    (hφ' : ∀ i, φ (.inr i) = .inr i) (hψ' : ∀ i, ψ (.inr i) = .inr i) : φ = ψ := by
  funext C
  rcases C with C | i
  · induction C using Quotient.ind
    rw [hφ, hψ]
  · rw [hφ', hψ']

/-- If only one circle of `t'` passes through each of `c` and `c'`, and `t` agrees with `t'` away
from these crossings, then every circle of `t` lies on a circle of `t'`. -/
private theorem forall_card_circlesAt_eq_one_of_eq_of_ne {t t' : Fin n → Bool}
    (hc : #(D.circlesAt t' c) = 1) (hc' : #(D.circlesAt t' c') = 1)
    (h : ∀ j, j ≠ c → j ≠ c' → t j = t' j) : ∀ j, t j ≠ t' j → #(D.circlesAt t' j) = 1 :=
  fun j hj ↦ by
    by_cases hjc : j = c
    · exact hjc ▸ hc
    by_cases hjc' : j = c'
    · exact hjc' ▸ hc'
    exact absurd (h j hjc hjc') hj

/-- **Associativity.** If both routes around a face merge twice, the two composite merges agree:
both multiply the factors on each circle of `u` coming from the circles of `s` on it. -/
theorem resolutionMergeMap_comp_resolutionMergeMap_comm
    (hs : #(D.circlesAt s c) = 2) (ht₁ : #(D.circlesAt t₁ c') = 2)
    (hs' : #(D.circlesAt s c') = 2) (ht₂ : #(D.circlesAt t₂ c) = 2) :
    (D.resolutionMergeMap ht₁u hc₁' ht₁ R).comp (D.resolutionMergeMap hst₁ hc₁ hs R) =
      (D.resolutionMergeMap ht₂u hc₂' ht₂ R).comp (D.resolutionMergeMap hst₂ hc₂ hs' R) := by
  simp only [resolutionMergeMap_def, fiberwiseMul_comp]
  congr 1
  exact D.resolvedCircle_funext (by simp) (by simp) (by simp) (by simp)

/-- **Coassociativity.** If both routes around a face split twice, the two composite splits
agree. -/
theorem resolutionSplitMap_comp_resolutionSplitMap_comm
    (ht₁ : #(D.circlesAt t₁ c) = 2) (hu : #(D.circlesAt u c') = 2)
    (ht₂ : #(D.circlesAt t₂ c') = 2) (hu' : #(D.circlesAt u c) = 2) :
    D.resolutionSplitMap ht₁u hc₁' hu R ∘ₗ D.resolutionSplitMap hst₁ hc₁ ht₁ R =
      D.resolutionSplitMap ht₂u hc₂' hu' R ∘ₗ D.resolutionSplitMap hst₂ hc₂ ht₂ R := by
  simp only [resolutionSplitMap_def, Khovanov.fiberwiseSplit_comp]
  congr 1
  exact D.resolvedCircle_funext (by simp) (by simp) (by simp) (by simp)

/-- **The Frobenius relation on a face.** Merging at `c` and then splitting at `c'` equals
splitting at `c'` and then merging at `c`. -/
theorem resolutionSplitMap_comp_resolutionMergeMap_eq_resolutionMergeMap_comp_resolutionSplitMap
    (hs : #(D.circlesAt s c) = 2) (hu : #(D.circlesAt u c') = 2)
    (ht₂ : #(D.circlesAt t₂ c') = 2) (ht₂' : #(D.circlesAt t₂ c) = 2) :
    D.resolutionSplitMap ht₁u hc₁' hu R ∘ₗ (D.resolutionMergeMap hst₁ hc₁ hs R).toLinearMap =
      (D.resolutionMergeMap ht₂u hc₂' ht₂' R).toLinearMap ∘ₗ
        D.resolutionSplitMap hst₂ hc₂ ht₂ R := by
  -- Merging the split of `1` at `c'` along the saddle at `c` gives the split of `1` at `c'`.
  have hone : D.resolutionMergeMap ht₂u hc₂' ht₂' R (D.resolutionSplitMap hst₂ hc₂ ht₂ R 1) =
      D.resolutionSplitMap ht₁u hc₁' hu R 1 := by
    simp only [resolutionSplitMap_one, map_add, resolutionMergeMap_def, fiberwiseMul_singleAlgHom,
      saddleResolvedCircleMap_inl, saddleCircleMap_mk]
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, resolutionSplitMap_def,
    resolutionMergeMap_def] at hone ⊢
  refine Khovanov.fiberwiseSplit_fiberwiseMul_of_comp_eq
    (D.saddleResolvedCircleMap_surjective _ _) ?_ hone x
  exact D.resolvedCircle_funext (by simp) (by simp) (by simp) (by simp)

/-- **Merging and then splitting along both routes.** If both routes around a face merge and then
split, the two composites agree. This is the face of two crossings joining the same two circles in
a planar diagram. -/
theorem resolutionSplitMap_comp_resolutionMergeMap_comm
    (hs : #(D.circlesAt s c) = 2) (hu : #(D.circlesAt u c') = 2)
    (hs' : #(D.circlesAt s c') = 2) (hu' : #(D.circlesAt u c) = 2) :
    D.resolutionSplitMap ht₁u hc₁' hu R ∘ₗ (D.resolutionMergeMap hst₁ hc₁ hs R).toLinearMap =
      D.resolutionSplitMap ht₂u hc₂' hu' R ∘ₗ
        (D.resolutionMergeMap hst₂ hc₂ hs' R).toLinearMap := by
  -- The two middle states have a single circle through both crossings, so they have the same
  -- circles.
  have ht₁c := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst₁ hc₁ hs
  have ht₁c' := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two
    (fun j hj ↦ (ht₁u j hj).symm) hc₁'.symm hu
  have ht₂c' := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst₂ hc₂ hs'
  have ht₂c := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two
    (fun j hj ↦ (ht₂u j hj).symm) hc₂'.symm hu'
  have h₁₂ := D.forall_card_circlesAt_eq_one_of_eq_of_ne (t := t₁) ht₂c ht₂c'
    fun j hjc hjc' ↦ by rw [← hst₁ j hjc, hst₂ j hjc']
  have h₂₁ := D.forall_card_circlesAt_eq_one_of_eq_of_ne (t := t₂) ht₁c ht₁c'
    fun j hjc hjc' ↦ by rw [← hst₂ j hjc', hst₁ j hjc]
  let e : D.ResolvedCircle t₁ ≃ D.ResolvedCircle t₂ :=
    { toFun := D.coarseningResolvedCircleMap h₁₂
      invFun := D.coarseningResolvedCircleMap h₂₁
      left_inv := fun C ↦ congrFun (D.resolvedCircle_funext (φ := _ ∘ _) (ψ := id)
        (by simp) (by simp) (by simp) (by simp)) C
      right_inv := fun C ↦ congrFun (D.resolvedCircle_funext (φ := _ ∘ _) (ψ := id)
        (by simp) (by simp) (by simp) (by simp)) C }
  simp only [resolutionSplitMap_def, resolutionMergeMap_def]
  rw [← Khovanov.fiberwiseSplit_comp_fiberwiseMul_equiv_comp e]
  congr 2
  · exact D.resolvedCircle_funext (by simp [e]) (by simp) (by simp [e]) (by simp)
  · congr 1
    exact D.resolvedCircle_funext (by simp [e]) (by simp) (by simp [e]) (by simp)

/-- **Splitting and then merging along both routes.** If both routes around a face split and then
merge, the two composites agree: after identifying the circles of `s` with those of `u`, both
multiply by `2X` on the circle of `u` through `c` and `c'`. This is the face of two interleaved
crossings on one circle in a planar diagram. -/
theorem resolutionMergeMap_comp_resolutionSplitMap_comm
    (ht₁ : #(D.circlesAt t₁ c) = 2) (ht₁' : #(D.circlesAt t₁ c') = 2)
    (ht₂ : #(D.circlesAt t₂ c') = 2) (ht₂' : #(D.circlesAt t₂ c) = 2) :
    (D.resolutionMergeMap ht₁u hc₁' ht₁' R).toLinearMap ∘ₗ
        D.resolutionSplitMap hst₁ hc₁ ht₁ R =
      (D.resolutionMergeMap ht₂u hc₂' ht₂' R).toLinearMap ∘ₗ
        D.resolutionSplitMap hst₂ hc₂ ht₂ R := by
  have huc := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two ht₂u hc₂' ht₂'
  have huc' := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two ht₁u hc₁' ht₁'
  -- The state `u` has a single circle through both crossings, so `s` maps to it.
  have hsu := D.forall_card_circlesAt_eq_one_of_eq_of_ne (t := s) huc huc'
    fun j hjc hjc' ↦ (hst₁ j hjc).trans (ht₁u j hjc')
  -- The circles of `u` through `c` and through `c'` coincide: the saddle at `c'` identifies the
  -- two circles of `t₁` through `c`, so they are the two circles of `t₁` through `c'`.
  have hcc' : (⟦D.crossing c 0⟧ : D.CrossingCircle u) = ⟦D.crossing c' 0⟧ := by
    have h := (D.saddleResolvedCircleMap_eq_iff ht₁u huc' (.inl ⟦D.crossing c 0⟧)
      (.inl ⟦D.crossing c 2⟧)).mp (by
        simp only [saddleResolvedCircleMap_inl, saddleCircleMap_mk, Sum.inl.injEq]
        exact (D.card_circlesAt_eq_one_iff u c).mp huc)
    rcases h with h | ⟨h | h, -⟩
    · exact absurd (Sum.inl.inj h) ((D.card_circlesAt_eq_two_iff t₁ c).mp ht₁)
    · simpa only [saddleResolvedCircleMap_inl, saddleCircleMap_mk, Sum.inl.injEq] using
        congrArg (D.saddleResolvedCircleMap ht₁u huc') h
    · have h' := congrArg (D.saddleResolvedCircleMap ht₁u huc') h
      simp only [saddleResolvedCircleMap_inl, saddleCircleMap_mk, Sum.inl.injEq] at h'
      rwa [((D.card_circlesAt_eq_one_iff u c').mp huc').symm] at h'
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, resolutionSplitMap_def,
    resolutionMergeMap_def]
  rw [Khovanov.fiberwiseMul_fiberwiseSplit (D.saddleResolvedCircleMap_surjective _ _)
      (h := D.coarseningResolvedCircleMap hsu)
      (D.resolvedCircle_funext (by simp) (by simp) (by simp) (by simp)) x,
    Khovanov.fiberwiseMul_fiberwiseSplit (D.saddleResolvedCircleMap_surjective _ _)
      (h := D.coarseningResolvedCircleMap hsu)
      (D.resolvedCircle_funext (by simp) (by simp) (by simp) (by simp)) x]
  congr 1
  rw [← D.resolutionSplitMap_def hst₁ hc₁ ht₁, ← D.resolutionSplitMap_def hst₂ hc₂ ht₂]
  simp only [resolutionSplitMap_one, map_add, fiberwiseMul_singleAlgHom,
    saddleResolvedCircleMap_inl, saddleCircleMap_mk,
    ((D.card_circlesAt_eq_one_iff u c).mp huc).symm,
    ((D.card_circlesAt_eq_one_iff u c').mp huc').symm, hcc']

end TauCeti.PDCode
