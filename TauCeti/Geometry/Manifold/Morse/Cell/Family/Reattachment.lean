/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.CharacteristicHomotopy
public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCell.ReattachmentInv

/-!
# Restricting the reattachment data of families of Morse charts

Let `ψ₀ p i` and `ψ₁ p i`, for `p` in a parameter space `P` and `i : ι`, be two families of charts
of a manifold `M` with common centres, in which a smooth function `f` has the normal form
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`. Write `M_a = {f ≤ a}`. Each family attaches, over each
`p`, one cell `D^{k i}` to the lower sublevel `M_{c-ε}` along its attaching maps
(`TauCeti.morseFamilyAttachingMap`), giving the fiberwise adjunction spaces

`Xⱼ = (P × M_{c-ε}) ∪_{αⱼ} ⨆ᵢ (P × D^{k i})`

over `P` (`TauCeti.fiberwiseCellAttachment`). Given linear isometries `g i p` of `ℝ^{k i}` depending
continuously on `p` and homotopies `K i` over `P` from the characteristic maps of `ψ₁` to those of
`ψ₀` composed with `g i`, keeping the boundary spheres in `M_{c-ε}`, the fiberwise reattachment map
`E : X₁ → X₀` (`TauCeti.fiberwiseCellReattachment`) and its inverse
(`TauCeti.fiberwiseCellReattachmentInv`) are defined. For the polar factors of the transitions and
the homotopies of `TauCeti.exists_homotopy_morseFamilyCharacteristicMap_polarFactor`, `E` is a
homotopy equivalence over a compact `P` relative to `P × M_{c-ε}`
(`TauCeti.exists_fiberwiseCellReattachmentInv_homotopyRel_morseFamily`), which is Milnor's
Lemma 3.6 over a compact parameter space.

This file shows that these data restrict along any continuous map `φ : P' → P` of parameter
spaces, for instance the inclusion of a subcomplex
(`TauCeti.exists_fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap_morseFamily`): the
homotopies `K i` restricted along `φ` are homotopies of the same kind for the charts `ψⱼ (φ p) i`
and the isometries `g i (φ p)`, and the reattachment maps and their inverses built from the
restricted data commute with the maps of fiberwise adjunction spaces over `φ`
(`TauCeti.fiberwiseCellAttachmentMap`).

## Main results

* `TauCeti.exists_fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap_morseFamily`: the
  reattachment data restrict along maps of parameter spaces, compatibly with the reattachment maps
  and their inverses.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

universe u

open Set Metric CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

section Restriction

variable {M : Type u} [TopologicalSpace M] {f : M → ℝ} {c ε : ℝ} {n : ℕ}

/-- **The reattachment data of two families of Morse charts restrict along maps of parameter
spaces.** Let `ψ₀ p i` and `ψ₁ p i` be families of charts over `P` as in
`TauCeti.exists_fiberwiseCellReattachmentInv_homotopyRel_morseFamily`, `g i p` linear isometries
of `ℝ^{k i}` depending continuously on `p`, and `K i` homotopies over `P` from the characteristic
maps of the cells of `ψ₁` to those of `ψ₀` composed with `g i`, keeping the boundary spheres in
`M_{c-ε}`. Let `φ : P' → P` be continuous, for instance the inclusion of a subcomplex. Then the
homotopies `K' i (t, (p, x)) = K i (t, (φ p, x))` are homotopies of the same kind for the charts
`ψⱼ (φ p) i` and the isometries `g i (φ p)`. The fiberwise reattachment map over `P'` of these
restricted data, followed by the map of fiberwise adjunction spaces over `φ`, is the map over `φ`
followed by the reattachment map over `P`; the same holds for their inverses. -/
theorem exists_fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap_morseFamily
    {ι P P' : Type u} [TopologicalSpace P] [TopologicalSpace P'] (φ : C(P', P))
    (ψ₀ ψ₁ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε)
    (hball₀ : ∀ p i, closedBall 0 √ε ⊆ (ψ₀ p i).target)
    (hball₁ : ∀ p i, closedBall 0 √ε ⊆ (ψ₁ p i).target)
    (hf₀ : ∀ p i, ∀ y ∈ (ψ₀ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₀ p i y j ^ 2)
    (hf₁ : ∀ p i, ∀ y ∈ (ψ₁ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₁ p i y j ^ 2)
    (hs₀ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₀' : ∀ i, ContinuousOn (fun q : P' × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ (φ q.1) i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁' : ∀ i, ContinuousOn (fun q : P' × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ (φ q.1) i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
    (hgc : ∀ i, Continuous fun p ↦ (g i p :
      EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i))))
    (K : ∀ i, (morseFamilyCharacteristicMap ψ₁ k hk hε hball₁ hf₁ hs₁ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₀ k hk hε hball₀ hf₀ hs₀ i).comp
        (ContinuousMap.fst.prodMk (diskMapFamily.{u} (g i) (hgc i)))))
    (hK : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
      K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
        {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) :
    ∃ (K' : ∀ i, (morseFamilyCharacteristicMap (fun p ↦ ψ₁ (φ p)) k hk hε
          (fun p ↦ hball₁ (φ p)) (fun p ↦ hf₁ (φ p)) hs₁' i).Homotopy
        ((morseFamilyCharacteristicMap (fun p ↦ ψ₀ (φ p)) k hk hε
          (fun p ↦ hball₀ (φ p)) (fun p ↦ hf₀ (φ p)) hs₀' i).comp
          (ContinuousMap.fst.prodMk
            (diskMapFamily.{u} (fun p ↦ g i (φ p)) ((hgc i).comp φ.continuous)))))
      (hK' : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
        K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
          {y : {x | f x ≤ c + ε} | f y ≤ c - ε}),
      (∀ i t p x, K' i (t, (p, x)) = K i (t, (φ p, x))) ∧
      fiberwiseCellReattachment
          (morseFamilyAttachingMap (fun p ↦ ψ₀ (φ p)) k hk hε (fun p ↦ hball₀ (φ p))
            (fun p ↦ hf₀ (φ p)) hs₀')
          (morseFamilyAttachingMap (fun p ↦ ψ₁ (φ p)) k hk hε (fun p ↦ hball₁ (φ p))
            (fun p ↦ hf₁ (φ p)) hs₁')
          (morseFamilyCharacteristicMap (fun p ↦ ψ₀ (φ p)) k hk hε (fun p ↦ hball₀ (φ p))
            (fun p ↦ hf₀ (φ p)) hs₀')
          (morseFamilyCharacteristicMap (fun p ↦ ψ₁ (φ p)) k hk hε (fun p ↦ hball₁ (φ p))
            (fun p ↦ hf₁ (φ p)) hs₁')
          (morseFamilyCharacteristicMap_diskBoundaryInclusion (fun p ↦ ψ₀ (φ p)) k hk hε
            (fun p ↦ hball₀ (φ p)) (fun p ↦ hf₀ (φ p)) hs₀')
          (morseFamilyCharacteristicMap_diskBoundaryInclusion (fun p ↦ ψ₁ (φ p)) k hk hε
            (fun p ↦ hball₁ (φ p)) (fun p ↦ hf₁ (φ p)) hs₁')
          (fun i ↦ diskMapFamily (fun p ↦ g i (φ p)) ((hgc i).comp φ.continuous))
          (fun i ↦ mapsTo_diskMapFamily_range_diskBoundaryInclusion (fun p ↦ g i (φ p))
            ((hgc i).comp φ.continuous)) K' hK' ≫
        fiberwiseCellAttachmentMap φ (morseFamilyAttachingMap ψ₀ k hk hε hball₀ hf₀ hs₀)
          (morseFamilyAttachingMap (fun p ↦ ψ₀ (φ p)) k hk hε (fun p ↦ hball₀ (φ p))
            (fun p ↦ hf₀ (φ p)) hs₀')
          (morseFamilyAttachingMap_comp_apply ψ₀ k hk hε hball₀ hf₀ hs₀ φ hs₀') =
      fiberwiseCellAttachmentMap φ (morseFamilyAttachingMap ψ₁ k hk hε hball₁ hf₁ hs₁)
          (morseFamilyAttachingMap (fun p ↦ ψ₁ (φ p)) k hk hε (fun p ↦ hball₁ (φ p))
            (fun p ↦ hf₁ (φ p)) hs₁')
          (morseFamilyAttachingMap_comp_apply ψ₁ k hk hε hball₁ hf₁ hs₁ φ hs₁') ≫
        fiberwiseCellReattachment (morseFamilyAttachingMap ψ₀ k hk hε hball₀ hf₀ hs₀)
          (morseFamilyAttachingMap ψ₁ k hk hε hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap ψ₀ k hk hε hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap ψ₁ k hk hε hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε hball₁ hf₁ hs₁)
          (fun i ↦ diskMapFamily (g i) (hgc i))
          (fun i ↦ mapsTo_diskMapFamily_range_diskBoundaryInclusion (g i) (hgc i)) K hK ∧
      fiberwiseCellReattachmentInv
          (morseFamilyAttachingMap (fun p ↦ ψ₀ (φ p)) k hk hε (fun p ↦ hball₀ (φ p))
            (fun p ↦ hf₀ (φ p)) hs₀')
          (morseFamilyAttachingMap (fun p ↦ ψ₁ (φ p)) k hk hε (fun p ↦ hball₁ (φ p))
            (fun p ↦ hf₁ (φ p)) hs₁')
          (morseFamilyCharacteristicMap (fun p ↦ ψ₀ (φ p)) k hk hε (fun p ↦ hball₀ (φ p))
            (fun p ↦ hf₀ (φ p)) hs₀')
          (morseFamilyCharacteristicMap (fun p ↦ ψ₁ (φ p)) k hk hε (fun p ↦ hball₁ (φ p))
            (fun p ↦ hf₁ (φ p)) hs₁')
          (morseFamilyCharacteristicMap_diskBoundaryInclusion (fun p ↦ ψ₀ (φ p)) k hk hε
            (fun p ↦ hball₀ (φ p)) (fun p ↦ hf₀ (φ p)) hs₀')
          (morseFamilyCharacteristicMap_diskBoundaryInclusion (fun p ↦ ψ₁ (φ p)) k hk hε
            (fun p ↦ hball₁ (φ p)) (fun p ↦ hf₁ (φ p)) hs₁')
          (fun i ↦ diskMapFamily (fun p ↦ g i (φ p)) ((hgc i).comp φ.continuous)) K' hK'
          (fun i p ↦ g i (φ p))
          (fun i p w ↦ coe_diskMapFamily_apply_down (fun p ↦ g i (φ p))
            ((hgc i).comp φ.continuous) (p, w)) ≫
        fiberwiseCellAttachmentMap φ (morseFamilyAttachingMap ψ₁ k hk hε hball₁ hf₁ hs₁)
          (morseFamilyAttachingMap (fun p ↦ ψ₁ (φ p)) k hk hε (fun p ↦ hball₁ (φ p))
            (fun p ↦ hf₁ (φ p)) hs₁')
          (morseFamilyAttachingMap_comp_apply ψ₁ k hk hε hball₁ hf₁ hs₁ φ hs₁') =
      fiberwiseCellAttachmentMap φ (morseFamilyAttachingMap ψ₀ k hk hε hball₀ hf₀ hs₀)
          (morseFamilyAttachingMap (fun p ↦ ψ₀ (φ p)) k hk hε (fun p ↦ hball₀ (φ p))
            (fun p ↦ hf₀ (φ p)) hs₀')
          (morseFamilyAttachingMap_comp_apply ψ₀ k hk hε hball₀ hf₀ hs₀ φ hs₀') ≫
        fiberwiseCellReattachmentInv (morseFamilyAttachingMap ψ₀ k hk hε hball₀ hf₀ hs₀)
          (morseFamilyAttachingMap ψ₁ k hk hε hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap ψ₀ k hk hε hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap ψ₁ k hk hε hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε hball₁ hf₁ hs₁)
          (fun i ↦ diskMapFamily (g i) (hgc i)) K hK g
          (fun i p w ↦ coe_diskMapFamily_apply_down (g i) (hgc i) (p, w)) := by
  -- The restricted homotopies, whose ends are the restricted characteristic maps.
  let K' (i : ι) : (morseFamilyCharacteristicMap (fun p ↦ ψ₁ (φ p)) k hk hε
        (fun p ↦ hball₁ (φ p)) (fun p ↦ hf₁ (φ p)) hs₁' i).Homotopy
      ((morseFamilyCharacteristicMap (fun p ↦ ψ₀ (φ p)) k hk hε
        (fun p ↦ hball₀ (φ p)) (fun p ↦ hf₀ (φ p)) hs₀' i).comp
        (ContinuousMap.fst.prodMk
          (diskMapFamily.{u} (fun p ↦ g i (φ p)) ((hgc i).comp φ.continuous)))) :=
    ((K i).compContinuousMap (φ.prodMap (ContinuousMap.id _))).cast
      (ContinuousMap.ext fun x ↦
        (morseFamilyCharacteristicMap_comp_apply ψ₁ k hk hε hball₁ hf₁ hs₁ φ hs₁' i x.1 x.2).symm)
      (ContinuousMap.ext fun x ↦ by
        simp only [ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply,
          ContinuousMap.prodMap_apply, ContinuousMap.id_apply, Prod.map, diskMapFamily_apply]
        exact (morseFamilyCharacteristicMap_comp_apply ψ₀ k hk hε hball₀ hf₀ hs₀ φ hs₀' i x.1
          _).symm)
  have hK'K (i : ι) (t : unitInterval) (p : P') (x : TopCat.disk.{u} (k i)) :
      K' i (t, (p, x)) = K i (t, (φ p, x)) :=
    rfl
  have hK' (i : ι) (t : unitInterval) (p : P') (s : TopCat.diskBoundary.{u} (k i)) :
      K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
        {y : {x | f x ≤ c + ε} | f y ≤ c - ε} := by
    rw [hK'K]
    exact hK i t (φ p) s
  -- The restricted disc maps are the disc maps over `P` at `φ p`, and the restricted isometries
  -- are the isometries over `P` at `φ p`.
  have hh'h (i : ι) (p : P') (x : TopCat.disk.{u} (k i)) :
      diskMapFamily (fun p ↦ g i (φ p)) ((hgc i).comp φ.continuous) (p, x) =
        diskMapFamily (g i) (hgc i) (φ p, x) := by
    rw [diskMapFamily_apply, diskMapFamily_apply]
  exact ⟨K', hK', hK'K,
    fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap (g := φ) (K := K) (hK := hK)
      (K' := K') (hK' := hK') (hh'h := hh'h) (hK'K := hK'K) ..,
    fiberwiseCellReattachmentInv_comp_fiberwiseCellAttachmentMap (g := φ) (K := K) (hK := hK)
      (e := g) (K' := K') (hK' := hK') (e' := fun i p ↦ g i (φ p)) (he'e := fun _ _ ↦ rfl)
      (hK'K := hK'K) ..⟩

end Restriction

end TauCeti
