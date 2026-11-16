/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.CharacteristicHomotopy
public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCell.ReattachmentInv

/-!
# Reattaching the Morse cells of two compact families of charts

Let `ψ₀ p i` and `ψ₁ p i`, for `p` in a compact space `P` and `i` in a type `ι`, be two families of
charts of a manifold `M` centred at the same critical points of a smooth function `f`, in which

`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`,

whose targets contain the closed ball of radius `√ε` and which vary continuously with `p`. Each
family attaches, over every `p`, one cell `D^{k i}` to the lower sublevel `M_{c-ε} = {f ≤ c - ε}`
for each `i`, along the attaching maps `α₀ i` and `α₁ i` of its characteristic maps
(`TauCeti.morseFamilyAttachingMap`). These give two fiberwise adjunction spaces over `P`,

`(P × M_{c-ε}) ∪_{α₀} ⨆ᵢ (P × D^{k i})` and `(P × M_{c-ε}) ∪_{α₁} ⨆ᵢ (P × D^{k i})`

(`TauCeti.fiberwiseCellAttachment`). This file shows that they are homotopy equivalent over `P`
relative to `P × M_{c-ε}`, by Milnor's comparison of the cells of two charts carried out
continuously in `p`
(`TauCeti.exists_fiberwiseCellReattachmentInv_homotopyRel_morseFamily`).

The equivalence is Milnor's reattachment map `E` (`TauCeti.fiberwiseCellReattachment`). It is the
identity on `P × M_{c-ε}`; on the disc of radius `1/2` of the `i`-th cell over `p` it is
`x ↦ g i p (2x)`, where `g i p` is the polar factor of the negative block of the derivative at the
origin of the transition `ψ₀ p i ∘ (ψ₁ p i)⁻¹`; on the outer annulus it follows a homotopy `K i`
from the characteristic maps of `ψ₁` to those of `ψ₀` composed with `g i`, which keeps the boundary
spheres in `M_{c-ε}` (`TauCeti.exists_homotopy_morseFamilyCharacteristicMap_polarFactor`). Since
each `g i p` is a linear isometry, the reattachment map of the inverse isometries and the reversed
homotopies (`TauCeti.fiberwiseCellReattachmentInv`) is an inverse of `E`: both composites are
homotopic to the identity relative to `P × M_{c-ε}`, through maps over `P`. Moreover `E` is
compatible with the comparison maps `Φⱼ` of the attachments into `P × M_{c+ε}`: `Φ₀ ∘ E` is
homotopic to `Φ₁` relative to `P × M_{c-ε}` over `P` (`TauCeti.fiberwiseCellReattachmentHomotopy`),
and likewise `Φ₁ ∘ E⁻¹` to `Φ₀` (`TauCeti.fiberwiseCellReattachmentInvHomotopy`).

The data are stated explicitly, so that `E` and its inverse are the fiberwise reattachment maps of
the given polar factors and homotopies. Restricting this data along a map `P' → P` of parameter
spaces, for instance the inclusion of a subcomplex, gives the reattachment maps of the restricted
chart families, compatibly with the maps of fiberwise adjunction spaces
(`TauCeti.fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap`,
`TauCeti.fiberwiseCellReattachmentInv_comp_fiberwiseCellAttachmentMap`).

For a single pair of charts, where `P` is a point, the reattachment map is
`TauCeti.morseCellReattachment`.

## Main results

* `TauCeti.exists_fiberwiseCellReattachmentInv_homotopyRel_morseFamily`:
  for two compact families of Morse charts, the fiberwise reattachment map along the polar factors
  of their transitions is a homotopy equivalence over the parameter space, relative to the lower
  sublevel.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval CategoryTheory
open LinearIsometry (piLpExtendByZero)
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n : ℕ}

/-- **The cells of two compact families of Morse charts are reattached by a homotopy equivalence
over the parameter space.** Let `ψ₀ p i` and `ψ₁ p i`, for `p` in a compact space `P` and `i : ι`,
be charts with common centres `(ψ₀ p i)⁻¹ 0 = (ψ₁ p i)⁻¹ 0` in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose targets contain the closed ball of radius `√ε`
and whose inverses are jointly continuous in `p` and the point of that ball. Suppose that on a ball
of radius `r i` about the origin the transitions `ψ₀ p i ∘ (ψ₁ p i)⁻¹` are defined and
differentiable, with derivatives `D i p y` jointly continuous in `p` and `y`, that
`f⁻¹[c - ε, c]` is compact and that `f` has no critical point with value in `[c - ε, c)`.

Then the polar factors `g i p` of the negative blocks `ι† (D i p 0) ι` are linear isometries
depending continuously on `p`, where `ι : ℝ^{k i} → ℝⁿ` extends by zero onto the first `k i`
coordinates, and there are homotopies `K i` over `P` from the characteristic maps of `ψ₁` to those
of `ψ₀` composed with `g i`, keeping the boundary spheres in `M_{c-ε}`. The fiberwise reattachment
map `E : (P × M_{c-ε}) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × M_{c-ε}) ∪_{α₀} ⨆ᵢ (P × D^{k i})` of this
data and the reattachment map `E⁻¹` of the inverse isometries and the reversed homotopies are
homotopy inverse to each other: `E⁻¹ ∘ E` and `E ∘ E⁻¹` are homotopic to the identities relative to
`P × M_{c-ε}`, through maps over `P`. -/
theorem exists_fiberwiseCellReattachmentInv_homotopyRel_morseFamily
    (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f) {ι P : Type u} [TopologicalSpace P] [CompactSpace P]
    (ψ₀ ψ₁ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n) (hε : 0 < ε)
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
    (hp : ∀ p i, (ψ₀ p i).symm 0 = (ψ₁ p i).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (ψ₁ p i).symm ⁻¹' (ψ₀ p i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ ψ₀ p i ((ψ₁ p i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)),
      (∀ i p, ⇑(g i p) = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (hk i))).toContinuousLinearMap ∘L D i p 0 ∘L
            (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (hk i))).toContinuousLinearMap).polarFactor) ∧
      ∃ (hgc : ∀ i, Continuous fun p ↦ (g i p :
          EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i))))
        (K : ∀ i, (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁ i).Homotopy
          ((morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
            (ContinuousMap.fst.prodMk (diskMapFamily.{u} (g i) (hgc i)))))
        (hK : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
          K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
            {y : {x | f x ≤ c + ε} | f y ≤ c - ε}),
        (∃ G : (fiberwiseCellReattachment (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (fun i ↦ diskMapFamily.{u} (g i) (hgc i))
              (fun i ↦ mapsTo_diskMapFamily_range_diskBoundaryInclusion (g i) (hgc i)) K hK ≫
            fiberwiseCellReattachmentInv (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (fun i ↦ diskMapFamily.{u} (g i) (hgc i)) K hK g
              (fun i p w ↦ coe_diskMapFamily_apply_down (g i) (hgc i) (p, w))).hom.HomotopyRel
            (ContinuousMap.id _)
            (range (fiberwiseCellAttachmentIncl
              (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁))),
          ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y) ∧
        ∃ G : (fiberwiseCellReattachmentInv (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (fun i ↦ diskMapFamily.{u} (g i) (hgc i)) K hK g
              (fun i p w ↦ coe_diskMapFamily_apply_down (g i) (hgc i) (p, w)) ≫
            fiberwiseCellReattachment (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
              (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
              (fun i ↦ diskMapFamily.{u} (g i) (hgc i))
              (fun i ↦ mapsTo_diskMapFamily_range_diskBoundaryInclusion (g i) (hgc i))
              K hK).hom.HomotopyRel
            (ContinuousMap.id _)
            (range (fiberwiseCellAttachmentIncl
              (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀))),
          ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y := by
  obtain ⟨g, hg, hgc, K, hK⟩ := exists_homotopy_morseFamilyCharacteristicMap_polarFactor hfs ψ₀ ψ₁
    k hk hε hball₀ hball₁ hf₀ hf₁ hs₀ hs₁ hp hr htr hT hD hcompact hreg
  exact ⟨g, hg, hgc, K, hK,
    exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachmentInv ..,
    exists_homotopyRel_fiberwiseCellReattachmentInv_comp_fiberwiseCellReattachment ..⟩

end TauCeti
