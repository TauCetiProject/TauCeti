/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Family.Reattachment

/-!
# Milnor's comparison of Morse cells for compact families of charts

Let `f` be a smooth function on a boundaryless manifold `M`, write `M_a = {f ≤ a}`, and let
`ψ₀ p i` and `ψ₁ p i` be two families of normal-form charts at a critical level `c`, indexed by `i`
in a type `ι` and depending continuously on a parameter `p` in a compact space `P`, with common
centres and the same indices `k i`. Each family attaches, over every `p`, one disc `D^{k i}` to the
lower sublevel `M_{c-ε}` for each `i`, along its attaching maps `αⱼ i (p, ·) : ∂D^{k i} → M_{c-ε}`;
together these are the fiberwise adjunction spaces

`(P × M_{c-ε}) ∪_{αⱼ} ⨆ᵢ (P × D^{k i})`

(`TauCeti.fiberwiseCellAttachment` of `TauCeti.morseFamilyAttachingMap`), lying over `P`, with
comparison maps `Φⱼ` to `P × M_{c+ε}` given by the characteristic maps of the charts
(`TauCeti.fiberwiseCellComparison` of `TauCeti.morseFamilyCharacteristicMap`).

This file compares the two families continuously in `p`
(`TauCeti.exists_fiberwiseCellReattachment_morseFamily`). Let `g i p` be the polar factor of the
negative block of the derivative at the origin of the transition `ψ₀ p i ∘ (ψ₁ p i)⁻¹`, an
orthogonal map of `ℝ^{k i}` depending continuously on `p`. Then there is a map

`ρ : (P × M_{c-ε}) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × M_{c-ε}) ∪_{α₀} ⨆ᵢ (P × D^{k i})`

over `P` which is the identity on `P × M_{c-ε}`, which on the disc of radius `1/2` of the `i`-th
cell over `p` is `x ↦ g i p (2x)`, and which is a homotopy equivalence over `P` relative to
`P × M_{c-ε}`: it has an inverse over `P` which is also the identity on `P × M_{c-ε}`, both
composites are homotopic to the identities relative to `P × M_{c-ε}` through maps over `P`, and
`Φ₀ ∘ ρ` is homotopic to `Φ₁` relative to `P × M_{c-ε}` through maps over `P`. For `P` a point
this is Milnor's Lemma 3.6 for the cells of two charts.

The map `ρ` is the fiberwise reattachment map `TauCeti.fiberwiseCellReattachment` of the polar
factors and of the homotopies of characteristic maps
`TauCeti.exists_homotopy_morseFamilyCharacteristicMap_polarFactor`, and its inverse is
`TauCeti.fiberwiseCellReattachmentInv`, the reattachment map of the inverse isometries and the
reversed homotopies. The statement keeps the polar factors: even when every `g i p` lies in the
special orthogonal group, a map `P → SO(k i)` need not be homotopic to a constant one, so the
argument removing an orientation-preserving polar factor for a single pair of charts
(`TauCeti.homotopic_morseAttachingMap_of_det_pos`) does not apply over `P`.

With the reattachment data `(g, K)` stated explicitly, the homotopy equivalence is
`TauCeti.exists_fiberwiseCellReattachmentInv_homotopyRel_morseFamily`: there `ρ` is the fiberwise
reattachment map of the given polar factors `g` and of the homotopies `K` of characteristic maps,
and `ρ'` that of the inverse isometries and the reversed homotopies.

The whole construction, maps and homotopies alike, is compatible with restriction of the
parameter along a continuous map `u : P' → P`, for instance the inclusion of a subcomplex. The
restricted data are the polar factors `g i (u p)` and the homotopies `K i` read at `u p`
(`TauCeti.exists_fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap_morseFamily`). They give
maps `ρᵤ` and `ρᵤ'` over `P'` between the cell attachments of the chart families `ψⱼ (u p) i`, with
homotopies `ρᵤ' ∘ ρᵤ ≃ id`, `ρᵤ ∘ ρᵤ' ≃ id` and `Φ₀ ∘ ρᵤ ≃ Φ₁` relative to `P' × M_{c-ε}` through
maps over `P'`. The maps of fiberwise adjunction spaces over `u`
(`TauCeti.fiberwiseCellAttachmentMap`) carry `ρᵤ` and `ρᵤ'` to `ρ` and `ρ'`, and each homotopy over
`P'` to the corresponding homotopy over `P`. So the restriction of the homotopy equivalence over
`P` to `P'` is the homotopy equivalence of the restricted families, with its homotopies.

## Main results

* `TauCeti.exists_fiberwiseCellReattachment_morseFamily`: **Milnor's Lemma 3.6 for compact
  families of Morse charts.** The cell attachments of two compact families of normal-form charts
  are homotopy equivalent over the parameter space relative to the lower sublevel, by the
  reattachment map of the polar factors of their transitions, compatibly with the comparison maps
  and with restriction of the parameter, homotopies included.
* `TauCeti.exists_fiberwiseCellReattachmentInv_homotopyRel_morseFamily`: the same homotopy
  equivalence, with the polar factors and the homotopies of characteristic maps given explicitly.

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

variable {ι P : Type u} [TopologicalSpace P]
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

omit [T2Space M] in
/-- **The reattachment map of two chart families and its inverse.** For the data `(g, K)` of a
fiberwise reattachment map `ρ` between the cell attachments of two chart families over `P`, with
inverse `ρ'`, both lie over `P` and are the identity on `P × M_{c-ε}`, and the homotopies
`ρ' ∘ ρ ≃ id`, `ρ ∘ ρ' ≃ id` and `Φ₀ ∘ ρ ≃ Φ₁` relative to `P × M_{c-ε}` built from these data
(`TauCeti.fiberwiseCellReattachmentCompInvHomotopy`,
`TauCeti.fiberwiseCellReattachmentInvCompHomotopy` and `TauCeti.fiberwiseCellReattachmentHomotopy`)
lie over `P` at all times. -/
private theorem fiberwiseCellReattachment_morseFamily_spec
    (g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
    (hgc : ∀ i, Continuous fun p ↦
      (g i p : EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i))))
    (hh : ∀ i p, MapsTo (fun w ↦ diskMapFamily.{u} (g i) (hgc i) (p, w))
      (range (TopCat.diskBoundaryInclusion (k i))) (range (TopCat.diskBoundaryInclusion (k i))))
    (he : ∀ i p (w : TopCat.disk.{u} (k i)),
      ((diskMapFamily (g i) (hgc i) (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = g i p w.down)
    (K : ∀ i, (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
        (ContinuousMap.fst.prodMk (diskMapFamily.{u} (g i) (hgc i)))))
    (hK : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
      K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) :
    let hχ₀ := morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀
    let hχ₁ := morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁
    let ρ := fiberwiseCellReattachment _ _ _ _ hχ₀ hχ₁ _ hh K hK
    let ρ' := fiberwiseCellReattachmentInv _ _ _ _ hχ₀ hχ₁ _ K hK g he
    fiberwiseCellAttachmentIncl _ ≫ ρ = fiberwiseCellAttachmentIncl _ ∧
      fiberwiseCellAttachmentIncl _ ≫ ρ' = fiberwiseCellAttachmentIncl _ ∧
      (∀ y, fiberwiseCellAttachmentProj _ (ρ y) = fiberwiseCellAttachmentProj _ y) ∧
      (∀ y, fiberwiseCellAttachmentProj _ (ρ' y) = fiberwiseCellAttachmentProj _ y) ∧
      (∀ t y, fiberwiseCellAttachmentProj _
        (fiberwiseCellReattachmentCompInvHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK g he (t, y)) =
          fiberwiseCellAttachmentProj _ y) ∧
      (∀ t y, fiberwiseCellAttachmentProj _
        (fiberwiseCellReattachmentInvCompHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK g he (t, y)) =
          fiberwiseCellAttachmentProj _ y) ∧
      ∀ t y, (fiberwiseCellReattachmentHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK (t, y)).1 =
        fiberwiseCellAttachmentProj _ y := by
  intro hχ₀ hχ₁ ρ ρ'
  refine ⟨?_, ?_, fiberwiseCellAttachmentProj_fiberwiseCellReattachment _ _ _ _ hχ₀ hχ₁ _ hh K hK,
    fiberwiseCellAttachmentProj_fiberwiseCellReattachmentInv _ _ _ _ hχ₀ hχ₁ _ K hK g he,
    fiberwiseCellAttachmentProj_fiberwiseCellReattachmentCompInvHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK
      g he,
    fiberwiseCellAttachmentProj_fiberwiseCellReattachmentInvCompHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK
      g he,
    fst_fiberwiseCellReattachmentHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK⟩
  · ext x
    exact fiberwiseCellReattachment_fiberwiseCellAttachmentIncl _ _ _ _ hχ₀ hχ₁ _ hh K hK x
  · ext x
    exact fiberwiseCellReattachmentInv_fiberwiseCellAttachmentIncl _ _ _ _ hχ₀ hχ₁ _ K hK g he x

/-- **Milnor's Lemma 3.6 for compact families of Morse charts.** Let `ψ₀ p i` and `ψ₁ p i`, for
`p` in a compact space `P` and `i : ι`, be charts with common centres
`(ψ₀ p i)⁻¹ 0 = (ψ₁ p i)⁻¹ 0` in which `f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose targets
contain the closed ball of radius `√ε` and whose inverses are jointly continuous in `p` and the
point of that ball. Suppose that on a ball of radius `r i` about the origin the transitions
`ψ₀ p i ∘ (ψ₁ p i)⁻¹` are defined and differentiable, with derivatives `D i p y` jointly
continuous in `p` and `y`, that `f⁻¹[c - ε, c]` is compact and that `f` has no critical point with
value in `[c - ε, c)`. Let `g i p` be the polar factor of the negative block `ι† (D i p 0) ι`,
where `ι : ℝ^{k i} → ℝⁿ` extends by zero onto the first `k i` coordinates.

Then each `g i p` is a linear isometry, depending continuously on `p`, and there are maps `ρ` and
`ρ'` over `P` between the cell attachments `(P × M_{c-ε}) ∪_{αⱼ} ⨆ᵢ (P × D^{k i})` of the two
families, in both directions, with homotopies `G₁`, `G₂` and `G₃`, such that:
* both maps are the identity on `P × M_{c-ε}`;
* on the disc of radius `1/2` of the `i`-th cell over `p`, `ρ` is `x ↦ g i p (2x)`;
* `G₁ : ρ' ∘ ρ ≃ id` and `G₂ : ρ ∘ ρ' ≃ id` are homotopies relative to `P × M_{c-ε}` through maps
  over `P`;
* `G₃ : Φ₀ ∘ ρ ≃ Φ₁` is a homotopy relative to `P × M_{c-ε}` through maps over `P`, for the
  comparison maps `Φⱼ` to `P × M_{c+ε}` of the characteristic maps of the two families;
* the whole construction restricts along every continuous `u : P' → P`, for instance the
  inclusion of a subcomplex: for the chart families `ψⱼ (u p) i` there are maps `ρᵤ`, `ρᵤ'` and
  homotopies `G₁ᵤ`, `G₂ᵤ`, `G₃ᵤ` over `P'` with the same properties relative to `P' × M_{c-ε}`,
  and the maps of fiberwise adjunction spaces over `u` (`TauCeti.fiberwiseCellAttachmentMap`)
  carry `ρᵤ` and `ρᵤ'` to `ρ` and `ρ'`, and each of `G₁ᵤ`, `G₂ᵤ`, `G₃ᵤ` to the corresponding
  homotopy over `P`. -/
theorem exists_fiberwiseCellReattachment_morseFamily [CompactSpace P]
    (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f) (hp : ∀ p i, (ψ₀ p i).symm 0 = (ψ₁ p i).symm 0)
    {r : ι → ℝ} (hr : ∀ i, 0 < r i)
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
      (∀ i, Continuous fun p ↦
        (g i p : EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i)))) ∧
      ∃ (ρ : fiberwiseCellAttachment (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁) ⟶
          fiberwiseCellAttachment (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀))
        (ρ' : fiberwiseCellAttachment (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀) ⟶
          fiberwiseCellAttachment (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁))
        (G₁ : (ρ ≫ ρ').hom.HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl _)))
        (G₂ : (ρ' ≫ ρ).hom.HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl _)))
        (G₃ : (ρ ≫ fiberwiseCellComparison _
            (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
            (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀
              hs₀)).hom.HomotopyRel
          (fiberwiseCellComparison _ (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
            (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)).hom
          (range (fiberwiseCellAttachmentIncl _))),
        fiberwiseCellAttachmentIncl _ ≫ ρ = fiberwiseCellAttachmentIncl _ ∧
        fiberwiseCellAttachmentIncl _ ≫ ρ' = fiberwiseCellAttachmentIncl _ ∧
        (∀ i p (w v : TopCat.disk.{u} (k i)), ‖w.down.val‖ ≤ 1 / 2 →
          v.down.val = (2 : ℝ) • w.down.val →
          ρ (fiberwiseCellAttachmentCell _ i (p, w)) =
            fiberwiseCellAttachmentCell _ i (p, (g i p).diskMap v)) ∧
        (∀ y, fiberwiseCellAttachmentProj _ (ρ y) = fiberwiseCellAttachmentProj _ y) ∧
        (∀ y, fiberwiseCellAttachmentProj _ (ρ' y) = fiberwiseCellAttachmentProj _ y) ∧
        (∀ t y, fiberwiseCellAttachmentProj _ (G₁ (t, y)) = fiberwiseCellAttachmentProj _ y) ∧
        (∀ t y, fiberwiseCellAttachmentProj _ (G₂ (t, y)) = fiberwiseCellAttachmentProj _ y) ∧
        (∀ t y, (G₃ (t, y)).1 = fiberwiseCellAttachmentProj _ y) ∧
        ∀ {P' : Type u} [TopologicalSpace P'] (u : C(P', P))
          (hs₀' : ∀ i, ContinuousOn
            (fun q : P' × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ (u q.1) i).symm q.2)
            (univ ×ˢ closedBall 0 √ε))
          (hs₁' : ∀ i, ContinuousOn
            (fun q : P' × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ (u q.1) i).symm q.2)
            (univ ×ˢ closedBall 0 √ε)),
          ∃ (ρᵤ : fiberwiseCellAttachment (morseFamilyAttachingMap (fun p ↦ ψ₁ (u p)) k hk hε.le
                (fun p ↦ hball₁ (u p)) (fun p ↦ hf₁ (u p)) hs₁') ⟶
              fiberwiseCellAttachment (morseFamilyAttachingMap (fun p ↦ ψ₀ (u p)) k hk hε.le
                (fun p ↦ hball₀ (u p)) (fun p ↦ hf₀ (u p)) hs₀'))
            (ρᵤ' : fiberwiseCellAttachment (morseFamilyAttachingMap (fun p ↦ ψ₀ (u p)) k hk hε.le
                (fun p ↦ hball₀ (u p)) (fun p ↦ hf₀ (u p)) hs₀') ⟶
              fiberwiseCellAttachment (morseFamilyAttachingMap (fun p ↦ ψ₁ (u p)) k hk hε.le
                (fun p ↦ hball₁ (u p)) (fun p ↦ hf₁ (u p)) hs₁'))
            (G₁ᵤ : (ρᵤ ≫ ρᵤ').hom.HomotopyRel (ContinuousMap.id _)
              (range (fiberwiseCellAttachmentIncl _)))
            (G₂ᵤ : (ρᵤ' ≫ ρᵤ).hom.HomotopyRel (ContinuousMap.id _)
              (range (fiberwiseCellAttachmentIncl _)))
            (G₃ᵤ : (ρᵤ ≫ fiberwiseCellComparison _
                (morseFamilyCharacteristicMap (fun p ↦ ψ₀ (u p)) k hk hε.le (fun p ↦ hball₀ (u p))
                  (fun p ↦ hf₀ (u p)) hs₀')
                (morseFamilyCharacteristicMap_diskBoundaryInclusion (fun p ↦ ψ₀ (u p)) k hk hε.le
                  (fun p ↦ hball₀ (u p)) (fun p ↦ hf₀ (u p)) hs₀')).hom.HomotopyRel
              (fiberwiseCellComparison _
                (morseFamilyCharacteristicMap (fun p ↦ ψ₁ (u p)) k hk hε.le (fun p ↦ hball₁ (u p))
                  (fun p ↦ hf₁ (u p)) hs₁')
                (morseFamilyCharacteristicMap_diskBoundaryInclusion (fun p ↦ ψ₁ (u p)) k hk hε.le
                  (fun p ↦ hball₁ (u p)) (fun p ↦ hf₁ (u p)) hs₁')).hom
              (range (fiberwiseCellAttachmentIncl _))),
            fiberwiseCellAttachmentIncl _ ≫ ρᵤ = fiberwiseCellAttachmentIncl _ ∧
            fiberwiseCellAttachmentIncl _ ≫ ρᵤ' = fiberwiseCellAttachmentIncl _ ∧
            (∀ y, fiberwiseCellAttachmentProj _ (ρᵤ y) = fiberwiseCellAttachmentProj _ y) ∧
            (∀ y, fiberwiseCellAttachmentProj _ (ρᵤ' y) = fiberwiseCellAttachmentProj _ y) ∧
            (∀ t y, fiberwiseCellAttachmentProj _ (G₁ᵤ (t, y)) =
              fiberwiseCellAttachmentProj _ y) ∧
            (∀ t y, fiberwiseCellAttachmentProj _ (G₂ᵤ (t, y)) =
              fiberwiseCellAttachmentProj _ y) ∧
            (∀ t y, (G₃ᵤ (t, y)).1 = fiberwiseCellAttachmentProj _ y) ∧
            ρᵤ ≫ fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₀ k hk hε.le hball₀ hf₀ hs₀ u hs₀') =
              fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₁ k hk hε.le hball₁ hf₁ hs₁ u hs₁') ≫ ρ ∧
            ρᵤ' ≫ fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₁ k hk hε.le hball₁ hf₁ hs₁ u hs₁') =
              fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₀ k hk hε.le hball₀ hf₀ hs₀ u hs₀') ≫ ρ' ∧
            (∀ t y, G₁ (t, fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₁ k hk hε.le hball₁ hf₁ hs₁ u hs₁') y) =
              fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₁ k hk hε.le hball₁ hf₁ hs₁ u hs₁')
                (G₁ᵤ (t, y))) ∧
            (∀ t y, G₂ (t, fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₀ k hk hε.le hball₀ hf₀ hs₀ u hs₀') y) =
              fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₀ k hk hε.le hball₀ hf₀ hs₀ u hs₀')
                (G₂ᵤ (t, y))) ∧
            ∀ t y, G₃ (t, fiberwiseCellAttachmentMap u _ _
                (morseFamilyAttachingMap_comp_apply ψ₁ k hk hε.le hball₁ hf₁ hs₁ u hs₁') y) =
              (u (G₃ᵤ (t, y)).1, (G₃ᵤ (t, y)).2) := by
  obtain ⟨g, hg, hgc, K, hK⟩ := exists_homotopy_morseFamilyCharacteristicMap_polarFactor hfs ψ₀ ψ₁
    k hk hε hball₀ hball₁ hf₀ hf₁ hs₀ hs₁ hp hr htr hT hD hcompact hreg
  -- The reattachment data: the disc maps of the polar factors and the homotopies `K i`.
  have hχ₀ := morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀
  have hχ₁ := morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁
  have hh (i : ι) (p : P) := mapsTo_diskMapFamily_range_diskBoundaryInclusion (g i) (hgc i) p
  have he (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
      ((diskMapFamily (g i) (hgc i) (p, w)).down : EuclideanSpace ℝ (Fin (k i))) =
        g i p w.down := by
    rw [diskMapFamily_apply, LinearIsometryEquiv.coe_diskMap_apply_down]
  obtain ⟨hι, hι', hπ, hπ', hG₁, hG₂, hG₃⟩ := fiberwiseCellReattachment_morseFamily_spec ψ₀ ψ₁ k
    hk hε hball₀ hball₁ hf₀ hf₁ hs₀ hs₁ g hgc hh he K hK
  refine ⟨g, hg, hgc, fiberwiseCellReattachment _ _ _ _ hχ₀ hχ₁ _ hh K hK,
    fiberwiseCellReattachmentInv _ _ _ _ hχ₀ hχ₁ _ K hK g he,
    fiberwiseCellReattachmentCompInvHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK g he,
    fiberwiseCellReattachmentInvCompHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK g he,
    fiberwiseCellReattachmentHomotopy _ _ _ _ hχ₀ hχ₁ _ hh K hK, hι, hι',
    fun i p w v hw hv ↦ (fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le _ _ _ _
      hχ₀ hχ₁ _ hh K hK i p hw hv).trans (by rw [diskMapFamily_apply]),
    hπ, hπ', hG₁, hG₂, hG₃, fun u hs₀' hs₁' ↦ ?_⟩
  -- The same construction for the restricted data `(g ∘ u, K ∘ (u × id))` over `P'`.
  obtain ⟨K', hK', hK'K, hρ, hρ'⟩ :=
    exists_fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap_morseFamily u ψ₀ ψ₁ k hk hε.le
      hball₀ hball₁ hf₀ hf₁ hs₀ hs₁ hs₀' hs₁' g hgc K hK
  have hgc' (i : ι) := (hgc i).comp u.continuous
  have hh' (i : ι) p := mapsTo_diskMapFamily_range_diskBoundaryInclusion _ (hgc' i) p
  have hh'h (i : ι) p (w : TopCat.disk.{u} (k i)) :
      diskMapFamily (fun p ↦ g i (u p)) (hgc' i) (p, w) = diskMapFamily (g i) (hgc i) (u p, w) := by
    rw [diskMapFamily_apply, diskMapFamily_apply]
  have he' (i : ι) p (w : TopCat.disk.{u} (k i)) :
      ((diskMapFamily (fun p ↦ g i (u p)) (hgc' i) (p, w)).down :
        EuclideanSpace ℝ (Fin (k i))) = g i (u p) w.down := by
    rw [hh'h, he]
  obtain ⟨hι, hι', hπ, hπ', hG₁, hG₂, hG₃⟩ := fiberwiseCellReattachment_morseFamily_spec _ _ k hk
    hε _ _ _ _ hs₀' hs₁' _ hgc' hh' he' K' hK'
  exact ⟨_, _, _, _, _, hι, hι', hπ, hπ', hG₁, hG₂, hG₃, hρ, hρ',
    fun t y ↦ fiberwiseCellReattachmentCompInvHomotopy_fiberwiseCellAttachmentMap (g := u)
      (hh := hh) (K := K) (hK := hK) (e := g) (he := he) (hh' := hh') (K' := K') (hK' := hK')
      (he' := he') (hK'K := hK'K) (t := t) (y := y) ..,
    fun t y ↦ fiberwiseCellReattachmentInvCompHomotopy_fiberwiseCellAttachmentMap (g := u)
      (hh := hh) (K := K) (hK := hK) (e := g) (he := he) (hh' := hh') (K' := K') (hK' := hK')
      (he' := he') (he'e := fun _ _ ↦ rfl) (hK'K := hK'K) (t := t) (y := y) ..,
    fun t y ↦ fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentMap (g := u) (hh := hh)
      (K := K) (hK := hK) (hh' := hh') (K' := K') (hK' := hK') (hK'K := hK'K) (t := t)
      (y := y) ..⟩

end TauCeti
