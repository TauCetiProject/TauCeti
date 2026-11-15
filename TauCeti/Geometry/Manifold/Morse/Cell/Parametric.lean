/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.CharacteristicHomotopy
public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCellAttachment

/-!
# Comparing families of Morse cell attachments over a compact parameter space

Let `ψ p i`, for `p` in a parameter space `P` and `i` in an index type `ι`, be charts of `M` with
values in `ℝⁿ` in which

`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`,

whose targets contain the closed ball of radius `√ε` and whose inverses are jointly continuous in
`p` and the point of that ball. Their characteristic maps
`χ i : P × (D^{k i}, ∂D^{k i}) → (M_{c+ε}, M_{c-ε})`, `(p, w) ↦ (ψ p i)⁻¹(√ε • (w, 0))`, where
`M_a = {f ≤ a}`, and their attaching maps `α i : P × ∂D^{k i} → M_{c-ε}` are continuous families
over `P` (`TauCeti.morseFamilyCharacteristicMap`, `TauCeti.morseFamilyAttachingMap`). Attaching
their cells over each `p` gives the fiberwise adjunction space
`(P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i})` (`TauCeti.fiberwiseCellAttachment`), with its comparison
map to `P × M_{c+ε}`.

For two such families `ψ₀` and `ψ₁` with common centres, whose transitions `ψ₀ p i ∘ (ψ₁ p i)⁻¹`
have derivatives jointly continuous in `p` near the origin, and a compact band `f⁻¹[c - ε, c]`
with no critical point below `c`, Milnor's comparison of the two attachments holds continuously
over a compact `P`
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap`). There is a
fibre homotopy equivalence over `P` between the two fiberwise adjunction spaces which is the
identity on `P × M_{c-ε}`, which followed by the comparison map of `ψ₀` is homotopic to that of
`ψ₁`, and whose two composites are homotopic to the identities; all of these homotopies are
relative to `P × M_{c-ε}` and stay over `P`.

The characteristic maps of the two families are homotopic as maps of pairs, continuously in `p`, up
to the polar factors `g i p` of the negative blocks of the derivatives of the transitions at the
origin (`TauCeti.exists_homotopy_morseFamilyCharacteristicMap_polarFactor`). Since these are
linear isometries, the reattachment map along such a homotopy is a fibre homotopy equivalence
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_of_homotopy`); unlike the comparison at
a single parameter (`TauCeti.exists_homotopicRel_morseCellReattachment_comp`), this needs no
deformation of `M_{c+ε}` onto the attached cells.

## Main results

* `TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap`: **Milnor's
  Lemma 3.6 over a compact parameter space.**

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open Set Metric
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n : ℕ} {P : Type u} [TopologicalSpace P] {ι : Type u}

/-- **Milnor's Lemma 3.6 over a compact parameter space.** Let `f` be smooth, let `P` be compact,
and let `ψ₀ p i` and `ψ₁ p i`, for `p : P` and `i : ι`, be charts with common centres in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose targets contain the closed ball of radius `√ε`,
and whose inverses are jointly continuous in `p` and the point of that ball. Suppose that on a ball
of radius `r i` about the origin the transitions `ψ₀ p i ∘ (ψ₁ p i)⁻¹` are defined and
differentiable, with derivatives `D i p y` jointly continuous in `p` and `y`, and that the band
`f⁻¹[c - ε, c]` is compact and contains no critical point below the level `c`.

Let `Xⱼ = (P × M_{c-ε}) ∪_{αⱼ} ⨆ᵢ (P × D^{k i})` be the fiberwise adjunction spaces of the
attaching families `αⱼ i` of the cells of `ψⱼ`, and `Φⱼ : Xⱼ → P × M_{c+ε}` their comparison
maps. Then there is a fibre homotopy equivalence `X₁ → X₀` over `P` which is the identity on
`P × M_{c-ε}` in both directions, whose composite with `Φ₀` is homotopic to `Φ₁`, and whose two
composites are homotopic to the identities, all by homotopies relative to `P × M_{c-ε}` which stay
over `P`. -/
theorem exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap [CompactSpace P]
    (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
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
    ∃ Ψ : FiberHomotopyEquiv
        (fiberwiseCellAttachmentProj
          (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)).hom
        (fiberwiseCellAttachmentProj
          (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)).hom,
      (∀ x, Ψ.toFun (fiberwiseCellAttachmentIncl _ x) = fiberwiseCellAttachmentIncl _ x) ∧
      (∀ x, Ψ.invFun (fiberwiseCellAttachmentIncl _ x) = fiberwiseCellAttachmentIncl _ x) ∧
      (∃ G : ((fiberwiseCellComparison (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
            (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
            (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀
              hs₀)).hom.comp Ψ.toFun).HomotopyRel
          (fiberwiseCellComparison (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
            (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
            (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁
              hs₁)).hom
          (range (fiberwiseCellAttachmentIncl _)),
        ∀ t y, (G (t, y)).1 = fiberwiseCellAttachmentProj _ y) ∧
      (∃ G : (Ψ.invFun.comp Ψ.toFun).HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl _)),
        ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y) ∧
      ∃ G : (Ψ.toFun.comp Ψ.invFun).HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl _)),
        ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y := by
  -- For each `i`, the polar factors `g i p` and a homotopy `K i : χ₁ i ≃ χ₀ i ∘ g i` over `P`.
  obtain ⟨g, -, hg, K, hK⟩ := exists_homotopy_morseFamilyCharacteristicMap_polarFactor hfs ψ₀ ψ₁
    k hk hε hball₀ hball₁ hf₀ hf₁ hs₀ hs₁ hp hr htr hT hD hcompact hreg
  exact exists_fiberHomotopyEquiv_fiberwiseCellAttachment_of_homotopy _ _ _ _
    (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
    (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁) g hg K hK

end TauCeti
