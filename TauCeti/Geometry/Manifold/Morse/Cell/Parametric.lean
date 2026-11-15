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

Let `ψ p`, for `p` in a parameter space `P`, be charts of `M` with values in `ℝⁿ` in which

`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`,

whose targets contain the closed ball of radius `√ε` and whose inverses are jointly continuous in
`p` and the point of that ball. Their characteristic maps
`χ p : (D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`, `w ↦ (ψ p)⁻¹(√ε • (w, 0))`, where `M_a = {f ≤ a}`, form
a continuous family over `P` (`TauCeti.morseCharacteristicFamily`), and so do their attaching maps
`∂D^k → M_{c-ε}` (`TauCeti.morseAttachingFamily`). Attaching, over each `p`, the cells of a
family `ψ i` of such chart families gives the fiberwise adjunction space
`(P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i})` (`TauCeti.fiberwiseCellAttachment`), with its comparison
map to `P × M_{c+ε}`.

For two such families `ψ₀ i` and `ψ₁ i` with common centres, whose transitions `ψ₀ i p ∘ (ψ₁ i p)⁻¹`
have derivatives jointly continuous in `p` near the origin, and a compact band `f⁻¹[c - ε, c]`
with no critical point below `c`, Milnor's comparison of the two attachments holds continuously
over a compact `P`
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseAttachingFamily`). There is a
fibre homotopy equivalence over `P` between the two fiberwise adjunction spaces which is the
identity on `P × M_{c-ε}`, which followed by the comparison map of `ψ₀` is homotopic to that of
`ψ₁`, and whose two composites are homotopic to the identities; all of these homotopies are
relative to `P × M_{c-ε}` and stay over `P`.

The characteristic maps of the two families are homotopic as maps of pairs, continuously in `p`, up
to the polar factors `g i p` of the negative blocks of the derivatives of the transitions at the
origin (`TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor_family`). Since these are
linear isometries, the reattachment map along such a homotopy is a fibre homotopy equivalence
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_of_homotopy`); unlike the comparison at
a single parameter (`TauCeti.exists_homotopicRel_morseCellReattachment_comp`), this needs no
deformation of `M_{c+ε}` onto the attached cells.

## Main results

* `TauCeti.exists_homotopy_morseCharacteristicFamily`: the characteristic family of `ψ₁` is
  homotopic over `P`, as a family of maps of pairs, to that of `ψ₀` composed with the disk maps of
  a jointly continuous family of linear isometries.
* `TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseAttachingFamily`: **Milnor's
  Lemma 3.6 over a compact parameter space.**

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open Set Metric Topology unitInterval CategoryTheory
open scoped ContDiff Manifold

universe u

namespace TauCeti

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n : ℕ} {P : Type u} [TopologicalSpace P] {ι : Type u} {k : ι → ℕ}

/-- **Characteristic families of two chart families are homotopic up to isometries.** Let `P` be
compact and let `ψ₀ p` and `ψ₁ p` be normal-form charts with common centres, as in
`TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor_family`. Then there are linear
isometries `g p` of `ℝᵏ`, jointly continuous in `p` and the point, and a homotopy over `P` from the
characteristic family of `ψ₁` to that of `ψ₀` composed with the disk maps of the `g p`, which keeps
the boundary spheres in `M_{c-ε}`. The `g p` are the polar factors of the negative blocks of the
derivatives of the transitions at the origin. -/
theorem exists_homotopy_morseCharacteristicFamily [CompactSpace P] {k : ℕ}
    (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f) (ψ₀ ψ₁ : P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hk : k ≤ n) (hε : 0 < ε) (hball₀ : ∀ p, closedBall 0 √ε ⊆ (ψ₀ p).target)
    (hball₁ : ∀ p, closedBall 0 √ε ⊆ (ψ₁ p).target)
    (hf₀ : ∀ p, ∀ y ∈ (ψ₀ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ p y j ^ 2)
    (hf₁ : ∀ p, ∀ y ∈ (ψ₁ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ p y j ^ 2)
    (hs₀ : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁ : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hp : ∀ p, (ψ₀ p).symm 0 = (ψ₁ p).symm 0) {r : ℝ} (hr : 0 < r)
    (htr : ∀ p, ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ (ψ₁ p).symm ⁻¹' (ψ₀ p).source)
    {D : P → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      HasFDerivAt (fun z ↦ ψ₀ p ((ψ₁ p).symm z)) (D p y) y)
    (hD : ContinuousOn (Function.uncurry D) (univ ×ˢ ball 0 r))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ (g : P → EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
      (hg : Continuous fun q : P × EuclideanSpace ℝ (Fin k) ↦ g q.1 q.2)
      (K : (morseCharacteristicFamily ψ₁ hk hε.le hball₁ hf₁ hs₁).Homotopy
        ((morseCharacteristicFamily ψ₀ hk hε.le hball₀ hf₀ hs₀).comp
          (ContinuousMap.fst.prodMk (TopCat.diskMapFamily.{u} g hg)))),
      ∀ t p s, K (t, (p, TopCat.diskBoundaryInclusion k s)) ∈
        {y : {x | f x ≤ c + ε} | f y ≤ c - ε} := by
  obtain ⟨g, hg, hgc, K, hK0, hK1, hKb⟩ := exists_homotopy_morseCharacteristicMap_polarFactor_family
    hf ψ₀ ψ₁ hk hε hball₀ hball₁ hf₀ hf₁ hs₀ hs₁ hp hr htr hT hD hcompact hreg
  -- The polar factors are continuous in the operator norm.
  have hgc' : Continuous fun p ↦
      (g p : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    hgc.congr fun p ↦ ContinuousLinearMap.ext fun x ↦ (congrFun (hg p) x).symm
  refine ⟨g, (hgc'.comp continuous_fst).clm_apply continuous_snd,
    { toContinuousMap := K
      map_zero_left := fun q ↦ (hK0 q.1 q.2).trans (morseCharacteristicFamily_apply ..).symm
      map_one_left := fun q ↦ (hK1 q.1 q.2).trans (by
        simp only [ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply,
          morseCharacteristicFamily_apply]
        exact congrArg _ (TopCat.diskMapFamily_apply _ _ q).symm) }, hKb⟩

/-- **Milnor's Lemma 3.6 over a compact parameter space.** Let `f` be smooth, let `P` be compact,
and let `ψ₀ i p` and `ψ₁ i p`, for `i : ι` and `p : P`, be charts with common centres in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose targets contain the closed ball of radius `√ε`,
and whose inverses are jointly continuous in `p` and the point of that ball. Suppose that on a ball
of radius `r i` about the origin the transitions `ψ₀ i p ∘ (ψ₁ i p)⁻¹` are defined and
differentiable, with derivatives `D i p y` jointly continuous in `p` and `y`, and that the band
`f⁻¹[c - ε, c]` is compact and contains no critical point below the level `c`.

Let `Xⱼ = (P × M_{c-ε}) ∪_{αⱼ} ⨆ᵢ (P × D^{k i})` be the fiberwise adjunction spaces of the
attaching families `αⱼ i` of the cells of `ψⱼ i`, and `Φⱼ : Xⱼ → P × M_{c+ε}` their comparison
maps. Then there is a fibre homotopy equivalence `X₁ → X₀` over `P` which is the identity on
`P × M_{c-ε}` in both directions, whose composite with `Φ₀` is homotopic to `Φ₁`, and whose two
composites are homotopic to the identities, all by homotopies relative to `P × M_{c-ε}` which stay
over `P`. -/
theorem exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseAttachingFamily [CompactSpace P]
    (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : ι → P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball₀ : ∀ i p, closedBall 0 √ε ⊆ (ψ₀ i p).target)
    (hball₁ : ∀ i p, closedBall 0 √ε ⊆ (ψ₁ i p).target)
    (hf₀ : ∀ i p, ∀ y ∈ (ψ₀ i p).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₀ i p y j ^ 2)
    (hf₁ : ∀ i p, ∀ y ∈ (ψ₁ i p).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₁ i p y j ^ 2)
    (hs₀ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ i q.1).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ i q.1).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hp : ∀ i p, (ψ₀ i p).symm 0 = (ψ₁ i p).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ i p, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (ψ₁ i p).symm ⁻¹' (ψ₀ i p).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ i p, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ ψ₀ i p ((ψ₁ i p).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ Ψ : FiberHomotopyEquiv
        (fiberwiseCellAttachmentProj fun i ↦
          morseAttachingFamily (ψ₁ i) (hk i) hε.le (hball₁ i) (hf₁ i) (hs₁ i)).hom
        (fiberwiseCellAttachmentProj fun i ↦
          morseAttachingFamily (ψ₀ i) (hk i) hε.le (hball₀ i) (hf₀ i) (hs₀ i)).hom,
      (∀ x, Ψ.toFun (fiberwiseCellAttachmentIncl _ x) = fiberwiseCellAttachmentIncl _ x) ∧
      (∀ x, Ψ.invFun (fiberwiseCellAttachmentIncl _ x) = fiberwiseCellAttachmentIncl _ x) ∧
      (∃ G : ((fiberwiseCellComparison
            (fun i ↦ morseAttachingFamily (ψ₀ i) (hk i) hε.le (hball₀ i) (hf₀ i) (hs₀ i))
            (fun i ↦ morseCharacteristicFamily (ψ₀ i) (hk i) hε.le (hball₀ i) (hf₀ i) (hs₀ i))
            fun i ↦ morseCharacteristicFamily_diskBoundaryInclusion (hk i) hε.le (hball₀ i)
              (hf₀ i) (hs₀ i)).hom.comp Ψ.toFun).HomotopyRel
          (fiberwiseCellComparison
            (fun i ↦ morseAttachingFamily (ψ₁ i) (hk i) hε.le (hball₁ i) (hf₁ i) (hs₁ i))
            (fun i ↦ morseCharacteristicFamily (ψ₁ i) (hk i) hε.le (hball₁ i) (hf₁ i) (hs₁ i))
            fun i ↦ morseCharacteristicFamily_diskBoundaryInclusion (hk i) hε.le (hball₁ i)
              (hf₁ i) (hs₁ i)).hom
          (range (fiberwiseCellAttachmentIncl _)),
        ∀ t y, (G (t, y)).1 = fiberwiseCellAttachmentProj _ y) ∧
      (∃ G : (Ψ.invFun.comp Ψ.toFun).HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl _)),
        ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y) ∧
      ∃ G : (Ψ.toFun.comp Ψ.invFun).HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl _)),
        ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y := by
  -- For each `i`, the polar factors `g i p` and a homotopy `K i : χ₁ i ≃ χ₀ i ∘ g i`.
  choose g hg K hK using fun i ↦ exists_homotopy_morseCharacteristicFamily hf (ψ₀ i) (ψ₁ i)
    (hk i) hε (hball₀ i) (hball₁ i) (hf₀ i) (hf₁ i) (hs₀ i) (hs₁ i) (hp i) (hr i) (htr i) (hT i)
    (hD i) hcompact hreg
  exact exists_fiberHomotopyEquiv_fiberwiseCellAttachment_of_homotopy _ _ _ _
    (fun i ↦ morseCharacteristicFamily_diskBoundaryInclusion (hk i) hε.le (hball₀ i) (hf₀ i)
      (hs₀ i))
    (fun i ↦ morseCharacteristicFamily_diskBoundaryInclusion (hk i) hε.le (hball₁ i) (hf₁ i)
      (hs₁ i)) g hg K hK

end Comparison

end TauCeti
