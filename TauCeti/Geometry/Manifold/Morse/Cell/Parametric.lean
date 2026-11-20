/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.CharacteristicHomotopy
public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCell.ReattachmentInv

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

Such a deformation does enter the composition law for three families. At a single parameter, the
reattachment maps `E₀₁`, `E₁₂` and `E₀₂` between the attachments of three chart families satisfy
`E₀₁ ∘ E₁₂ ≃ E₀₂` relative to `M_{c-ε}` because the comparison map `Φ₀` of the target family has a
left inverse, from Milnor's deformation of `M_{c+ε}` onto the attached cells
(`TauCeti.exists_morseCellAttachment_deformation`). Over `P` the same argument
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment`) needs a map
`g : P × M_{c+ε} → X₀` over `P` with `g ∘ Φ₀` homotopic to the identity relative to
`P × M_{c-ε}` through maps over `P`. When the family `ψ₀` is comparable, as above, with one family
`φ` of charts not depending on `p`, such a `g` exists
(`TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_morseFamily`): for the constant family
`φ`, the product of `P` with Milnor's left inverse is a left inverse over a locally compact `P`, and
the fibre homotopy equivalence comparing `φ` with `ψ₀` carries it to a left inverse of `Φ₀` up to
homotopy. Hence fiberwise reattachment maps compose up to homotopy over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_morseFamily`).

## Main results

* `TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap`: **Milnor's
  Lemma 3.6 over a compact parameter space.**
* `TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_morseFamily`: the comparison map of a
  family of Morse cells has a left inverse up to homotopy over `P`, relative to `P × M_{c-ε}`.
* `TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_morseFamily`: **the composition law
  `E₀₁ ∘ E₁₂ ≃ E₀₂` over a compact parameter space.**

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2, Remark 3.3 and Lemma 3.6.
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

/-! ### A left inverse of the comparison map, and the composition law, over `P` -/

section Composition

open CategoryTheory Filter Function Topology

variable (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
  (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)

omit [T2Space M] in
include hball in
/-- The inverses of a family of charts constant in the parameter are jointly continuous on the
closed ball of radius `√ε`. -/
private theorem continuousOn_symm_const (i : ι) :
    ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (φ i).symm q.2)
      (univ ×ˢ closedBall 0 √ε) :=
  (φ i).continuousOn_symm.comp continuous_snd.continuousOn fun _ hq ↦ hball i hq.2

/-- The attaching maps over `P` of a family of charts constant in the parameter. -/
private abbrev constAttachingMap :=
  morseFamilyAttachingMap (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball) (fun _ ↦ hf)
    (continuousOn_symm_const φ hball)

/-- On the lower sublevel, the map `TauCeti.constFamilyCurry` sends `x` to `p ↦ (p, x)`. -/
private def constFamilyCurryIncl : C({x | f x ≤ c - ε},
    C(P, fiberwiseCellAttachment (constAttachingMap (P := P) φ k hk hε hball hf))) :=
  ((fiberwiseCellAttachmentIncl _).hom.comp
    (ContinuousMap.prodSwap.comp ((sublevelInclusionHomeomorph f (c - ε) (c + ε)
      (by linarith) : C(_, _)).prodMap (ContinuousMap.id P)))).curry

/-- On the cell of `φ i`, the map `TauCeti.constFamilyCurry` sends `w` to `p ↦ (p, w)`. -/
private def constFamilyCurryCell (i : ι) : C(TopCat.disk.{u} (k i),
    C(P, fiberwiseCellAttachment (constAttachingMap (P := P) φ k hk hε hball hf))) :=
  ((fiberwiseCellAttachmentCell _ i).hom.comp ContinuousMap.prodSwap).curry

omit [T2Space M] in
private theorem constFamilyCurry_compat (i : ι) :
    (φ i).morseAttachingMap (hk i) hε (hball i) (hf i) ≫
        TopCat.ofHom (constFamilyCurryIncl (P := P) φ k hk hε hball hf) =
      TopCat.diskBoundaryInclusion (k i) ≫
        TopCat.ofHom (constFamilyCurryCell (P := P) φ k hk hε hball hf i) := by
  ext s p
  have ha : constAttachingMap (P := P) φ k hk hε hball hf i (p, s) =
      sublevelInclusionHomeomorph f (c - ε) (c + ε) (by linarith)
        ((φ i).morseAttachingMap (hk i) hε (hball i) (hf i) s) :=
    Subtype.ext (Subtype.ext ((coe_morseFamilyAttachingMap_apply _ _ _ _ _ _ _ i (p, s)).trans
      (coe_coe_sublevelInclusionHomeomorph_apply f _ _).symm))
  have h := fiberwiseCellAttachmentCell_diskBoundaryInclusion
    (constAttachingMap (P := P) φ k hk hε hball hf) i p s
  rw [ha] at h
  exact h.symm

/-- The map from the cell attachment of `φ` to the maps from `P` to the fiberwise cell attachment
over `P` of the constant family `φ`, sending a point `x` to `p ↦ (p, x)`. -/
private def constFamilyCurry :
    morseCellAttachment φ k hk hε hball hf ⟶
      TopCat.of C(P, fiberwiseCellAttachment (constAttachingMap (P := P) φ k hk hε hball hf)) :=
  morseCellAttachmentDesc φ k hk hε hball hf
    (TopCat.ofHom (constFamilyCurryIncl φ k hk hε hball hf))
    (fun i ↦ TopCat.ofHom (constFamilyCurryCell φ k hk hε hball hf i))
    (constFamilyCurry_compat φ k hk hε hball hf)

omit [T2Space M] in
private theorem constFamilyCurry_morseCellAttachmentIncl (x : {x | f x ≤ c - ε}) (p : P) :
    constFamilyCurry φ k hk hε hball hf (morseCellAttachmentIncl φ k hk hε hball hf x) p =
      fiberwiseCellAttachmentIncl _ (p, sublevelInclusionHomeomorph f (c - ε) (c + ε)
        (by linarith) x) := by
  have h := ConcreteCategory.congr_hom (morseCellAttachmentIncl_desc φ k hk hball hf hε
    (TopCat.ofHom (constFamilyCurryIncl (P := P) φ k hk hε hball hf))
    (fun i ↦ TopCat.ofHom (constFamilyCurryCell φ k hk hε hball hf i))
    (constFamilyCurry_compat φ k hk hε hball hf)) x
  exact congrArg (fun g : C(P, fiberwiseCellAttachment (constAttachingMap (P := P) φ k hk hε hball
    hf)) ↦ g p) h

omit [T2Space M] in
private theorem constFamilyCurry_morseCellAttachmentCell (i : ι) (w : TopCat.disk.{u} (k i))
    (p : P) :
    constFamilyCurry φ k hk hε hball hf (morseCellAttachmentCell φ k hk hε hball hf i w) p =
      fiberwiseCellAttachmentCell _ i (p, w) := by
  have h := ConcreteCategory.congr_hom (morseCellAttachmentCell_desc φ k hk hball hf hε
    (TopCat.ofHom (constFamilyCurryIncl (P := P) φ k hk hε hball hf))
    (fun i ↦ TopCat.ofHom (constFamilyCurryCell φ k hk hε hball hf i))
    (constFamilyCurry_compat φ k hk hε hball hf) i) w
  exact congrArg (fun g : C(P, fiberwiseCellAttachment (constAttachingMap (P := P) φ k hk hε hball
    hf)) ↦ g p) h

omit [T2Space M] in
private theorem fiberwiseCellAttachmentProj_constFamilyCurry
    (y : morseCellAttachment φ k hk hε hball hf) (p : P) :
    fiberwiseCellAttachmentProj _ (constFamilyCurry φ k hk hε hball hf y p) = p := by
  obtain ⟨x, rfl⟩ | hy :=
    (range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ k hk hball hf
      hε).symm ▸ mem_univ y
  · rw [constFamilyCurry_morseCellAttachmentIncl,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]
  · obtain ⟨i, w, rfl⟩ := mem_iUnion.1 hy
    rw [constFamilyCurry_morseCellAttachmentCell,
      fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]

variable [Finite ι] [LocallyCompactSpace P]

/-- **Milnor's cell attachment for a constant family of charts.** For a family of normal-form
charts which does not depend on the parameter, and which satisfies the hypotheses of Milnor's cell
attachment theorem `TauCeti.exists_morseCellAttachment_deformation`, the comparison map of the
fiberwise cell attachment over a locally compact `P` has a left inverse over `P`: it is the
product of `P` with the left inverse at a single parameter. -/
private theorem exists_leftInverse_fiberwiseCellComparison_const (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (φ : ι → PartialDiffeomorph Iₘ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball : ∀ i, closedBall 0 √(2 * ε) ⊆ (φ i).target)
    (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints Iₘ f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (φ i).source) :
    ∃ g : C(P × {x | f x ≤ c + ε}, fiberwiseCellAttachment (constAttachingMap (P := P)
        (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le
        (fun i ↦ (hball i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        hf)),
      Function.LeftInverse g (fiberwiseCellComparison _
        (morseFamilyCharacteristicMap (fun _ : P ↦ fun i ↦ (φ i).toOpenPartialHomeomorph) k hk
          hε.le (fun _ i ↦ (hball i).trans'
            (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε))) (fun _ ↦ hf)
          (continuousOn_symm_const _ fun i ↦ (hball i).trans'
            (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε))))
        (morseFamilyCharacteristicMap_diskBoundaryInclusion _ _ _ _ _ _ _)) ∧
      ∀ y, fiberwiseCellAttachmentProj _ (g y) = y.1 := by
  have hball' (i : ι) : closedBall 0 √ε ⊆ (φ i).target :=
    (hball i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε))
  obtain ⟨g, hg, -⟩ := exists_morseCellAttachment_deformation hfs φ hφ k hk hε hball hf hcompact
    hcrit
  let j := constFamilyCurry (P := P) (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hball' hf
  let g' : C(P × {x | f x ≤ c + ε}, _) := ((j.hom.comp g).uncurry).comp ContinuousMap.prodSwap
  have hg' (q : P × {x | f x ≤ c + ε}) : g' q = j (g q.2) q.1 := rfl
  refine ⟨g', fun y ↦ ?_, fun y ↦ ?_⟩
  · refine fiberwiseCellAttachment_induction _ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · -- A point of `P × M_{c-ε}` is the image of the lower sublevel of the cell attachment.
      have hx : (x.2 : {x | f x ≤ c + ε}) =
          morseCellComparison (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hball' hf
            (morseCellAttachmentIncl (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hball' hf
              ⟨x.2.1, x.2.2⟩) :=
        Subtype.ext (coe_morseCellComparison_morseCellAttachmentIncl
          (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hball' hf hε.le ⟨x.2.1, x.2.2⟩).symm
      rw [fiberwiseCellComparison_fiberwiseCellAttachmentIncl, hg', hx, hg]
      refine (constFamilyCurry_morseCellAttachmentIncl (P := P)
        (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hball' hf _ _).trans
          (congrArg _ (Prod.ext rfl (Subtype.ext (Subtype.ext ?_))))
      exact coe_coe_sublevelInclusionHomeomorph_apply f _ _
    · -- A point of the cell over `p` is the image of the cell of the attachment.
      have hx : morseFamilyCharacteristicMap (fun _ : P ↦ fun i ↦ (φ i).toOpenPartialHomeomorph) k
          hk hε.le (fun _ ↦ hball') (fun _ ↦ hf)
          (continuousOn_symm_const (fun i ↦ (φ i).toOpenPartialHomeomorph) hball') i x =
          morseCellComparison (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hball' hf
            (morseCellAttachmentCell (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hball' hf
              i x.2) :=
        (morseFamilyCharacteristicMap_apply _ _ _ _ _ _ _ i x).trans
          (ConcreteCategory.congr_hom (morseCellAttachmentCell_comp_morseCellComparison
            (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hball' hf hε.le i) x.2).symm
      rw [fiberwiseCellComparison_fiberwiseCellAttachmentCell, hg', hx, hg]
      exact constFamilyCurry_morseCellAttachmentCell (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk
        hε.le hball' hf i _ _
  · exact fiberwiseCellAttachmentProj_constFamilyCurry (fun i ↦ (φ i).toOpenPartialHomeomorph) k
      hk hε.le hball' hf _ _

/-- **The comparison map of a family of Morse cells has a left inverse up to homotopy over `P`.**
Let `f` be smooth, `P` compact and locally compact, and `ψ p i`, for `p : P` and `i : ι`, charts
in which `f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose targets contain the closed ball of
radius `√ε`, with inverses jointly continuous in `p` and the point of that ball. Suppose that the
family is comparable with one family `φ i` of charts which does not depend on `p`: the `φ i` are
smooth normal-form charts with the same centres and pairwise disjoint sources, whose targets
contain the closed ball of radius `√(2ε)`, the band `f⁻¹[c - ε, c + ε]` is compact with its
critical points in the sources of the `φ i`, and on a ball of radius `r i` the transitions
`φ i ∘ (ψ p i)⁻¹` are defined and differentiable, with derivatives jointly continuous in `p` and the
point.

Let `X = (P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i})` be the fiberwise adjunction space of the cells of `ψ`
and `Φ : X → P × M_{c+ε}` its comparison map. Then there is a map `g : P × M_{c+ε} → X` over `P`
such that `g ∘ Φ` is homotopic to the identity of `X` relative to `P × M_{c-ε}`, through maps over
`P`. This is the input that the composition law
`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment` and the
independence of the homotopies
`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_fiberwiseCellReattachment` of fiberwise
reattachment maps require.

The map `g` is the product of `P` with Milnor's left inverse
(`TauCeti.exists_morseCellAttachment_deformation`) for the charts `φ`, followed by the inverse of
the fibre homotopy equivalence comparing the cells of `φ` and `ψ` over `P`
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap`). -/
theorem exists_homotopyRel_comp_fiberwiseCellComparison_morseFamily [CompactSpace P]
    (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (φ : ι → PartialDiffeomorph Iₘ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball : ∀ p i, closedBall 0 √ε ⊆ (ψ p i).target)
    (hballφ : ∀ i, closedBall 0 √(2 * ε) ⊆ (φ i).target)
    (hf : ∀ p i, ∀ y ∈ (ψ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ p i y j ^ 2)
    (hfφ : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    (hs : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hp : ∀ p i, (φ i).symm 0 = (ψ p i).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (ψ p i).symm ⁻¹' (φ i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ φ i ((ψ p i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints Iₘ f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (φ i).source) :
    ∃ (g : C(P × {x | f x ≤ c + ε},
        fiberwiseCellAttachment (morseFamilyAttachingMap ψ k hk hε.le hball hf hs)))
      (G : (g.comp (fiberwiseCellComparison _
          (morseFamilyCharacteristicMap ψ k hk hε.le hball hf hs)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ k hk hε.le hball hf
            hs)).hom).HomotopyRel (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl _))),
      (∀ y, fiberwiseCellAttachmentProj _ (g y) = y.1) ∧
      ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y := by
  have hball' (i : ι) : closedBall 0 √ε ⊆ (φ i).target :=
    (hballφ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε))
  -- The critical points in the band are centres of the charts `φ i`, at the level `c`.
  have hreg (x : M) (hx₁ : c - ε ≤ f x) (hx₂ : f x < c) : mfderiv Iₘ 𝓘(ℝ) f x ≠ 0 := fun h0 ↦ by
    have hx := mem_criticalPoints_iff_mfderiv_eq_zero.2 h0
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcrit ⟨hx, hx₁, by linarith⟩)
    exact hx₂.ne (eq_of_mem_criticalPoints_of_mem_source (hfφ i) hi hx)
  -- The left inverse `g₀` over `P` for the constant family `φ`.
  obtain ⟨g₀, hg₀, hg₀P⟩ := exists_leftInverse_fiberwiseCellComparison_const (P := P) hfs φ hφ k hk
    hε hballφ hfφ hcompact hcrit
  -- The fibre homotopy equivalence `Ψ` from the cells of `ψ` to those of `φ`.
  obtain ⟨Ψ, -, -, ⟨G₁, hG₁⟩, ⟨G₂, hG₂⟩, -⟩ :=
    exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap hfs
      (fun _ i ↦ (φ i).toOpenPartialHomeomorph) ψ k hk hε (fun _ ↦ hball') hball (fun _ ↦ hfφ) hf
      (continuousOn_symm_const _ hball') hs hp hr htr hT hD
      (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous)
        (preimage_mono (Icc_subset_Icc_right (by linarith)))) hreg
  have hgP (y : P × {x | f x ≤ c + ε}) :
      fiberwiseCellAttachmentProj _ (Ψ.invFun (g₀ y)) = y.1 :=
    (DFunLike.congr_fun Ψ.comp_invFun (g₀ y)).trans (hg₀P y)
  -- `g ∘ Φ ≃ Ψ⁻¹ ∘ g₀ ∘ Φ_φ ∘ Ψ = Ψ⁻¹ ∘ Ψ ≃ id`.
  have heq : (Ψ.invFun.comp g₀).comp ((fiberwiseCellComparison _ _
      (morseFamilyCharacteristicMap_diskBoundaryInclusion (fun _ i ↦ (φ i).toOpenPartialHomeomorph)
        k hk hε.le (fun _ ↦ hball') (fun _ ↦ hfφ) (continuousOn_symm_const _ hball'))).hom.comp
          Ψ.toFun) = Ψ.invFun.comp Ψ.toFun :=
    ContinuousMap.ext fun y ↦ congrArg Ψ.invFun (hg₀ _)
  refine ⟨Ψ.invFun.comp g₀, ((G₁.symm.compContinuousMap (Ψ.invFun.comp g₀)).cast rfl heq).trans G₂,
    hgP, fun t y ↦ ?_⟩
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · rw [ContinuousMap.HomotopyRel.cast_apply, ContinuousMap.HomotopyRel.compContinuousMap_apply,
      ContinuousMap.comp_apply, hgP, ContinuousMap.HomotopyRel.symm_apply, hG₁]
  · exact hG₂ _ y

/-- **Milnor's comparisons of Morse cells compose over a compact parameter space.** Let
`ψ₀ p i`, `ψ₁ p i` and `ψ₂ p i`, for `p` in a compact, locally compact `P`, be three families of
normal-form charts of a smooth `f` as in
`TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_morseFamily`, the family `ψ₀` being
comparable there with a family `φ` of charts which does not depend on `p`. Let
`Xⱼ = (P × M_{c-ε}) ∪_{αⱼ} ⨆ᵢ (P × D^{k i})` be their fiberwise adjunction spaces, and let
`E₀₁ : X₁ → X₀`, `E₁₂ : X₂ → X₁` and `E₀₂ : X₂ → X₀` be fiberwise reattachment maps
(`TauCeti.fiberwiseCellReattachment`), built from any self-maps `h i` over `P` of the disc pairs
and any homotopies over `P` between the characteristic maps of the cells, from `χ₁ i` to
`χ₀ i ∘ (p, h₀₁ i)` and so on, keeping the boundary spheres in `M_{c-ε}`. Then `E₀₁ ∘ E₁₂` is
homotopic to `E₀₂` relative to `P × M_{c-ε}`, through maps over `P`. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_morseFamily [CompactSpace P]
    (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ ψ₂ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (φ : ι → PartialDiffeomorph Iₘ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball₀ : ∀ p i, closedBall 0 √ε ⊆ (ψ₀ p i).target)
    (hball₁ : ∀ p i, closedBall 0 √ε ⊆ (ψ₁ p i).target)
    (hball₂ : ∀ p i, closedBall 0 √ε ⊆ (ψ₂ p i).target)
    (hballφ : ∀ i, closedBall 0 √(2 * ε) ⊆ (φ i).target)
    (hf₀ : ∀ p i, ∀ y ∈ (ψ₀ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₀ p i y j ^ 2)
    (hf₁ : ∀ p i, ∀ y ∈ (ψ₁ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₁ p i y j ^ 2)
    (hf₂ : ∀ p i, ∀ y ∈ (ψ₂ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₂ p i y j ^ 2)
    (hfφ : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    (hs₀ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₂ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₂ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (h₀₁ h₁₂ h₀₂ : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
    (hh₀₁ : ∀ i p, MapsTo (fun w ↦ h₀₁ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (hh₁₂ : ∀ i p, MapsTo (fun w ↦ h₁₂ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (hh₀₂ : ∀ i p, MapsTo (fun w ↦ h₀₂ i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (K₀₁ : ∀ i, (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
        (ContinuousMap.fst.prodMk (h₀₁ i))))
    (hK₀₁ : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
      K₀₁ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
        {y : {x | f x ≤ c + ε} | f y ≤ c - ε})
    (K₁₂ : ∀ i, (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁ i).comp
        (ContinuousMap.fst.prodMk (h₁₂ i))))
    (hK₁₂ : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
      K₁₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
        {y : {x | f x ≤ c + ε} | f y ≤ c - ε})
    (K₀₂ : ∀ i, (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
        (ContinuousMap.fst.prodMk (h₀₂ i))))
    (hK₀₂ : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
      K₀₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
        {y : {x | f x ≤ c + ε} | f y ≤ c - ε})
    (hp : ∀ p i, (φ i).symm 0 = (ψ₀ p i).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (ψ₀ p i).symm ⁻¹' (φ i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ φ i ((ψ₀ p i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints Iₘ f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (φ i).source) :
    ∃ G : (fiberwiseCellReattachment (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyAttachingMap ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          h₁₂ hh₁₂ K₁₂ hK₁₂ ≫
        fiberwiseCellReattachment (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          h₀₁ hh₀₁ K₀₁ hK₀₁).hom.HomotopyRel
        (fiberwiseCellReattachment (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyAttachingMap ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          h₀₂ hh₀₂ K₀₂ hK₀₂).hom
        (range (fiberwiseCellAttachmentIncl _)),
      ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y := by
  obtain ⟨g, G, hgP, hG⟩ := exists_homotopyRel_comp_fiberwiseCellComparison_morseFamily hfs ψ₀ φ
    hφ k hk hε hball₀ hballφ hf₀ hfφ hs₀ hp hr htr hT hD hcompact hcrit
  exact exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment (K₀₁ := K₀₁)
    (hK₀₁ := hK₀₁) (K₁₂ := K₁₂) (hK₁₂ := hK₁₂) (K₀₂ := K₀₂) (hK₀₂ := hK₀₂) (g₀ := g) (G₀ := G)
    (hG₀ := hG) (hg₀P := hgP) ..

end Composition

end TauCeti
