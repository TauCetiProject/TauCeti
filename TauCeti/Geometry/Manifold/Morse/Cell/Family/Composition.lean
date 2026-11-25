/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import TauCeti.Geometry.Manifold.Morse.Cell.Family.Comparison

/-!
# Composing reattachment maps of compact families of Morse charts

Let `f` be a smooth function on a boundaryless manifold `M`, write `M_a = {f ≤ a}`, and let `ψ p i`,
for `p` in a compact parameter space `P` and `i : ι`, be a family of charts in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`. Its cells form the fiberwise adjunction space
`X = (P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i})` over `P`, with the comparison map `Φ : X → P × M_{c+ε}`
given by the characteristic maps of the charts (`TauCeti.morseFamilyAttachingMap`,
`TauCeti.morseFamilyCharacteristicMap`).

This file shows that `Φ` has a left homotopy inverse over `P`
(`TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_id_morseFamily`): a map
`g : P × M_{c+ε} → X` over `P` such that `g ∘ Φ` is homotopic to the identity relative to
`P × M_{c-ε}` through maps over `P`. At a single parameter, Milnor's deformation of `M_{c+ε}` onto
the lower sublevel with the cells attached gives such a map, even a left inverse; over `P` the left
homotopy inverse is what makes Milnor's comparison maps unique and composable up to homotopy. It
comes from an admissible family `φ i` of normal-form charts at the same critical points,
independent of `p`, to which the transitions from `ψ p i` have derivatives jointly continuous in
`p`. Milnor's cell attachment theorem gives a left inverse of the comparison map of
`φ` (`TauCeti.exists_morseCellAttachment_deformation`); since `φ` does not depend on `p`, it is a
left inverse over `P` of the comparison map of the constant family
(`TauCeti.leftInverse_fiberwiseCellAttachmentOfProd_comp_fiberwiseCellComparison`). Milnor's
Lemma 3.6 over `P` compares the cells of `ψ` and of the constant family `φ` by a fibre homotopy
equivalence compatible with the comparison maps
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap`), and the
left homotopy inverse transfers along it
(`TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_id`).

Consequently, for three families `ψ₀`, `ψ₁`, `ψ₂` and fiberwise reattachment maps `E₀₁`, `E₁₂`,
`E₀₂` between their cell attachments, built from any self-maps of the discs and homotopies of
characteristic maps, `E₀₁ ∘ E₁₂` is homotopic to `E₀₂` relative to `P × M_{c-ε}` through maps
over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_morseFamily`).
This is the composition law of Milnor's comparison maps for compact families of charts.

## Main results

* `TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_id_morseFamily`: the comparison map
  of a compact family of Morse charts has a left homotopy inverse over the parameter space.
* `TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_morseFamily`:
  **the composition law of Milnor's comparison maps over a compact parameter space.**

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

open Set Metric Function CategoryTheory Limits
open scoped ContDiff Manifold Topology

universe u

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n : ℕ} {P : Type u} [TopologicalSpace P] {ι : Type u}

/-- The comparison map of the constant family of a single admissible family of normal-form charts
has a left inverse over `P`: Milnor's left inverse at one parameter, applied over each `p`. -/
private theorem exists_leftInverse_fiberwiseCellComparison_const [LocallyCompactSpace P]
    [Finite ι] (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (φ : ι → PartialDiffeomorph Iₘ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hballφ : ∀ i, closedBall 0 √(2 * ε) ⊆ (φ i).target)
    (hballφ' : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
    (hfφ : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    (hsφ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦
      (φ i).toOpenPartialHomeomorph.symm q.2) (univ ×ˢ closedBall 0 √ε))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints Iₘ f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (φ i).source) :
    ∃ L : C(P × {x | f x ≤ c + ε}, fiberwiseCellAttachment (morseFamilyAttachingMap
        (fun (_ : P) i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le (fun _ ↦ hballφ')
        (fun _ ↦ hfφ) hsφ)),
      (∀ y, fiberwiseCellAttachmentProj _ (L y) = y.1) ∧
      LeftInverse L (fiberwiseCellComparison _
        (morseFamilyCharacteristicMap (fun (_ : P) i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le
          (fun _ ↦ hballφ') (fun _ ↦ hfφ) hsφ)
        (morseFamilyCharacteristicMap_diskBoundaryInclusion
          (fun (_ : P) i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le (fun _ ↦ hballφ')
          (fun _ ↦ hfφ) hsφ)) := by
  set φ' : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    fun _ i ↦ (φ i).toOpenPartialHomeomorph
  -- Milnor's cell attachment theorem gives a left inverse of the comparison map of `φ`.
  obtain ⟨g', hg', -⟩ :=
    exists_morseCellAttachment_deformation hfs φ hφ k hk hε hballφ hfφ hcompact hcrit
  -- It is a left inverse over `P` of the comparison map of the constant family. The apply lemmas
  -- below are used as terms: `hballφ'` and `hfφ` speak of `(φ i).target` and `φ i`, which agree
  -- with those of `(φ i).toOpenPartialHomeomorph` only after unfolding `toOpenPartialHomeomorph`,
  -- so `simp` and `rw` cannot instantiate them on these goals.
  let e : C({x | f x ≤ c - ε}, {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) :=
    ⟨fun x ↦ ⟨⟨x, le_trans x.property (by linarith : c - ε ≤ c + ε)⟩, x.property⟩, by fun_prop⟩
  have he (i : ι) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
      morseFamilyAttachingMap φ' k hk hε.le (fun _ ↦ hballφ') (fun _ ↦ hfφ) hsφ i (p, s) =
        e ((Sigma.desc fun i ↦ (φ i).toOpenPartialHomeomorph.morseAttachingMap (hk i) hε.le
          (hballφ' i) (hfφ i)) (Sigma.ι (fun i ↦ TopCat.diskBoundary.{u} (k i)) i s)) := by
    rw [← ConcreteCategory.comp_apply, Sigma.ι_comp_desc]
    exact Subtype.ext (Subtype.ext (coe_morseFamilyAttachingMap_apply ..))
  have hX := isPushout_morseCellAttachment (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hballφ'
    hfφ hε.le
  have hes : Function.Surjective e := fun y ↦ ⟨⟨y.val.val, y.property⟩, rfl⟩
  have hgZ (z : {x | f x ≤ c - ε}) :
      g' (e z) = morseCellAttachmentIncl _ k hk hε.le hballφ' hfφ z :=
    (congrArg g' (Subtype.ext (coe_morseCellComparison_morseCellAttachmentIncl _ k hk hballφ'
      hfφ hε.le z).symm)).trans (hg' _)
  have hgχ (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
      g' (morseFamilyCharacteristicMap φ' k hk hε.le (fun _ ↦ hballφ') (fun _ ↦ hfφ) hsφ i (p, w)) =
        Sigma.desc (morseCellAttachmentCell _ k hk hε.le hballφ' hfφ)
          (Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i w) := by
    have hχ : morseFamilyCharacteristicMap φ' k hk hε.le (fun _ ↦ hballφ') (fun _ ↦ hfφ) hsφ i
        (p, w) = morseCellComparison (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hballφ' hfφ
          (morseCellAttachmentCell (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hballφ'
            hfφ i w) :=
      Subtype.ext ((congrArg Subtype.val (morseFamilyCharacteristicMap_apply φ' k hk hε.le
        (fun _ ↦ hballφ') (fun _ ↦ hfφ) hsφ i (p, w))).trans
        ((OpenPartialHomeomorph.coe_morseCharacteristicMap_apply (hballφ' i) (hfφ i) (hk i) hε.le
          w).trans (coe_morseCellComparison_morseCellAttachmentCell _ k hk hballφ' hfφ hε.le i
            w).symm))
    rw [← ConcreteCategory.comp_apply, Sigma.ι_comp_desc, hχ]
    exact hg' _
  have hL := leftInverse_fiberwiseCellAttachmentOfProd_comp_fiberwiseCellComparison _ hX e he
    (morseFamilyCharacteristicMap φ' k hk hε.le (fun _ ↦ hballφ') (fun _ ↦ hfφ) hsφ)
    (morseFamilyCharacteristicMap_diskBoundaryInclusion φ' k hk hε.le (fun _ ↦ hballφ')
      (fun _ ↦ hfφ) hsφ) hes g' hgZ hgχ
  exact ⟨(fiberwiseCellAttachmentOfProd _ hX e he).comp ((ContinuousMap.id P).prodMap g'),
    fun y ↦ fiberwiseCellAttachmentProj_fiberwiseCellAttachmentOfProd _ hX e he _, hL⟩

/-- **The comparison map of a compact family of Morse charts has a left homotopy inverse over the
parameter space.** Let `f` be smooth, let `P` be compact and locally compact, and let `ψ p i`, for
`p : P` and `i` in a finite type `ι`, be charts in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose targets contain the closed ball of radius `√ε`
and whose inverses are jointly continuous in `p` and the point of that ball. Suppose there is a
reference family of smooth charts `φ i`, independent of `p`, with pairwise disjoint sources, in
which `f` has the same normal form, whose targets contain the closed ball of radius `√(2ε)`, with
the same centres as the `ψ p i`, whose sources cover the critical points of the compact band
`f⁻¹[c - ε, c + ε]`, and such that on a ball of radius `r i` about the origin the transitions
`φ i ∘ (ψ p i)⁻¹` are defined and differentiable with derivatives jointly continuous in `p`.

Then the comparison map `Φ : (P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i}) → P × M_{c+ε}` of the cells of `ψ`
has a left homotopy inverse over `P`: a map `g` over `P` such that `g ∘ Φ` is homotopic to the
identity relative to `P × M_{c-ε}` through maps over `P`. -/
theorem exists_homotopyRel_comp_fiberwiseCellComparison_id_morseFamily [CompactSpace P]
    [LocallyCompactSpace P] [Finite ι] (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
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
    (hp : ∀ p i, (φ i).toOpenPartialHomeomorph.symm 0 = (ψ p i).symm 0) {r : ι → ℝ}
    (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (ψ p i).symm ⁻¹' (φ i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ φ i ((ψ p i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints Iₘ f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (φ i).source) :
    ∃ g : C(P × {x | f x ≤ c + ε},
        fiberwiseCellAttachment (morseFamilyAttachingMap ψ k hk hε.le hball hf hs)),
      (∀ y, fiberwiseCellAttachmentProj _ (g y) = y.1) ∧
      ∃ G : (g.comp (fiberwiseCellComparison (morseFamilyAttachingMap ψ k hk hε.le hball hf hs)
            (morseFamilyCharacteristicMap ψ k hk hε.le hball hf hs)
            (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ k hk hε.le hball hf
              hs)).hom).HomotopyRel
          (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl _)),
        ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y := by
  set φ' : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    fun _ i ↦ (φ i).toOpenPartialHomeomorph
  have hballφ' (i : ι) : closedBall 0 √ε ⊆ (φ i).target :=
    (hballφ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε))
  have hsφ (i : ι) : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (φ' q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε) :=
    continuousOn_symm_const (fun i ↦ (φ i).toOpenPartialHomeomorph) hballφ' i
  -- No critical point lies below the level `c` in the band, since the critical points of the band
  -- lie in the reference charts, where they have value `c`.
  have hreg (x : M) (h₁ : c - ε ≤ f x) (h₂ : f x < c) : mfderiv Iₘ 𝓘(ℝ) f x ≠ 0 := fun h0 ↦ by
    have hx := mem_criticalPoints_iff_mfderiv_eq_zero.2 h0
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcrit ⟨hx, h₁, by linarith⟩)
    linarith [(φ i).eq_of_mem_criticalPoints_of_mem_source (hfφ i) hi hx]
  have hcompact' : IsCompact (f ⁻¹' Icc (c - ε) c) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous)
      (preimage_mono (Icc_subset_Icc le_rfl (by linarith)))
  -- Milnor's Lemma 3.6 over `P` compares the cells of `ψ` with those of the constant family `φ`.
  obtain ⟨Ψ, hΨ, -, ⟨K, hK⟩, ⟨K', hK'⟩, -⟩ :=
    exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap hfs φ' ψ k hk hε
      (fun _ ↦ hballφ') hball (fun _ ↦ hfφ) hf hsφ hs hp hr htr hT hD hcompact' hreg
  -- The constant family `φ` has a left inverse over `P` of its comparison map.
  obtain ⟨L, hLP, hL⟩ := exists_leftInverse_fiberwiseCellComparison_const hfs φ hφ k hk hε hballφ
    hballφ' hfφ hsφ hcompact hcrit
  let Φφ := fiberwiseCellComparison _
    (morseFamilyCharacteristicMap φ' k hk hε.le (fun _ ↦ hballφ') (fun _ ↦ hfφ) hsφ)
    (morseFamilyCharacteristicMap_diskBoundaryInclusion φ' k hk hε.le (fun _ ↦ hballφ')
      (fun _ ↦ hfφ) hsφ)
  let G₀ := (ContinuousMap.HomotopyRel.refl (L.comp Φφ.hom)
    (range (fiberwiseCellAttachmentIncl _))).cast rfl
    (ContinuousMap.ext fun y ↦ hL y : L.comp Φφ.hom = ContinuousMap.id _)
  have hG₀ (t : unitInterval) y :
      fiberwiseCellAttachmentProj _ (G₀ (t, y)) = fiberwiseCellAttachmentProj _ y :=
    (hLP _).trans (fst_fiberwiseCellComparison ..)
  -- The left homotopy inverse transfers along the comparison of `ψ` with `φ`.
  obtain ⟨G, hG⟩ := exists_homotopyRel_comp_fiberwiseCellComparison_id _ _ _ _ _ _ Ψ.toFun
    Ψ.invFun hΨ (fun y ↦ DFunLike.congr_fun Ψ.comp_toFun y)
    (fun y ↦ DFunLike.congr_fun Ψ.comp_invFun y) K hK K' hK' L hLP G₀ hG₀
  exact ⟨Ψ.invFun.comp L, fun y ↦ (DFunLike.congr_fun Ψ.comp_invFun (L y)).trans (hLP y), G, hG⟩

/-- **Milnor's comparison maps compose over a compact parameter space.** Let `ψ₀`, `ψ₁` and `ψ₂` be
three families of charts over a compact, locally compact `P`, with the same indices `k i`, in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose targets contain the closed ball of radius `√ε`
and whose inverses are jointly continuous in `p` and the point of that ball. Suppose that `ψ₀` is
compared with a reference family `φ` as in
`TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_id_morseFamily`. Let
`E₀₁ : X₁ → X₀`, `E₁₂ : X₂ → X₁` and `E₀₂ : X₂ → X₀` be fiberwise reattachment maps between the
cell attachments `Xⱼ = (P × M_{c-ε}) ∪_{αⱼ} ⨆ᵢ (P × D^{k i})` of the three families, built from any
families `h` of self-maps of the discs over `P` and homotopies `K` over `P` between the
characteristic maps keeping the boundary spheres in `M_{c-ε}`. Then `E₀₁ ∘ E₁₂` is homotopic to
`E₀₂` relative to `P × M_{c-ε}` through maps over `P`. Since `0 < ε`, the homotopies `K` force the
maps `h` to preserve the boundary spheres
(`TauCeti.mapsTo_range_diskBoundaryInclusion_of_homotopy_morseFamilyCharacteristicMap`). -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_morseFamily
    [CompactSpace P] [LocallyCompactSpace P] [Finite ι] (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
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
    (hp : ∀ p i, (φ i).toOpenPartialHomeomorph.symm 0 = (ψ₀ p i).symm 0) {r : ι → ℝ}
    (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (ψ₀ p i).symm ⁻¹' (φ i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ φ i ((ψ₀ p i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints Iₘ f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (φ i).source)
    (h₀₁ h₁₂ h₀₂ : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
    (K₀₁ : ∀ i, (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
        (ContinuousMap.fst.prodMk (h₀₁ i))))
    (hK₀₁ : ∀ i t p s, f (K₀₁ i (t, (p, TopCat.diskBoundaryInclusion (k i) s))) ≤ c - ε)
    (K₁₂ : ∀ i, (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁ i).comp
        (ContinuousMap.fst.prodMk (h₁₂ i))))
    (hK₁₂ : ∀ i t p s, f (K₁₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s))) ≤ c - ε)
    (K₀₂ : ∀ i, (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
        (ContinuousMap.fst.prodMk (h₀₂ i))))
    (hK₀₂ : ∀ i t p s, f (K₀₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s))) ≤ c - ε) :
    ∃ G : (fiberwiseCellReattachment (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyAttachingMap ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₂ k hk hε.le hball₂ hf₂ hs₂) h₁₂
          (fun i p ↦ mapsTo_range_diskBoundaryInclusion_of_homotopy_morseFamilyCharacteristicMap
            (hε := hε) (K := K₁₂ i) (p := p) (hK := fun t s ↦ hK₁₂ i t p s)) K₁₂ hK₁₂ ≫
        fiberwiseCellReattachment (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyAttachingMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁) h₀₁
          (fun i p ↦ mapsTo_range_diskBoundaryInclusion_of_homotopy_morseFamilyCharacteristicMap
            (hε := hε) (K := K₀₁ i) (p := p) (hK := fun t s ↦ hK₀₁ i t p s))
          K₀₁ hK₀₁).hom.HomotopyRel
        (fiberwiseCellReattachment (morseFamilyAttachingMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyAttachingMap ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          (morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₂ k hk hε.le hball₂ hf₂ hs₂) h₀₂
          (fun i p ↦ mapsTo_range_diskBoundaryInclusion_of_homotopy_morseFamilyCharacteristicMap
            (hε := hε) (K := K₀₂ i) (p := p) (hK := fun t s ↦ hK₀₂ i t p s))
          K₀₂ hK₀₂).hom
        (range (fiberwiseCellAttachmentIncl _)),
      ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y := by
  obtain ⟨g₀, hg₀P, G₀, hG₀⟩ := exists_homotopyRel_comp_fiberwiseCellComparison_id_morseFamily
    hfs ψ₀ φ hφ k hk hε hball₀ hballφ hf₀ hfφ hs₀ hp hr htr hT hD hcompact hcrit
  exact exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment _ _ _ _ _ _ _
    _ _ h₀₁ h₁₂ h₀₂ _ _ _ K₀₁ hK₀₁ K₁₂ hK₁₂ K₀₂ hK₀₂ g₀ hg₀P G₀ hG₀

end TauCeti
