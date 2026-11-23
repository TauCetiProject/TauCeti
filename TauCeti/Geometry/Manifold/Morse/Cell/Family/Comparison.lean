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

The comparison map `Φ : (P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i}) → P × M_{c+ε}` of a family `ψ` is itself
a fibre homotopy equivalence over `P`, relative to `P × M_{c-ε}`, when `P` is moreover locally
compact and `ψ` is continuously differentiable over `P` in the coordinates of a fixed family `φ` of
normal-form charts around the critical points of the compact band `f⁻¹[c - ε, c + ε]`
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellComparison_morseFamilyAttachingMap`). No
deformation of `M_{c+ε}` depending on `p` is constructed: Milnor's deformation retraction of
`M_{c+ε}` onto the cells of `φ` (`TauCeti.exists_morseCellAttachment_deformation`) is applied over
every `p`, and the comparison over `P` above carries the cells of `φ` to those of `ψ`.

Consequently, for three families `ψ₀`, `ψ₁`, `ψ₂`, any fiberwise reattachment maps `E₀₁`, `E₁₂`,
`E₀₂` between their cell attachments satisfy `E₀₁ ∘ E₁₂ ≃ E₀₂` relative to `P × M_{c-ε}` over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_morseFamilyAttachingMap`), as for a
single parameter (`TauCeti.homotopicRel_morseCellReattachment_comp_morseCellReattachment`).

The same conclusions hold when the transitions are differentiated in the other direction, that is,
when `φ i ∘ (ψ p i)⁻¹` rather than `ψ p i ∘ (φ i)⁻¹` has derivatives near the origin jointly
continuous in `p`: the fibre homotopy equivalence comparing the cells of `φ` with those of `ψ`
then runs from the cells of `ψ`, and carries the left inverse over `P` of the comparison map of the
constant family `φ` to a left inverse of `Φ` up to homotopy relative to `P × M_{c-ε}` over `P`
(`TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_morseFamily`). Hence fiberwise
reattachment maps compose up to homotopy over `P` under these hypotheses too
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_morseFamily`).

## Main results

* `TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap`: **Milnor's
  Lemma 3.6 over a compact parameter space.**
* `TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellComparison_morseFamilyAttachingMap`: **Milnor's
  cell attachment theorem over a compact parameter space**, in homotopy form.
* `TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_morseFamilyAttachingMap`: Milnor's
  reattachment maps compose up to homotopy over a compact parameter space.
* `TauCeti.exists_homotopyRel_comp_fiberwiseCellComparison_morseFamily`,
  `TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_morseFamily`: the left inverse up to
  homotopy over `P` of the comparison map and the composition law, with the transitions
  differentiated in the other direction.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 (Theorem 3.2, Remark 3.3, Theorem 3.5 and Lemma 3.6).
-/

public section

noncomputable section

open Function Set Metric CategoryTheory
open scoped ContDiff Manifold Topology

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


section Reference

omit [T2Space M]

/-! ### Cells of a fixed chart family, attached over `P`

The cells of a single chart family `φ` attached over every `p` give the fiberwise adjunction space
of the constant family `fun _ ↦ φ`. A point `z` of the cell attachment of `φ` gives the map
`p ↦ (p, z)` into that space, and so a left inverse of the comparison map of `φ` gives a left
inverse over `P` of the comparison map of the constant family. -/

variable (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
  (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)

include hball in
/-- The inverses of the charts of a fixed family are continuous on the closed ball of radius `√ε`,
uniformly in a parameter on which they do not depend. -/
private theorem continuousOn_symm_const (i : ι) :
    ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (φ i).symm q.2)
      (univ ×ˢ closedBall 0 √ε) :=
  ((φ i).continuousOn_symm.mono (hball i)).comp continuous_snd.continuousOn fun _ hq ↦ hq.2

/-- On the boundary spheres, the attaching maps of the constant family are those of `φ`. -/
private theorem sublevelInclusionHomeomorph_morseAttachingMap (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    sublevelInclusionHomeomorph f (c - ε) (c + ε) (by linarith)
        ((φ i).morseAttachingMap (hk i) hε (hball i) (hf i) s) =
      morseFamilyAttachingMap (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball) (fun _ ↦ hf)
        (continuousOn_symm_const φ hball) i (p, s) :=
  Subtype.ext (Subtype.ext ((coe_coe_sublevelInclusionHomeomorph_apply f _ _).trans
    (coe_morseFamilyAttachingMap_apply (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball) (fun _ ↦ hf)
      (continuousOn_symm_const φ hball) i (p, s)).symm))

/-- The attaching maps of the cells of `φ`, as a constant family over `P`. -/
private abbrev constAttachingMap :=
  morseFamilyAttachingMap (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball) (fun _ ↦ hf)
    (continuousOn_symm_const φ hball)

/-- The map sending a point `x` of the lower sublevel to `p ↦ (p, x)`. -/
private def constInclFamily : TopCat.of {x : M | f x ≤ c - ε} ⟶
    TopCat.of C(P, fiberwiseCellAttachment (constAttachingMap (P := P) φ k hk hε hball hf)) :=
  TopCat.ofHom (ContinuousMap.curry ((fiberwiseCellAttachmentIncl _).hom.comp
    ((ContinuousMap.snd : C({x : M | f x ≤ c - ε} × P, P)).prodMk
      ((sublevelInclusionHomeomorph f (c - ε) (c + ε) (by linarith) : C(_, _)).comp
        ContinuousMap.fst))))

/-- The map sending a point `w` of the `i`-th disc to `p ↦ (p, w)`. -/
private def constCellFamily (i : ι) : TopCat.disk.{u} (k i) ⟶
    TopCat.of C(P, fiberwiseCellAttachment (constAttachingMap (P := P) φ k hk hε hball hf)) :=
  TopCat.ofHom (ContinuousMap.curry ((fiberwiseCellAttachmentCell _ i).hom.comp
    (ContinuousMap.prodSwap : C(TopCat.disk.{u} (k i) × P, P × TopCat.disk.{u} (k i)))))

private theorem morseAttachingMap_comp_constInclFamily (i : ι) :
    (φ i).morseAttachingMap (hk i) hε (hball i) (hf i) ≫
        constInclFamily (P := P) φ k hk hε hball hf =
      TopCat.diskBoundaryInclusion (k i) ≫ constCellFamily φ k hk hε hball hf i := by
  ext s p
  -- Evaluate both composites of curried maps at `(s, p)`. This needs `change`: the morphism
  -- `constCellFamily` starts at `TopCat.disk (k i)`, a definition rather than a `TopCat.of`, so
  -- `TopCat.hom_ofHom` and `ConcreteCategory.hom_ofHom` do not match it syntactically.
  change fiberwiseCellAttachmentIncl _
      (p, sublevelInclusionHomeomorph f (c - ε) (c + ε) (by linarith)
        ((φ i).morseAttachingMap (hk i) hε (hball i) (hf i) s)) =
    fiberwiseCellAttachmentCell _ i (p, TopCat.diskBoundaryInclusion (k i) s)
  rw [sublevelInclusionHomeomorph_morseAttachingMap φ k hk hε hball hf i p,
    fiberwiseCellAttachmentCell_diskBoundaryInclusion]

/-- The map from the cell attachment of `φ` to the maps from `P` to the fiberwise cell attachment
of the constant family `fun _ ↦ φ`, sending `z` to `p ↦ (p, z)`. -/
private def morseCellAttachmentToConst : morseCellAttachment φ k hk hε hball hf ⟶
    TopCat.of C(P, fiberwiseCellAttachment (constAttachingMap (P := P) φ k hk hε hball hf)) :=
  morseCellAttachmentDesc φ k hk hε hball hf (constInclFamily φ k hk hε hball hf)
    (constCellFamily φ k hk hε hball hf) (morseAttachingMap_comp_constInclFamily φ k hk hε hball hf)

private theorem morseCellAttachmentToConst_morseCellAttachmentIncl (x : {x : M | f x ≤ c - ε})
    (p : P) :
    morseCellAttachmentToConst φ k hk hε hball hf (morseCellAttachmentIncl φ k hk hε hball hf x) p =
      fiberwiseCellAttachmentIncl _
        (p, sublevelInclusionHomeomorph f (c - ε) (c + ε) (by linarith) x) := by
  have h := ConcreteCategory.congr_hom (morseCellAttachmentIncl_desc φ k hk hball hf hε
    (constInclFamily (P := P) φ k hk hε hball hf) (constCellFamily φ k hk hε hball hf)
    (morseAttachingMap_comp_constInclFamily φ k hk hε hball hf)) x
  exact ContinuousMap.congr_fun h p

private theorem morseCellAttachmentToConst_morseCellAttachmentCell (i : ι)
    (w : TopCat.disk.{u} (k i)) (p : P) :
    morseCellAttachmentToConst φ k hk hε hball hf (morseCellAttachmentCell φ k hk hε hball hf i w)
        p =
      fiberwiseCellAttachmentCell _ i (p, w) := by
  have h := ConcreteCategory.congr_hom (morseCellAttachmentCell_desc φ k hk hball hf hε
    (constInclFamily (P := P) φ k hk hε hball hf) (constCellFamily φ k hk hε hball hf)
    (morseAttachingMap_comp_constInclFamily φ k hk hε hball hf) i) w
  exact ContinuousMap.congr_fun h p

/-- Over `p`, the comparison map of the constant family reads `p ↦ (p, z)` as `(p, Φ z)`, for the
comparison map `Φ` of `φ`. -/
private theorem fiberwiseCellComparison_morseCellAttachmentToConst
    (z : morseCellAttachment φ k hk hε hball hf) (p : P) :
    fiberwiseCellComparison _ (morseFamilyCharacteristicMap (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball)
        (fun _ ↦ hf) (continuousOn_symm_const φ hball))
        (morseFamilyCharacteristicMap_diskBoundaryInclusion _ _ _ _ _ _ _)
        (morseCellAttachmentToConst φ k hk hε hball hf z p) =
      (p, morseCellComparison φ k hk hε hball hf z) := by
  obtain ⟨x, rfl⟩ | hz :=
    (range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ k hk hball hf
      hε).symm ▸ mem_univ z
  · rw [morseCellAttachmentToConst_morseCellAttachmentIncl,
      fiberwiseCellComparison_fiberwiseCellAttachmentIncl]
    exact Prod.ext rfl (Subtype.ext ((coe_coe_sublevelInclusionHomeomorph_apply f _ x).trans
      (coe_morseCellComparison_morseCellAttachmentIncl φ k hk hball hf hε x).symm))
  · obtain ⟨i, w, rfl⟩ := mem_iUnion.1 hz
    rw [morseCellAttachmentToConst_morseCellAttachmentCell,
      fiberwiseCellComparison_fiberwiseCellAttachmentCell]
    refine Prod.ext rfl ?_
    rw [morseFamilyCharacteristicMap_apply]
    exact (ConcreteCategory.congr_hom
      (morseCellAttachmentCell_comp_morseCellComparison φ k hk hball hf hε i) w).symm

/-- The map `(p, y) ↦ (p, g y)` from `P × M_{c+ε}` to the fiberwise cell attachment of the
constant family `fun _ ↦ φ`, for a map `g` from `M_{c+ε}` to the cell attachment of `φ`. -/
private def constLeftInverse [LocallyCompactSpace P]
    (g : C({x : M | f x ≤ c + ε}, morseCellAttachment φ k hk hε hball hf)) :
    C(P × {x : M | f x ≤ c + ε}, fiberwiseCellAttachment
      (morseFamilyAttachingMap (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball) (fun _ ↦ hf)
        (continuousOn_symm_const φ hball))) :=
  (ContinuousMap.uncurry ((morseCellAttachmentToConst φ k hk hε hball hf).hom.comp g)).comp
    ContinuousMap.prodSwap

private theorem constLeftInverse_apply [LocallyCompactSpace P]
    (g : C({x : M | f x ≤ c + ε}, morseCellAttachment φ k hk hε hball hf))
    (y : P × {x : M | f x ≤ c + ε}) :
    constLeftInverse φ k hk hε hball hf g y = morseCellAttachmentToConst φ k hk hε hball hf (g y.2)
      y.1 :=
  rfl

/-- A left inverse of the comparison map of `φ` gives a left inverse of the comparison map of the
constant family `fun _ ↦ φ`. -/
private theorem constLeftInverse_fiberwiseCellComparison [LocallyCompactSpace P]
    {g : C({x : M | f x ≤ c + ε}, morseCellAttachment φ k hk hε hball hf)}
    (hg : LeftInverse g (morseCellComparison φ k hk hε hball hf))
    (z : fiberwiseCellAttachment (morseFamilyAttachingMap (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball)
      (fun _ ↦ hf) (continuousOn_symm_const φ hball))) :
    constLeftInverse φ k hk hε hball hf g (fiberwiseCellComparison _
        (morseFamilyCharacteristicMap (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball) (fun _ ↦ hf)
          (continuousOn_symm_const φ hball))
        (morseFamilyCharacteristicMap_diskBoundaryInclusion _ _ _ _ _ _ _) z) = z := by
  refine fiberwiseCellAttachment_induction _ (fun x ↦ ?_) (fun i x ↦ ?_) z
  · rw [fiberwiseCellComparison_fiberwiseCellAttachmentIncl, constLeftInverse_apply]
    have hx : (x.2 : {x : M | f x ≤ c + ε}) =
        morseCellComparison φ k hk hε hball hf (morseCellAttachmentIncl φ k hk hε hball hf
          ⟨x.2.val.val, x.2.property⟩) :=
      Subtype.ext (coe_morseCellComparison_morseCellAttachmentIncl φ k hk hball hf hε
        ⟨x.2.val.val, x.2.property⟩).symm
    rw [hx, hg, morseCellAttachmentToConst_morseCellAttachmentIncl]
    exact congrArg _ (Prod.ext rfl (Subtype.ext (Subtype.ext
      (coe_coe_sublevelInclusionHomeomorph_apply f _ _))))
  · rw [fiberwiseCellComparison_fiberwiseCellAttachmentCell, constLeftInverse_apply]
    have hx : morseFamilyCharacteristicMap (fun _ : P ↦ φ) k hk hε (fun _ ↦ hball) (fun _ ↦ hf)
        (continuousOn_symm_const φ hball) i x =
          morseCellComparison φ k hk hε hball hf
            (morseCellAttachmentCell φ k hk hε hball hf i x.2) :=
      (morseFamilyCharacteristicMap_apply ..).trans (ConcreteCategory.congr_hom
        (morseCellAttachmentCell_comp_morseCellComparison φ k hk hball hf hε i) x.2).symm
    rw [hx, hg, morseCellAttachmentToConst_morseCellAttachmentCell]

/-- The map `(p, y) ↦ (p, g y)` lies over `P`. -/
private theorem fiberwiseCellAttachmentProj_constLeftInverse [LocallyCompactSpace P]
    (g : C({x : M | f x ≤ c + ε}, morseCellAttachment φ k hk hε hball hf))
    (y : P × {x : M | f x ≤ c + ε}) :
    fiberwiseCellAttachmentProj _ (constLeftInverse φ k hk hε hball hf g y) = y.1 := by
  rw [← fst_fiberwiseCellComparison _ (morseFamilyCharacteristicMap (fun _ : P ↦ φ) k hk hε
    (fun _ ↦ hball) (fun _ ↦ hf) (continuousOn_symm_const φ hball))
    (morseFamilyCharacteristicMap_diskBoundaryInclusion _ _ _ _ _ _ _), constLeftInverse_apply,
    fiberwiseCellComparison_morseCellAttachmentToConst]

/-- On `P × M_{c-ε}`, the map `(p, y) ↦ (p, g y)` is the inclusion, when `g` is a left inverse of
the comparison map of `φ`. -/
private theorem constLeftInverse_of_le [LocallyCompactSpace P]
    {g : C({x : M | f x ≤ c + ε}, morseCellAttachment φ k hk hε hball hf)}
    (hg : LeftInverse g (morseCellComparison φ k hk hε hball hf)) (p : P)
    (y : {y : {x : M | f x ≤ c + ε} | f y ≤ c - ε}) :
    constLeftInverse φ k hk hε hball hf g (p, y) = fiberwiseCellAttachmentIncl _ (p, y) := by
  have h := constLeftInverse_fiberwiseCellComparison φ k hk hε hball hf hg
    (fiberwiseCellAttachmentIncl _ (p, y))
  rwa [fiberwiseCellComparison_fiberwiseCellAttachmentIncl] at h

/-- If `Φ ∘ g` is homotopic to the identity relative to the image of the comparison map `Φ` of `φ`,
then `(p, y) ↦ Φφ (p, g y)` is homotopic to the identity relative to the points over `M_{c-ε}`, by
a homotopy over `P`, for the comparison map `Φφ` of the constant family `fun _ ↦ φ`. -/
private theorem exists_homotopyRel_fiberwiseCellComparison_comp_constLeftInverse
    [LocallyCompactSpace P] (g : C({x : M | f x ≤ c + ε}, morseCellAttachment φ k hk hε hball hf))
    (H : (ContinuousMap.id _).HomotopyRel ((morseCellComparison φ k hk hε hball hf).hom.comp g)
      (range (morseCellComparison φ k hk hε hball hf))) :
    ∃ G : ((fiberwiseCellComparison _ (morseFamilyCharacteristicMap (fun _ : P ↦ φ) k hk hε
          (fun _ ↦ hball) (fun _ ↦ hf) (continuousOn_symm_const φ hball))
          (morseFamilyCharacteristicMap_diskBoundaryInclusion _ _ _ _ _ _ _)).hom.comp
          (constLeftInverse φ k hk hε hball hf g)).HomotopyRel (ContinuousMap.id _)
        {y : P × {x : M | f x ≤ c + ε} | f y.2 ≤ c - ε},
      ∀ t y, (G (t, y)).1 = y.1 := by
  have hΦL (y : P × {x : M | f x ≤ c + ε}) :=
    fiberwiseCellComparison_morseCellAttachmentToConst (P := P) φ k hk hε hball hf (g y.2) y.1
  -- The homotopy `(t, (p, y)) ↦ (p, H (1 - t, y))`.
  refine ⟨{ toHomotopy :=
              ((ContinuousMap.Homotopy.refl ContinuousMap.fst).prodMk
                (H.symm.toHomotopy.compContinuousMap ContinuousMap.snd)).cast
                  (ContinuousMap.ext fun y ↦ (hΦL y).symm) (ContinuousMap.ext fun _ ↦ rfl)
            prop' := fun t y hy ↦ ?_ }, fun _ _ ↦ rfl⟩
  -- On the points over `M_{c-ε}`, `H` is constant, equal to `Φ ∘ g`.
  have hy' : y.2 ∈ range (morseCellComparison φ k hk hε hball hf) :=
    ⟨morseCellAttachmentIncl φ k hk hε hball hf ⟨y.2, hy⟩,
      Subtype.ext (coe_morseCellComparison_morseCellAttachmentIncl φ k hk hball hf hε _)⟩
  have h : (y.1, H.symm (t, y.2)) = (y.1, morseCellComparison φ k hk hε hball hf (g y.2)) := by
    rw [H.symm.eq_fst t hy', ContinuousMap.comp_apply]
  exact h.trans (hΦL y).symm

end Reference

section FiberHomotopyEquiv

open unitInterval

/-- **Milnor's cell attachment theorem over a compact parameter space.** Let `f` be smooth, and let
`φ i` be normal-form charts with disjoint sources around the critical points of a compact band
`f⁻¹[c - ε, c + ε]`, in which `f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²` and whose targets contain
the closed ball of radius `√(2ε)`. Let `ψ p i`, for `p` in a compact, locally compact space `P`, be
normal-form charts with the same centres, whose targets contain the closed ball of radius `√ε`,
whose inverses are jointly continuous in `p` and the point of that ball, and which are `C¹` in the
coordinates of `φ i` near the centres, with derivatives `D i p y` of `ψ p i ∘ (φ i)⁻¹` jointly
continuous in `p` and `y`.

Then the comparison map `Φ : (P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i}) → P × M_{c+ε}` of the cells of the
family `ψ` is a fibre homotopy equivalence over `P`. Its homotopy inverse `θ` composed with `Φ` is
homotopic to the identity relative to `P × M_{c-ε}`, and `Φ ∘ θ` is homotopic to the identity
relative to the points of `P × M_{c+ε}` over `M_{c-ε}`, by homotopies over `P`. -/
theorem exists_fiberHomotopyEquiv_fiberwiseCellComparison_morseFamilyAttachingMap [CompactSpace P]
    [LocallyCompactSpace P] [Finite ι] (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (φ : ι → PartialDiffeomorph Iₘ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hballφ : ∀ i, closedBall 0 √(2 * ε) ⊆ (φ i).target)
    (hfφ : ∀ i, ∀ y ∈ (φ i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints Iₘ f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (φ i).source)
    (ψ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hball : ∀ p i, closedBall 0 √ε ⊆ (ψ p i).target)
    (hf : ∀ p i, ∀ y ∈ (ψ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ p i y j ^ 2)
    (hs : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hp : ∀ p i, (ψ p i).symm 0 = (φ i).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (φ i).symm ⁻¹' (ψ p i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ ψ p i ((φ i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i))) :
    ∃ Θ : FiberHomotopyEquiv
        (fiberwiseCellAttachmentProj (morseFamilyAttachingMap ψ k hk hε.le hball hf hs)).hom
        (ContinuousMap.fst : C(P × {x : M | f x ≤ c + ε}, P)),
      Θ.toFun = (fiberwiseCellComparison (morseFamilyAttachingMap ψ k hk hε.le hball hf hs)
          (morseFamilyCharacteristicMap ψ k hk hε.le hball hf hs)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ k hk hε.le hball hf hs)).hom ∧
      (∃ G : (Θ.invFun.comp Θ.toFun).HomotopyRel (ContinuousMap.id _)
          (range (fiberwiseCellAttachmentIncl (morseFamilyAttachingMap ψ k hk hε.le hball hf hs))),
        ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y) ∧
      ∃ G : (Θ.toFun.comp Θ.invFun).HomotopyRel (ContinuousMap.id _) {y | f y.2 ≤ c - ε},
        ∀ t y, (G (t, y)).1 = y.1 := by
  set φ' := fun i ↦ (φ i).toOpenPartialHomeomorph
  have hballφ' (i : ι) : closedBall 0 √ε ⊆ (φ' i).target :=
    (hballφ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε))
  -- Milnor's left inverse `g` of the comparison map of `φ`.
  obtain ⟨g, hg, ⟨H⟩⟩ :=
    exists_morseCellAttachment_deformation hfs φ hφ k hk hε hballφ hfφ hcompact hcrit
  -- The band `f⁻¹[c - ε, c)` has no critical points, since those of `f⁻¹[c - ε, c + ε]` lie in the
  -- charts `φ i`, where they lie on the level `c`.
  have hreg (x : M) (h₁ : c - ε ≤ f x) (h₂ : f x < c) : mfderiv Iₘ 𝓘(ℝ) f x ≠ 0 := fun h0 ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1
      (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 h0, h₁, by linarith⟩)
    exact (φ i).mfderiv_ne_zero_of_mem_source_of_ne_level (by simp) (hfφ i)
      (hfs.mdifferentiableAt (by simp)) hi h₂.ne h0
  -- Milnor's comparison over `P` of the cells of the constant family `φ` with those of `ψ`: linear
  -- isometries `e i p` of the discs and homotopies `K i : χφ i ≃ χ i ∘ e i` of characteristic maps.
  obtain ⟨e, -, he, K, hK⟩ :=
    exists_homotopy_morseFamilyCharacteristicMap_polarFactor hfs ψ (fun _ ↦ φ') k hk hε hball
      (fun _ ↦ hballφ') hf (fun _ ↦ hfφ) hs (continuousOn_symm_const φ' hballφ') hp hr htr hT hD
      (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous)
        (preimage_mono (Icc_subset_Icc_right (by linarith)))) hreg
  -- `L (p, y) = (p, g y)` is a left inverse over `P` of the comparison map of the constant family
  -- `φ`, and a right inverse up to homotopy relative to the points over `M_{c-ε}`.
  obtain ⟨B, hB⟩ :=
    exists_homotopyRel_fiberwiseCellComparison_comp_constLeftInverse (P := P) φ' k hk hε.le hballφ'
      hfφ g H
  exact exists_fiberHomotopyEquiv_fiberwiseCellComparison_of_homotopy
    (hχ₀ := morseFamilyCharacteristicMap_diskBoundaryInclusion ψ k hk hε.le hball hf hs)
    (hχ₁ := morseFamilyCharacteristicMap_diskBoundaryInclusion (fun _ : P ↦ φ') k hk hε.le
      (fun _ ↦ hballφ') (fun _ ↦ hfφ) (continuousOn_symm_const φ' hballφ'))
    (g := e) (hg := he) (K := K) (hK := hK)
    (g₁ := constLeftInverse φ' k hk hε.le hballφ' hfφ g)
    (hg₁P := fiberwiseCellAttachmentProj_constLeftInverse φ' k hk hε.le hballφ' hfφ g)
    (G₁ := (ContinuousMap.HomotopyRel.refl _ _).cast rfl (ContinuousMap.ext fun z ↦
      constLeftInverse_fiberwiseCellComparison φ' k hk hε.le hballφ' hfφ hg z))
    (hG₁ := fun _ z ↦ congrArg _
      (constLeftInverse_fiberwiseCellComparison φ' k hk hε.le hballφ' hfφ hg z))
    (hT := fun y hy ↦ ⟨(y.1, ⟨y.2, hy⟩),
      (constLeftInverse_of_le φ' k hk hε.le hballφ' hfφ hg y.1 ⟨y.2, hy⟩).symm⟩)
    (G₂ := B) (hG₂ := hB)

/-- **Milnor's reattachment maps compose over a compact parameter space.** Let `ψ₀`, `ψ₁`, `ψ₂` be
three families over a compact, locally compact `P` of normal-form charts around the critical points
of a compact band `f⁻¹[c - ε, c + ε]`, as in
`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap`, with `ψ₀`
continuously differentiable over `P` in the coordinates of a fixed family `φ` of normal-form charts
as in `TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellComparison_morseFamilyAttachingMap`. For any
fiberwise reattachment maps `E₀₁`, `E₁₂`, `E₀₂` between the cell attachments of the three families,
built from any self-maps `hᵢⱼ` of the disc pairs and any homotopies `Kᵢⱼ : χⱼ ≃ χᵢ ∘ hᵢⱼ` of the
characteristic maps keeping the boundary spheres in `M_{c-ε}`, the composite `E₀₁ ∘ E₁₂` is
homotopic to `E₀₂` relative to `P × M_{c-ε}`, by a homotopy over `P`.

No relation between the self-maps `h₀₁ ∘ h₁₂` and `h₀₂` of the discs is assumed: the comparison
map of `ψ₀` has a homotopy inverse over `P`, so a reattachment map into the attachment of `ψ₀` is
determined up to homotopy by the cells it starts from. -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_morseFamilyAttachingMap [CompactSpace P]
    [LocallyCompactSpace P] [Finite ι] (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (φ : ι → PartialDiffeomorph Iₘ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hballφ : ∀ i, closedBall 0 √(2 * ε) ⊆ (φ i).target)
    (hfφ : ∀ i, ∀ y ∈ (φ i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints Iₘ f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (φ i).source)
    (ψ₀ ψ₁ ψ₂ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hball₀ : ∀ p i, closedBall 0 √ε ⊆ (ψ₀ p i).target)
    (hball₁ : ∀ p i, closedBall 0 √ε ⊆ (ψ₁ p i).target)
    (hball₂ : ∀ p i, closedBall 0 √ε ⊆ (ψ₂ p i).target)
    (hf₀ : ∀ p i, ∀ y ∈ (ψ₀ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₀ p i y j ^ 2)
    (hf₁ : ∀ p i, ∀ y ∈ (ψ₁ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₁ p i y j ^ 2)
    (hf₂ : ∀ p i, ∀ y ∈ (ψ₂ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₂ p i y j ^ 2)
    (hs₀ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₂ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₂ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hp : ∀ p i, (ψ₀ p i).symm 0 = (φ i).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (φ i).symm ⁻¹' (ψ₀ p i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ ψ₀ p i ((φ i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
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
        {y : {x : M | f x ≤ c + ε} | f y ≤ c - ε})
    (K₁₂ : ∀ i, (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁ i).comp
        (ContinuousMap.fst.prodMk (h₁₂ i))))
    (hK₁₂ : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
      K₁₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
        {y : {x : M | f x ≤ c + ε} | f y ≤ c - ε})
    (K₀₂ : ∀ i, (morseFamilyCharacteristicMap ψ₂ k hk hε.le hball₂ hf₂ hs₂ i).Homotopy
      ((morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
        (ContinuousMap.fst.prodMk (h₀₂ i))))
    (hK₀₂ : ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
      K₀₂ i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
        {y : {x : M | f x ≤ c + ε} | f y ≤ c - ε}) :
    ∃ G : (fiberwiseCellReattachment _ _ _ _
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          h₁₂ hh₁₂ K₁₂ hK₁₂ ≫
        fiberwiseCellReattachment _ _ _ _
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
          h₀₁ hh₀₁ K₀₁ hK₀₁).hom.HomotopyRel
        (fiberwiseCellReattachment _ _ _ _
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₀ k hk hε.le hball₀ hf₀ hs₀)
          (morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₂ k hk hε.le hball₂ hf₂ hs₂)
          h₀₂ hh₀₂ K₀₂ hK₀₂).hom
        (range (fiberwiseCellAttachmentIncl
          (morseFamilyAttachingMap ψ₂ k hk hε.le hball₂ hf₂ hs₂))),
      ∀ t y, fiberwiseCellAttachmentProj _ (G (t, y)) = fiberwiseCellAttachmentProj _ y := by
  obtain ⟨Θ, hΘ, ⟨G, hG⟩, -⟩ :=
    exists_fiberHomotopyEquiv_fiberwiseCellComparison_morseFamilyAttachingMap hfs φ hφ k hk hε
      hballφ hfφ hcompact hcrit ψ₀ hball₀ hf₀ hs₀ hp hr htr hT hD
  exact exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment
    (hχ₁ := morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₁ k hk hε.le hball₁ hf₁ hs₁)
    (hχ₂ := morseFamilyCharacteristicMap_diskBoundaryInclusion ψ₂ k hk hε.le hball₂ hf₂ hs₂)
    (h₀₁ := h₀₁) (h₁₂ := h₁₂) (h₀₂ := h₀₂) (hh₀₁ := hh₀₁) (hh₁₂ := hh₁₂) (hh₀₂ := hh₀₂)
    (K₀₁ := K₀₁) (hK₀₁ := hK₀₁) (K₁₂ := K₁₂) (hK₁₂ := hK₁₂) (K₀₂ := K₀₂) (hK₀₂ := hK₀₂)
    (g₀ := Θ.invFun) (hg₀P := ContinuousMap.congr_fun Θ.comp_invFun)
    (G₀ := G.cast (by rw [hΘ]) rfl) (hG₀ := hG)

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
reattachment maps require. It is the variant of
`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellComparison_morseFamilyAttachingMap` whose
hypotheses differentiate the transitions `φ i ∘ (ψ p i)⁻¹` rather than `ψ p i ∘ (φ i)⁻¹`.

The map `g` is the product of `P` with Milnor's left inverse
(`TauCeti.exists_morseCellAttachment_deformation`) for the charts `φ`, followed by the inverse of
the fibre homotopy equivalence comparing the cells of `φ` and `ψ` over `P`
(`TauCeti.exists_fiberHomotopyEquiv_fiberwiseCellAttachment_morseFamilyAttachingMap`). -/
theorem exists_homotopyRel_comp_fiberwiseCellComparison_morseFamily [CompactSpace P]
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
  -- The left inverse `g₀ = (p, y) ↦ (p, g y)` over `P` for the constant family `φ`, from Milnor's
  -- left inverse `g` of the comparison map of `φ`.
  obtain ⟨g, hg, -⟩ :=
    exists_morseCellAttachment_deformation hfs φ hφ k hk hε hballφ hfφ hcompact hcrit
  set g₀ := constLeftInverse (P := P) (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hball'
    hfφ g
  have hg₀P := fiberwiseCellAttachmentProj_constLeftInverse (P := P)
    (fun i ↦ (φ i).toOpenPartialHomeomorph) k hk hε.le hball' hfφ g
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
    ContinuousMap.ext fun y ↦ congrArg Ψ.invFun
      (constLeftInverse_fiberwiseCellComparison _ k hk hε.le hball' hfφ hg _)
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
    [LocallyCompactSpace P] [Finite ι] (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
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

end FiberHomotopyEquiv


end TauCeti
