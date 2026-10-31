/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Attachment
public import TauCeti.Geometry.Manifold.Morse.Cell.Map
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import TauCeti.Analysis.Real.Sqrt
import TauCeti.Topology.Category.TopCat.OpenEmbedding

/-!
# The handle-to-cell comparison across a critical level

Let `f` be a continuous function on `M` and let `φ i` be finitely many charts with values in
`ℝⁿ`, with pairwise disjoint sources, in which `f` has the normal form

`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`,

and whose targets contain the closed ball of radius `√ε`. Each chart carries the characteristic
map `χᵢ : (D^{k i}, ∂D^{k i}) → (M_{c+ε}, M_{c-ε})`, `w ↦ φ i⁻¹(√ε • (w, 0))`, of its cell, and
its attaching map `αᵢ : ∂D^{k i} → M_{c-ε}` (`OpenPartialHomeomorph.morseCharacteristicMap` and
`OpenPartialHomeomorph.morseAttachingMap`), where `M_a = {f ≤ a}`.

This file forms the space `M_{c-ε} ∪_α ⨆ᵢ D^{k i}` obtained by attaching one disc along each `αᵢ`,
as a pushout in `TopCat` (`TauCeti.morseCellAttachment`), and the comparison map

`Φ : M_{c-ε} ∪_α ⨆ᵢ D^{k i} → M_{c+ε}`

induced on the pushout by the inclusion of the lower sublevel and the characteristic maps
(`TauCeti.morseCellComparison`). When `M` is Hausdorff, `f` is continuous, `ε > 0` and the
charts have pairwise disjoint sources, `Φ` is a closed embedding: it is injective because the open
discs are carried into the disjoint chart sources and off the lower sublevel, and closed because
the lower sublevel is closed and the discs are compact. Its image is the lower sublevel together
with the cells `{‖φ i x‖² ≤ ε, (φ i x)ⱼ = 0 for j ≥ k i}`.

Milnor's cell attachment theorem (`TauCeti.exists_sublevel_union_cells_deformation`) strong
deformation retracts `M_{c+ε}` onto exactly this image when `f` is smooth, the charts are smooth
and their targets contain the closed ball of radius `√(2ε)`, and the band `f⁻¹[c - ε, c + ε]` is
compact with its critical points in the charts. Transported along `Φ`, this gives a map
`g : M_{c+ε} → M_{c-ε} ∪_α ⨆ᵢ D^{k i}` with `g ∘ Φ = id` and a homotopy from `Φ ∘ g` to the
identity fixing the image of `Φ`, in particular the whole lower sublevel. So `Φ` is a homotopy
equivalence relative to `M_{c-ε}`; this is the form of the attachment in which a sublevel of a
Morse function is built from the previous one by attaching cells. The charts may have any indices,
including `0` (a disc attached along the empty sphere) and `n`, and several critical points on one
level are handled simultaneously.

## Main definitions

* `TauCeti.morseCellAttachment`: the space `M_{c-ε} ∪_α ⨆ᵢ D^{k i}`.
* `TauCeti.morseCellAttachmentIncl`, `TauCeti.morseCellAttachmentCell`: its inclusion of the lower
  sublevel and the characteristic maps of its cells.
* `TauCeti.morseCellAttachmentDesc`: the map out of `TauCeti.morseCellAttachment` induced by
  compatible maps on the lower sublevel and on the discs.
* `TauCeti.morseCellComparison`: the comparison map `M_{c-ε} ∪_α ⨆ᵢ D^{k i} → M_{c+ε}`.

## Main results

* `TauCeti.isPushout_morseCellAttachment`: the pushout square defining the attachment.
* `TauCeti.isClosedEmbedding_morseCellComparison`: the comparison map is a closed embedding.
* `TauCeti.range_morseCellComparison`: its image is the lower sublevel together with the cells.
* `TauCeti.exists_morseCellAttachment_deformation`: the comparison map is the inclusion of a
  strong deformation retract of `M_{c+ε}`.
* `TauCeti.IsMorse.exists_morseCellAttachment_deformation`: the same for a Morse function at any
  value `c` with a compact band (the cells are indexed by the critical points on the level), with
  the normalized Morse charts and the width `ε` supplied by
  `TauCeti.IsMorse.exists_admissible_morseCharts`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Metric Topology CategoryTheory Limits
open scoped ContDiff Manifold

universe u

namespace TauCeti

section Attachment

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type u} {f : M → ℝ} {c ε : ℝ}

/-- The space `M_{c-ε} ∪_α ⨆ᵢ D^{k i}` obtained from the lower sublevel `M_{c-ε} = {f ≤ c - ε}`
by attaching one `k i`-disc along the attaching map
`OpenPartialHomeomorph.morseAttachingMap (φ i)` of each chart `φ i`, in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²` and whose target contains the closed ball of radius
`√ε`. It is the pushout in `TopCat` of the coproduct of the attaching maps and of the boundary
inclusions `∂D^{k i} → D^{k i}` (`TauCeti.isPushout_morseCellAttachment`). -/
def morseCellAttachment (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
    (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2) :
    TopCat.{u} :=
  pushout (Sigma.desc fun i ↦ (φ i).morseAttachingMap (hk i) hε (hball i) (hf i))
    (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion.{u} (k i))

/-- The inclusion of the lower sublevel `M_{c-ε}` into `TauCeti.morseCellAttachment`. -/
def morseCellAttachmentIncl (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
    (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2) :
    TopCat.of {x | f x ≤ c - ε} ⟶ morseCellAttachment φ k hk hε hball hf :=
  pushout.inl _ _

/-- The characteristic map `D^{k i} → TauCeti.morseCellAttachment` of the cell attached along the
attaching map of the chart `φ i`. -/
def morseCellAttachmentCell (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
    (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    (i : ι) : TopCat.disk.{u} (k i) ⟶ morseCellAttachment φ k hk hε hball hf :=
  Sigma.ι (fun i ↦ TopCat.disk.{u} (k i)) i ≫ pushout.inr _ _

variable (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
  (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)

/-- `TauCeti.morseCellAttachment` is the pushout of the coproduct of the attaching maps along the
coproduct of the boundary inclusions `∂D^{k i} → D^{k i}`, with the inclusion of the lower sublevel
and the characteristic maps of the cells as its legs. -/
theorem isPushout_morseCellAttachment (hε : 0 ≤ ε) :
    IsPushout (Sigma.desc fun i ↦ (φ i).morseAttachingMap (hk i) hε (hball i) (hf i))
      (Limits.Sigma.map fun i ↦ TopCat.diskBoundaryInclusion.{u} (k i))
      (morseCellAttachmentIncl φ k hk hε hball hf)
      (Sigma.desc (morseCellAttachmentCell φ k hk hε hball hf)) := by
  have h : Sigma.desc (morseCellAttachmentCell φ k hk hε hball hf) =
      (pushout.inr _ _ : _ ⟶ morseCellAttachment φ k hk hε hball hf) :=
    Sigma.hom_ext _ _ fun i ↦ by rw [Sigma.ι_comp_desc, morseCellAttachmentCell]
  rw [h]
  exact IsPushout.of_hasPushout _ _

/-- In `TauCeti.morseCellAttachment`, the characteristic map of a cell restricts on the boundary
sphere to the attaching map followed by the inclusion of the lower sublevel. -/
@[reassoc]
theorem morseAttachingMap_comp_morseCellAttachmentIncl (hε : 0 ≤ ε) (i : ι) :
    (φ i).morseAttachingMap (hk i) hε (hball i) (hf i) ≫
        morseCellAttachmentIncl φ k hk hε hball hf =
      TopCat.diskBoundaryInclusion (k i) ≫ morseCellAttachmentCell φ k hk hε hball hf i := by
  simpa using Sigma.ι (fun i ↦ TopCat.diskBoundary.{u} (k i)) i ≫=
    (isPushout_morseCellAttachment φ k hk hball hf hε).w

/-- A map on the lower sublevel and maps on the discs which agree on the boundary spheres induce a
map out of `TauCeti.morseCellAttachment`. -/
def morseCellAttachmentDesc (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
    (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    {Z : TopCat.{u}} (g : TopCat.of {x | f x ≤ c - ε} ⟶ Z)
    (G : ∀ i, TopCat.disk.{u} (k i) ⟶ Z)
    (h : ∀ i, (φ i).morseAttachingMap (hk i) hε (hball i) (hf i) ≫ g =
      TopCat.diskBoundaryInclusion (k i) ≫ G i) :
    morseCellAttachment φ k hk hε hball hf ⟶ Z :=
  (isPushout_morseCellAttachment φ k hk hball hf hε).desc g (Sigma.desc G)
    (Sigma.hom_ext _ _ fun i ↦ by simpa using h i)

/-- The map out of `TauCeti.morseCellAttachment` restricts to the prescribed map on the lower
sublevel. -/
@[reassoc (attr := simp)]
theorem morseCellAttachmentIncl_desc (hε : 0 ≤ ε) {Z : TopCat.{u}}
    (g : TopCat.of {x | f x ≤ c - ε} ⟶ Z) (G : ∀ i, TopCat.disk.{u} (k i) ⟶ Z)
    (h : ∀ i, (φ i).morseAttachingMap (hk i) hε (hball i) (hf i) ≫ g =
      TopCat.diskBoundaryInclusion (k i) ≫ G i) :
    morseCellAttachmentIncl φ k hk hε hball hf ≫
      morseCellAttachmentDesc φ k hk hε hball hf g G h = g :=
  IsPushout.inl_desc _ _ _ _

/-- The map out of `TauCeti.morseCellAttachment` restricts to the prescribed map on each disc. -/
@[reassoc (attr := simp)]
theorem morseCellAttachmentCell_desc (hε : 0 ≤ ε) {Z : TopCat.{u}}
    (g : TopCat.of {x | f x ≤ c - ε} ⟶ Z) (G : ∀ i, TopCat.disk.{u} (k i) ⟶ Z)
    (h : ∀ i, (φ i).morseAttachingMap (hk i) hε (hball i) (hf i) ≫ g =
      TopCat.diskBoundaryInclusion (k i) ≫ G i) (i : ι) :
    morseCellAttachmentCell φ k hk hε hball hf i ≫
      morseCellAttachmentDesc φ k hk hε hball hf g G h = G i := by
  rw [morseCellAttachmentDesc, ← Sigma.ι_comp_desc (morseCellAttachmentCell φ k hk hε hball hf) i,
    Category.assoc, IsPushout.inr_desc, Sigma.ι_comp_desc]

/-- Maps out of `TauCeti.morseCellAttachment` are determined by their restrictions to the lower
sublevel and to the cells. -/
theorem morseCellAttachment_hom_ext {Z : TopCat.{u}} (hε : 0 ≤ ε)
    {g g' : morseCellAttachment φ k hk hε hball hf ⟶ Z}
    (h₀ : morseCellAttachmentIncl φ k hk hε hball hf ≫ g =
      morseCellAttachmentIncl φ k hk hε hball hf ≫ g')
    (h : ∀ i, morseCellAttachmentCell φ k hk hε hball hf i ≫ g =
      morseCellAttachmentCell φ k hk hε hball hf i ≫ g') :
    g = g' :=
  (isPushout_morseCellAttachment φ k hk hball hf hε).hom_ext h₀ (Sigma.hom_ext _ _ fun i ↦ by
    simpa using h i)

/-- Every point of `TauCeti.morseCellAttachment` lies in the lower sublevel or in a cell. -/
theorem range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell (hε : 0 ≤ ε) :
    range (morseCellAttachmentIncl φ k hk hε hball hf) ∪
        ⋃ i, range (morseCellAttachmentCell φ k hk hε hball hf i) = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  by_cases hy : y ∈ range (morseCellAttachmentIncl φ k hk hε hball hf)
  · exact Or.inl hy
  rw [← mem_compl_iff,
    ← TopCat.image_compl_range_of_isPushout (isPushout_morseCellAttachment φ k hk hball hf hε)]
    at hy
  obtain ⟨z, -, rfl⟩ := hy
  obtain ⟨⟨i, w⟩, hz⟩ : ∃ s, (TopCat.sigmaIsoSigma _).inv s = z :=
    ⟨(TopCat.sigmaIsoSigma _).hom z, by
      rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]⟩
  rw [TopCat.sigmaIsoSigma_inv_apply] at hz
  refine Or.inr (mem_iUnion.2 ⟨i, w, ?_⟩)
  rw [← hz, ← ConcreteCategory.comp_apply, Sigma.ι_comp_desc]

/-- The comparison map `M_{c-ε} ∪_α ⨆ᵢ D^{k i} → M_{c+ε}` from `TauCeti.morseCellAttachment` to
the sublevel `M_{c+ε} = {f ≤ c + ε}`, induced on the pushout by the inclusion of the lower sublevel
`M_{c-ε}` and by the characteristic maps `OpenPartialHomeomorph.morseCharacteristicMap` of the
cells. -/
def morseCellComparison (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
    (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2) :
    morseCellAttachment φ k hk hε hball hf ⟶ TopCat.of {x | f x ≤ c + ε} :=
  morseCellAttachmentDesc φ k hk hε hball hf
    (TopCat.ofHom (sublevelInclusion f (c - ε) (c + ε) (by linarith)))
    (fun i ↦ (φ i).morseCharacteristicMap (hk i) hε (hball i) (hf i)) fun i ↦
      OpenPartialHomeomorph.morseAttachingMap_comp_sublevelInclusion (hball i) (hf i) (hk i) hε

/-- On the lower sublevel, the comparison map is the inclusion `M_{c-ε} → M_{c+ε}`. -/
@[reassoc (attr := simp)]
theorem morseCellAttachmentIncl_comp_morseCellComparison (hε : 0 ≤ ε) :
    morseCellAttachmentIncl φ k hk hε hball hf ≫ morseCellComparison φ k hk hε hball hf =
      TopCat.ofHom (sublevelInclusion f (c - ε) (c + ε) (by linarith)) :=
  morseCellAttachmentIncl_desc _ _ _ _ _ _ _ _ _

/-- On the cell of the chart `φ i`, the comparison map is the characteristic map of the cell. -/
@[reassoc (attr := simp)]
theorem morseCellAttachmentCell_comp_morseCellComparison (hε : 0 ≤ ε) (i : ι) :
    morseCellAttachmentCell φ k hk hε hball hf i ≫ morseCellComparison φ k hk hε hball hf =
      (φ i).morseCharacteristicMap (hk i) hε (hball i) (hf i) :=
  morseCellAttachmentCell_desc _ _ _ _ _ _ _ _ _ _

/-- The comparison map sends a point of the lower sublevel to itself. -/
@[simp]
theorem coe_morseCellComparison_morseCellAttachmentIncl (hε : 0 ≤ ε) (x : {x | f x ≤ c - ε}) :
    (morseCellComparison φ k hk hε hball hf (morseCellAttachmentIncl φ k hk hε hball hf x) : M) =
      x := by
  rw [← ConcreteCategory.comp_apply, morseCellAttachmentIncl_comp_morseCellComparison]
  exact coe_sublevelInclusion_apply f _ x

/-- The comparison map sends the point `w` of the cell of the chart `φ i` to
`φ i⁻¹(√ε • (w, 0))`. -/
@[simp]
theorem coe_morseCellComparison_morseCellAttachmentCell (hε : 0 ≤ ε) (i : ι)
    (w : TopCat.disk.{u} (k i)) :
    (morseCellComparison φ k hk hε hball hf (morseCellAttachmentCell φ k hk hε hball hf i w) :
        M) = (φ i).morseCellMap (hk i) ε w.down := by
  rw [← ConcreteCategory.comp_apply, morseCellAttachmentCell_comp_morseCellComparison,
    OpenPartialHomeomorph.coe_morseCharacteristicMap_apply]

/-- The image of the comparison map is the lower sublevel `M_{c-ε}` together with the cells
`{‖φ i x‖² ≤ ε, (φ i x)ⱼ = 0 for j ≥ k i}` of the charts. -/
theorem range_morseCellComparison (hε : 0 < ε) :
    range (morseCellComparison φ k hk hε.le hball hf) =
      {x : ↥{x | f x ≤ c + ε} | (x : M) ∈ {x | f x ≤ c - ε} ∪
        ⋃ i, (φ i).source ∩ φ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0}} := by
  refine Set.ext fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ | hy :=
      (range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ k hk hball hf
        hε.le).symm ▸ mem_univ y
    · refine Or.inl ?_
      rw [mem_ofPred_eq, coe_morseCellComparison_morseCellAttachmentIncl]
      exact x.2
    obtain ⟨i, w, rfl⟩ := mem_iUnion.1 hy
    have hw : (φ i).morseCharacteristicMap (hk i) hε.le (hball i) (hf i) w ∈
        range ((φ i).morseCharacteristicMap (hk i) hε.le (hball i) (hf i)) := mem_range_self w
    rw [OpenPartialHomeomorph.range_morseCharacteristicMap (hball i) (hf i) (hk i) hε] at hw
    refine Or.inr (mem_iUnion.2 ⟨i, ?_⟩)
    rwa [← ConcreteCategory.comp_apply, morseCellAttachmentCell_comp_morseCellComparison]
  · rintro (hx | hx)
    · exact ⟨morseCellAttachmentIncl φ k hk hε.le hball hf ⟨x, hx⟩,
        Subtype.ext (coe_morseCellComparison_morseCellAttachmentIncl φ k hk hball hf hε.le _)⟩
    obtain ⟨i, hx⟩ := mem_iUnion.1 hx
    have hx' : x ∈ range ((φ i).morseCharacteristicMap (hk i) hε.le (hball i) (hf i)) := by
      rw [OpenPartialHomeomorph.range_morseCharacteristicMap (hball i) (hf i) (hk i) hε]
      exact hx
    obtain ⟨w, rfl⟩ := hx'
    exact ⟨morseCellAttachmentCell φ k hk hε.le hball hf i w, by
      rw [← ConcreteCategory.comp_apply, morseCellAttachmentCell_comp_morseCellComparison]⟩

/-- A point of the cell of the chart `φ i` which lies in the lower sublevel is the image of a point
of the lower sublevel in `TauCeti.morseCellAttachment`. -/
private theorem morseCellAttachmentIncl_eq_morseCellAttachmentCell (hε : 0 < ε)
    {x : {x | f x ≤ c - ε}} {i : ι} {w : TopCat.disk.{u} (k i)}
    (hxw : (x : M) = (φ i).morseCellMap (hk i) ε w.down) :
    morseCellAttachmentIncl φ k hk hε.le hball hf x =
      morseCellAttachmentCell φ k hk hε.le hball hf i w := by
  have hw : w ∈ (φ i).morseCharacteristicMap (hk i) hε.le (hball i) (hf i) ⁻¹'
      {x | f x ≤ c - ε} := by
    rw [mem_preimage, mem_ofPred_eq, OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
      ← hxw]
    exact x.2
  rw [OpenPartialHomeomorph.preimage_morseCharacteristicMap_sublevel (hball i) (hf i) (hk i) hε]
    at hw
  obtain ⟨s, rfl⟩ := hw
  rw [← ConcreteCategory.comp_apply, ← morseAttachingMap_comp_morseCellAttachmentIncl,
    ConcreteCategory.comp_apply]
  refine congrArg _ (Subtype.ext ?_)
  rw [hxw, OpenPartialHomeomorph.coe_morseAttachingMap_apply,
    TauCeti.TopCat.coe_diskBoundaryInclusion_apply_down]

/-- The comparison map is injective: the open discs are carried off the lower sublevel and into
the pairwise disjoint chart sources. -/
theorem morseCellComparison_injective (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source))
    (hε : 0 < ε) : Injective (morseCellComparison φ k hk hε.le hball hf) := by
  have hsurj :=
    range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ k hk hball hf hε.le
  intro a b hab
  have hab' : (morseCellComparison φ k hk hε.le hball hf a : M) =
      morseCellComparison φ k hk hε.le hball hf b := congrArg Subtype.val hab
  obtain ⟨x, rfl⟩ | ha := hsurj.symm ▸ mem_univ a <;>
    obtain ⟨y, rfl⟩ | hb := hsurj.symm ▸ mem_univ b
  · rw [coe_morseCellComparison_morseCellAttachmentIncl,
      coe_morseCellComparison_morseCellAttachmentIncl] at hab'
    exact congrArg _ (Subtype.ext hab')
  · obtain ⟨j, w, rfl⟩ := mem_iUnion.1 hb
    rw [coe_morseCellComparison_morseCellAttachmentIncl,
      coe_morseCellComparison_morseCellAttachmentCell] at hab'
    exact morseCellAttachmentIncl_eq_morseCellAttachmentCell φ k hk hball hf hε hab'
  · obtain ⟨i, w, rfl⟩ := mem_iUnion.1 ha
    rw [coe_morseCellComparison_morseCellAttachmentIncl,
      coe_morseCellComparison_morseCellAttachmentCell] at hab'
    exact (morseCellAttachmentIncl_eq_morseCellAttachmentCell φ k hk hball hf hε hab'.symm).symm
  · obtain ⟨i, v, rfl⟩ := mem_iUnion.1 ha
    obtain ⟨j, w, rfl⟩ := mem_iUnion.1 hb
    rw [coe_morseCellComparison_morseCellAttachmentCell,
      coe_morseCellComparison_morseCellAttachmentCell] at hab'
    obtain rfl | hij := eq_or_ne i j
    · exact congrArg _ (ULift.ext (Subtype.ext
        ((φ i).injOn_morseCellMap (hball i) (hk i) hε v.down.2 w.down.2 hab')))
    · exact absurd hab' ((hφ hij).ne_of_mem
        ((φ i).morseCellMap_mem_source (hball i) (hk i) (mem_closedBall_zero_iff.1 v.down.2))
        ((φ j).morseCellMap_mem_source (hball j) (hk j) (mem_closedBall_zero_iff.1 w.down.2)))

/-- **The handle-to-cell comparison is a closed embedding.** For a continuous `f` on a Hausdorff
space, the comparison map `M_{c-ε} ∪_α ⨆ᵢ D^{k i} → M_{c+ε}` of finitely many normal-form charts
with disjoint sources is a closed embedding. -/
theorem isClosedEmbedding_morseCellComparison [T2Space M] [Finite ι] (hfc : Continuous f)
    (hφ : Pairwise (Disjoint on fun i ↦ (φ i).source)) (hε : 0 < ε) :
    IsClosedEmbedding (morseCellComparison φ k hk hε.le hball hf) := by
  refine .of_continuous_injective_isClosedMap (morseCellComparison φ k hk hε.le hball hf).hom.2
    (morseCellComparison_injective φ k hk hball hf hφ hε) fun A hA ↦ ?_
  -- `A` is the union of its parts in the lower sublevel and in the cells.
  have hA' : A = morseCellAttachmentIncl φ k hk hε.le hball hf ''
      (morseCellAttachmentIncl φ k hk hε.le hball hf ⁻¹' A) ∪
        ⋃ i, morseCellAttachmentCell φ k hk hε.le hball hf i ''
          (morseCellAttachmentCell φ k hk hε.le hball hf i ⁻¹' A) := by
    conv_lhs => rw [← inter_univ A,
      ← range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ k hk hball hf
        hε.le, inter_union_distrib_left, inter_iUnion]
    simp only [inter_comm A, ← image_preimage_eq_range_inter]
  -- The lower sublevel is closed in `M_{c+ε}` and the discs are compact.
  have hab : c - ε ≤ c + ε := by linarith
  have h₀ : morseCellComparison φ k hk hε.le hball hf ∘
      morseCellAttachmentIncl φ k hk hε.le hball hf =
      sublevelInclusion f (c - ε) (c + ε) hab :=
    funext (ConcreteCategory.congr_hom
      (morseCellAttachmentIncl_comp_morseCellComparison φ k hk hball hf hε.le))
  have h₁ (i : ι) : morseCellComparison φ k hk hε.le hball hf ∘
      morseCellAttachmentCell φ k hk hε.le hball hf i =
        (φ i).morseCharacteristicMap (hk i) hε.le (hball i) (hf i) :=
    funext (ConcreteCategory.congr_hom
      (morseCellAttachmentCell_comp_morseCellComparison φ k hk hball hf hε.le i))
  rw [hA', image_union, image_iUnion, ← image_comp, h₀]
  refine ((isClosedEmbedding_sublevelInclusion hfc hab).isClosedMap _
    (hA.preimage (morseCellAttachmentIncl φ k hk hε.le hball hf).hom.2)).union
    (isClosed_iUnion_of_finite fun i ↦ ?_)
  rw [← image_comp, h₁]
  exact ((φ i).isClosedEmbedding_morseCharacteristicMap (hball i) (hf i) (hk i) hε).isClosedMap
    _ (hA.preimage (morseCellAttachmentCell φ k hk hε.le hball hf i).hom.2)

end Attachment

section Deformation

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {n : ℕ} {ι : Type u} {f : M → ℝ} {c ε : ℝ}

/-- **The handle-to-cell comparison is a homotopy equivalence relative to the lower sublevel.**
Let `f` be smooth and let `ψ i` be finitely many charts with pairwise disjoint sources, each
containing the closed ball of radius `√(2ε)` about `0`, in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`. If the band `f⁻¹[c - ε, c + ε]` is compact and its
critical points lie in the charts, then the comparison map
`Φ : M_{c-ε} ∪_α ⨆ᵢ D^{k i} → M_{c+ε}` has a left inverse `g` such that `Φ ∘ g` is homotopic to
the identity of `M_{c+ε}` relative to the image of `Φ`, which contains the lower sublevel
`M_{c-ε}`. -/
theorem exists_morseCellAttachment_deformation [Finite ι] (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ : Pairwise (Disjoint on fun i ↦ (ψ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ i).target)
    (hf : ∀ i, ∀ y ∈ (ψ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ i).source) :
    ∃ g : C({x | f x ≤ c + ε}, morseCellAttachment (fun i ↦ (ψ i).toOpenPartialHomeomorph) k hk
        hε.le
        (fun i ↦ (hball i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε))) hf),
      LeftInverse g (morseCellComparison (fun i ↦ (ψ i).toOpenPartialHomeomorph) k hk hε.le
        (fun i ↦ (hball i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        hf) ∧
      (ContinuousMap.id _).HomotopicRel
        ((morseCellComparison (fun i ↦ (ψ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf).hom.comp g)
        (range (morseCellComparison (fun i ↦ (ψ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf)) := by
  have hball' (i : ι) : closedBall 0 √ε ⊆ (ψ i).target :=
    (hball i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε))
  set φ := fun i ↦ (ψ i).toOpenPartialHomeomorph
  set Φ := morseCellComparison φ k hk hε.le hball' hf
  obtain ⟨r, hr, ⟨G⟩⟩ :=
    exists_sublevel_union_cells_deformation hfs ψ hψ k hε hball hf hcompact hcrit
  have hΦ := isClosedEmbedding_morseCellComparison φ k hk hball' hf hfs.continuous hψ hε
  have hrange := range_morseCellComparison φ k hk hball' hf hε
  -- The retraction `r` lands in the image of `Φ`, which `Φ` identifies with the attachment.
  let j : C(↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪
      ⋃ i, (φ i).source ∩ φ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0})),
      range Φ) :=
    ⟨fun x ↦ ⟨⟨x, x.2.1⟩, hrange ▸ x.2.2⟩,
      ((continuous_subtype_val.subtype_mk _).subtype_mk _)⟩
  refine ⟨(hΦ.isEmbedding.toHomeomorph.symm : C(range Φ, _)).comp (j.comp r), fun y ↦ ?_, ?_⟩
  · have hy : (Φ y : M) ∈ {x | f x ≤ c - ε} ∪
        ⋃ i, (φ i).source ∩ φ i ⁻¹' {y | ‖y‖ ^ 2 ≤ ε ∧ ∀ j : Fin n, k i ≤ j.val → y j = 0} := by
      have := mem_range_self (f := Φ) y
      rwa [hrange] at this
    have hry : r (Φ y) = ⟨Φ y, (Φ y).2, hy⟩ := hr ⟨Φ y, (Φ y).2, hy⟩
    have hjr : j (r (Φ y)) = ⟨Φ y, mem_range_self y⟩ := by
      rw [hry]
      rfl
    exact (congrArg hΦ.isEmbedding.toHomeomorph.symm hjr).trans
      (hΦ.isEmbedding.toHomeomorph_symm_apply y)
  · have hcomp : Φ.hom.comp ((hΦ.isEmbedding.toHomeomorph.symm : C(range Φ, _)).comp (j.comp r)) =
        (ContinuousMap.inclusion inter_subset_left).comp r := by
      ext x
      have h := congrArg Subtype.val (hΦ.isEmbedding.toHomeomorph.apply_symm_apply (j (r x)))
      rw [IsEmbedding.toHomeomorph_apply_coe] at h
      exact congrArg Subtype.val h
    rw [hcomp, hrange]
    exact ⟨G.symm⟩

/-- **Milnor's cell attachment theorem, in pushout form.** Let `f` be a Morse function and `c` a
value with a compact band `f⁻¹[c - δ, c + δ]`. Then for some `0 < ε ≤ δ` there are normalized Morse
charts `ψ p` at the critical points `p` on the level `c`, with pairwise disjoint sources, such that
the comparison map `Φ : M_{c-ε} ∪_α ⨆ₚ D^{λ p} → M_{c+ε}` from the lower sublevel with one cell of
dimension the Morse index `λ p` attached at each `p` has a left inverse `g`, and `Φ ∘ g` is
homotopic to the identity of `M_{c+ε}` relative to the image of `Φ`, which contains the lower
sublevel `M_{c-ε}`. -/
theorem IsMorse.exists_morseCellAttachment_deformation (hf : IsMorse I f) {δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧
      ∃ ψ : ↥(criticalPoints I f ∩ f ⁻¹' {c}) →
          PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
        Pairwise (Disjoint on fun p ↦ (ψ p).source) ∧ (∀ p, ↑p ∈ (ψ p).source ∧ ψ p p = 0) ∧
        ∃ (hball : ∀ p, closedBall 0 √ε ⊆ (ψ p).target)
          (hψ : ∀ p, ∀ y ∈ (ψ p).source,
            f y = c + ∑ i, (if i.val < manifoldMorseIndex I f p then -1 else 1) * ψ p y i ^ 2),
          ∃ g : C({x | f x ≤ c + ε}, morseCellAttachment (fun p ↦ (ψ p).toOpenPartialHomeomorph)
              (manifoldMorseIndex I f ·) (fun _ ↦ manifoldMorseIndex_le_finrank) hε.le hball hψ),
            LeftInverse g (morseCellComparison (fun p ↦ (ψ p).toOpenPartialHomeomorph)
              (manifoldMorseIndex I f ·) (fun _ ↦ manifoldMorseIndex_le_finrank) hε.le hball hψ) ∧
            (ContinuousMap.id _).HomotopicRel
              ((morseCellComparison (fun p ↦ (ψ p).toOpenPartialHomeomorph)
                (manifoldMorseIndex I f ·) (fun _ ↦ manifoldMorseIndex_le_finrank) hε.le hball
                hψ).hom.comp g)
              (range (morseCellComparison (fun p ↦ (ψ p).toOpenPartialHomeomorph)
                (manifoldMorseIndex I f ·) (fun _ ↦ manifoldMorseIndex_le_finrank) hε.le hball
                hψ)) := by
  obtain ⟨ε, hε, hεδ, hband, ψ, hψ, hψp⟩ :=
    hf.exists_admissible_morseCharts hδ hcompact (U := fun _ ↦ univ) fun _ _ ↦ Filter.univ_mem
  simp only [forall_and] at hψp
  obtain ⟨hmem, -, hzero, hball, hψf⟩ := hψp
  have : Finite ↥(criticalPoints I f ∩ f ⁻¹' {c}) :=
    ((hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))).to_subtype
  exact ⟨ε, hε, hεδ, ψ, hψ, fun p ↦ ⟨hmem p, hzero p⟩, _, _,
    TauCeti.exists_morseCellAttachment_deformation hf.contMDiff ψ hψ _
      (fun _ ↦ manifoldMorseIndex_le_finrank) hε hball hψf
      (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
        (preimage_mono (Icc_subset_Icc (by linarith) (by linarith))))
      fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx.1, hband hx⟩, hmem _⟩⟩

end Deformation

end TauCeti
