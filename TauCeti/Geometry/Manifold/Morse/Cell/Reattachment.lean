/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCellAttachment
public import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Reattaching Morse cells along a homotopy of characteristic maps

Passing a critical level `c` of a Morse function attaches one cell at each critical point on the
level (`TauCeti.morseCellAttachment`), but the attaching maps depend on the chosen normal-form
charts. This file compares the attachments built from two chart families `φ₀` and `φ₁` with the
same indices, following Milnor's Lemma 3.6.

Write `M_a = {f ≤ a}`, `χⱼ i : (D^{k i}, ∂D^{k i}) → (M_{c+ε}, M_{c-ε})` for the characteristic
maps of the cells and `αⱼ i` for their attaching maps. Suppose given, for each chart index `i`, a
self-map `h i` of the pair `(D^{k i}, ∂D^{k i})` and a homotopy of maps of pairs
`K i : χ₁ i ≃ χ₀ i ∘ h i`, that is, a homotopy whose restriction `H i` to the boundary sphere stays
in the lower sublevel `M_{c-ε}`. Then `H i` is a homotopy from `α₁ i` to `α₀ i ∘ h i`, and the
*reattachment map*

`E : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}`

(`TauCeti.morseCellReattachment`) is the identity on `M_{c-ε}`, sends a point `x` of the disc of
`i` with `‖x‖ ≤ 1/2` to the point `h i (2x)` of the disc of `i`, and sends a point with
`1/2 ≤ ‖x‖` to the point `H i (2 - 2‖x‖, x/‖x‖)` of `M_{c-ε}`. These pieces agree on the seam
`‖x‖ = 1/2`, because `H i (1, ·) = α₀ i ∘ h i` and `h i` preserves the boundary sphere, and on the
attaching sphere `‖x‖ = 1`, because `H i (0, ·) = α₁ i`. It is the fiberwise reattachment map
`TauCeti.fiberwiseCellReattachment` over a point. When `0 < ε`, any self-map `h i` of the
disc admitting such a homotopy `K i` preserves the boundary sphere: at the end of `K i` the sphere
is sent by `χ₀ i ∘ h i` into `M_{c-ε}`, which `χ₀ i` meets exactly on the sphere.

Composed with the handle-to-cell comparison `Φ₀ : M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i} → M_{c+ε}`
(`TauCeti.morseCellComparison`), the map `E` reads `K i` along the map
`x ↦ (τ x, ρ x)` from the disc to the cylinder `I × D^{k i}`, where `τ x = 1` and `ρ x = 2x` for
`‖x‖ ≤ 1/2` and `τ x = 2 - 2‖x‖` and `ρ x = x/‖x‖` for `1/2 ≤ ‖x‖`. On the boundary sphere this
map is `x ↦ (0, x)`, so the straight-line homotopy to `x ↦ (0, x)` in the convex cylinder fixes
the boundary sphere. Through `K i`, it gives a homotopy from `Φ₀ ∘ E` to `Φ₁` relative to the
lower sublevel (`TauCeti.homotopicRel_morseCellReattachment_comp_morseCellComparison`), which is
the homotopy `TauCeti.fiberwiseCellReattachmentHomotopy` over a point.

Consequently, if `g₀` is a left inverse of `Φ₀`, then `E` is homotopic to `g₀ ∘ Φ₁` relative to the
lower sublevel. Milnor's cell attachment theorem supplies such left inverses for admissible charts
(`TauCeti.exists_morseCellAttachment_deformation`), with `Φⱼ ∘ gⱼ` homotopic to the identity
relative to the image of `Φⱼ`. From this:

* `E` is a homotopy equivalence whose homotopy inverse and both homotopies fix the lower sublevel;
* the relative homotopy class of `E` does not depend on the homotopies `K i`;
* for three chart families the reattachment maps compose up to homotopy relative to the lower
  sublevel.

## Main definitions

* `TauCeti.morseCellReattachment`: the reattachment map
  `M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}` of a family of homotopies of pairs
  `χ₁ i ≃ χ₀ i ∘ h i`.

## Main results

* `TauCeti.homotopicRel_morseCellReattachment_comp_morseCellComparison`: `Φ₀ ∘ E` is homotopic to
  `Φ₁` relative to the lower sublevel.
* `TauCeti.homotopicRel_morseCellReattachment_of_leftInverse`: for a left inverse `g₀` of `Φ₀`,
  `E` is homotopic to `g₀ ∘ Φ₁` relative to the lower sublevel.
* `TauCeti.homotopicRel_morseCellReattachment_morseCellReattachment`: two reattachment maps
  between the same attachments are homotopic relative to the lower sublevel, provided `Φ₀` has a
  left inverse.
* `TauCeti.homotopicRel_morseCellReattachment_comp_morseCellReattachment`: reattachment maps
  compose up to homotopy relative to the lower sublevel, provided `Φ₀` has a left inverse.
* `TauCeti.exists_homotopicRel_morseCellReattachment_comp`: **Milnor's Lemma 3.6 for Morse
  cells.** For admissible chart families, the reattachment map is a homotopy equivalence relative
  to the lower sublevel.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Metric Topology CategoryTheory
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type u} {f : M → ℝ} {c ε : ℝ}

section Fiberwise

/-! The cell attachment of a chart family is the fiberwise cell attachment over a point, with the
lower sublevel `M_{c-ε}` viewed inside the upper sublevel `M_{c+ε}`. -/

variable (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
  (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)

/-- The inclusion of the lower sublevel `M_{c-ε}` over a point, into `PUnit × M_{c-ε}` with
`M_{c-ε}` viewed inside `M_{c+ε}`. -/
private def morseFiberwiseBase :
    C({x | f x ≤ c - ε}, PUnit.{u + 1} × {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) :=
  ⟨fun x ↦ (PUnit.unit, ⟨⟨x, (mem_ofPred.1 x.2).trans
      ((sub_le_self c hε).trans (le_add_of_nonneg_right hε))⟩, x.2⟩),
    continuous_const.prodMk ((continuous_subtype_val.subtype_mk _).subtype_mk _)⟩

/-- The projection of `PUnit × M_{c-ε}`, with `M_{c-ε}` viewed inside `M_{c+ε}`, to the lower
sublevel `M_{c-ε}`: the inverse of `TauCeti.morseFiberwiseBase`. -/
private def morseFiberwiseBaseInv :
    C(PUnit.{u + 1} × {y : {x | f x ≤ c + ε} | f y ≤ c - ε}, {x | f x ≤ c - ε}) :=
  ⟨fun x ↦ ⟨x.2.1.1, x.2.2⟩,
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

private theorem morseFiberwiseBaseInv_morseFiberwiseBase (p : PUnit.{u + 1})
    (x : {x | f x ≤ c - ε}) : morseFiberwiseBaseInv (p, (morseFiberwiseBase hε x).2) = x :=
  rfl

private theorem coe_morseFiberwiseBaseInv (p : PUnit.{u + 1})
    (y : {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) :
    (morseFiberwiseBaseInv (p, y) : M) = y :=
  rfl

/-- The attaching maps of the cells of `φ`, as families over a point. -/
private def morseFiberwiseAttachingMap (i : ι) :
    C(PUnit.{u + 1} × TopCat.diskBoundary.{u} (k i), {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) :=
  ContinuousMap.snd.comp ((morseFiberwiseBase hε).comp
    (((φ i).morseAttachingMap (hk i) hε (hball i) (hf i)).hom.comp ContinuousMap.snd))

/-- The characteristic maps of the cells of `φ`, as families over a point. -/
private def morseFiberwiseCharacteristicMap (i : ι) :
    C(PUnit.{u + 1} × TopCat.disk.{u} (k i), {x | f x ≤ c + ε}) :=
  ((φ i).morseCharacteristicMap (hk i) hε (hball i) (hf i)).hom.comp ContinuousMap.snd

private theorem morseFiberwiseCharacteristicMap_apply (i : ι)
    (x : PUnit.{u + 1} × TopCat.disk.{u} (k i)) :
    morseFiberwiseCharacteristicMap φ k hk hε hball hf i x =
      (φ i).morseCharacteristicMap (hk i) hε (hball i) (hf i) x.2 :=
  rfl

private theorem coe_morseFiberwiseAttachingMap (i : ι) (p : PUnit.{u + 1})
    (s : TopCat.diskBoundary.{u} (k i)) :
    (morseFiberwiseAttachingMap φ k hk hε hball hf i (p, s)).1.1 =
      ((φ i).morseAttachingMap (hk i) hε (hball i) (hf i) s).1 :=
  rfl

private theorem morseFiberwiseBaseInv_morseFiberwiseAttachingMap (i : ι) (p q : PUnit.{u + 1})
    (s : TopCat.diskBoundary.{u} (k i)) :
    morseFiberwiseBaseInv (q, morseFiberwiseAttachingMap φ k hk hε hball hf i (p, s)) =
      (φ i).morseAttachingMap (hk i) hε (hball i) (hf i) s :=
  rfl

private theorem morseFiberwiseCharacteristicMap_diskBoundaryInclusion (i : ι) (p : PUnit.{u + 1})
    (s : TopCat.diskBoundary.{u} (k i)) :
    morseFiberwiseCharacteristicMap φ k hk hε hball hf i (p, TopCat.diskBoundaryInclusion (k i) s) =
      morseFiberwiseAttachingMap φ k hk hε hball hf i (p, s) :=
  Subtype.ext <| by
    rw [morseFiberwiseCharacteristicMap_apply, coe_morseFiberwiseAttachingMap]
    exact OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion (hball i) (hf i)
      (hk i) hε s

/-- The map from the cell attachment of `φ` to the fiberwise cell attachment over a point. -/
private def morseCellAttachmentToFiberwise :
    morseCellAttachment φ k hk hε hball hf ⟶
      fiberwiseCellAttachment (morseFiberwiseAttachingMap φ k hk hε hball hf) :=
  morseCellAttachmentDesc φ k hk hε hball hf
    (TopCat.ofHom (morseFiberwiseBase hε) ≫ fiberwiseCellAttachmentIncl _)
    (fun i ↦ TopCat.ofHom (ContinuousMap.const _ PUnit.unit |>.prodMk (ContinuousMap.id _)) ≫
      fiberwiseCellAttachmentCell _ i) fun i ↦ by
    ext s
    exact (fiberwiseCellAttachmentCell_diskBoundaryInclusion _ i PUnit.unit s).symm

/-- The map from the fiberwise cell attachment over a point to the cell attachment of `φ`. -/
private def morseCellAttachmentOfFiberwise :
    fiberwiseCellAttachment (morseFiberwiseAttachingMap φ k hk hε hball hf) ⟶
      morseCellAttachment φ k hk hε hball hf :=
  fiberwiseCellAttachmentDesc _
    (TopCat.ofHom morseFiberwiseBaseInv ≫ morseCellAttachmentIncl φ k hk hε hball hf)
    (fun i ↦ TopCat.ofHom ContinuousMap.snd ≫ morseCellAttachmentCell φ k hk hε hball hf i)
    fun i p s ↦ by
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopCat.ofHom_apply,
        TopCat.ofHom_apply, ContinuousMap.snd_apply,
        morseFiberwiseBaseInv_morseFiberwiseAttachingMap]
      exact (ConcreteCategory.congr_hom
        (morseAttachingMap_comp_morseCellAttachmentIncl φ k hk hball hf hε i) s).symm

private theorem morseCellAttachmentToFiberwise_morseCellAttachmentIncl (x : {x | f x ≤ c - ε}) :
    morseCellAttachmentToFiberwise φ k hk hε hball hf
        (morseCellAttachmentIncl φ k hk hε hball hf x) =
      fiberwiseCellAttachmentIncl _ (morseFiberwiseBase hε x) :=
  ConcreteCategory.congr_hom (morseCellAttachmentIncl_desc _ _ _ _ _ _ _ _ _) x

private theorem morseCellAttachmentToFiberwise_morseCellAttachmentCell (i : ι)
    (w : TopCat.disk.{u} (k i)) :
    morseCellAttachmentToFiberwise φ k hk hε hball hf
        (morseCellAttachmentCell φ k hk hε hball hf i w) =
      fiberwiseCellAttachmentCell _ i (PUnit.unit, w) :=
  ConcreteCategory.congr_hom (morseCellAttachmentCell_desc _ _ _ _ _ _ _ _ _ i) w

private theorem morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentIncl
    (x : PUnit.{u + 1} × {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) :
    morseCellAttachmentOfFiberwise φ k hk hε hball hf (fiberwiseCellAttachmentIncl _ x) =
      morseCellAttachmentIncl φ k hk hε hball hf (morseFiberwiseBaseInv x) :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentIncl_desc _ _ _ _) x

private theorem morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentCell (i : ι)
    (x : PUnit.{u + 1} × TopCat.disk.{u} (k i)) :
    morseCellAttachmentOfFiberwise φ k hk hε hball hf (fiberwiseCellAttachmentCell _ i x) =
      morseCellAttachmentCell φ k hk hε hball hf i x.2 :=
  ConcreteCategory.congr_hom (fiberwiseCellAttachmentCell_desc _ _ _ _ i) x

private theorem morseCellAttachmentOfFiberwise_morseCellAttachmentToFiberwise
    (y : morseCellAttachment φ k hk hε hball hf) :
    morseCellAttachmentOfFiberwise φ k hk hε hball hf
      (morseCellAttachmentToFiberwise φ k hk hε hball hf y) = y := by
  obtain ⟨x, rfl⟩ | hy :=
    (range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ k hk hball hf
      hε).symm ▸ mem_univ y
  · rw [morseCellAttachmentToFiberwise_morseCellAttachmentIncl,
      morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentIncl,
      morseFiberwiseBaseInv_morseFiberwiseBase]
  · obtain ⟨i, w, rfl⟩ := mem_iUnion.1 hy
    rw [morseCellAttachmentToFiberwise_morseCellAttachmentCell,
      morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentCell]

/-- The comparison map of `φ` is the comparison map of the fiberwise cell attachment over a point,
read in `M_{c+ε}`. -/
private theorem morseCellComparison_morseCellAttachmentOfFiberwise
    (y : fiberwiseCellAttachment (morseFiberwiseAttachingMap φ k hk hε hball hf)) :
    morseCellComparison φ k hk hε hball hf (morseCellAttachmentOfFiberwise φ k hk hε hball hf y) =
      (fiberwiseCellComparison _ (morseFiberwiseCharacteristicMap φ k hk hε hball hf)
        (morseFiberwiseCharacteristicMap_diskBoundaryInclusion φ k hk hε hball hf) y).2 := by
  refine fiberwiseCellAttachment_induction _ (fun x ↦ ?_) (fun i x ↦ ?_) y
  · rw [morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentIncl,
      fiberwiseCellComparison_fiberwiseCellAttachmentIncl]
    exact Subtype.ext (coe_morseCellComparison_morseCellAttachmentIncl _ _ _ _ _ hε _)
  · rw [morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentCell,
      fiberwiseCellComparison_fiberwiseCellAttachmentCell]
    exact ConcreteCategory.congr_hom
      (morseCellAttachmentCell_comp_morseCellComparison _ _ _ _ _ hε i) x.2

end Fiberwise

section Reattachment

open unitInterval

variable (φ₀ φ₁ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball₀ : ∀ i, closedBall 0 √ε ⊆ (φ₀ i).target)
  (hball₁ : ∀ i, closedBall 0 √ε ⊆ (φ₁ i).target)
  (hf₀ : ∀ i, ∀ y ∈ (φ₀ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₀ i y j ^ 2)
  (hf₁ : ∀ i, ∀ y ∈ (φ₁ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₁ i y j ^ 2)
  (h : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
  (hh : ∀ i, MapsTo (h i) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, ((φ₁ i).morseCharacteristicMap (hk i) hε (hball₁ i) (hf₁ i)).hom.Homotopy
    (h i ≫ (φ₀ i).morseCharacteristicMap (hk i) hε (hball₀ i) (hf₀ i)).hom)
  (hK : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
    f (K i (t, TopCat.diskBoundaryInclusion (k i) s)) ≤ c - ε)

/-- The homotopy `K i : χ₁ i ≃ χ₀ i ∘ h i`, as a family over a point. -/
private def morseFiberwiseHomotopy (i : ι) :
    (morseFiberwiseCharacteristicMap φ₁ k hk hε hball₁ hf₁ i).Homotopy
      ((morseFiberwiseCharacteristicMap φ₀ k hk hε hball₀ hf₀ i).comp
        (ContinuousMap.fst.prodMk ((h i).hom.comp ContinuousMap.snd))) where
  toFun q := K i (q.1, q.2.2)
  continuous_toFun :=
    (K i).continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  map_zero_left q := (K i).apply_zero q.2
  map_one_left q := (K i).apply_one q.2

private theorem morseFiberwiseHomotopy_apply (i : ι) (t : I)
    (x : PUnit.{u + 1} × TopCat.disk.{u} (k i)) :
    morseFiberwiseHomotopy φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K i (t, x) = K i (t, x.2) :=
  rfl

include hK in
/-- The homotopies `K i`, as families over a point, keep the boundary spheres in `M_{c-ε}`. -/
private theorem morseFiberwiseHomotopy_mem (i : ι) (t : I) (p : PUnit.{u + 1})
    (s : TopCat.diskBoundary.{u} (k i)) :
    morseFiberwiseHomotopy φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K i
        (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
      {y : {x | f x ≤ c + ε} | f y ≤ c - ε} := by
  rw [morseFiberwiseHomotopy_apply]
  exact hK i t s

include hh in
/-- The self-maps `h i` of the disc pairs, as families over a point, preserve the boundary
spheres. -/
private theorem mapsTo_morseFiberwise (i : ι) (p : PUnit.{u + 1}) :
    MapsTo (fun w ↦ ((h i).hom.comp ContinuousMap.snd) (p, w))
      (range (TopCat.diskBoundaryInclusion (k i))) (range (TopCat.diskBoundaryInclusion (k i))) :=
  fun _ hw ↦ hh i hw

/-- The reattachment map over a point, between the fiberwise cell attachments of `φ₁` and `φ₀`. -/
private def morseFiberwiseReattachment :
    fiberwiseCellAttachment (morseFiberwiseAttachingMap φ₁ k hk hε hball₁ hf₁) ⟶
      fiberwiseCellAttachment (morseFiberwiseAttachingMap φ₀ k hk hε hball₀ hf₀) :=
  fiberwiseCellReattachment (morseFiberwiseAttachingMap φ₀ k hk hε hball₀ hf₀)
    (morseFiberwiseAttachingMap φ₁ k hk hε hball₁ hf₁)
    (morseFiberwiseCharacteristicMap φ₀ k hk hε hball₀ hf₀)
    (morseFiberwiseCharacteristicMap φ₁ k hk hε hball₁ hf₁)
    (morseFiberwiseCharacteristicMap_diskBoundaryInclusion φ₀ k hk hε hball₀ hf₀)
    (morseFiberwiseCharacteristicMap_diskBoundaryInclusion φ₁ k hk hε hball₁ hf₁)
    (fun i ↦ (h i).hom.comp ContinuousMap.snd) (mapsTo_morseFiberwise k h hh)
    (morseFiberwiseHomotopy φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K)
    (morseFiberwiseHomotopy_mem φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK)

/-- **The reattachment map** `E : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}` of a
family of self-maps `h i` of the disc pairs `(D^{k i}, ∂D^{k i})` and of homotopies of maps of pairs
`K i : χ₁ i ≃ χ₀ i ∘ h i` between the characteristic maps of the cells of the chart families `φ₁`
and `φ₀`. It is the identity on the lower sublevel `M_{c-ε}`; on the disc of `i` it sends `x` to
the point `h i (2x)` of the disc of `i` when `‖x‖ ≤ 1/2`, and to the point
`K i (2 - 2‖x‖, x/‖x‖)` of `M_{c-ε}` when `1/2 ≤ ‖x‖`. It is the fiberwise reattachment map
`TauCeti.fiberwiseCellReattachment` over a point. -/
def morseCellReattachment : morseCellAttachment φ₁ k hk hε hball₁ hf₁ ⟶
    morseCellAttachment φ₀ k hk hε hball₀ hf₀ :=
  morseCellAttachmentToFiberwise φ₁ k hk hε hball₁ hf₁ ≫
    morseFiberwiseReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK ≫
      morseCellAttachmentOfFiberwise φ₀ k hk hε hball₀ hf₀

/-- The reattachment map sends a point of the lower sublevel to itself. -/
@[simp]
theorem morseCellReattachment_morseCellAttachmentIncl (x : {x | f x ≤ c - ε}) :
    morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK
        (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ x) =
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ x := by
  rw [morseCellReattachment, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    morseCellAttachmentToFiberwise_morseCellAttachmentIncl, morseFiberwiseReattachment,
    fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
    morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentIncl,
    morseFiberwiseBaseInv_morseFiberwiseBase]

/-- The reattachment map is the identity on the lower sublevel. -/
@[reassoc (attr := simp)]
theorem morseCellAttachmentIncl_comp_morseCellReattachment :
    morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ ≫
        morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK =
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ := by
  ext x
  exact morseCellReattachment_morseCellAttachmentIncl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K
    hK x

/-- On the disc of radius `1/2` of the cell of `i`, the reattachment map is `x ↦ h i (2x)`, read in
the cell of `i`. -/
theorem morseCellReattachment_morseCellAttachmentCell_of_norm_le (i : ι)
    {w v : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 2) (hv : v.down.1 = (2 : ℝ) • w.down.1) :
    morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK
        (morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w) =
      morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i (h i v) := by
  rw [morseCellReattachment, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    morseCellAttachmentToFiberwise_morseCellAttachmentCell, morseFiberwiseReattachment,
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le (hw := hw) (hv := hv),
    morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentCell, ContinuousMap.comp_apply,
    ContinuousMap.snd_apply]

/-- Outside the disc of radius `1/2` of the cell of `i`, the reattachment map is
`x ↦ K i (2 - 2‖x‖, x/‖x‖)`, read in the lower sublevel. -/
theorem morseCellReattachment_morseCellAttachmentCell_of_le_norm (i : ι)
    {w : TopCat.disk.{u} (k i)} (hw : 1 / 2 ≤ ‖w.down.1‖) {t : I}
    (ht : (t : ℝ) = 2 - 2 * ‖w.down.1‖) {s : TopCat.diskBoundary.{u} (k i)}
    (hs : s.down.1 = ‖w.down.1‖⁻¹ • w.down.1) :
    morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK
        (morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w) =
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀
        ⟨K i (t, TopCat.diskBoundaryInclusion (k i) s), hK i t s⟩ := by
  rw [morseCellReattachment, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    morseCellAttachmentToFiberwise_morseCellAttachmentCell, morseFiberwiseReattachment,
    fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm (hw := hw) (ht := ht)
      (hs := hs),
    morseCellAttachmentOfFiberwise_fiberwiseCellAttachmentIncl]
  refine congrArg _ (Subtype.ext ?_)
  rw [coe_morseFiberwiseBaseInv, Subtype.coe_mk, morseFiberwiseHomotopy_apply]

/-- **`Φ₀ ∘ E` is homotopic to `Φ₁` relative to the lower sublevel.** The reattachment map followed
by the handle-to-cell comparison `Φ₀` is homotopic to the handle-to-cell comparison `Φ₁`, by a
homotopy fixing the lower sublevel `M_{c-ε}`: the homotopy
`TauCeti.fiberwiseCellReattachmentHomotopy` over a point. -/
theorem homotopicRel_morseCellReattachment_comp_morseCellComparison :
    (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK ≫
        morseCellComparison φ₀ k hk hε hball₀ hf₀).hom.HomotopicRel
      (morseCellComparison φ₁ k hk hε hball₁ hf₁).hom
      (range (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁)) := by
  have hF := ((ContinuousMap.HomotopicRel.comp_continuousMap
    ⟨fiberwiseCellReattachmentHomotopy (morseFiberwiseAttachingMap φ₀ k hk hε hball₀ hf₀)
      (morseFiberwiseAttachingMap φ₁ k hk hε hball₁ hf₁)
      (morseFiberwiseCharacteristicMap φ₀ k hk hε hball₀ hf₀)
      (morseFiberwiseCharacteristicMap φ₁ k hk hε hball₁ hf₁)
      (morseFiberwiseCharacteristicMap_diskBoundaryInclusion φ₀ k hk hε hball₀ hf₀)
      (morseFiberwiseCharacteristicMap_diskBoundaryInclusion φ₁ k hk hε hball₁ hf₁)
      (fun i ↦ (h i).hom.comp ContinuousMap.snd) (mapsTo_morseFiberwise k h hh)
      (morseFiberwiseHomotopy φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K)
      (morseFiberwiseHomotopy_mem φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h K hK)⟩
      ContinuousMap.snd).precomp
    (morseCellAttachmentToFiberwise φ₁ k hk hε hball₁ hf₁).hom).mono
    (T := range (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁)) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨_, (morseCellAttachmentToFiberwise_morseCellAttachmentIncl _ _ _ _ _ _ x).symm⟩)
  convert hF using 1 <;> refine ContinuousMap.ext fun y ↦ ?_
  · exact morseCellComparison_morseCellAttachmentOfFiberwise φ₀ k hk hε hball₀ hf₀ _
  · conv_lhs => rw [← morseCellAttachmentOfFiberwise_morseCellAttachmentToFiberwise φ₁ k hk hε
      hball₁ hf₁ y]
    exact morseCellComparison_morseCellAttachmentOfFiberwise φ₁ k hk hε hball₁ hf₁ _

/-- For a left inverse `g₀` of the handle-to-cell comparison `Φ₀`, the reattachment map is
homotopic to `g₀ ∘ Φ₁` relative to the lower sublevel. -/
theorem homotopicRel_morseCellReattachment_of_leftInverse
    (g₀ : C(TopCat.of {x | f x ≤ c + ε}, morseCellAttachment φ₀ k hk hε hball₀ hf₀))
    (hg₀ : LeftInverse g₀ (morseCellComparison φ₀ k hk hε hball₀ hf₀)) :
    (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK).hom.HomotopicRel
      (g₀.comp (morseCellComparison φ₁ k hk hε hball₁ hf₁).hom)
      (range (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁)) := by
  have hE : g₀.comp (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK ≫
      morseCellComparison φ₀ k hk hε hball₀ hf₀).hom =
        (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK).hom :=
    ContinuousMap.ext fun a ↦ hg₀ _
  rw [← hE]
  exact (homotopicRel_morseCellReattachment_comp_morseCellComparison φ₀ φ₁ k hk hε hball₀ hball₁
    hf₀ hf₁ h hh K hK).comp_continuousMap g₀

/-- **The reattachment map does not depend on the homotopy of characteristic maps.** Two
reattachment maps between the same attachments, built from any self-maps of the disc pairs and any
homotopies of maps of pairs, are homotopic relative to the lower sublevel, provided the target
handle-to-cell comparison `Φ₀` has a left inverse. -/
theorem homotopicRel_morseCellReattachment_morseCellReattachment
    (h' : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
    (hh' : ∀ i, MapsTo (h' i) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (K' : ∀ i, ((φ₁ i).morseCharacteristicMap (hk i) hε (hball₁ i) (hf₁ i)).hom.Homotopy
      (h' i ≫ (φ₀ i).morseCharacteristicMap (hk i) hε (hball₀ i) (hf₀ i)).hom)
    (hK' : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
      f (K' i (t, TopCat.diskBoundaryInclusion (k i) s)) ≤ c - ε)
    (g₀ : C(TopCat.of {x | f x ≤ c + ε}, morseCellAttachment φ₀ k hk hε hball₀ hf₀))
    (hg₀ : LeftInverse g₀ (morseCellComparison φ₀ k hk hε hball₀ hf₀)) :
    (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK).hom.HomotopicRel
      (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h' hh' K' hK').hom
      (range (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁)) :=
  (homotopicRel_morseCellReattachment_of_leftInverse φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK
    g₀ hg₀).trans (homotopicRel_morseCellReattachment_of_leftInverse φ₀ φ₁ k hk hε hball₀ hball₁
      hf₀ hf₁ h' hh' K' hK' g₀ hg₀).symm

end Reattachment

section Comparison

variable (φ₀ φ₁ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball₀ : ∀ i, closedBall 0 √ε ⊆ (φ₀ i).target)
  (hball₁ : ∀ i, closedBall 0 √ε ⊆ (φ₁ i).target)
  (hf₀ : ∀ i, ∀ y ∈ (φ₀ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₀ i y j ^ 2)
  (hf₁ : ∀ i, ∀ y ∈ (φ₁ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₁ i y j ^ 2)

/-- The handle-to-cell comparisons of two chart families agree on the lower sublevel. -/
private theorem morseCellComparison_morseCellAttachmentIncl_eq (x : {x | f x ≤ c - ε}) :
    morseCellComparison φ₀ k hk hε hball₀ hf₀ (morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ x) =
      morseCellComparison φ₁ k hk hε hball₁ hf₁ (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ x) :=
  Subtype.ext ((coe_morseCellComparison_morseCellAttachmentIncl _ _ _ _ _ _ x).trans
    (coe_morseCellComparison_morseCellAttachmentIncl _ _ _ _ _ _ x).symm)

/-- A left inverse of `Φ₁` sends the image under `Φ₀` of a point of the lower sublevel back to that
point. -/
private theorem leftInverse_morseCellComparison_morseCellAttachmentIncl
    {g₁ : C(TopCat.of {x | f x ≤ c + ε}, morseCellAttachment φ₁ k hk hε hball₁ hf₁)}
    (hg₁ : LeftInverse g₁ (morseCellComparison φ₁ k hk hε hball₁ hf₁)) (x : {x | f x ≤ c - ε}) :
    g₁ (morseCellComparison φ₀ k hk hε hball₀ hf₀
        (morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ x)) =
      morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ x := by
  rw [morseCellComparison_morseCellAttachmentIncl_eq φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁, hg₁]

/-- If `Φ₁ ∘ g₁` is homotopic to the identity relative to the image of `Φ₁`, then for any `g₀` the
map `g₀ ∘ Φ₁ ∘ g₁ ∘ Φ₂` is homotopic to
`g₀ ∘ Φ₂` relative to the lower sublevel, for every third chart family `φ₂`. -/
private theorem homotopicRel_comp_morseCellComparison_comp
    (φ₂ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hball₂ : ∀ i, closedBall 0 √ε ⊆ (φ₂ i).target)
    (hf₂ : ∀ i, ∀ y ∈ (φ₂ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₂ i y j ^ 2)
    (g₀ : C(TopCat.of {x | f x ≤ c + ε}, morseCellAttachment φ₀ k hk hε hball₀ hf₀))
    (g₁ : C(TopCat.of {x | f x ≤ c + ε}, morseCellAttachment φ₁ k hk hε hball₁ hf₁))
    (hΦ₁ : (ContinuousMap.id _).HomotopicRel
      ((morseCellComparison φ₁ k hk hε hball₁ hf₁).hom.comp g₁)
      (range (morseCellComparison φ₁ k hk hε hball₁ hf₁))) :
    (g₀.comp ((morseCellComparison φ₁ k hk hε hball₁ hf₁).hom.comp
        (g₁.comp (morseCellComparison φ₂ k hk hε hball₂ hf₂).hom))).HomotopicRel
      (g₀.comp (morseCellComparison φ₂ k hk hε hball₂ hf₂).hom)
      (range (morseCellAttachmentIncl φ₂ k hk hε hball₂ hf₂)) := by
  refine ((hΦ₁.precomp (morseCellComparison φ₂ k hk hε hball₂ hf₂).hom).mono
    ?_).symm.comp_continuousMap g₀
  rintro _ ⟨x, rfl⟩
  exact ⟨morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ x,
    (morseCellComparison_morseCellAttachmentIncl_eq φ₂ φ₁ k hk hε hball₂ hball₁ hf₂ hf₁ x).symm⟩

/-- **Reattachment maps compose up to homotopy.** For three chart families `φ₀`, `φ₁`, `φ₂` and
reattachment maps `E₀₁`, `E₁₂`, `E₀₂` between their attachments, `E₀₁ ∘ E₁₂` is homotopic to `E₀₂`
relative to the lower sublevel, provided `Φ₀` has a left inverse. -/
theorem homotopicRel_morseCellReattachment_comp_morseCellReattachment
    (φ₂ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hball₂ : ∀ i, closedBall 0 √ε ⊆ (φ₂ i).target)
    (hf₂ : ∀ i, ∀ y ∈ (φ₂ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₂ i y j ^ 2)
    (h₀₁ : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
    (hh₀₁ : ∀ i, MapsTo (h₀₁ i) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (K₀₁ : ∀ i, ((φ₁ i).morseCharacteristicMap (hk i) hε (hball₁ i) (hf₁ i)).hom.Homotopy
      (h₀₁ i ≫ (φ₀ i).morseCharacteristicMap (hk i) hε (hball₀ i) (hf₀ i)).hom)
    (hK₀₁ : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
      f (K₀₁ i (t, TopCat.diskBoundaryInclusion (k i) s)) ≤ c - ε)
    (h₁₂ : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
    (hh₁₂ : ∀ i, MapsTo (h₁₂ i) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (K₁₂ : ∀ i, ((φ₂ i).morseCharacteristicMap (hk i) hε (hball₂ i) (hf₂ i)).hom.Homotopy
      (h₁₂ i ≫ (φ₁ i).morseCharacteristicMap (hk i) hε (hball₁ i) (hf₁ i)).hom)
    (hK₁₂ : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
      f (K₁₂ i (t, TopCat.diskBoundaryInclusion (k i) s)) ≤ c - ε)
    (h₀₂ : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
    (hh₀₂ : ∀ i, MapsTo (h₀₂ i) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
    (K₀₂ : ∀ i, ((φ₂ i).morseCharacteristicMap (hk i) hε (hball₂ i) (hf₂ i)).hom.Homotopy
      (h₀₂ i ≫ (φ₀ i).morseCharacteristicMap (hk i) hε (hball₀ i) (hf₀ i)).hom)
    (hK₀₂ : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
      f (K₀₂ i (t, TopCat.diskBoundaryInclusion (k i) s)) ≤ c - ε)
    (g₀ : C(TopCat.of {x | f x ≤ c + ε}, morseCellAttachment φ₀ k hk hε hball₀ hf₀))
    (hg₀ : LeftInverse g₀ (morseCellComparison φ₀ k hk hε hball₀ hf₀)) :
    (morseCellReattachment φ₁ φ₂ k hk hε hball₁ hball₂ hf₁ hf₂ h₁₂ hh₁₂ K₁₂ hK₁₂ ≫
        morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h₀₁ hh₀₁ K₀₁
          hK₀₁).hom.HomotopicRel
      (morseCellReattachment φ₀ φ₂ k hk hε hball₀ hball₂ hf₀ hf₂ h₀₂ hh₀₂ K₀₂ hK₀₂).hom
      (range (morseCellAttachmentIncl φ₂ k hk hε hball₂ hf₂)) := by
  -- `E₀₁ ∘ E₁₂ ≃ g₀ ∘ Φ₁ ∘ E₁₂ ≃ g₀ ∘ Φ₂ ≃ E₀₂`.
  have h₁ := ((homotopicRel_morseCellReattachment_of_leftInverse φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁
    h₀₁ hh₀₁ K₀₁ hK₀₁ g₀ hg₀).precomp
      (morseCellReattachment φ₁ φ₂ k hk hε hball₁ hball₂ hf₁ hf₂ h₁₂ hh₁₂ K₁₂ hK₁₂).hom).mono
      (T := range (morseCellAttachmentIncl φ₂ k hk hε hball₂ hf₂)) (by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, (morseCellReattachment_morseCellAttachmentIncl φ₁ φ₂ k hk hε hball₁ hball₂ hf₁
          hf₂ h₁₂ hh₁₂ K₁₂ hK₁₂ x).symm⟩)
  exact h₁.trans (((homotopicRel_morseCellReattachment_comp_morseCellComparison φ₁ φ₂ k hk hε hball₁
    hball₂ hf₁ hf₂ h₁₂ hh₁₂ K₁₂ hK₁₂).comp_continuousMap g₀).trans
      (homotopicRel_morseCellReattachment_of_leftInverse φ₀ φ₂ k hk hε hball₀ hball₂ hf₀ hf₂ h₀₂
        hh₀₂ K₀₂ hK₀₂ g₀ hg₀).symm)

variable (h : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
  (hh : ∀ i, MapsTo (h i) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, ((φ₁ i).morseCharacteristicMap (hk i) hε (hball₁ i) (hf₁ i)).hom.Homotopy
    (h i ≫ (φ₀ i).morseCharacteristicMap (hk i) hε (hball₀ i) (hf₀ i)).hom)
  (hK : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
    f (K i (t, TopCat.diskBoundaryInclusion (k i) s)) ≤ c - ε)

/-- **The reattachment map is a homotopy equivalence relative to the lower sublevel.** If both
handle-to-cell comparisons `Φⱼ` have left inverses `gⱼ`, and `Φ₁ ∘ g₁` is homotopic to the
identity relative to the image of `Φ₁`, then the reattachment map `E` has a homotopy inverse `E'`
which is the identity on the lower sublevel, with `E' ∘ E` and `E ∘ E'` homotopic to the identities
relative to the lower sublevel. The inverse is `g₁ ∘ Φ₀`. -/
theorem exists_homotopicRel_morseCellReattachment_comp_of_leftInverse
    (g₀ : C(TopCat.of {x | f x ≤ c + ε}, morseCellAttachment φ₀ k hk hε hball₀ hf₀))
    (hg₀ : LeftInverse g₀ (morseCellComparison φ₀ k hk hε hball₀ hf₀))
    (g₁ : C(TopCat.of {x | f x ≤ c + ε}, morseCellAttachment φ₁ k hk hε hball₁ hf₁))
    (hg₁ : LeftInverse g₁ (morseCellComparison φ₁ k hk hε hball₁ hf₁))
    (hΦ₁ : (ContinuousMap.id _).HomotopicRel
      ((morseCellComparison φ₁ k hk hε hball₁ hf₁).hom.comp g₁)
      (range (morseCellComparison φ₁ k hk hε hball₁ hf₁))) :
    ∃ E' : morseCellAttachment φ₀ k hk hε hball₀ hf₀ ⟶ morseCellAttachment φ₁ k hk hε hball₁ hf₁,
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ ≫ E' =
          morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ ∧
        (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK ≫ E').hom.HomotopicRel
          (ContinuousMap.id _) (range (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁)) ∧
        (E' ≫ morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK).hom.HomotopicRel
          (ContinuousMap.id _) (range (morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀)) := by
  have hE := homotopicRel_morseCellReattachment_of_leftInverse φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁
    h hh K hK g₀ hg₀
  have hg₀Φ₀ : g₀.comp (morseCellComparison φ₀ k hk hε hball₀ hf₀).hom = ContinuousMap.id _ :=
    ContinuousMap.ext hg₀
  have hg₁Φ₁ : g₁.comp (morseCellComparison φ₁ k hk hε hball₁ hf₁).hom = ContinuousMap.id _ :=
    ContinuousMap.ext hg₁
  refine ⟨morseCellComparison φ₀ k hk hε hball₀ hf₀ ≫ TopCat.ofHom g₁, ?_, ?_, ?_⟩
  · ext x
    exact leftInverse_morseCellComparison_morseCellAttachmentIncl φ₀ φ₁ k hk hε hball₀ hball₁ hf₀
      hf₁ hg₁ x
  · -- `g₁ ∘ Φ₀ ∘ E ≃ g₁ ∘ Φ₁ = id`.
    rw [← hg₁Φ₁]
    exact (homotopicRel_morseCellReattachment_comp_morseCellComparison φ₀ φ₁ k hk hε hball₀ hball₁
      hf₀ hf₁ h hh K hK).comp_continuousMap g₁
  · -- `E ∘ g₁ ∘ Φ₀ ≃ g₀ ∘ Φ₁ ∘ g₁ ∘ Φ₀ ≃ g₀ ∘ Φ₀ = id`.
    rw [← hg₀Φ₀]
    refine ((hE.precomp (g₁.comp (morseCellComparison φ₀ k hk hε hball₀ hf₀).hom)).mono
      (T := range (morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀)) ?_).trans
      (homotopicRel_comp_morseCellComparison_comp φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ φ₀ hball₀ hf₀
        g₀ g₁ hΦ₁)
    rintro _ ⟨x, rfl⟩
    exact ⟨x, (leftInverse_morseCellComparison_morseCellAttachmentIncl φ₀ φ₁ k hk hε hball₀ hball₁
      hf₀ hf₁ hg₁ x).symm⟩

end Comparison

section Smooth

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M] [T2Space M]

/-- **Milnor's Lemma 3.6 for Morse cells.** Let `f` be smooth and let `ψ₀`, `ψ₁` be two families of
normal-form charts with the same indices `k i`, each with pairwise disjoint sources, targets
containing the closed ball of radius `√(2ε)`, and sources covering the critical points of the
compact band `f⁻¹[c - ε, c + ε]`. Given self-maps `h i` of the discs and homotopies of maps of
pairs `K i : χ₁ i ≃ χ₀ i ∘ h i` between the characteristic maps of the cells, the reattachment map
`E : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}` is a homotopy equivalence relative to
the lower sublevel: it has a homotopy inverse which is the identity on `M_{c-ε}`, and both
composites are homotopic to the identities relative to `M_{c-ε}`. The maps `h i` need not be given
as maps of pairs: since `0 < ε`, the homotopies `K i` force them to preserve the boundary spheres
(`TauCeti.mapsTo_range_diskBoundaryInclusion_of_homotopy_morseCharacteristicMap`). -/
theorem exists_homotopicRel_morseCellReattachment_comp [Finite ι] (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hψ₀ : Pairwise (Disjoint on fun i ↦ (ψ₀ i).source))
    (hψ₁ : Pairwise (Disjoint on fun i ↦ (ψ₁ i).source)) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 < ε) (hball₀ : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ₀ i).target)
    (hball₁ : ∀ i, closedBall 0 √(2 * ε) ⊆ (ψ₁ i).target)
    (hf₀ : ∀ i, ∀ y ∈ (ψ₀ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₀ i y j ^ 2)
    (hf₁ : ∀ i, ∀ y ∈ (ψ₁ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₁ i y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit₀ : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ₀ i).source)
    (hcrit₁ : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (ψ₁ i).source)
    (h : ∀ i, TopCat.disk.{u} (k i) ⟶ TopCat.disk.{u} (k i))
    (K : ∀ i, ((ψ₁ i).toOpenPartialHomeomorph.morseCharacteristicMap (hk i) hε.le
        ((hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        (hf₁ i)).hom.Homotopy
      (h i ≫ (ψ₀ i).toOpenPartialHomeomorph.morseCharacteristicMap (hk i) hε.le
        ((hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        (hf₀ i)).hom)
    (hK : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
      f (K i (t, TopCat.diskBoundaryInclusion (k i) s)) ≤ c - ε) :
    ∃ E' : morseCellAttachment (fun i ↦ (ψ₀ i).toOpenPartialHomeomorph) k hk hε.le
        (fun i ↦ (hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        hf₀ ⟶
      morseCellAttachment (fun i ↦ (ψ₁ i).toOpenPartialHomeomorph) k hk hε.le
        (fun i ↦ (hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
        hf₁,
      morseCellAttachmentIncl (fun i ↦ (ψ₀ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₀ ≫ E' =
        morseCellAttachmentIncl (fun i ↦ (ψ₁ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₁ ∧
      (morseCellReattachment (fun i ↦ (ψ₀ i).toOpenPartialHomeomorph)
          (fun i ↦ (ψ₁ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          (fun i ↦ (hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₀ hf₁ h
          (fun i ↦ mapsTo_range_diskBoundaryInclusion_of_homotopy_morseCharacteristicMap (hk i) hε
            ((hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
            (hf₀ i) (K i) (hK i))
          K hK ≫ E').hom.HomotopicRel (ContinuousMap.id _)
        (range (morseCellAttachmentIncl (fun i ↦ (ψ₁ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₁)) ∧
      (E' ≫ morseCellReattachment (fun i ↦ (ψ₀ i).toOpenPartialHomeomorph)
          (fun i ↦ (ψ₁ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          (fun i ↦ (hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₀ hf₁ h
          (fun i ↦ mapsTo_range_diskBoundaryInclusion_of_homotopy_morseCharacteristicMap (hk i) hε
            ((hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
            (hf₀ i) (K i) (hK i))
          K hK).hom.HomotopicRel (ContinuousMap.id _)
        (range (morseCellAttachmentIncl (fun i ↦ (ψ₀ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₀)) := by
  obtain ⟨g₀, hg₀, -⟩ :=
    exists_morseCellAttachment_deformation hfs ψ₀ hψ₀ k hk hε hball₀ hf₀ hcompact hcrit₀
  obtain ⟨g₁, hg₁, hΦ₁⟩ :=
    exists_morseCellAttachment_deformation hfs ψ₁ hψ₁ k hk hε hball₁ hf₁ hcompact hcrit₁
  exact exists_homotopicRel_morseCellReattachment_comp_of_leftInverse _ _ k hk hε.le _ _ hf₀ hf₁ h
    _ K hK g₀ hg₀ g₁ hg₁ hΦ₁

end Smooth

end TauCeti
