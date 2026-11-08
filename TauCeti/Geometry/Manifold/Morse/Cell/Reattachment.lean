/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.Annulus
public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
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
attaching sphere `‖x‖ = 1`, because `H i (0, ·) = α₁ i`.

Composed with the handle-to-cell comparison `Φ₀ : M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i} → M_{c+ε}`
(`TauCeti.morseCellComparison`), the map `E` reads `K i` along the map
`x ↦ (τ x, ρ x)` from the disc to the cylinder `I × D^{k i}`, where `τ x = 1` and `ρ x = 2x` for
`‖x‖ ≤ 1/2` and `τ x = 2 - 2‖x‖` and `ρ x = x/‖x‖` for `1/2 ≤ ‖x‖`. On the boundary sphere this
map is `x ↦ (0, x)`, so the straight-line homotopy to `x ↦ (0, x)` in the convex cylinder fixes
the boundary sphere. Through `K i`, it gives a homotopy from `Φ₀ ∘ E` to `Φ₁` relative to the
lower sublevel (`TauCeti.homotopicRel_morseCellReattachment_comp_morseCellComparison`).

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

section Cylinder

open unitInterval

variable {k : ℕ}

/-- The radial part `x ↦ x / max(1/2, ‖x‖)` of the map from the disc to the cylinder: it is `2x`
on the disc of radius `1/2` and `x / ‖x‖` outside it. It is the end of the radial push
`TauCeti.TopCat.diskRadialPush` with radius `1/2`. -/
private def diskRadial (w : TopCat.disk.{u} k) : TopCat.disk.{u} k :=
  TopCat.diskRadialPush k (by norm_num : (0 : ℝ) ≤ 1 / 2) (1, w)

private theorem continuous_diskRadial : Continuous (diskRadial.{u} (k := k)) :=
  (TopCat.diskRadialPush k _).continuous.comp (continuous_const.prodMk continuous_id)

private theorem coe_diskRadial_of_norm_le {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ 1 / 2) :
    (diskRadial w).down.1 = (2 : ℝ) • w.down.1 := by
  rw [diskRadial, TopCat.coe_diskRadialPush_one_of_norm_le _ hw]
  norm_num

/-- The point `2 • (1/2) • θ = θ` of the boundary sphere, for `θ` on the boundary sphere. -/
private theorem diskRadial_half_smul (θ : TopCat.diskBoundary.{u} k)
    (hθ : (1 / 2 : ℝ) • θ.down.1 ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :
    diskRadial (ULift.up ⟨(1 / 2 : ℝ) • θ.down.1, hθ⟩) = TopCat.diskBoundaryInclusion k θ := by
  have hθ' : ‖(1 / 2 : ℝ) • θ.down.1‖ ≤ 1 / 2 :=
    mem_closedBall_zero_iff.1 (TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ)
  refine ULift.ext (Subtype.ext ?_)
  rw [coe_diskRadial_of_norm_le (w := ULift.up ⟨(1 / 2 : ℝ) • θ.down.1, hθ⟩) hθ', smul_smul,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  exact (TopCat.coe_diskBoundaryInclusion_apply_down _ _).symm

/-- The time part `x ↦ 2 - 2‖x‖`, clamped to `[0, 1]`, of the map from the disc to the cylinder:
the reversed radial parameter of the annulus `1/2 ≤ ‖x‖`. It is `1` on the disc of radius `1/2`
and `0` on the boundary sphere. -/
private def diskTime (w : TopCat.disk.{u} k) : I :=
  σ (TopCat.annulusParam (1 / 2) w)

private theorem continuous_diskTime : Continuous (diskTime.{u} (k := k)) :=
  continuous_symm.comp TopCat.continuous_annulusParam

private theorem diskTime_of_norm_le {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ 1 / 2) :
    diskTime w = 1 := by
  rw [diskTime, TopCat.annulusParam_of_norm_le (by norm_num) hw, symm_zero]

private theorem coe_diskTime_of_le_norm {w : TopCat.disk.{u} k} (hw : 1 / 2 ≤ ‖w.down.1‖) :
    (diskTime w : ℝ) = 2 - 2 * ‖w.down.1‖ := by
  have h := TopCat.add_one_sub_mul_annulusParam (by norm_num : (1 / 2 : ℝ) ≤ 1) hw
  rw [diskTime, coe_symm_eq]
  linarith

private theorem diskTime_diskBoundaryInclusion (s : TopCat.diskBoundary.{u} k) :
    diskTime (TopCat.diskBoundaryInclusion k s) = 0 := by
  rw [diskTime, TopCat.annulusParam_of_norm_eq_one (by norm_num)
    (TopCat.norm_diskBoundaryInclusion s), symm_one]

/-- The straight-line homotopy in the cylinder `I × D^k` from `x ↦ (diskTime x, diskRadial x)` at
time `0` to `x ↦ (0, x)` at time `1`. Its disc coordinate is the radial push
`TauCeti.TopCat.diskRadialPush` with radius `1/2`, run backwards. -/
private def diskCylinderPath (p : TopCat.disk.{u} k × I) : I × TopCat.disk.{u} k :=
  (⟨(1 - (p.2 : ℝ)) * diskTime p.1, mul_mem (symm p.2).2 (diskTime p.1).2⟩,
    TopCat.diskRadialPush k (by norm_num : (0 : ℝ) ≤ 1 / 2) (σ p.2, p.1))

private theorem continuous_diskCylinderPath : Continuous (diskCylinderPath.{u} (k := k)) := by
  have hs : Continuous fun p : TopCat.disk.{u} k × I ↦ (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  exact .prodMk ((((continuous_const.sub hs).mul (continuous_subtype_val.comp
    (continuous_diskTime.comp continuous_fst))).subtype_mk _))
    ((TopCat.diskRadialPush k _).continuous.comp
      ((continuous_symm.comp continuous_snd).prodMk continuous_fst))

private theorem diskCylinderPath_zero (w : TopCat.disk.{u} k) :
    diskCylinderPath (w, 0) = (diskTime w, diskRadial w) := by
  refine Prod.ext (Subtype.ext ?_) ?_ <;> simp [diskCylinderPath, diskRadial]

private theorem diskCylinderPath_one (w : TopCat.disk.{u} k) :
    diskCylinderPath (w, 1) = (0, w) := by
  refine Prod.ext (Subtype.ext ?_) ?_ <;> simp [diskCylinderPath]

private theorem diskCylinderPath_diskBoundaryInclusion (s : TopCat.diskBoundary.{u} k) (t : I) :
    diskCylinderPath (TopCat.diskBoundaryInclusion k s, t) =
      (0, TopCat.diskBoundaryInclusion k s) := by
  refine Prod.ext (Subtype.ext ?_) ?_
  · simp [diskCylinderPath, diskTime_diskBoundaryInclusion]
  · exact TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num) _ s

end Cylinder

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type u} {f : M → ℝ} {c ε : ℝ}

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

/-- The reattachment map on the disc of the chart index `i`: the map `x ↦ h i (2x)` into the cell
of `i` on the disc of radius `1/2`, glued to `K i` read in the annulus coordinates of the annulus
`1/2 ≤ ‖x‖`. The pieces agree on the seam `‖x‖ = 1/2` because `K i (1, ·) = χ₀ i ∘ h i` and `h i`
preserves the boundary sphere. -/
private def morseCellReattachmentFun (i : ι) :
    C(TopCat.disk.{u} (k i), morseCellAttachment φ₀ k hk hε hball₀ hf₀) :=
  (TopCat.discGlue (P := Unit) (by norm_num : (0 : ℝ) < 1 / 2)
    ⟨fun p ↦ morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i
        (h i (diskRadial (ULift.up ⟨p.2.1, closedBall_subset_closedBall (by norm_num) p.2.2⟩))),
      (morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i).hom.continuous.comp
        ((h i).hom.continuous.comp (continuous_diskRadial.comp (continuous_uliftUp.comp
          ((continuous_subtype_val.comp continuous_snd).subtype_mk _))))⟩
    ⟨fun p ↦ morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀
        ⟨K i (σ p.2.1, TopCat.diskBoundaryInclusion (k i) p.2.2), hK i _ p.2.2⟩,
      (morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀).hom.continuous.comp
        ((continuous_subtype_val.comp ((K i).continuous.comp
          ((continuous_symm.comp (continuous_fst.comp continuous_snd)).prodMk
            ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
              (continuous_snd.comp continuous_snd))))).subtype_mk _)⟩
    fun _ θ ↦ by
      simp only [ContinuousMap.coe_mk, symm_zero, diskRadial_half_smul]
      obtain ⟨s, hs⟩ := hh i ⟨θ, rfl⟩
      -- At the seam `K i (1, ·) = χ₀ i ∘ h i`, and `h i` lands on the boundary sphere.
      have hseam : (⟨K i (1, TopCat.diskBoundaryInclusion (k i) θ), hK i _ θ⟩ :
          {x | f x ≤ c - ε}) = (φ₀ i).morseAttachingMap (hk i) hε (hball₀ i) (hf₀ i) s := by
        refine Subtype.ext ?_
        simp only [ContinuousMap.Homotopy.apply_one, TopCat.hom_comp, ContinuousMap.comp_apply,
          ← hs]
        exact OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion
          (hball₀ i) (hf₀ i) (hk i) hε s
      rw [hseam, ← hs, ← ConcreteCategory.comp_apply,
        morseAttachingMap_comp_morseCellAttachmentIncl, ConcreteCategory.comp_apply]).curry ()

private theorem morseCellReattachmentFun_of_norm_le (i : ι) {w : TopCat.disk.{u} (k i)}
    (hw : ‖w.down.1‖ ≤ 1 / 2) :
    morseCellReattachmentFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK i w =
      morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i (h i (diskRadial w)) := by
  rw [morseCellReattachmentFun, ContinuousMap.curry_apply,
    TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw]
  rfl

private theorem morseCellReattachmentFun_of_le_norm (i : ι) {w : TopCat.disk.{u} (k i)}
    (hw : 1 / 2 ≤ ‖w.down.1‖) :
    morseCellReattachmentFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK i w =
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀
        ⟨K i (diskTime w, TopCat.diskBoundaryInclusion (k i)
          (TopCat.annulusDir (by norm_num) ⟨w, hw⟩)), hK i _ _⟩ := by
  rw [morseCellReattachmentFun, ContinuousMap.curry_apply,
    TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw]
  rfl

/-- On the boundary sphere of the disc of `i`, the reattachment map is the attaching map `α₁ i`. -/
private theorem morseCellReattachmentFun_diskBoundaryInclusion (i : ι)
    (s : TopCat.diskBoundary.{u} (k i)) :
    morseCellReattachmentFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK i
        (TopCat.diskBoundaryInclusion (k i) s) =
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀
        ((φ₁ i).morseAttachingMap (hk i) hε (hball₁ i) (hf₁ i) s) := by
  have hw : 1 / 2 ≤ ‖(TopCat.diskBoundaryInclusion (k i) s).down.1‖ := by
    rw [TopCat.norm_diskBoundaryInclusion]; norm_num
  rw [morseCellReattachmentFun_of_le_norm (hw := hw)]
  refine congrArg _ (Subtype.ext ?_)
  simp only [TopCat.annulusDir_diskBoundaryInclusion, diskTime_diskBoundaryInclusion,
    ContinuousMap.Homotopy.apply_zero]
  exact OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion
    (hball₁ i) (hf₁ i) (hk i) hε s

/-- **The reattachment map** `E : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}` of a
family of self-maps `h i` of the disc pairs `(D^{k i}, ∂D^{k i})` and of homotopies of maps of pairs
`K i : χ₁ i ≃ χ₀ i ∘ h i` between the characteristic maps of the cells of the chart families `φ₁`
and `φ₀`. It is the identity on the lower sublevel `M_{c-ε}`; on the disc of `i` it sends `x` to
the point `h i (2x)` of the disc of `i` when `‖x‖ ≤ 1/2`, and to the point
`K i (2 - 2‖x‖, x/‖x‖)` of `M_{c-ε}` when `1/2 ≤ ‖x‖`. -/
def morseCellReattachment : morseCellAttachment φ₁ k hk hε hball₁ hf₁ ⟶
    morseCellAttachment φ₀ k hk hε hball₀ hf₀ :=
  morseCellAttachmentDesc φ₁ k hk hε hball₁ hf₁ (morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀)
    (fun i ↦ TopCat.ofHom
      (morseCellReattachmentFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK i))
    fun i ↦ by
      ext s
      exact (morseCellReattachmentFun_diskBoundaryInclusion φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh
        K hK i s).symm

/-- The reattachment map is the identity on the lower sublevel. -/
@[reassoc (attr := simp)]
theorem morseCellAttachmentIncl_comp_morseCellReattachment :
    morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ ≫
        morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK =
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ :=
  morseCellAttachmentIncl_desc _ _ _ _ _ _ _ _ _

/-- The reattachment map sends a point of the lower sublevel to itself. -/
@[simp]
theorem morseCellReattachment_morseCellAttachmentIncl (x : {x | f x ≤ c - ε}) :
    morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK
        (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ x) =
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ x := by
  rw [← ConcreteCategory.comp_apply, morseCellAttachmentIncl_comp_morseCellReattachment]

private theorem morseCellReattachment_morseCellAttachmentCell (i : ι) (w : TopCat.disk.{u} (k i)) :
    morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK
        (morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w) =
      morseCellReattachmentFun φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK i w := by
  exact ConcreteCategory.congr_hom (morseCellAttachmentCell_desc _ _ _ _ _ _ _ _ _ i) w

/-- On the disc of radius `1/2` of the cell of `i`, the reattachment map is `x ↦ h i (2x)`, read in
the cell of `i`. -/
theorem morseCellReattachment_morseCellAttachmentCell_of_norm_le (i : ι)
    {w v : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 2) (hv : v.down.1 = (2 : ℝ) • w.down.1) :
    morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK
        (morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w) =
      morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i (h i v) := by
  rw [morseCellReattachment_morseCellAttachmentCell, morseCellReattachmentFun_of_norm_le (hw := hw)]
  exact congrArg _ (congrArg _ (ULift.ext (Subtype.ext (hv ▸ coe_diskRadial_of_norm_le hw))))

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
  have ht' : diskTime w = t := Subtype.ext ((coe_diskTime_of_le_norm hw).trans ht.symm)
  have hs' : TopCat.annulusDir (by norm_num) ⟨w, hw⟩ = s :=
    ULift.ext (Subtype.ext ((TopCat.coe_annulusDir _ _).trans hs.symm))
  subst ht' hs'
  rw [morseCellReattachment_morseCellAttachmentCell, morseCellReattachmentFun_of_le_norm (hw := hw)]

/-- On the cell of `i`, the reattachment map followed by the handle-to-cell comparison `Φ₀` is
`K i` read along the map `x ↦ (diskTime x, diskRadial x)` from the disc to the cylinder. -/
private theorem coe_morseCellComparison_morseCellReattachment_morseCellAttachmentCell (i : ι)
    (w : TopCat.disk.{u} (k i)) :
    (morseCellComparison φ₀ k hk hε hball₀ hf₀
        (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK
          (morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w)) : M) =
      K i (diskTime w, diskRadial w) := by
  rw [morseCellReattachment_morseCellAttachmentCell]
  by_cases hw : 1 / 2 ≤ ‖w.down.1‖
  · rw [morseCellReattachmentFun_of_le_norm (hw := hw),
      coe_morseCellComparison_morseCellAttachmentIncl]
    exact congrArg (fun v ↦ (K i (diskTime w, v) : M))
      (TopCat.diskBoundaryInclusion_annulusDir _ ⟨w, hw⟩)
  · rw [morseCellReattachmentFun_of_norm_le (hw := (not_le.1 hw).le),
      coe_morseCellComparison_morseCellAttachmentCell, diskTime_of_norm_le (not_le.1 hw).le,
      ContinuousMap.Homotopy.apply_one, TopCat.hom_comp, ContinuousMap.comp_apply]
    exact (OpenPartialHomeomorph.coe_morseCharacteristicMap_apply (hball₀ i) (hf₀ i) (hk i) hε
      _).symm

/-- **`Φ₀ ∘ E` is homotopic to `Φ₁` relative to the lower sublevel.** The reattachment map followed
by the handle-to-cell comparison `Φ₀` is homotopic to the handle-to-cell comparison `Φ₁`, by a
homotopy fixing the lower sublevel `M_{c-ε}`. -/
theorem homotopicRel_morseCellReattachment_comp_morseCellComparison :
    (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hh K hK ≫
        morseCellComparison φ₀ k hk hε hball₀ hf₀).hom.HomotopicRel
      (morseCellComparison φ₁ k hk hε hball₁ hf₁).hom
      (range (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁)) := by
  have hab : c - ε ≤ c + ε := by linarith
  -- The homotopy is constant on the lower sublevel. On the disc of `i` it is the homotopy `K i`
  -- read along the straight-line homotopy in the cylinder `I × D^{k i}` from
  -- `x ↦ (diskTime x, diskRadial x)` to `x ↦ (0, x)`, which fixes the boundary sphere.
  let G := morseCellAttachmentProdDesc φ₁ k hk hball₁ hf₁ hε
    ((sublevelInclusion f (c - ε) (c + ε) hab).comp ContinuousMap.snd)
    (fun i ↦ ⟨fun p ↦ K i (diskCylinderPath (p.2, p.1)),
      (K i).continuous.comp (continuous_diskCylinderPath.comp continuous_swap)⟩)
    fun i t s ↦ Subtype.ext <| by
      rw [ContinuousMap.coe_mk, diskCylinderPath_diskBoundaryInclusion,
        ContinuousMap.Homotopy.apply_zero, ContinuousMap.comp_apply, ContinuousMap.snd_apply,
        coe_sublevelInclusion_apply]
      exact OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion
        (hball₁ i) (hf₁ i) (hk i) hε s
  have hG₀ (t : I) (x : {x | f x ≤ c - ε}) :
      (G (t, morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ x) : M) = x :=
    (congrArg Subtype.val (morseCellAttachmentProdDesc_morseCellAttachmentIncl ..)).trans
      (coe_sublevelInclusion_apply f hab x)
  have hG₁ (t : I) (i : ι) (w : TopCat.disk.{u} (k i)) :
      G (t, morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w) = K i (diskCylinderPath (w, t)) :=
    morseCellAttachmentProdDesc_morseCellAttachmentCell ..
  have hcover :=
    range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ₁ k hk hball₁ hf₁ hε
  refine ⟨{ toFun := G
            continuous_toFun := G.continuous
            map_zero_left a := ?_
            map_one_left a := ?_
            prop' t a ha := ?_ }⟩
  -- At time `0`, on the disc of `i` the cylinder path is `x ↦ (diskTime x, diskRadial x)`, along
  -- which `K i` is `Φ₀ ∘ E` on both pieces of `E`.
  · rw [TopCat.hom_comp, ContinuousMap.comp_apply]
    obtain ⟨x, rfl⟩ | ha := hcover.symm ▸ mem_univ a
    · refine Subtype.ext ?_
      rw [hG₀, morseCellReattachment_morseCellAttachmentIncl,
        coe_morseCellComparison_morseCellAttachmentIncl]
    obtain ⟨i, w, rfl⟩ := mem_iUnion.1 ha
    refine Subtype.ext ?_
    rw [hG₁, diskCylinderPath_zero,
      coe_morseCellComparison_morseCellReattachment_morseCellAttachmentCell]
  -- At time `1` the cylinder path is `x ↦ (0, x)`, along which `K i` is `χ₁ i`.
  · obtain ⟨x, rfl⟩ | ha := hcover.symm ▸ mem_univ a
    · refine Subtype.ext ?_
      rw [hG₀, coe_morseCellComparison_morseCellAttachmentIncl]
    obtain ⟨i, w, rfl⟩ := mem_iUnion.1 ha
    refine Subtype.ext ?_
    rw [hG₁, diskCylinderPath_one, coe_morseCellComparison_morseCellAttachmentCell,
      ContinuousMap.Homotopy.apply_zero]
    exact OpenPartialHomeomorph.coe_morseCharacteristicMap_apply (hball₁ i) (hf₁ i) (hk i) hε _
  -- On the lower sublevel the homotopy is constant.
  · obtain ⟨x, rfl⟩ := ha
    refine Subtype.ext ?_
    rw [ContinuousMap.coe_mk, TopCat.hom_comp, ContinuousMap.comp_apply, hG₀,
      morseCellReattachment_morseCellAttachmentIncl,
      coe_morseCellComparison_morseCellAttachmentIncl]

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
compact band `f⁻¹[c - ε, c + ε]`. Given self-maps `h i` of the disc pairs and homotopies of maps of
pairs `K i : χ₁ i ≃ χ₀ i ∘ h i` between the characteristic maps of the cells, the reattachment map
`E : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}` is a homotopy equivalence relative to
the lower sublevel: it has a homotopy inverse which is the identity on `M_{c-ε}`, and both
composites are homotopic to the identities relative to `M_{c-ε}`. -/
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
    (hh : ∀ i, MapsTo (h i) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))))
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
          hf₀ hf₁ h hh K hK ≫ E').hom.HomotopicRel (ContinuousMap.id _)
        (range (morseCellAttachmentIncl (fun i ↦ (ψ₁ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₁)) ∧
      (E' ≫ morseCellReattachment (fun i ↦ (ψ₀ i).toOpenPartialHomeomorph)
          (fun i ↦ (ψ₁ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          (fun i ↦ (hball₁ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₀ hf₁ h hh K hK).hom.HomotopicRel (ContinuousMap.id _)
        (range (morseCellAttachmentIncl (fun i ↦ (ψ₀ i).toOpenPartialHomeomorph) k hk hε.le
          (fun i ↦ (hball₀ i).trans' (closedBall_subset_closedBall (Real.sqrt_le_sqrt_two_mul ε)))
          hf₀)) := by
  obtain ⟨g₀, hg₀, -⟩ :=
    exists_morseCellAttachment_deformation hfs ψ₀ hψ₀ k hk hε hball₀ hf₀ hcompact hcrit₀
  obtain ⟨g₁, hg₁, hΦ₁⟩ :=
    exists_morseCellAttachment_deformation hfs ψ₁ hψ₁ k hk hε hball₁ hf₁ hcompact hcrit₁
  exact exists_homotopicRel_morseCellReattachment_comp_of_leftInverse _ _ k hk hε.le _ _ hf₀ hf₁ h
    hh K hK g₀ hg₀ g₁ hg₁ hΦ₁

end Smooth

end TauCeti
