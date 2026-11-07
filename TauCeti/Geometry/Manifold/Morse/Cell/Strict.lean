/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Reattachment

/-!
# Strict reattachment of Morse cells

Passing a critical level `c` of a Morse function attaches one cell at each critical point on the
level (`TauCeti.morseCellAttachment`), along attaching maps `αⱼ i : ∂D^{k i} → M_{c-ε}` that
depend on the chosen normal-form charts `φⱼ`, where `M_a = {f ≤ a}`. In general two choices are
compared by Milnor's reattachment map (`TauCeti.morseCellReattachment`), which is only a homotopy
equivalence relative to the lower sublevel. This file treats the case where the attaching maps
agree on the nose up to homeomorphisms of the discs.

Let `h i : D^{k i} ≅ D^{k i}` and `h∂ i : ∂D^{k i} ≅ ∂D^{k i}` be homeomorphisms forming an
isomorphism of the pair `(D^{k i}, ∂D^{k i})`, and suppose `α₁ i = α₀ i ∘ h∂ i`. Then the map
`id ⊔ h : M_{c-ε} ∪_{α₁} ⨆ᵢ D^{k i} → M_{c-ε} ∪_{α₀} ⨆ᵢ D^{k i}`, which is the identity on the
lower sublevel and `h i` on the disc of `i`, is a homeomorphism (`TauCeti.morseCellAttachmentIso`,
in `Cell/Comparison.lean`). If moreover the characteristic maps satisfy `χ₁ i = χ₀ i ∘ h i`, it
intertwines the handle-to-cell comparisons `Φ₀` and `Φ₁`
(`TauCeti.morseCellAttachmentIso_hom_comp_morseCellComparison`).

This homeomorphism represents the relative homotopy class of Milnor's reattachment map whenever the
homotopy of pairs `K i : χ₁ i ≃ χ₀ i ∘ h i` is stationary on the boundary sphere
(`TauCeti.homotopicRel_morseCellReattachment_morseCellAttachmentIso`): there the reattachment map
is `id ⊔ (h ∘ ρ)` for the radial map `ρ` of the disc pushing the shell `1/2 ≤ ‖x‖` onto the
boundary sphere, and the radial push from the identity to `ρ` fixes that sphere.

## Main results

* `TauCeti.morseCellAttachmentIso_hom_comp_morseCellComparison`: the homeomorphism `id ⊔ h` is
  compatible with the handle-to-cell comparisons when the characteristic maps are strictly
  related.
* `TauCeti.homotopicRel_morseCellReattachment_morseCellAttachmentIso`: a reattachment map whose
  homotopy is stationary on the boundary spheres is homotopic to `id ⊔ h` relative to the lower
  sublevel.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open Function Set Metric Topology CategoryTheory

universe u

namespace TauCeti

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type u} {f : M → ℝ} {c ε : ℝ}

variable (φ₀ φ₁ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball₀ : ∀ i, closedBall 0 √ε ⊆ (φ₀ i).target)
  (hball₁ : ∀ i, closedBall 0 √ε ⊆ (φ₁ i).target)
  (hf₀ : ∀ i, ∀ y ∈ (φ₀ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₀ i y j ^ 2)
  (hf₁ : ∀ i, ∀ y ∈ (φ₁ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₁ i y j ^ 2)
  (h : ∀ i, TopCat.disk.{u} (k i) ≅ TopCat.disk.{u} (k i))
  (hb : ∀ i, TopCat.diskBoundary.{u} (k i) ≅ TopCat.diskBoundary.{u} (k i))
  (hhb : ∀ i, (hb i).hom ≫ TopCat.diskBoundaryInclusion (k i) =
    TopCat.diskBoundaryInclusion (k i) ≫ (h i).hom)
  (hα : ∀ i, (φ₁ i).morseAttachingMap (hk i) hε (hball₁ i) (hf₁ i) =
    (hb i).hom ≫ (φ₀ i).morseAttachingMap (hk i) hε (hball₀ i) (hf₀ i))

include hhb in
/-- Along the boundary homeomorphisms, the attaching maps of the charts `φ₀` followed by the lower
sublevel inclusion are the boundary inclusions followed by `h i` and the cells. -/
private theorem hom_comp_morseAttachingMap_comp_morseCellAttachmentIncl (i : ι) :
    (hb i).hom ≫ (φ₀ i).morseAttachingMap (hk i) hε (hball₀ i) (hf₀ i) ≫
        morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ =
      TopCat.diskBoundaryInclusion (k i) ≫ (h i).hom ≫
        morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i := by
  rw [morseAttachingMap_comp_morseCellAttachmentIncl, ← Category.assoc, hhb, Category.assoc]

/-- The adjunction homeomorphism sends a point of the lower sublevel to itself. -/
@[simp]
theorem morseCellAttachmentIso_hom_morseCellAttachmentIncl (x : {x | f x ≤ c - ε}) :
    (morseCellAttachmentIso φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hb hhb hα).hom
        (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ x) =
      morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ x := by
  rw [← ConcreteCategory.comp_apply, morseCellAttachmentIncl_comp_morseCellAttachmentIso_hom]

/-- The adjunction homeomorphism sends the point `w` of the disc of `i` to the point `h i w` of
the disc of `i`. -/
@[simp]
theorem morseCellAttachmentIso_hom_morseCellAttachmentCell (i : ι) (w : TopCat.disk.{u} (k i)) :
    (morseCellAttachmentIso φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hb hhb hα).hom
        (morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w) =
      morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i ((h i).hom w) := by
  rw [← ConcreteCategory.comp_apply, morseCellAttachmentCell_comp_morseCellAttachmentIso_hom,
    ConcreteCategory.comp_apply]

/-- If the characteristic maps are strictly related, `χ₁ i = χ₀ i ∘ h i`, then the adjunction
homeomorphism intertwines the handle-to-cell comparisons: `Φ₀ ∘ (id ⊔ h) = Φ₁`. -/
theorem morseCellAttachmentIso_hom_comp_morseCellComparison
    (hχ : ∀ i, (φ₁ i).morseCharacteristicMap (hk i) hε (hball₁ i) (hf₁ i) =
      (h i).hom ≫ (φ₀ i).morseCharacteristicMap (hk i) hε (hball₀ i) (hf₀ i)) :
    (morseCellAttachmentIso φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hb hhb hα).hom ≫
        morseCellComparison φ₀ k hk hε hball₀ hf₀ =
      morseCellComparison φ₁ k hk hε hball₁ hf₁ :=
  morseCellAttachment_hom_ext φ₁ k hk hball₁ hf₁ hε (by simp) fun i ↦ by simp [hχ]

section Reattachment

open unitInterval

/-- At its end, the radial push with radius `1/2` sends a point `x` of the disc with
`1/2 ≤ ‖x‖` to `x / ‖x‖`. -/
private theorem coe_diskRadialPush_one_of_le_norm {m : ℕ} {w : TopCat.disk.{u} m}
    (hw : 1 / 2 ≤ ‖w.down.1‖) :
    (TopCat.diskRadialPush m (by norm_num : (0 : ℝ) ≤ 1 / 2) (1, w)).down.1 =
      ‖w.down.1‖⁻¹ • w.down.1 := by
  rw [TopCat.coe_diskRadialPush_apply_down, radialPush_one, radialRetraction_of_le_norm hw,
    smul_smul]
  congr 1
  field_simp

/-- At its end, the radial push with radius `1/2` sends a point `x` of the disc with
`‖x‖ ≤ 1/2` to `2x`. -/
private theorem coe_diskRadialPush_one_of_norm_le {m : ℕ} {w : TopCat.disk.{u} m}
    (hw : ‖w.down.1‖ ≤ 1 / 2) :
    (TopCat.diskRadialPush m (by norm_num : (0 : ℝ) ≤ 1 / 2) (1, w)).down.1 =
      (2 : ℝ) • w.down.1 := by
  rw [TopCat.coe_diskRadialPush_apply_down, radialPush_one, radialRetraction_of_norm_le hw]
  norm_num

variable
  (K : ∀ i, ((φ₁ i).morseCharacteristicMap (hk i) hε (hball₁ i) (hf₁ i)).hom.Homotopy
    ((h i).hom ≫ (φ₀ i).morseCharacteristicMap (hk i) hε (hball₀ i) (hf₀ i)).hom)
  (hK : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
    f (K i (t, TopCat.diskBoundaryInclusion (k i) s)) ≤ c - ε)

/-- If the homotopy `K i` is stationary on the boundary sphere, then the reattachment map is
`h i ∘ ρ` on the disc of `i`, where `ρ` is the end of the radial push with radius `1/2`. -/
private theorem morseCellReattachment_morseCellAttachmentCell_of_stationary
    (hKb : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
      (K i (t, TopCat.diskBoundaryInclusion (k i) s) : M) =
        (φ₀ i).morseAttachingMap (hk i) hε (hball₀ i) (hf₀ i) ((hb i).hom s))
    (i : ι) (w : TopCat.disk.{u} (k i)) :
    morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ (fun i ↦ (h i).hom)
        (fun i ↦ Function.Semiconj.mapsTo_range (ConcreteCategory.congr_hom (hhb i))) K hK
        (morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w) =
      morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i
        ((h i).hom (TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 2) (1, w))) := by
  by_cases hw : 1 / 2 ≤ ‖w.down.1‖
  · have hw₁ : ‖w.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 w.down.2
    -- The point `x / ‖x‖` of the boundary sphere reached by the radial push.
    set s : TopCat.diskBoundary.{u} (k i) :=
      ULift.up ⟨‖w.down.1‖⁻¹ • w.down.1, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (by linarith)]⟩
    have hs : TopCat.diskBoundaryInclusion (k i) s =
        TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 2) (1, w) :=
      ULift.ext (Subtype.ext ((TopCat.coe_diskBoundaryInclusion_apply_down (k i) s).trans
        (coe_diskRadialPush_one_of_le_norm hw).symm))
    obtain ⟨t, ht⟩ : ∃ t : I, (t : ℝ) = 2 - 2 * ‖w.down.1‖ :=
      ⟨⟨2 - 2 * ‖w.down.1‖, by linarith, by linarith⟩, rfl⟩
    rw [morseCellReattachment_morseCellAttachmentCell_of_le_norm φ₀ φ₁ k hk hε hball₀ hball₁ hf₀
      hf₁ _ _ K hK i hw ht (s := s) rfl, ← hs]
    exact (congrArg _ (Subtype.ext (hKb i t s))).trans (ConcreteCategory.congr_hom
      (hom_comp_morseAttachingMap_comp_morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ h hb hhb i) s)
  · exact morseCellReattachment_morseCellAttachmentCell_of_norm_le φ₀ φ₁ k hk hε hball₀ hball₁ hf₀
      hf₁ _ _ K hK i (not_le.1 hw).le (coe_diskRadialPush_one_of_norm_le (not_le.1 hw).le)

/-- **The strict comparison represents the reattachment map.** If the homotopies of pairs
`K i : χ₁ i ≃ χ₀ i ∘ h i` are stationary on the boundary spheres, where they are
`α₁ i = α₀ i ∘ hb i`, then Milnor's reattachment map is homotopic to the adjunction homeomorphism
`id ⊔ h` relative to the lower sublevel. -/
theorem homotopicRel_morseCellReattachment_morseCellAttachmentIso
    (hKb : ∀ i t (s : TopCat.diskBoundary.{u} (k i)),
      (K i (t, TopCat.diskBoundaryInclusion (k i) s) : M) =
        (φ₀ i).morseAttachingMap (hk i) hε (hball₀ i) (hf₀ i) ((hb i).hom s)) :
    (morseCellReattachment φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ (fun i ↦ (h i).hom)
        (fun i ↦ Function.Semiconj.mapsTo_range (ConcreteCategory.congr_hom (hhb i))) K
        hK).hom.HomotopicRel
      (morseCellAttachmentIso φ₀ φ₁ k hk hε hball₀ hball₁ hf₀ hf₁ h hb hhb hα).hom.hom
      (range (morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁)) := by
  have hr : (0 : ℝ) ≤ 1 / 2 := by norm_num
  -- The homotopy is constant on the lower sublevel, and on the disc of `i` it is `h i` composed
  -- with the radial push, which fixes the boundary sphere.
  let G := morseCellAttachmentProdDesc φ₁ k hk hball₁ hf₁ hε
    ((morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀).hom.comp ContinuousMap.snd)
    (fun i ↦ (morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i).hom.comp
      ((h i).hom.hom.comp (TopCat.diskRadialPush (k i) hr)))
    fun i t s ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply,
        TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num),
        ContinuousMap.comp_apply, ContinuousMap.snd_apply, hα]
      exact (ConcreteCategory.congr_hom
        (hom_comp_morseAttachingMap_comp_morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ h hb hhb i)
        s).symm
  have hG₀ (t : I) (x : {x | f x ≤ c - ε}) :
      G (t, morseCellAttachmentIncl φ₁ k hk hε hball₁ hf₁ x) =
        morseCellAttachmentIncl φ₀ k hk hε hball₀ hf₀ x :=
    morseCellAttachmentProdDesc_morseCellAttachmentIncl ..
  have hG₁ (t : I) (i : ι) (w : TopCat.disk.{u} (k i)) :
      G (t, morseCellAttachmentCell φ₁ k hk hε hball₁ hf₁ i w) =
        morseCellAttachmentCell φ₀ k hk hε hball₀ hf₀ i
          ((h i).hom (TopCat.diskRadialPush (k i) hr (t, w))) :=
    morseCellAttachmentProdDesc_morseCellAttachmentCell ..
  have hcover :=
    range_morseCellAttachmentIncl_union_iUnion_range_morseCellAttachmentCell φ₁ k hk hball₁ hf₁ hε
  refine ContinuousMap.HomotopicRel.symm ⟨
    { toFun := G
      continuous_toFun := G.continuous
      map_zero_left a := ?_
      map_one_left a := ?_
      prop' t a ha := ?_ }⟩
  -- At time `0` the radial push is the identity, so the homotopy is `id ⊔ h`.
  · obtain ⟨x, rfl⟩ | ha := hcover.symm ▸ mem_univ a
    · exact (hG₀ 0 x).trans (morseCellAttachmentIso_hom_morseCellAttachmentIncl ..).symm
    obtain ⟨i, w, rfl⟩ := mem_iUnion.1 ha
    refine (hG₁ 0 i w).trans ?_
    rw [TopCat.diskRadialPush_zero]
    exact (morseCellAttachmentIso_hom_morseCellAttachmentCell ..).symm
  -- At time `1` it is the reattachment map.
  · obtain ⟨x, rfl⟩ | ha := hcover.symm ▸ mem_univ a
    · exact (hG₀ 1 x).trans (morseCellReattachment_morseCellAttachmentIncl ..).symm
    obtain ⟨i, w, rfl⟩ := mem_iUnion.1 ha
    exact (hG₁ 1 i w).trans (morseCellReattachment_morseCellAttachmentCell_of_stationary φ₀ φ₁ k
      hk hε hball₀ hball₁ hf₀ hf₁ h hb hhb K hK hKb i w).symm
  -- On the lower sublevel the homotopy is constant.
  · obtain ⟨x, rfl⟩ := ha
    exact (hG₀ t x).trans (morseCellAttachmentIso_hom_morseCellAttachmentIncl ..).symm

end Reattachment

end TauCeti
