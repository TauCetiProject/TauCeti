/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Annulus

/-!
# Changing the width of a Morse attaching map

For one normalized Morse chart, the attaching maps at widths `0 ≤ ε₀ ≤ ε₁` are
homotopic after including the lower sublevel `{f ≤ c - ε₁}` in `{f ≤ c - ε₀}`.
The homotopy is the actual negative-coordinate annulus between the two spheres.
Only the larger disc needs to lie in the chart.

If `r` retracts `{f ≤ c - ε₀}` onto `{f ≤ c - ε₁}`, postcomposing this annulus
with `r` compares the larger attaching map with `r` composed with the smaller
one. For a smooth function on a boundaryless manifold, a compact critical-free
band supplies such a retraction and a homotopy fixing the lower sublevel.
These comparisons let one change the width before comparing two different
charts; they never require a chart to contain the other chart's larger disc.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §3, Remark 3.3.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

variable {M : Type u} [TopologicalSpace M] {n k : ℕ} {f : M → ℝ} {c ε₀ ε₁ : ℝ}
  (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
  (h₀ : 0 ≤ ε₀) (hε : ε₀ ≤ ε₁)
  (hball₁ : closedBall 0 √ε₁ ⊆ ψ.target)
  (hchart : ∀ y ∈ ψ.source,
    f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)

/-- The attaching maps of a single chart at ordered widths are homotopic in the
higher of their two lower sublevels. The homotopy runs radially from the smaller
sphere to the larger sphere. No regularity or compactness of the band is needed. -/
theorem homotopic_morseAttachingMap_comp_sublevelInclusion :
    let hball₀ : closedBall 0 √ε₀ ⊆ ψ.target :=
      (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₁
    (ψ.morseAttachingMap hk h₀ hball₀ hchart).hom.Homotopic
      ((TauCeti.sublevelInclusion f (c - ε₁) (c - ε₀) (sub_le_sub_left hε c)).comp
        (ψ.morseAttachingMap hk (h₀.trans hε) hball₁ hchart).hom) := by
  dsimp only
  by_cases h₁ : ε₁ = 0
  · have hzero : ε₀ = 0 := le_antisymm (h₁ ▸ hε) h₀
    refine ⟨(ContinuousMap.Homotopy.refl _).cast rfl ?_⟩
    ext θ
    simp only [ContinuousMap.comp_apply, TauCeti.coe_sublevelInclusion_apply]
    rw [ψ.coe_morseAttachingMap_apply, ψ.coe_morseAttachingMap_apply, hzero, h₁]
  have h₁pos : 0 < ε₁ := lt_of_le_of_ne (h₀.trans hε) (Ne.symm h₁)
  let d : I := ⟨√ε₀ / √ε₁, div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    (div_le_one (Real.sqrt_pos.mpr h₁pos)).mpr (Real.sqrt_le_sqrt hε)⟩
  have hd : ε₁ * (d : ℝ) ^ 2 = ε₀ := by
    dsimp only [d]
    rw [div_pow, Real.sq_sqrt h₀, Real.sq_sqrt h₁pos.le]
    field_simp
  let γ := ψ.morseAnnulusMap hk (h₀.trans hε) hball₁ hchart d
  let H : C(I × TopCat.diskBoundary.{u} k, {x : M | f x ≤ c - ε₀}) :=
    (ContinuousMap.inclusion (by rw [hd])).comp γ
  refine ⟨{ toContinuousMap := H, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro θ
    apply Subtype.ext
    simp only [H, ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply,
      ContinuousMap.inclusion_apply_coe, γ, coe_morseAnnulusMap_zero,
      morseCellMap_smul hk d.property.1, hd]
    exact (ψ.coe_morseAttachingMap_apply _ _ hk h₀ θ).symm
  · intro θ
    apply Subtype.ext
    simp only [H, ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply,
      ContinuousMap.inclusion_apply_coe, γ, coe_morseAnnulusMap_one,
      TauCeti.coe_sublevelInclusion_apply]

/-- Retracting the annulus compares the attaching maps at different widths in
the lower sublevel. This holds for every continuous retraction of the intervening
band, not just one obtained from a particular metric or flow. -/
theorem homotopic_morseAttachingMap_comp_retraction
    (r : C({x : M | f x ≤ c - ε₀}, {x : M | f x ≤ c - ε₁}))
    (hr : ∀ x, r (TauCeti.sublevelInclusion f (c - ε₁) (c - ε₀)
      (sub_le_sub_left hε c) x) = x) :
    let hball₀ : closedBall 0 √ε₀ ⊆ ψ.target :=
      (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₁
    (r.comp (ψ.morseAttachingMap hk h₀ hball₀ hchart).hom).Homotopic
      (ψ.morseAttachingMap hk (h₀.trans hε) hball₁ hchart).hom := by
  have H := (ContinuousMap.Homotopic.refl r).comp
    (ψ.homotopic_morseAttachingMap_comp_sublevelInclusion hk h₀ hε hball₁ hchart)
  convert H using 1
  ext θ
  simp only [ContinuousMap.comp_apply, hr]

end OpenPartialHomeomorph

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε₀ ε₁ : ℝ} {n k : ℕ}

/-- A compact critical-free band gives an actual strong deformation retraction
which compares a chart's attaching maps at two ordered widths. The homotopy of
attaching maps is in `{f ≤ c - ε₁}`, and the sublevel deformation fixes that entire
sublevel pointwise. Width zero and index zero are allowed. -/
theorem exists_morseAttachingMap_change_width (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (h₀ : 0 ≤ ε₀) (hε : ε₀ ≤ ε₁) (hball₁ : closedBall 0 √ε₁ ⊆ ψ.target)
    (hchart : ∀ y ∈ ψ.source,
      f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₁) (c - ε₀)))
    (hreg : ∀ x, c - ε₁ ≤ f x → f x ≤ c - ε₀ → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    let hball₀ : closedBall 0 √ε₀ ⊆ ψ.target :=
      (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₁
    let j := sublevelInclusion f (c - ε₁) (c - ε₀) (sub_le_sub_left hε c)
    ∃ r : C({x : M | f x ≤ c - ε₀}, {x : M | f x ≤ c - ε₁}),
      (∀ x, r (j x) = x) ∧
      Nonempty ((j.comp r).HomotopyRel (ContinuousMap.id _) {x | f x.val ≤ c - ε₁}) ∧
      (r.comp (ψ.morseAttachingMap hk h₀ hball₀ hchart).hom).Homotopic
        (ψ.morseAttachingMap hk (h₀.trans hε) hball₁ hchart).hom := by
  obtain ⟨r, hr, hR⟩ := exists_sublevelDeformation hf (sub_le_sub_left hε c) hcompact hreg
  exact ⟨r, hr, hR, ψ.homotopic_morseAttachingMap_comp_retraction hk h₀ hε hball₁ hchart r hr⟩

end TauCeti
