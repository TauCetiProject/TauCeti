/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.ContinuousMap.Defs
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.ProjIcc
import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
import TauCeti.Geometry.Manifold.LocallyFlat.Separation

/-!
# Collapsing the outside of a bicollar onto two poles

Let `σ : Sᵐ⁻¹ → Sᵐ` be an embedding of the unit sphere of a real normed space `E` of dimension
`m ≥ 2` into the unit sphere of a real inner product space `F` of dimension `m + 1`, and let
`b : Sᵐ⁻¹ × ℝ → Sᵐ` be a bicollar of `σ` (`TauCeti.IsBicollar`). Fix a pole `p ∈ Sᵐ` and a
homeomorphism `e` of `Sᵐ⁻¹` with the equator `Sᵐ ∩ (ℝ ∙ p)ᗮ`. This file constructs a continuous
surjection `g : Sᵐ → Sᵐ` which is the latitude map

`g (b (x, t)) = √(1 - t²) • e x + t • p`

on the closed collar `b (Sᵐ⁻¹ × [-1, 1])`, sends one of the two closed pieces of `Sᵐ` outside the
open collar `b (Sᵐ⁻¹ × (-1, 1))` to `p` and the other to `-p`, and is injective elsewhere
(`TauCeti.IsBicollar.exists_collapse`). Thus the only fibres of `g` with more than one point are
the two outer pieces `g⁻¹(p)` and `g⁻¹(-p)`, and `g` sends the image of `σ` onto the equator.

This is the map with which M. Brown proves the generalized Schoenflies theorem: once the two outer
pieces are known to be cellular, collapsing them identifies the closure of each complementary
domain of the image of `σ` with a closed hemisphere, hence with a closed ball.

The outside of the open collar splits into two pieces because the image of `σ` separates `Sᵐ`, by
the Jordan–Brouwer separation theorem (`TauCeti.not_isPreconnected_compl_range_sphere`), and for
`m ≥ 2` the two sides of the bicollar are connected, so they lie on opposite sides of this
separation (`TauCeti.IsBicollar.exists_isOpen_compl_range_eq_union`). The dimension hypothesis
cannot be dropped: for `m = 1` the image of `σ` is two points of the circle, and if the positive
side of the collar at one point and the negative side at the other lie in the same complementary
arc, no such map exists, since `⟪g y, p⟫` would be a continuous function without zeros on that arc
taking both signs.

## Main results

* `TauCeti.IsBicollar.exists_collapse`: the collapse of the outside of a bicollar of `Sᵐ⁻¹` in
  `Sᵐ` onto the two poles.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, proof of Theorem 5.
-/

public section

namespace TauCeti

open Function Metric Module Set Topology
open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (p : sphere (0 : F) 1)

/-! ### The latitude map -/

/-- The point of the unit sphere at height `t` over a point `u` of the equator orthogonal to `p`,
with `t` clamped to `[-1, 1]`: the pole `p` for `t ≥ 1` and `-p` for `t ≤ -1`. -/
private noncomputable def latitude (u : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) (t : ℝ) :
    sphere (0 : F) 1 :=
  ⟨√(1 - (projIcc (-1 : ℝ) 1 (by norm_num) t : ℝ) ^ 2) • ((u : (ℝ ∙ (p : F))ᗮ) : F) +
      (projIcc (-1 : ℝ) 1 (by norm_num) t : ℝ) • (p : F), by
    set s : ℝ := (projIcc (-1 : ℝ) 1 (by norm_num) t : ℝ)
    have hs : s ∈ Icc (-1 : ℝ) 1 := (projIcc (-1 : ℝ) 1 (by norm_num) t).2
    have h1 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have hu : ⟪((u : (ℝ ∙ (p : F))ᗮ) : F), (p : F)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (u : (ℝ ∙ (p : F))ᗮ).2
    have hun : ‖((u : (ℝ ∙ (p : F))ᗮ) : F)‖ = 1 := by rw [Submodule.norm_coe]; simp
    have hpn : ‖(p : F)‖ = 1 := by simp
    have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_real
      (x := √(1 - s ^ 2) • ((u : (ℝ ∙ (p : F))ᗮ) : F)) (y := s • (p : F))
      (by rw [real_inner_smul_left, real_inner_smul_right, hu, mul_zero, mul_zero])
    rw [norm_smul, norm_smul, hun, hpn, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_eq_abs] at hsq
    rw [mem_sphere_zero_iff_norm]
    refine (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 ?_
    nlinarith [Real.sq_sqrt h1, sq_abs s]⟩

private theorem continuous_latitude {X : Type*} [TopologicalSpace X]
    {u : X → sphere (0 : (ℝ ∙ (p : F))ᗮ) 1} {t : X → ℝ} (hu : Continuous u) (ht : Continuous t) :
    Continuous fun x ↦ latitude p (u x) (t x) := by
  refine Continuous.subtype_mk ?_ _
  have hs : Continuous fun x ↦ (projIcc (-1 : ℝ) 1 (by norm_num) (t x) : ℝ) :=
    continuous_subtype_val.comp (continuous_projIcc.comp ht)
  fun_prop

private theorem coe_latitude_of_mem (u : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    (latitude p u t : F) = √(1 - t ^ 2) • ((u : (ℝ ∙ (p : F))ᗮ) : F) + t • (p : F) := by
  simp [latitude, projIcc_of_mem _ ht]

private theorem latitude_of_one_le (u : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) {t : ℝ} (ht : 1 ≤ t) :
    latitude p u t = p := by
  ext1
  simp [latitude, projIcc_of_right_le _ ht]

private theorem latitude_of_le_neg_one (u : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) {t : ℝ}
    (ht : t ≤ -1) : latitude p u t = -p := by
  ext1
  simp [latitude, projIcc_of_le_left _ ht]

/-- The height of a point of the latitude map is the clamped parameter. -/
private theorem inner_latitude (u : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) (t : ℝ) :
    ⟪(latitude p u t : F), (p : F)⟫ = projIcc (-1 : ℝ) 1 (by norm_num) t := by
  have hu : ⟪((u : (ℝ ∙ (p : F))ᗮ) : F), (p : F)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (u : (ℝ ∙ (p : F))ᗮ).2
  simp [latitude, inner_add_left, inner_smul_left, hu]

private theorem inner_latitude_eq_zero_iff (u : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) (t : ℝ) :
    ⟪(latitude p u t : F), (p : F)⟫ = 0 ↔ t = 0 := by
  rw [inner_latitude]
  rcases le_or_gt t (-1) with ht | ht
  · simp [projIcc_of_le_left _ ht]
    linarith
  rcases le_or_gt 1 t with ht' | ht'
  · simp [projIcc_of_right_le _ ht']
    linarith
  · simp [projIcc_of_mem _ ⟨ht.le, ht'.le⟩]

/-- The latitude map hits a pole exactly when the parameter lies outside `(-1, 1)`. -/
private theorem latitude_mem_pair_iff (u : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) (t : ℝ) :
    latitude p u t ∈ ({p, -p} : Set (sphere (0 : F) 1)) ↔ t ∉ Ioo (-1 : ℝ) 1 := by
  refine ⟨fun h ht ↦ ?_, fun ht ↦ ?_⟩
  · have hp : ⟪(p : F), (p : F)⟫ = 1 := by simp
    have hinner := inner_latitude p u t
    rw [projIcc_of_mem _ (Ioo_subset_Icc_self ht)] at hinner
    rcases h with h | h <;> rw [h] at hinner
    · exact ht.2.ne (hinner.symm.trans hp)
    · rw [coe_neg_sphere, inner_neg_left, hp] at hinner
      exact ht.1.ne hinner
  · rcases le_or_gt t (-1) with h | h
    · exact Or.inr (latitude_of_le_neg_one p u h)
    · exact Or.inl (latitude_of_one_le p u (not_lt.1 fun h' ↦ ht ⟨h, h'⟩))

/-- Off the poles, the latitude map is injective. -/
private theorem latitude_injOn {u u' : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1} {t t' : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (h : latitude p u t = latitude p u' t') : u = u' ∧ t = t' := by
  have htt : t = t' := by
    have h₁ := inner_latitude p u t
    rw [h, inner_latitude, projIcc_of_mem _ (Ioo_subset_Icc_self ht)] at h₁
    have ht' : t' ∈ Icc (-1 : ℝ) 1 := by
      rcases le_or_gt t' (-1) with h' | h'
      · simp only [projIcc_of_le_left _ h'] at h₁
        exact absurd h₁.symm ht.1.ne'
      rcases le_or_gt 1 t' with h'' | h''
      · simp only [projIcc_of_right_le _ h''] at h₁
        exact absurd h₁ ht.2.ne'
      exact ⟨h'.le, h''.le⟩
    rw [projIcc_of_mem _ ht'] at h₁
    exact h₁.symm
  subst htt
  refine ⟨?_, rfl⟩
  have hpos : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith [ht.1, ht.2])
  have h₂ := congrArg Subtype.val h
  rw [coe_latitude_of_mem p u (Ioo_subset_Icc_self ht),
    coe_latitude_of_mem p u' (Ioo_subset_Icc_self ht), add_left_inj] at h₂
  exact Subtype.ext (Subtype.ext (smul_right_injective F hpos.ne' h₂))

/-- Every point of the unit sphere is a point of the latitude map with parameter in `[-1, 1]`; the
poles are reached over any given point `u₀` of the equator. -/
private theorem exists_latitude_eq (u₀ : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) (z : sphere (0 : F) 1) :
    ∃ u t, t ∈ Icc (-1 : ℝ) 1 ∧ latitude p u t = z := by
  set s := ⟪(z : F), (p : F)⟫ with hs_def
  have hzn : ‖(z : F)‖ = 1 := by simp
  have hpn : ‖(p : F)‖ = 1 := by simp
  have hs : |s| ≤ 1 := by simpa [hzn, hpn] using abs_real_inner_le_norm (z : F) (p : F)
  rcases eq_or_ne s 1 with h1 | h1
  · refine ⟨u₀, 1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [latitude_of_one_le p u₀ le_rfl]
    exact (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one hzn hpn).1 h1)).symm
  rcases eq_or_ne s (-1) with h2 | h2
  · refine ⟨u₀, -1, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [latitude_of_le_neg_one p u₀ le_rfl]
    ext1
    rw [coe_neg_sphere]
    have hpn' : ‖-(p : F)‖ = 1 := by rw [norm_neg, hpn]
    refine ((inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) hzn hpn').1 ?_).symm
    rw [inner_neg_right, ← hs_def, h2, neg_neg]
  -- Away from the poles, `z` is `w + s • p` with `w ⟂ p` of norm `√(1 - s²)`.
  have hs' : s ∈ Ioo (-1 : ℝ) 1 := by
    rw [abs_le] at hs
    exact ⟨lt_of_le_of_ne hs.1 (Ne.symm h2), lt_of_le_of_ne hs.2 h1⟩
  set w : F := (z : F) - s • (p : F)
  have hw : ⟪w, (p : F)⟫ = 0 := by simp [w, inner_sub_left, inner_smul_left, ← hs_def]
  have hwn : ‖w‖ = √(1 - s ^ 2) := by
    have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_real (x := w) (y := s • (p : F))
      (by simp [inner_smul_right, hw])
    rw [show w + s • (p : F) = z by simp [w], hzn, norm_smul, hpn, Real.norm_eq_abs] at hsq
    rw [← Real.sqrt_sq (norm_nonneg w)]
    congr 1
    nlinarith [sq_abs s]
  have hpos : 0 < √(1 - s ^ 2) := Real.sqrt_pos.2 (by nlinarith [hs'.1, hs'.2])
  let u : sphere (0 : (ℝ ∙ (p : F))ᗮ) 1 :=
    ⟨⟨(√(1 - s ^ 2))⁻¹ • w,
      Submodule.smul_mem _ _ (Submodule.mem_orthogonal_singleton_iff_inner_left.2 hw)⟩, by
        rw [mem_sphere_zero_iff_norm, ← Submodule.norm_coe, Submodule.coe_mk, norm_smul, hwn,
          Real.norm_of_nonneg (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne']⟩
  refine ⟨u, s, Ioo_subset_Icc_self hs', Subtype.ext ?_⟩
  rw [coe_latitude_of_mem p u (Ioo_subset_Icc_self hs')]
  simp [u, w, smul_smul, mul_inv_cancel₀ hpos.ne']

/-! ### The collapse -/

variable {E : Type*} [NormedAddCommGroup E] [Nonempty (sphere (0 : E) 1)]
  {σ : sphere (0 : E) 1 → sphere (0 : F) 1} {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}
  (hb : IsBicollar σ b) (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)
  (A : Set (sphere (0 : F) 1))

/-- The collapse map: the latitude map read through the bicollar `b` on its image, and the pole
`p` on `A` and `-p` elsewhere off that image. -/
private noncomputable def collapse (y : sphere (0 : F) 1) : sphere (0 : F) 1 := by
  classical
  exact if y ∈ range b then
    latitude p (e ((hb.isOpenEmbedding.toOpenPartialHomeomorph b).symm y).1)
      ((hb.isOpenEmbedding.toOpenPartialHomeomorph b).symm y).2
  else if y ∈ A then p else -p

private theorem collapse_apply (q : sphere (0 : E) 1 × ℝ) :
    collapse p hb e A (b q) = latitude p (e q.1) q.2 := by
  simp only [collapse, mem_range_self, ite_true]
  rw [hb.isOpenEmbedding.toOpenPartialHomeomorph_left_inv]

private theorem collapse_mem_pair {y : sphere (0 : F) 1} (hy : y ∉ range b) :
    collapse p hb e A y ∈ ({p, -p} : Set (sphere (0 : F) 1)) := by
  simp only [collapse, hy, ↓reduceIte]
  split_ifs <;> simp

variable {p hb e A} {B : Set (sphere (0 : F) 1)} (hAB : Disjoint A B)
  (hpos : MapsTo b (univ ×ˢ Ioi 0) A) (hneg : MapsTo b (univ ×ˢ Iio 0) B)

include hAB hneg in
/-- Off the closed collar, the collapse map is `p` on the positive side. -/
private theorem collapse_of_mem_left {y : sphere (0 : F) 1} (hyA : y ∈ A)
    (hyC : y ∉ b '' (univ ×ˢ Icc (-1) 1)) : collapse p hb e A y = p := by
  by_cases hy : y ∈ range b
  · obtain ⟨⟨x, t⟩, rfl⟩ := hy
    have ht : 1 ≤ t := by
      by_contra! ht
      rcases le_or_gt (-1) t with ht' | ht'
      · exact hyC ⟨(x, t), ⟨mem_univ x, ht', ht.le⟩, rfl⟩
      · exact disjoint_left.1 hAB hyA (hneg (x := (x, t)) ⟨mem_univ x, mem_Iio.2 (by linarith)⟩)
    rw [collapse_apply]
    exact latitude_of_one_le p _ ht
  · simp only [collapse, hy, hyA, ↓reduceIte]

include hAB hpos in
/-- Off the closed collar, the collapse map is `-p` on the negative side. -/
private theorem collapse_of_mem_right {y : sphere (0 : F) 1} (hyB : y ∈ B)
    (hyC : y ∉ b '' (univ ×ˢ Icc (-1) 1)) : collapse p hb e A y = -p := by
  have hyA : y ∉ A := disjoint_right.1 hAB hyB
  by_cases hy : y ∈ range b
  · obtain ⟨⟨x, t⟩, rfl⟩ := hy
    have ht : t ≤ -1 := by
      by_contra! ht
      rcases le_or_gt t 1 with ht' | ht'
      · exact hyC ⟨(x, t), ⟨mem_univ x, ht.le, ht'⟩, rfl⟩
      · exact hyA (hpos (x := (x, t)) ⟨mem_univ x, mem_Ioi.2 (by linarith)⟩)
    rw [collapse_apply]
    exact latitude_of_le_neg_one p _ ht
  · simp only [collapse, hy, hyA, ↓reduceIte]

include hAB hpos hneg in
/-- The collapse map is continuous when `A` and `B` are open and separate the image of `σ`, with
the positive side of `b` in `A` and its negative side in `B`. -/
private theorem continuous_collapse [CompactSpace (sphere (0 : E) 1)] (hA : IsOpen A)
    (hB : IsOpen B) (hcompl : (range σ)ᶜ = A ∪ B) : Continuous (collapse p hb e A) := by
  have hC : IsClosed (b '' (univ ×ˢ Icc (-1) 1)) :=
    ((isCompact_univ.prod isCompact_Icc).image hb.isOpenEmbedding.continuous).isClosed
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  by_cases hy : y ∈ range b
  · -- On the open collar, the collapse map is the latitude map read through `b`.
    refine ((continuous_latitude p (u := fun q : sphere (0 : E) 1 × ℝ ↦ e q.1)
      (e.continuous.comp continuous_fst) continuous_snd).continuousAt.comp
      ((hb.isOpenEmbedding.toOpenPartialHomeomorph b).continuousAt_symm
        (by simpa using hy))).congr ?_
    filter_upwards [hb.isOpenEmbedding.isOpen_range.mem_nhds hy] with z ⟨q, hq⟩
    subst hq
    rw [collapse_apply, comp_apply, hb.isOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  · -- Off the closed collar, it is locally constant.
    have hyC : y ∉ b '' (univ ×ˢ Icc (-1) 1) := fun h ↦ hy (image_subset_range _ _ h)
    rcases (hcompl ▸ fun h ↦ hy (hb.range_subset_range h) : y ∈ A ∪ B) with hyA | hyB
    · refine (continuousAt_const (y := p)).congr ?_
      filter_upwards [hA.mem_nhds hyA, hC.isOpen_compl.mem_nhds hyC] with z hzA hzC
      exact (collapse_of_mem_left hAB hneg hzA hzC).symm
    · refine (continuousAt_const (y := -p)).congr ?_
      filter_upwards [hB.mem_nhds hyB, hC.isOpen_compl.mem_nhds hyC] with z hzB hzC
      exact (collapse_of_mem_right hAB hpos hzB hzC).symm

variable (p hb e A)

/-- The points sent to the poles are those outside the open collar. -/
private theorem preimage_collapse_pair :
    collapse p hb e A ⁻¹' {p, -p} = (b '' (univ ×ˢ Ioo (-1) 1))ᶜ := by
  ext y
  by_cases hy : y ∈ range b
  · obtain ⟨⟨x, t⟩, rfl⟩ := hy
    rw [mem_preimage, collapse_apply, mem_compl_iff, hb.isOpenEmbedding.injective.mem_set_image]
    simpa using latitude_mem_pair_iff p (e x) t
  · simp only [mem_preimage, collapse_mem_pair p hb e A hy, mem_compl_iff, true_iff]
    exact fun h ↦ hy (image_subset_range _ _ h)

/-- The points sent to the equator are those of the image of `σ`. -/
private theorem inner_collapse_eq_zero_iff (y : sphere (0 : F) 1) :
    ⟪(collapse p hb e A y : F), (p : F)⟫ = 0 ↔ y ∈ range σ := by
  by_cases hy : y ∈ range b
  · obtain ⟨⟨x, t⟩, rfl⟩ := hy
    rw [collapse_apply, inner_latitude_eq_zero_iff, ← mem_preimage (f := b), hb.preimage_range]
    simp
  · have hσ : y ∉ range σ := fun h ↦ hy (hb.range_subset_range h)
    have hp : ⟪(p : F), (p : F)⟫ = 1 := by simp
    rcases collapse_mem_pair p hb e A hy with h | h
    · rw [h, hp]
      simp [hσ]
    · rw [mem_singleton_iff.1 h, coe_neg_sphere, inner_neg_left, hp]
      simp [hσ]

/-- Off the preimage of the poles, the collapse map is injective. -/
private theorem injOn_collapse : InjOn (collapse p hb e A) (collapse p hb e A ⁻¹' {p, -p})ᶜ := by
  intro y hy y' hy' hyy
  simp only [mem_compl_iff, preimage_collapse_pair, not_not] at hy hy'
  obtain ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩ := hy
  obtain ⟨⟨x', t'⟩, -, rfl⟩ := hy'
  rw [collapse_apply, collapse_apply] at hyy
  obtain ⟨hxx, htt⟩ := latitude_injOn p ht hyy
  dsimp only at hxx htt
  rw [e.injective hxx, htt]

private theorem surjective_collapse : Surjective (collapse p hb e A) := by
  intro z
  obtain ⟨u, t, -, rfl⟩ := exists_latitude_eq p (e (Classical.arbitrary _)) z
  exact ⟨b (e.symm u, t), by rw [collapse_apply, e.apply_symm_apply]⟩

omit [Nonempty (sphere (0 : E) 1)] in
include hb in
/-- **Brown's collapse of the outside of a bicollar.** Let `b` be a bicollar of a map `σ` from the
unit sphere `Sᵐ⁻¹` of a real normed space of dimension `m ≥ 2` into the unit sphere `Sᵐ` of a real
inner product space of dimension `m + 1`. Fix a pole `p ∈ Sᵐ` and a homeomorphism `e` of `Sᵐ⁻¹`
with the equator orthogonal to `p`. Then there is a continuous surjection `g : Sᵐ → Sᵐ` such that

* on the closed collar, `g (b (x, t)) = √(1 - t²) • e x + t • p` for `t ∈ [-1, 1]`;
* the points sent to the poles `p` and `-p` are exactly those outside the open collar
  `b (Sᵐ⁻¹ × (-1, 1))`;
* the points sent to the equator are exactly those of the image of `σ`;
* `g` is injective off the preimage of the two poles.

So the two fibres `g⁻¹(p)` and `g⁻¹(-p)` are the only fibres of `g` with more than one point. -/
theorem IsBicollar.exists_collapse [NormedSpace ℝ E] (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : 1 < finrank ℝ E) :
    ∃ g : C(sphere (0 : F) 1, sphere (0 : F) 1), Surjective g ∧
      (∀ x : sphere (0 : E) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
        (g (b (x, t)) : F) = √(1 - t ^ 2) • ((e x : (ℝ ∙ (p : F))ᗮ) : F) + t • (p : F)) ∧
      g ⁻¹' {p, -p} = (b '' (univ ×ˢ Ioo (-1) 1))ᶜ ∧
      (∀ y, ⟪(g y : F), (p : F)⟫ = 0 ↔ y ∈ range σ) ∧
      InjOn g (g ⁻¹' {p, -p})ᶜ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  have : PreconnectedSpace (sphere (0 : E) 1) := Subtype.preconnectedSpace
    (isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast hE) 0 zero_le_one).2
  have : PreconnectedSpace (sphere (0 : F) 1) := Subtype.preconnectedSpace
    (isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F))
      0 zero_le_one).2
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  -- The image of `σ` separates the sphere into a positive side `A` and a negative side `B`.
  obtain ⟨A, B, hA, hB, hAB, hcompl, hpos, hneg⟩ := hb.exists_isOpen_compl_range_eq_union
    (not_isPreconnected_compl_range_sphere hEF hb.continuous hb.injective)
  refine ⟨⟨collapse p hb e A, continuous_collapse hAB hpos hneg hA hB hcompl⟩,
    surjective_collapse p hb e A, fun x t ht ↦ ?_, preimage_collapse_pair p hb e A,
    inner_collapse_eq_zero_iff p hb e A, injOn_collapse p hb e A⟩
  rw [ContinuousMap.coe_mk, collapse_apply]
  exact coe_latitude_of_mem p _ ht

end TauCeti
