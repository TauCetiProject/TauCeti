/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Convex.Measure
public import TauCeti.Analysis.LocallyConvex.Separation
public import TauCeti.MeasureTheory.Measure.Real

/-!
# Convex bodies with translated height distributions

For a set `s` in a real inner product space and a vector `e`, the **height distribution** of `s`
in direction `e` is the function `t ↦ μ {x ∈ s | ⟪e, x⟫ ≤ t}`. This file shows that a convex body
of positive measure is determined up to translation by its height distributions in all unit
directions: two convex bodies `K` and `L`, with `0 < μ K` for an additive Haar measure `μ`, are
translates of each other exactly when, for every unit vector `e`, the height distribution of `L`
in direction `e` is a translate of that of `K`
(`ConvexBody.exists_eq_vadd_iff_forall_measure_sep_inner_le_add_eq`).

This is the final step of the Kneser–Süss proof of the equality case of the Brunn–Minkowski
inequality for convex bodies: equality forces the height distributions of the two (equal-volume)
bodies to be translates in every direction, and the result here turns that into a translation of
the bodies themselves.

The proof combines three facts, each stated in its natural generality.

* The height distribution of a convex set `s` with nonempty interior and finite measure reaches
  the full measure `μ s` exactly at the upper bounds of the heights `⟪e, x⟫`, `x ∈ s`
  (`Convex.measure_sep_inner_le_eq_iff`). So translated height distributions shift the supporting
  half-spaces of the two bodies by the translation constant `c_e`.
* Translated height distributions shift the first moment `∫ x in s, ⟪e, x⟫ ∂μ` by `c_e` times
  the measure (`TauCeti.integral_inner_eq_add_mul_of_forall_measure_sep_inner_le_add_eq`). Hence
  `c_e` is `⟪e, v⟫`, where `v` is the measure-normalized difference of the two first moments, and in
  particular depends linearly on `e`.
* A closed convex set is determined by its supporting half-spaces in unit directions
  (`Convex.subset_of_forall_upperBounds_image_inner_subset`, in
  `TauCeti.Analysis.LocallyConvex.Separation`), a consequence of the geometric Hahn–Banach
  theorem `geometric_hahn_banach_closed_point`.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.1.
-/

public section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Measure

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- The height distribution of a convex set `s` with nonempty interior and finite measure reaches
the full measure `μ s` at the level `t` exactly when `t` bounds the heights `⟪e, x⟫` on `s`. -/
theorem Convex.measure_sep_inner_le_eq_iff [μ.IsOpenPosMeasure] {s : Set E} (hs : Convex ℝ s)
    (hint : (interior s).Nonempty) (hμ : μ s ≠ ∞) (e : E) (t : ℝ) :
    μ {x ∈ s | ⟪e, x⟫ ≤ t} = μ s ↔ t ∈ upperBounds ((⟪e, ·⟫) '' s) := by
  refine ⟨fun h ↦ ?_, fun h ↦ congrArg μ (sep_eq_self_iff_mem_true.2 fun x hx ↦ h ⟨x, hx, rfl⟩)⟩
  rintro _ ⟨x, hx, rfl⟩
  by_contra! hlt
  -- The interior points strictly above level `t` form a nonempty open subset of `s` missed by
  -- the part below level `t`, so that part has strictly smaller measure.
  have hopen : IsOpen {y : E | t < ⟪e, y⟫} := isOpen_lt continuous_const (by fun_prop)
  set U := interior s ∩ {y | t < ⟪e, y⟫}
  have hUo : IsOpen U := isOpen_interior.inter hopen
  have hUne : U.Nonempty := by
    have hx' : x ∈ closure (interior s) :=
      (hs.closure_interior_eq_closure_of_nonempty_interior hint).symm ▸ subset_closure hx
    simpa only [U, inter_comm] using mem_closure_iff.1 hx' _ hopen hlt
  have hdisj : Disjoint {x ∈ s | ⟪e, x⟫ ≤ t} U :=
    disjoint_left.2 fun y hy hyU ↦ hy.2.not_gt hyU.2
  have hsub : {x ∈ s | ⟪e, x⟫ ≤ t} ∪ U ⊆ s :=
    union_subset (sep_subset _ _) (inter_subset_left.trans interior_subset)
  have hle : μ s + μ U ≤ μ s + 0 := calc
    μ s + μ U = μ ({x ∈ s | ⟪e, x⟫ ≤ t} ∪ U) := by rw [measure_union hdisj hUo.measurableSet, h]
    _ ≤ μ s + 0 := (measure_mono hsub).trans_eq (add_zero _).symm
  exact hUo.measure_ne_zero μ hUne (nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_left hμ hle))

namespace TauCeti

omit [OpensMeasurableSpace E] in
/-- If the height distribution of `t` in direction `e` is that of `s` translated by `c`, then `s`
and `t` have the same measure. -/
theorem measure_eq_of_forall_measure_sep_inner_le_add_eq {s t : Set E} {e : E} {c : ℝ}
    (h : ∀ r : ℝ, μ {x ∈ t | ⟪e, x⟫ ≤ r + c} = μ {x ∈ s | ⟪e, x⟫ ≤ r}) :
    μ t = μ s := by
  -- Each set is the increasing union of its parts below the levels `n + a`, `n : ℕ`.
  have hU (u : Set E) (a : ℝ) : ⋃ n : ℕ, {x ∈ u | ⟪e, x⟫ ≤ n + a} = u := by
    refine Subset.antisymm (iUnion_subset fun _ ↦ sep_subset _ _) fun x hx ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (⟪e, x⟫ - a)
    exact mem_iUnion.2 ⟨n, hx, by linarith⟩
  have hmono (u : Set E) (a : ℝ) : Monotone fun n : ℕ ↦ {x ∈ u | ⟪e, x⟫ ≤ n + a} :=
    fun m n hmn x hx ↦ ⟨hx.1, hx.2.trans (by gcongr)⟩
  calc μ t = ⨆ n : ℕ, μ {x ∈ t | ⟪e, x⟫ ≤ n + c} := by rw [← (hmono t c).measure_iUnion, hU]
    _ = ⨆ n : ℕ, μ {x ∈ s | ⟪e, x⟫ ≤ n + 0} := by simp only [add_zero, h]
    _ = μ s := by rw [← (hmono s 0).measure_iUnion, hU]

/-- If the height distribution of `t` in direction `e` is that of `s` translated by `c`, then the
first moment of `t` in direction `e` is that of `s` plus `c` times the measure of `s`. -/
theorem integral_inner_eq_add_mul_of_forall_measure_sep_inner_le_add_eq {s t : Set E}
    (ht : μ t ≠ ∞) {e : E} (hs : IntegrableOn (⟪e, ·⟫) s μ) {c : ℝ}
    (h : ∀ r : ℝ, μ {x ∈ t | ⟪e, x⟫ ≤ r + c} = μ {x ∈ s | ⟪e, x⟫ ≤ r}) :
    ∫ x in t, ⟪e, x⟫ ∂μ = ∫ x in s, ⟪e, x⟫ ∂μ + c * μ.real s := by
  have hf : Measurable (⟪e, ·⟫ : E → ℝ) := (continuous_const.inner continuous_id).measurable
  have : IsFiniteMeasure (μ.restrict s) :=
    isFiniteMeasure_restrict.2 (measure_eq_of_forall_measure_sep_inner_le_add_eq h ▸ ht)
  -- Both first moments are means of the height laws, which differ by the translation `c`.
  calc ∫ x in t, ⟪e, x⟫ ∂μ = ∫ y, y ∂(μ.restrict t).map (⟪e, ·⟫) :=
        (integral_map (f := fun y ↦ y) hf.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ y, y + c ∂(μ.restrict s).map (⟪e, ·⟫) := by
        rw [Measure.map_restrict_eq_map_map_add_of_forall_measure_sep_le_add_eq ht hf h,
          integral_map (f := fun y ↦ y) (measurable_add_const c).aemeasurable
            aestronglyMeasurable_id]
    _ = ∫ x in s, ⟪e, x⟫ + c ∂μ :=
        integral_map hf.aemeasurable (measurable_id.add_const c).aestronglyMeasurable
    _ = ∫ x in s, ⟪e, x⟫ ∂μ + c * μ.real s := by
        rw [integral_add hs (integrable_const c), integral_const, smul_eq_mul, mul_comm,
          measureReal_restrict_apply_univ]

omit [OpensMeasurableSpace E] in
/-- Translating a set by `v` translates its height distribution in direction `e` by `⟪e, v⟫`. -/
theorem measure_sep_inner_le_add_inner_vadd [MeasurableConstVAdd E E] [μ.IsAddLeftInvariant]
    (s : Set E) (v e : E) (t : ℝ) :
    μ {x ∈ v +ᵥ s | ⟪e, x⟫ ≤ t + ⟪e, v⟫} = μ {x ∈ s | ⟪e, x⟫ ≤ t} := by
  have : {x ∈ v +ᵥ s | ⟪e, x⟫ ≤ t + ⟪e, v⟫} = v +ᵥ {x ∈ s | ⟪e, x⟫ ≤ t} := by
    ext x
    simp only [mem_sep_iff, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, inner_add_right,
      inner_neg_right]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, by linarith⟩
  rw [this, measure_vadd]

end TauCeti

end Measure

section ConvexBody

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- **Convex bodies with translated height distributions are translates.** Let `K` and `L` be
convex bodies with `0 < μ K` for an additive Haar measure `μ`. Then `L` is a translate of `K`
exactly when, in every unit direction `e`, the height distribution `t ↦ μ {x ∈ L | ⟪e, x⟫ ≤ t}`
of `L` is a translate of that of `K`. -/
theorem ConvexBody.exists_eq_vadd_iff_forall_measure_sep_inner_le_add_eq (K L : ConvexBody E)
    (hK : 0 < μ K) :
    (∃ v : E, (L : Set E) = v +ᵥ (K : Set E)) ↔ ∀ e : E, ‖e‖ = 1 → ∃ c : ℝ, ∀ t : ℝ,
      μ {x ∈ (L : Set E) | ⟪e, x⟫ ≤ t + c} = μ {x ∈ (K : Set E) | ⟪e, x⟫ ≤ t} := by
  refine ⟨fun ⟨v, hv⟩ e _ ↦ ⟨⟪e, v⟫, hv ▸ TauCeti.measure_sep_inner_le_add_inner_vadd _ v e⟩,
    fun h ↦ ?_⟩
  have hKfin : μ K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hLfin : μ L ≠ ∞ := L.isCompact.measure_lt_top.ne
  have hV : 0 < μ.real K := ENNReal.toReal_pos hK.ne' hKfin
  have hint (s : ConvexBody E) : IntegrableOn (fun x ↦ x) (s : Set E) μ :=
    continuousOn_id.integrableOn_compact s.isCompact
  -- The candidate translation: the normalized difference of the first moments.
  set v : E := (μ.real K)⁻¹ • (∫ x in L, x ∂μ - ∫ x in K, x ∂μ)
  refine ⟨v, ?_⟩
  -- In every unit direction, the supporting half-spaces of `L` and `v +ᵥ K` agree.
  have key (e : E) (he : ‖e‖ = 1) :
      upperBounds ((⟪e, ·⟫) '' (L : Set E)) = upperBounds ((⟪e, ·⟫) '' (v +ᵥ (K : Set E))) := by
    obtain ⟨c, hc⟩ := h e he
    have hmom := TauCeti.integral_inner_eq_add_mul_of_forall_measure_sep_inner_le_add_eq hLfin
      ((continuous_const.inner continuous_id).continuousOn.integrableOn_compact K.isCompact) hc
    rw [integral_inner (hint L) e, integral_inner (hint K) e] at hmom
    have hcv : c = ⟪e, v⟫ := by
      rw [real_inner_smul_right, inner_sub_right, hmom]
      field_simp
      ring
    have hLK : μ L = μ K :=
      TauCeti.measure_eq_of_forall_measure_sep_inner_le_add_eq hc
    have hLint : (interior (L : Set E)).Nonempty :=
      (L.convex.addHaar_pos_iff_interior_nonempty (μ := μ)).1 (hLK ▸ hK)
    have hKint : (interior (K : Set E)).Nonempty :=
      (K.convex.addHaar_pos_iff_interior_nonempty (μ := μ)).1 hK
    ext r
    have hshift : r ∈ upperBounds ((⟪e, ·⟫) '' (v +ᵥ (K : Set E))) ↔
        r - c ∈ upperBounds ((⟪e, ·⟫) '' (K : Set E)) := by
      rw [← image_vadd, image_image]
      simp only [mem_upperBounds, forall_mem_image, vadd_eq_add, inner_add_right, hcv]
      exact forall₂_congr fun _ _ ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
    rw [hshift, ← L.convex.measure_sep_inner_le_eq_iff hLint hLfin,
      ← K.convex.measure_sep_inner_le_eq_iff hKint hKfin, hLK, ← hc (r - c), sub_add_cancel]
  have hKv : IsClosed (v +ᵥ (K : Set E)) := (K.isCompact.vadd v).isClosed
  refine Subset.antisymm ?_ ?_
  · exact (K.convex.vadd v).subset_of_forall_upperBounds_image_inner_subset hKv
      (K.nonempty.vadd_set) fun e he ↦ (key e he).ge
  · exact L.convex.subset_of_forall_upperBounds_image_inner_subset L.isCompact.isClosed
      L.nonempty fun e he ↦ (key e he).le

end ConvexBody
