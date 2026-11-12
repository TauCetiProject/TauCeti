/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic

/-!
# Sobolev extension above a graph

For a `K`-Lipschitz graph function `φ`, reflection in flattened
coordinates gives a bounded extension from `W^{1,p}(normalEpigraph φ)` to the whole
Euclidean product, for every `1 ≤ p ≤ ∞`. The extension agrees with the original
function above the graph and with its reflection `(t, y) ↦ (2φ(y) - t, y)` below it.
Restriction back to the epigraph is a left inverse, and the extension has norm at most
`2 * (1 + K)²`.

This is the graph-domain model used in constructing extension operators by boundary
charts and partitions of unity. It uses the graph-flattening Sobolev equivalence and
the half-space reflection extension already constructed in this library.

## References

L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.4, Theorem 1
(extension by flattening and reflection).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : C(E, ℝ)} {K : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Unflatten a whole-space Sobolev function. -/
private def unflattenWholeL (hφ : LipschitzWith K φ) :
    W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p →L[ℝ]
      W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p :=
  W1p.compMeasurePreservingL (M := 1 + K)
    (measurePreserving_graphFlattening φ φ.continuous) (by simp)
    (lipschitzWith_graphFlattening hφ).locallyLipschitz.locallyLipschitzOn
    fun _ _ => by
      simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_graphFlattening hφ)

private theorem norm_unflattenWholeL_le (hφ : LipschitzWith K φ)
    (u : W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p) :
    ‖unflattenWholeL hφ u‖ ≤ (1 + K) * ‖u‖ := by
  have hop : ‖unflattenWholeL (p := p) hφ‖ ≤ 1 + K :=
    (W1p.norm_compMeasurePreservingL_le _ _ _ _).trans_eq
      (max_eq_right (le_add_of_nonneg_right K.coe_nonneg))
  exact ((unflattenWholeL (p := p) hφ).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg u))

private theorem value_unflattenWholeL_ae (hφ : LipschitzWith K φ)
    (u : W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p) :
    W1p.value (unflattenWholeL hφ u) =ᵐ[volume]
      fun x => W1p.value u (graphFlattening φ φ.continuous x) := by
  rw [unflattenWholeL]
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    W1p.value_compMeasurePreservingL_ae (p := p) (M := 1 + K) (U := ⊤) (V := ⊤)
      (measurePreserving_graphFlattening φ φ.continuous) (by simp)
      (lipschitzWith_graphFlattening hφ).locallyLipschitz.locallyLipschitzOn
      (fun _ _ => by
        simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_graphFlattening hφ)) u

/-- Unflattening transforms the weak gradient by the adjoint derivative of the graph chart. -/
private theorem gradient_unflattenWholeL_ae (hφ : LipschitzWith K φ)
    (u : W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p) :
    W1p.gradient (unflattenWholeL hφ u) =ᵐ[volume] fun x =>
      ContinuousLinearMap.adjoint (fderiv ℝ (graphFlattening φ φ.continuous) x)
        (W1p.gradient u (graphFlattening φ φ.continuous x)) := by
  rw [unflattenWholeL]
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    W1p.gradient_compMeasurePreservingL_ae (p := p) (M := 1 + K) (U := ⊤) (V := ⊤)
      (measurePreserving_graphFlattening φ φ.continuous) (by simp)
      (lipschitzWith_graphFlattening hφ).locallyLipschitz.locallyLipschitzOn
      (fun _ _ => by
        simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_graphFlattening hφ)) u

/-- Extension from the region above the graph of a `K`-Lipschitz function to the whole
space: flatten the graph, extend by even reflection, and unflatten. It is a bounded
right inverse of restriction, with norm at most `2 * (1 + K)²`. -/
def W1p.normalEpigraphExtensionL (hφ : LipschitzWith K φ) :
    W1p volume (normalEpigraph φ) p →L[ℝ]
      W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p :=
  (unflattenWholeL hφ).comp
    ((W1p.extendByReflectionL 0).comp (W1p.normalEpigraphEquivL hφ).toContinuousLinearMap)

private theorem normalEpigraphExtensionL_apply (hφ : LipschitzWith K φ)
    (u : W1p volume (normalEpigraph φ) p) :
    W1p.normalEpigraphExtensionL hφ u = unflattenWholeL hφ
      (W1p.extendByReflectionL 0 (W1p.normalEpigraphEquivL hφ u)) := (rfl)

/-- The extension is the original value above the graph, its even reflection below
the graph, and zero on the graph, almost everywhere with respect to volume. -/
theorem W1p.value_normalEpigraphExtensionL_ae (hφ : LipschitzWith K φ)
    (u : W1p volume (normalEpigraph φ) p) :
    W1p.value (W1p.normalEpigraphExtensionL hφ u) =ᵐ[volume] fun x =>
      if φ x.snd < x.fst then W1p.value u x
      else if x.fst < φ x.snd then
        W1p.value u (WithLp.toLp 2 (2 * φ x.snd - x.fst, x.snd)) else 0 := by
  let Φ := graphFlattening φ φ.continuous
  let H := (normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E)))
  let v := W1p.normalEpigraphEquivL hφ u
  have hflat : H.indicator (W1p.value v) =ᵐ[volume]
      H.indicator (fun z => W1p.value u (Φ.symm z)) :=
    (ae_eq_restrict_iff_indicator_ae_eq (normalHalfSpace (E := E) 0).isOpen.measurableSet).mp
      (W1p.value_normalEpigraphEquivL_ae hφ u)
  have hΦ := measurePreserving_graphFlattening φ φ.continuous
  have hρ := measurePreserving_normalReflection (E := E) 0
  rw [normalEpigraphExtensionL_apply]
  filter_upwards [value_unflattenWholeL_ae hφ (W1p.extendByReflectionL 0 v),
    hΦ.quasiMeasurePreserving.ae_eq_comp (W1p.value_extendByReflectionL_ae 0 v),
    hΦ.quasiMeasurePreserving.ae_eq_comp hflat,
    (hρ.comp hΦ).quasiMeasurePreserving.ae_eq_comp hflat] with x hx hreflect h1 h2
  simp only [Function.comp_apply] at hreflect h1 h2
  rw [hx, hreflect, h1, h2]
  simp only [H, Φ, Set.indicator, SetLike.mem_coe, mem_normalHalfSpace,
    graphFlattening_apply, graphFlattening_symm_apply, normalReflection_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, sub_add_cancel,
    mul_zero, zero_sub, neg_sub]
  have hreturn : WithLp.toLp 2 (x.fst, x.snd) = x := WithLp.toLp_ofLp 2 x
  rw [hreturn]
  simp only [sub_pos]
  have hheight : φ x.snd - x.fst + φ x.snd = 2 * φ x.snd - x.fst := by ring
  rw [hheight]
  rcases lt_trichotomy (φ x.snd) x.fst with habove | hon | hbelow
  · -- Above the graph, only the unreflected value contributes.
    simp [habove, not_lt_of_gt habove]
  · -- On the graph, both open-half-space indicators vanish.
    simp [hon]
  · -- Below the graph, only the reflected value contributes.
    simp [hbelow, not_lt_of_gt hbelow]

/-- Restricting the graph-domain extension back to the region above the graph recovers
the original Sobolev function. -/
@[simp↓]
theorem W1p.restrictL_normalEpigraphExtensionL (hφ : LipschitzWith K φ)
    (u : W1p volume (normalEpigraph φ) p) :
    W1p.restrictL (le_top : normalEpigraph φ ≤ ⊤)
      (W1p.normalEpigraphExtensionL hφ u) = u := by
  apply W1p.ext_value
  apply Lp.ext
  filter_upwards [W1p.value_restrictL_ae le_top (W1p.normalEpigraphExtensionL hφ u),
    ae_restrict_of_ae (W1p.value_normalEpigraphExtensionL_ae hφ u),
    ae_restrict_mem (normalEpigraph φ).isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2, ite_eq_left ((mem_normalEpigraph φ x).mp hx)]

/-- The extension has the original weak gradient above the graph. Below the graph,
the gradient at the reflected point is transformed by the adjoint derivatives of
unflattening and flattening, with normal reflection between them. On the graph the
formula is zero, almost everywhere with respect to volume. -/
theorem W1p.gradient_normalEpigraphExtensionL_ae (hφ : LipschitzWith K φ)
    (u : W1p volume (normalEpigraph φ) p) :
    let Φ := graphFlattening φ φ.continuous
    W1p.gradient (W1p.normalEpigraphExtensionL hφ u) =ᵐ[volume] fun x =>
      if φ x.snd < x.fst then W1p.gradient u x
      else if x.fst < φ x.snd then
        ContinuousLinearMap.adjoint (fderiv ℝ Φ x)
          (normalLinearReflection E
            (ContinuousLinearMap.adjoint (fderiv ℝ Φ.symm (normalReflection E 0 (Φ x)))
              (W1p.gradient u (WithLp.toLp 2 (2 * φ x.snd - x.fst, x.snd)))))
      else 0 := by
  let Φ := graphFlattening φ φ.continuous
  let H := (normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E)))
  let v := W1p.normalEpigraphEquivL hφ u
  have hflat : H.indicator (W1p.gradient v) =ᵐ[volume]
      H.indicator (fun z => ContinuousLinearMap.adjoint (fderiv ℝ Φ.symm z)
        (W1p.gradient u (Φ.symm z))) :=
    (ae_eq_restrict_iff_indicator_ae_eq (normalHalfSpace (E := E) 0).isOpen.measurableSet).mp
      (W1p.gradient_normalEpigraphEquivL_ae hφ u)
  have horiginal := W1p.gradient_restrictL_ae (le_top : normalEpigraph φ ≤ ⊤)
    (W1p.normalEpigraphExtensionL hφ u)
  rw [W1p.restrictL_normalEpigraphExtensionL] at horiginal
  have habove := (ae_eq_restrict_iff_indicator_ae_eq
    (normalEpigraph φ).isOpen.measurableSet).mp horiginal.symm
  have hΦ := measurePreserving_graphFlattening φ φ.continuous
  have hρ := measurePreserving_normalReflection (E := E) 0
  have hwhole := gradient_unflattenWholeL_ae hφ (W1p.extendByReflectionL 0 v)
  rw [← normalEpigraphExtensionL_apply] at hwhole
  filter_upwards [habove, hwhole,
    hΦ.quasiMeasurePreserving.ae_eq_comp (W1p.gradient_extendByReflectionL_ae 0 v),
    hΦ.quasiMeasurePreserving.ae_eq_comp hflat,
    (hρ.comp hΦ).quasiMeasurePreserving.ae_eq_comp hflat] with x hu hx hreflect h1 h2
  by_cases hab : φ x.snd < x.fst
  · -- Above the graph, restriction already identifies the weak gradient.
    simpa only [Set.indicator_of_mem ((mem_normalEpigraph φ x).mpr hab), hab, ite_true] using hu
  · -- Below or on the graph, use the chain rule and the reflected half-space gradient.
    simp only [Function.comp_apply] at hreflect h1 h2
    rw [hx, hreflect, h1, h2]
    simp only [H, Φ, Set.indicator, SetLike.mem_coe, mem_normalHalfSpace,
      graphFlattening_apply, graphFlattening_symm_apply, normalReflection_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, mul_zero, zero_sub, neg_sub, sub_pos]
    have hheight : φ x.snd - x.fst + φ x.snd = 2 * φ x.snd - x.fst := by ring
    rw [hheight]
    by_cases hbelow : x.fst < φ x.snd <;>
      simp only [hab, hbelow, ite_true, ite_false, map_zero, zero_add, add_zero]

/-- The graph-domain extension multiplies the Sobolev norm by at most
`2 * (1 + K)²`, uniformly in the exponent `p`. -/
theorem W1p.norm_normalEpigraphExtensionL_le (hφ : LipschitzWith K φ)
    (u : W1p volume (normalEpigraph φ) p) :
    ‖W1p.normalEpigraphExtensionL hφ u‖ ≤ (2 * (1 + K) ^ 2) * ‖u‖ := by
  rw [normalEpigraphExtensionL_apply]
  calc
    ‖unflattenWholeL hφ (W1p.extendByReflectionL 0 (W1p.normalEpigraphEquivL hφ u))‖ ≤
        (1 + K) * ‖W1p.extendByReflectionL 0 (W1p.normalEpigraphEquivL hφ u)‖ :=
      norm_unflattenWholeL_le hφ _
    _ ≤ (1 + K) * (2 * ((1 + K) * ‖u‖)) :=
      mul_le_mul_of_nonneg_left
        ((W1p.norm_extendByReflectionL_le 0 _).trans
          (mul_le_mul_of_nonneg_left (W1p.norm_normalEpigraphEquivL_le hφ u) zero_le_two))
        (add_nonneg zero_le_one K.coe_nonneg)
    _ = (2 * (1 + K) ^ 2) * ‖u‖ := by ring

/-- The graph-domain extension has operator norm at most `2 * (1 + K)²`. -/
theorem W1p.opNorm_normalEpigraphExtensionL_le (hφ : LipschitzWith K φ) :
    ‖W1p.normalEpigraphExtensionL (p := p) hφ‖ ≤ 2 * (1 + K) ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (W1p.norm_normalEpigraphExtensionL_le hφ)

end TauCeti
