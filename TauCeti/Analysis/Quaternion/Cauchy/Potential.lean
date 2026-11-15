/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Analytic
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Analyticity and power-series expansion of box Cauchy–Fueter potentials

For a coordinate box `Icc a b` in `Fin 4 → ℝ`, the boundary flux `boxBoundarySum` of the left and
right Cauchy–Fueter kernel fields

```text
q ↦ boxBoundarySum a b (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)),
q ↦ boxBoundarySum a b (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)
```

is a signed sum of eight compact three-dimensional face integrals. Specializing the compact
boundary-potential theory of `TauCeti.Analysis.Quaternion.Analytic` to the slice embeddings
`z ↦ dq (i.insertNth c z)` yields:

* quantitative `HasFPowerSeriesOnBall` expansions on `Metric.eball q₀ ((√2 - 1) δ)` whenever every
  point of the box boundary `boxBoundarySet a b` lies at Euclidean distance at least `δ > 0` from
  `q₀`, assuming only face integrability (or continuity on `dq '' Icc a b`);
* real analyticity at every point away from the eight closed faces, and in particular throughout
  the open box `dq '' pi univ (fun i ↦ Ioo (a i) (b i))` and, when `a ≤ b`, the exterior
  `(dq '' Icc a b)ᶜ`.

## Main declarations

* `TauCeti.boxSliceMap`: continuous embedding `z ↦ dq (i.insertNth c z)` of a three-dimensional
  box face into `ℍ`.
* `TauCeti.boxBoundarySet`, `TauCeti.mem_boxBoundarySet_iff`, `TauCeti.isCompact_boxBoundarySet`,
  `TauCeti.isClosed_boxBoundarySet`, `TauCeti.boxBoundarySet_subset_image_Icc`: the union in `ℍ`
  of the eight closed faces of a coordinate box and its basic topological properties.
* `ContinuousOn.integrableOn_dq_insertNth_Icc`: continuity on `dq '' Icc a b` implies integrability
  on each coordinate slice `x i = c` (`a i ≤ c ≤ b i`).
* `TauCeti.exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul`,
  `TauCeti.exists_hasFPowerSeriesOnBall_boxBoundarySum_mul_cauchyFueterKernel`: quantitative
  power-series expansion of left and right box Cauchy–Fueter potentials on
  `eball q₀ ((√2 - 1) δ)`.
* `TauCeti.analyticOnNhd_boxBoundarySum_cauchyFueterKernel_mul`,
  `TauCeti.analyticOnNhd_boxBoundarySum_mul_cauchyFueterKernel`: real analyticity away from the
  eight closed faces of the box.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9 and the remark following it.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open MeasureTheory Set
open scoped Quaternion ENNReal

namespace TauCeti

open TauCeti.Quaternion _root_.Quaternion

/-! ### Coordinate-slice embeddings -/

/-- Continuous embedding in `ℍ` of the coordinate slice `x i = c` over the three-dimensional face
`Icc (a ∘ i.succAbove) (b ∘ i.succAbove)`. -/
noncomputable def boxSliceMap (a b : Fin 4 → ℝ) (i : Fin 4) (c : ℝ) :
    C(Icc (a ∘ i.succAbove) (b ∘ i.succAbove), ℍ) where
  toFun z := dq (i.insertNth c z.1)
  continuous_toFun := by fun_prop

@[simp]
theorem boxSliceMap_apply (a b : Fin 4 → ℝ) (i : Fin 4) (c : ℝ)
    (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
    boxSliceMap a b i c z = dq (i.insertNth c z.1) :=
  (rfl)

/-- If the slice coordinate `c` is separated from `x₀ i` by at least `δ`, every point of the slice
lies at Euclidean distance at least `δ` from `dq x₀`. -/
theorem le_norm_boxSliceMap_sub_dq {a b x₀ : Fin 4 → ℝ} {i : Fin 4} {c δ : ℝ}
    (hδ : δ ≤ |c - x₀ i|) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
    δ ≤ ‖boxSliceMap a b i c z - dq x₀‖ := by
  rw [boxSliceMap_apply, ← dq.map_sub]
  have h := abs_apply_le_norm_dq (i.insertNth c z.1 - x₀) i
  simp only [Pi.sub_apply, Fin.insertNth_apply_same] at h
  exact hδ.trans h

/-- A quaternion `dq x₀` lies in the range of `boxSliceMap a b i c` if and only if `x₀ i = c` and
the remaining three coordinates lie in `Icc (a ∘ i.succAbove) (b ∘ i.succAbove)`. -/
theorem dq_mem_range_boxSliceMap_iff {a b x₀ : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} :
    dq x₀ ∈ range (boxSliceMap a b i c) ↔
      x₀ i = c ∧ x₀ ∘ i.succAbove ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove) := by
  have hrem : i.removeNth x₀ = x₀ ∘ i.succAbove := funext (Fin.removeNth_apply i x₀)
  simp only [mem_range, boxSliceMap_apply, coe_dq, EquivLike.apply_eq_iff_eq,
    Fin.insertNth_eq_iff, hrem, Subtype.exists]
  constructor
  · rintro ⟨_, hz, hc, rfl⟩
    exact ⟨hc.symm, hz⟩
  · rintro ⟨hc, hx⟩
    exact ⟨x₀ ∘ i.succAbove, hx, hc.symm, rfl⟩

/-- A point `dq x₀` with `x₀ i ≠ c` does not lie in the image of the slice `x i = c`. -/
theorem dq_notMem_range_boxSliceMap {a b x₀ : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} (hc : c ≠ x₀ i) :
    dq x₀ ∉ range (boxSliceMap a b i c) :=
  fun h ↦ hc (dq_mem_range_boxSliceMap_iff.1 h).1.symm

/-- The union in `ℍ` of the eight closed faces of the coordinate box `Icc a b`. -/
noncomputable def boxBoundarySet (a b : Fin 4 → ℝ) : Set ℍ :=
  ⋃ i : Fin 4, range (boxSliceMap a b i (b i)) ∪ range (boxSliceMap a b i (a i))

/-- Definitional expansion of `boxBoundarySet a b` as the union of the eight face ranges. -/
theorem boxBoundarySet_def (a b : Fin 4 → ℝ) :
    boxBoundarySet a b =
      ⋃ i : Fin 4, range (boxSliceMap a b i (b i)) ∪ range (boxSliceMap a b i (a i)) :=
  (rfl)

/-- Membership in `boxBoundarySet a b` holds if and only if the point lies on one of the eight
closed faces of the box. -/
@[simp]
theorem mem_boxBoundarySet_iff {a b : Fin 4 → ℝ} {q : ℍ} :
    q ∈ boxBoundarySet a b ↔
      ∃ i : Fin 4, q ∈ range (boxSliceMap a b i (b i)) ∨ q ∈ range (boxSliceMap a b i (a i)) := by
  simp only [boxBoundarySet_def, mem_iUnion, mem_union]

/-- The union of the eight closed faces of a coordinate box is compact. -/
theorem isCompact_boxBoundarySet (a b : Fin 4 → ℝ) : IsCompact (boxBoundarySet a b) :=
  isCompact_iUnion fun i ↦
    (isCompact_range (boxSliceMap a b i (b i)).continuous).union
      (isCompact_range (boxSliceMap a b i (a i)).continuous)

/-- The union of the eight closed faces of a coordinate box is closed. -/
theorem isClosed_boxBoundarySet (a b : Fin 4 → ℝ) : IsClosed (boxBoundarySet a b) :=
  (isCompact_boxBoundarySet a b).isClosed

/-- When `a ≤ b`, every point of `boxBoundarySet a b` lies in the closed coordinate box
`dq '' Icc a b`. -/
theorem boxBoundarySet_subset_image_Icc {a b : Fin 4 → ℝ} (hab : a ≤ b) :
    boxBoundarySet a b ⊆ dq '' Icc a b := by
  intro q hq
  rcases mem_boxBoundarySet_iff.1 hq with ⟨i, ⟨z, rfl⟩ | ⟨z, rfl⟩⟩
  · rw [boxSliceMap_apply]
    exact mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨⟨hab i, le_rfl⟩, z.2⟩)
  · rw [boxSliceMap_apply]
    exact mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨⟨le_rfl, hab i⟩, z.2⟩)

/-- If `x₀` is separated by at least `δ` from all eight coordinate hyperplanes `x i = a i` and
`x i = b i`, every point of `boxBoundarySet a b` lies at Euclidean distance at least `δ` from
`dq x₀`. -/
theorem le_norm_sub_dq_of_mem_boxBoundarySet {a b x₀ : Fin 4 → ℝ} {δ : ℝ}
    (ha : ∀ i, δ ≤ |a i - x₀ i|) (hb : ∀ i, δ ≤ |b i - x₀ i|)
    {q : ℍ} (hq : q ∈ boxBoundarySet a b) :
    δ ≤ ‖q - dq x₀‖ := by
  rcases mem_boxBoundarySet_iff.1 hq with ⟨i, ⟨z, rfl⟩ | ⟨z, rfl⟩⟩
  · exact le_norm_boxSliceMap_sub_dq (hb i) z
  · exact le_norm_boxSliceMap_sub_dq (ha i) z

/-- Every point of the open coordinate box avoids all eight closed faces. -/
theorem dq_notMem_boxBoundarySet_of_lt {a b x₀ : Fin 4 → ℝ}
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    dq x₀ ∉ boxBoundarySet a b := by
  simp only [mem_boxBoundarySet_iff, not_exists, not_or]
  exact fun i ↦ ⟨dq_notMem_range_boxSliceMap (hb i).ne', dq_notMem_range_boxSliceMap (ha i).ne⟩

/-- If `f` is continuous on `dq '' Icc a b`, then its restriction to a slice `x i = c` with
`a i ≤ c ≤ b i` is integrable on the three-dimensional face `Icc`. -/
theorem _root_.ContinuousOn.integrableOn_dq_insertNth_Icc
    {E : Type*} [NormedAddCommGroup E] {a b : Fin 4 → ℝ} {f : ℍ → E}
    (hc : ContinuousOn f (dq '' Icc a b)) {i : Fin 4} {c : ℝ} (hac : a i ≤ c) (hcb : c ≤ b i) :
    IntegrableOn (fun z ↦ f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
  (hc.comp (by fun_prop) fun _ hz ↦
    mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨⟨hac, hcb⟩, hz⟩)).integrableOn_Icc

/-! ### Single-slice potentials -/

private theorem hasFPowerSeriesOnBall_setIntegral_boxSlice_left
    {a b : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ z, δ ≤ ‖boxSliceMap a b i c z - q₀‖) {f : ℍ → ℍ}
    (hf : IntegrableOn (fun z ↦ f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ ∫ z in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          cauchyFueterKernel (dq (i.insertNth c z)) q * dq (Pi.single i 1) *
            f (dq (i.insertNth c z)))
        p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hne : ∀ z, boxSliceMap a b i c z ≠ q₀ :=
    fun z ↦ sub_ne_zero.1 (norm_ne_zero_iff.1 (hδ₀.trans_le (hδ z)).ne')
  have hg : Integrable
      (fun z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove) ↦
        dq (Pi.single i 1) * f (boxSliceMap a b i c z))
      (volume.comap Subtype.val) := by
    simpa only [Function.comp_def, ContinuousLinearMap.mul_apply', ← boxSliceMap_apply] using
      (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1
        ((ContinuousLinearMap.mul ℝ ℍ (dq (Pi.single i 1))).integrable_comp hf)
  refine ⟨_, (hasFPowerSeriesOnBall_integral_cauchyFueterKernel_mul
    (boxSliceMap a b i c) hne hδ₀ hδ hg).congr fun q _ ↦ ?_⟩
  simpa only [boxSliceMap_apply, mul_assoc] using
    integral_subtype_comap (μ := volume) measurableSet_Icc
      fun z ↦ cauchyFueterKernel (dq (i.insertNth c z)) q *
        (dq (Pi.single i 1) * f (dq (i.insertNth c z)))

private theorem hasFPowerSeriesOnBall_setIntegral_boxSlice_right
    {a b : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ z, δ ≤ ‖boxSliceMap a b i c z - q₀‖) {f : ℍ → ℍ}
    (hf : IntegrableOn (fun z ↦ f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ ∫ z in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          f (dq (i.insertNth c z)) * dq (Pi.single i 1) *
            cauchyFueterKernel (dq (i.insertNth c z)) q)
        p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hne : ∀ z, boxSliceMap a b i c z ≠ q₀ :=
    fun z ↦ sub_ne_zero.1 (norm_ne_zero_iff.1 (hδ₀.trans_le (hδ z)).ne')
  have hg : Integrable
      (fun z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove) ↦
        f (boxSliceMap a b i c z) * dq (Pi.single i 1))
      (volume.comap Subtype.val) := by
    simpa only [Function.comp_def, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
      ← boxSliceMap_apply] using
      (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1
        (((ContinuousLinearMap.mul ℝ ℍ).flip (dq (Pi.single i 1))).integrable_comp hf)
  refine ⟨_, (hasFPowerSeriesOnBall_integral_mul_cauchyFueterKernel
    (boxSliceMap a b i c) hne hδ₀ hδ hg).congr fun q _ ↦ ?_⟩
  simpa only [boxSliceMap_apply] using
    integral_subtype_comap (μ := volume) measurableSet_Icc
      fun z ↦ f (dq (i.insertNth c z)) * dq (Pi.single i 1) *
        cauchyFueterKernel (dq (i.insertNth c z)) q

/-! ### Quantitative power series and analyticity of `boxBoundarySum` potentials -/

/-- Quantitative power-series expansion on `eball q₀ ((√2 - 1) δ)` of the left Cauchy–Fueter box
boundary potential whenever every point of `boxBoundarySet a b` lies at Euclidean distance at least
`δ > 0` from `q₀` and `f` is integrable on each face. -/
theorem exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul
    {a b : Fin 4 → ℝ} {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ q ∈ boxBoundarySet a b, δ ≤ ‖q - q₀‖) {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ boxBoundarySum a b fun i x ↦
          cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x))
        p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  choose pb hpb using fun i ↦ hasFPowerSeriesOnBall_setIntegral_boxSlice_left hδ₀
    (fun z ↦ hδ _ (mem_boxBoundarySet_iff.2 ⟨i, Or.inl ⟨z, rfl⟩⟩)) (hfb i)
  choose pa hpa using fun i ↦ hasFPowerSeriesOnBall_setIntegral_boxSlice_left hδ₀
    (fun z ↦ hδ _ (mem_boxBoundarySet_iff.2 ⟨i, Or.inr ⟨z, rfl⟩⟩)) (hfa i)
  have hr : 0 < ENNReal.ofReal ((Real.sqrt 2 - 1) * δ) :=
    ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)
  refine ⟨∑ i : Fin 4, (pb i - pa i),
    (Finset.univ.hasFPowerSeriesOnBall_fun_sum hr fun i _ ↦ (hpb i).sub (hpa i)).congr
      fun q _ ↦ ?_⟩
  simp only [boxBoundarySum_def, Pi.sub_apply]

/-- Quantitative power-series expansion on `eball q₀ ((√2 - 1) δ)` of the right Cauchy–Fueter box
boundary potential whenever every point of `boxBoundarySet a b` lies at Euclidean distance at least
`δ > 0` from `q₀` and `f` is integrable on each face. -/
theorem exists_hasFPowerSeriesOnBall_boxBoundarySum_mul_cauchyFueterKernel
    {a b : Fin 4 → ℝ} {q₀ : ℍ} {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ q ∈ boxBoundarySet a b, δ ≤ ‖q - q₀‖) {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ boxBoundarySum a b fun i x ↦
          f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)
        p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  choose pb hpb using fun i ↦ hasFPowerSeriesOnBall_setIntegral_boxSlice_right hδ₀
    (fun z ↦ hδ _ (mem_boxBoundarySet_iff.2 ⟨i, Or.inl ⟨z, rfl⟩⟩)) (hfb i)
  choose pa hpa using fun i ↦ hasFPowerSeriesOnBall_setIntegral_boxSlice_right hδ₀
    (fun z ↦ hδ _ (mem_boxBoundarySet_iff.2 ⟨i, Or.inr ⟨z, rfl⟩⟩)) (hfa i)
  have hr : 0 < ENNReal.ofReal ((Real.sqrt 2 - 1) * δ) :=
    ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)
  refine ⟨∑ i : Fin 4, (pb i - pa i),
    (Finset.univ.hasFPowerSeriesOnBall_fun_sum hr fun i _ ↦ (hpb i).sub (hpa i)).congr
      fun q _ ↦ ?_⟩
  simp only [boxBoundarySum_def, Pi.sub_apply]

/-- The left Cauchy–Fueter box boundary potential is real analytic at every point outside the eight
closed faces of the box. -/
theorem analyticAt_boxBoundarySum_cauchyFueterKernel_mul {a b : Fin 4 → ℝ} {q₀ : ℍ}
    (hq₀ : q₀ ∉ boxBoundarySet a b) {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticAt ℝ (fun q ↦ boxBoundarySum a b fun i x ↦
      cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)) q₀ := by
  obtain ⟨δ, hδ₀, hball⟩ := Metric.isOpen_iff.1 (isClosed_boxBoundarySet a b).isOpen_compl q₀ hq₀
  exact (exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul hδ₀
    (fun q hq ↦ not_lt.1 fun hlt ↦ hball (by rwa [Metric.mem_ball, dist_eq_norm]) hq)
    hfb hfa).choose_spec.analyticAt

/-- The right Cauchy–Fueter box boundary potential is real analytic at every point outside the eight
closed faces of the box. -/
theorem analyticAt_boxBoundarySum_mul_cauchyFueterKernel {a b : Fin 4 → ℝ} {q₀ : ℍ}
    (hq₀ : q₀ ∉ boxBoundarySet a b) {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticAt ℝ (fun q ↦ boxBoundarySum a b fun i x ↦
      f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q) q₀ := by
  obtain ⟨δ, hδ₀, hball⟩ := Metric.isOpen_iff.1 (isClosed_boxBoundarySet a b).isOpen_compl q₀ hq₀
  exact (exists_hasFPowerSeriesOnBall_boxBoundarySum_mul_cauchyFueterKernel hδ₀
    (fun q hq ↦ not_lt.1 fun hlt ↦ hball (by rwa [Metric.mem_ball, dist_eq_norm]) hq)
    hfb hfa).choose_spec.analyticAt

/-- The left Cauchy–Fueter box boundary potential is real analytic away from the eight closed faces
of the box. -/
theorem analyticOnNhd_boxBoundarySum_cauchyFueterKernel_mul {a b : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticOnNhd ℝ (fun q ↦ boxBoundarySum a b fun i x ↦
      cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)) (boxBoundarySet a b)ᶜ :=
  fun _ hq₀ ↦ analyticAt_boxBoundarySum_cauchyFueterKernel_mul hq₀ hfb hfa

/-- The right Cauchy–Fueter box boundary potential is real analytic away from the eight closed faces
of the box. -/
theorem analyticOnNhd_boxBoundarySum_mul_cauchyFueterKernel {a b : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticOnNhd ℝ (fun q ↦ boxBoundarySum a b fun i x ↦
      f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q) (boxBoundarySet a b)ᶜ :=
  fun _ hq₀ ↦ analyticAt_boxBoundarySum_mul_cauchyFueterKernel hq₀ hfb hfa

end TauCeti
