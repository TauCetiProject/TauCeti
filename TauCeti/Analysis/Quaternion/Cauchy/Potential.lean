/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Analytic
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Analytic.Constructions

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

* quantitative `HasFPowerSeriesOnBall` expansions on `Metric.eball (dq x₀) ((√2 - 1) δ)` whenever
  `x₀` is separated by at least `δ > 0` from all eight coordinate hyperplanes `x i = a i` and
  `x i = b i`, assuming only face integrability (or continuity on `dq '' Icc a b`);
* real analyticity at every point away from the eight closed faces, and in particular throughout
  the open box `dq '' pi univ (fun i ↦ Ioo (a i) (b i))`.

## Main declarations

* `TauCeti.boxSliceMap`: continuous embedding `z ↦ dq (i.insertNth c z)` of a three-dimensional
  box face into `ℍ`.
* `TauCeti.boxBoundarySet`: the union in `ℍ` of the eight closed faces of a coordinate box.
* `ContinuousOn.integrableOn_boxSlice`: continuity on `dq '' Icc a b` implies integrability on
  each coordinate slice `x i = c` (`a i ≤ c ≤ b i`).
* `TauCeti.exists_hasFPowerSeriesOnBall_boxBoundarySum_left`,
  `TauCeti.exists_hasFPowerSeriesOnBall_boxBoundarySum_right`: quantitative power-series expansion
  of left and right box Cauchy–Fueter potentials on `eball (dq x₀) ((√2 - 1) δ)`.
* `TauCeti.analyticOnNhd_boxBoundarySum_left`, `TauCeti.analyticOnNhd_boxBoundarySum_right`:
  real analyticity away from the eight closed faces of the box.

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
  let y : Fin 4 → ℝ := i.insertNth c z.1 - x₀
  have hsub : dq y = boxSliceMap a b i c z - dq x₀ := dq.map_sub (i.insertNth c z.1) x₀
  have hy : y i = c - x₀ i := by simp [y]
  have habs : |c - x₀ i| ≤ ‖dq y‖ := hy ▸ abs_apply_le_norm_dq y i
  exact (hδ.trans habs).trans_eq (congrArg norm hsub)

/-- A point `dq x₀` with `x₀ i ≠ c` does not lie in the image of the slice `x i = c`. -/
theorem dq_notMem_range_boxSliceMap {a b x₀ : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} (hc : c ≠ x₀ i) :
    dq x₀ ∉ range (boxSliceMap a b i c) := by
  rintro ⟨z, hz⟩
  rw [boxSliceMap_apply, coe_dq] at hz
  have hinj : i.insertNth c z.1 = x₀ :=
    (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.injective hz
  exact hc (by simpa using congrFun hinj i)

/-- The union in `ℍ` of the eight closed faces of the coordinate box `Icc a b`. -/
noncomputable def boxBoundarySet (a b : Fin 4 → ℝ) : Set ℍ :=
  ⋃ i : Fin 4, range (boxSliceMap a b i (b i)) ∪ range (boxSliceMap a b i (a i))

/-- Every point of the open coordinate box avoids all eight closed faces. -/
theorem notMem_boxBoundarySet_of_mem_openBox {a b x₀ : Fin 4 → ℝ}
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    dq x₀ ∉ boxBoundarySet a b := by
  simp only [boxBoundarySet, mem_iUnion, mem_union, not_exists, not_or]
  exact fun i ↦ ⟨dq_notMem_range_boxSliceMap (hb i).ne', dq_notMem_range_boxSliceMap (ha i).ne⟩

/-- If `f` is continuous on `dq '' Icc a b`, then its restriction to a slice `x i = c` with
`a i ≤ c ≤ b i` is integrable on the three-dimensional face `Icc`. -/
theorem _root_.ContinuousOn.integrableOn_boxSlice {a b : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b)) {i : Fin 4} {c : ℝ} (hac : a i ≤ c) (hcb : c ≤ b i) :
    IntegrableOn (fun z ↦ f (dq (i.insertNth c z))) (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
  refine (hc.comp (dq.continuous.comp (Continuous.finInsertNth i continuous_const
    continuous_id)).continuousOn ?_).integrableOn_Icc
  intro z hz
  refine mem_image_of_mem _ ⟨fun j ↦ ?_, fun j ↦ ?_⟩
  · exact i.succAboveCases (by simpa using hac) (fun k ↦ by simpa using hz.1 k) j
  · exact i.succAboveCases (by simpa using hcb) (fun k ↦ by simpa using hz.2 k) j

/-! ### Single-slice potentials -/

private theorem hasFPowerSeriesOnBall_setIntegral_boxSlice_left
    {a b : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} {q₀ : ℍ}
    (hne : ∀ z, boxSliceMap a b i c z ≠ q₀) {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ z, δ ≤ ‖boxSliceMap a b i c z - q₀‖) {f : ℍ → ℍ}
    (hf : IntegrableOn (fun z ↦ f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ ∫ z in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          cauchyFueterKernel (dq (i.insertNth c z)) q * dq (Pi.single i 1) *
            f (dq (i.insertNth c z)))
        p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hint : IntegrableOn
      (fun z ↦ dq (Pi.single i 1) * f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    (ContinuousLinearMap.mul ℝ ℍ (dq (Pi.single i 1))).integrable_comp hf
  have hg : Integrable
      (fun z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove) ↦
        dq (Pi.single i 1) * f (boxSliceMap a b i c z))
      (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1 hint
  refine ⟨_, (hasFPowerSeriesOnBall_integral_cauchyFueterKernel_mul
    (boxSliceMap a b i c) hne hδ₀ hδ hg).congr fun q _ ↦ ?_⟩
  have heq := integral_subtype_comap (μ := volume)
    (s := Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) measurableSet_Icc
    fun z ↦ cauchyFueterKernel (dq (i.insertNth c z)) q *
      (dq (Pi.single i 1) * f (dq (i.insertNth c z)))
  simpa only [boxSliceMap_apply, mul_assoc] using heq

private theorem hasFPowerSeriesOnBall_setIntegral_boxSlice_right
    {a b : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} {q₀ : ℍ}
    (hne : ∀ z, boxSliceMap a b i c z ≠ q₀) {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ z, δ ≤ ‖boxSliceMap a b i c z - q₀‖) {f : ℍ → ℍ}
    (hf : IntegrableOn (fun z ↦ f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ ∫ z in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          f (dq (i.insertNth c z)) * dq (Pi.single i 1) *
            cauchyFueterKernel (dq (i.insertNth c z)) q)
        p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hint : IntegrableOn
      (fun z ↦ f (dq (i.insertNth c z)) * dq (Pi.single i 1))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    ((ContinuousLinearMap.mul ℝ ℍ).flip (dq (Pi.single i 1))).integrable_comp hf
  have hg : Integrable
      (fun z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove) ↦
        f (boxSliceMap a b i c z) * dq (Pi.single i 1))
      (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1 hint
  refine ⟨_, (hasFPowerSeriesOnBall_integral_mul_cauchyFueterKernel
    (boxSliceMap a b i c) hne hδ₀ hδ hg).congr fun q _ ↦ ?_⟩
  have heq := integral_subtype_comap (μ := volume)
    (s := Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) measurableSet_Icc
    fun z ↦ f (dq (i.insertNth c z)) * dq (Pi.single i 1) *
      cauchyFueterKernel (dq (i.insertNth c z)) q
  simpa only [boxSliceMap_apply] using heq

private theorem analyticAt_setIntegral_boxSlice_left
    {a b : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} {q₀ : ℍ}
    (hq₀ : q₀ ∉ range (boxSliceMap a b i c)) {f : ℍ → ℍ}
    (hf : IntegrableOn (fun z ↦ f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticAt ℝ
      (fun q ↦ ∫ z in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        cauchyFueterKernel (dq (i.insertNth c z)) q * dq (Pi.single i 1) *
          f (dq (i.insertNth c z))) q₀ := by
  have hint : IntegrableOn
      (fun z ↦ dq (Pi.single i 1) * f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    (ContinuousLinearMap.mul ℝ ℍ (dq (Pi.single i 1))).integrable_comp hf
  have hg : Integrable
      (fun z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove) ↦
        dq (Pi.single i 1) * f (boxSliceMap a b i c z))
      (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1 hint
  refine (analyticAt_integral_cauchyFueterKernel_mul (boxSliceMap a b i c) hq₀ hg).congr
    (Filter.Eventually.of_forall fun q ↦ ?_)
  have heq := integral_subtype_comap (μ := volume)
    (s := Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) measurableSet_Icc
    fun z ↦ cauchyFueterKernel (dq (i.insertNth c z)) q *
      (dq (Pi.single i 1) * f (dq (i.insertNth c z)))
  simpa only [boxSliceMap_apply, mul_assoc] using heq

private theorem analyticAt_setIntegral_boxSlice_right
    {a b : Fin 4 → ℝ} {i : Fin 4} {c : ℝ} {q₀ : ℍ}
    (hq₀ : q₀ ∉ range (boxSliceMap a b i c)) {f : ℍ → ℍ}
    (hf : IntegrableOn (fun z ↦ f (dq (i.insertNth c z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticAt ℝ
      (fun q ↦ ∫ z in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f (dq (i.insertNth c z)) * dq (Pi.single i 1) *
          cauchyFueterKernel (dq (i.insertNth c z)) q) q₀ := by
  have hint : IntegrableOn
      (fun z ↦ f (dq (i.insertNth c z)) * dq (Pi.single i 1))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    ((ContinuousLinearMap.mul ℝ ℍ).flip (dq (Pi.single i 1))).integrable_comp hf
  have hg : Integrable
      (fun z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove) ↦
        f (boxSliceMap a b i c z) * dq (Pi.single i 1))
      (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1 hint
  refine (analyticAt_integral_mul_cauchyFueterKernel (boxSliceMap a b i c) hq₀ hg).congr
    (Filter.Eventually.of_forall fun q ↦ ?_)
  have heq := integral_subtype_comap (μ := volume)
    (s := Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) measurableSet_Icc
    fun z ↦ f (dq (i.insertNth c z)) * dq (Pi.single i 1) *
      cauchyFueterKernel (dq (i.insertNth c z)) q
  simpa only [boxSliceMap_apply] using heq

/-! ### Quantitative power series and analyticity of `boxBoundarySum` potentials -/

/-- Quantitative power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` of the left Cauchy–Fueter
box boundary potential when `x₀` is separated by at least `δ > 0` from all eight coordinate faces
and `f` is integrable on each face. -/
theorem exists_hasFPowerSeriesOnBall_boxBoundarySum_left
    {a b x₀ : Fin 4 → ℝ} {δ : ℝ} (hδ₀ : 0 < δ)
    (ha : ∀ i, δ ≤ x₀ i - a i) (hb : ∀ i, δ ≤ b i - x₀ i) {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ boxBoundarySum a b fun i x ↦
          cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x))
        p (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hb_sep (i : Fin 4) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      δ ≤ ‖boxSliceMap a b i (b i) z - dq x₀‖ :=
    le_norm_boxSliceMap_sub_dq ((hb i).trans (le_abs_self _)) z
  have ha_sep (i : Fin 4) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      δ ≤ ‖boxSliceMap a b i (a i) z - dq x₀‖ :=
    le_norm_boxSliceMap_sub_dq (by rw [abs_sub_comm]; exact (ha i).trans (le_abs_self _)) z
  have hb_ne (i : Fin 4) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      boxSliceMap a b i (b i) z ≠ dq x₀ :=
    sub_ne_zero.1 (norm_ne_zero_iff.1 (hδ₀.trans_le (hb_sep i z)).ne')
  have ha_ne (i : Fin 4) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      boxSliceMap a b i (a i) z ≠ dq x₀ :=
    sub_ne_zero.1 (norm_ne_zero_iff.1 (hδ₀.trans_le (ha_sep i z)).ne')
  choose pb hpb using fun i ↦
    hasFPowerSeriesOnBall_setIntegral_boxSlice_left (hb_ne i) hδ₀ (hb_sep i) (hfb i)
  choose pa hpa using fun i ↦
    hasFPowerSeriesOnBall_setIntegral_boxSlice_left (ha_ne i) hδ₀ (ha_sep i) (hfa i)
  have hr : 0 < ENNReal.ofReal ((Real.sqrt 2 - 1) * δ) :=
    ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)
  refine ⟨∑ i : Fin 4, (pb i - pa i),
    (Finset.univ.hasFPowerSeriesOnBall_fun_sum hr fun i _ ↦ (hpb i).sub (hpa i)).congr
      fun q _ ↦ ?_⟩
  simp only [boxBoundarySum_def, Pi.sub_apply]

/-- Quantitative power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` of the right Cauchy–Fueter
box boundary potential when `x₀` is separated by at least `δ > 0` from all eight coordinate faces
and `f` is integrable on each face. -/
theorem exists_hasFPowerSeriesOnBall_boxBoundarySum_right
    {a b x₀ : Fin 4 → ℝ} {δ : ℝ} (hδ₀ : 0 < δ)
    (ha : ∀ i, δ ≤ x₀ i - a i) (hb : ∀ i, δ ≤ b i - x₀ i) {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall
        (fun q ↦ boxBoundarySum a b fun i x ↦
          f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)
        p (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hb_sep (i : Fin 4) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      δ ≤ ‖boxSliceMap a b i (b i) z - dq x₀‖ :=
    le_norm_boxSliceMap_sub_dq ((hb i).trans (le_abs_self _)) z
  have ha_sep (i : Fin 4) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      δ ≤ ‖boxSliceMap a b i (a i) z - dq x₀‖ :=
    le_norm_boxSliceMap_sub_dq (by rw [abs_sub_comm]; exact (ha i).trans (le_abs_self _)) z
  have hb_ne (i : Fin 4) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      boxSliceMap a b i (b i) z ≠ dq x₀ :=
    sub_ne_zero.1 (norm_ne_zero_iff.1 (hδ₀.trans_le (hb_sep i z)).ne')
  have ha_ne (i : Fin 4) (z : Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      boxSliceMap a b i (a i) z ≠ dq x₀ :=
    sub_ne_zero.1 (norm_ne_zero_iff.1 (hδ₀.trans_le (ha_sep i z)).ne')
  choose pb hpb using fun i ↦
    hasFPowerSeriesOnBall_setIntegral_boxSlice_right (hb_ne i) hδ₀ (hb_sep i) (hfb i)
  choose pa hpa using fun i ↦
    hasFPowerSeriesOnBall_setIntegral_boxSlice_right (ha_ne i) hδ₀ (ha_sep i) (hfa i)
  have hr : 0 < ENNReal.ofReal ((Real.sqrt 2 - 1) * δ) :=
    ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)
  refine ⟨∑ i : Fin 4, (pb i - pa i),
    (Finset.univ.hasFPowerSeriesOnBall_fun_sum hr fun i _ ↦ (hpb i).sub (hpa i)).congr
      fun q _ ↦ ?_⟩
  simp only [boxBoundarySum_def, Pi.sub_apply]

/-- The left Cauchy–Fueter box boundary potential is real analytic at every point outside the eight
closed faces of the box. -/
theorem analyticAt_boxBoundarySum_left {a b : Fin 4 → ℝ} {q₀ : ℍ}
    (hq₀ : q₀ ∉ boxBoundarySet a b) {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticAt ℝ (fun q ↦ boxBoundarySum a b fun i x ↦
      cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)) q₀ := by
  simp only [boxBoundarySet, mem_iUnion, mem_union, not_exists, not_or] at hq₀
  simp_rw [boxBoundarySum_def]
  exact Finset.univ.analyticAt_fun_sum fun i _ ↦
    (analyticAt_setIntegral_boxSlice_left (hq₀ i).1 (hfb i)).fun_sub
      (analyticAt_setIntegral_boxSlice_left (hq₀ i).2 (hfa i))

/-- The right Cauchy–Fueter box boundary potential is real analytic at every point outside the eight
closed faces of the box. -/
theorem analyticAt_boxBoundarySum_right {a b : Fin 4 → ℝ} {q₀ : ℍ}
    (hq₀ : q₀ ∉ boxBoundarySet a b) {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticAt ℝ (fun q ↦ boxBoundarySum a b fun i x ↦
      f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q) q₀ := by
  simp only [boxBoundarySet, mem_iUnion, mem_union, not_exists, not_or] at hq₀
  simp_rw [boxBoundarySum_def]
  exact Finset.univ.analyticAt_fun_sum fun i _ ↦
    (analyticAt_setIntegral_boxSlice_right (hq₀ i).1 (hfb i)).fun_sub
      (analyticAt_setIntegral_boxSlice_right (hq₀ i).2 (hfa i))

/-- The left Cauchy–Fueter box boundary potential is real analytic away from the eight closed faces
of the box. -/
theorem analyticOnNhd_boxBoundarySum_left {a b : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticOnNhd ℝ (fun q ↦ boxBoundarySum a b fun i x ↦
      cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)) (boxBoundarySet a b)ᶜ :=
  fun _ hq₀ ↦ analyticAt_boxBoundarySum_left hq₀ hfb hfa

/-- The right Cauchy–Fueter box boundary potential is real analytic away from the eight closed faces
of the box. -/
theorem analyticOnNhd_boxBoundarySum_right {a b : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hfb : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hfa : ∀ i : Fin 4, IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    AnalyticOnNhd ℝ (fun q ↦ boxBoundarySum a b fun i x ↦
      f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q) (boxBoundarySet a b)ᶜ :=
  fun _ hq₀ ↦ analyticAt_boxBoundarySum_right hq₀ hfb hfa

end TauCeti
