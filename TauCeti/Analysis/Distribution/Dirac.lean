/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A Dirac mass is not a locally integrable function

Let `E` be a finite-dimensional real vector space with a measure `μ` giving points measure zero,
and let `f : E → F` be locally integrable on a neighbourhood `U` of a point `a`. If `f` represents
a multiple `c δₐ` of the Dirac mass at `a` against the smooth functions supported in `U`,

`∫ g • f ∂μ = g a • c` for every smooth compactly supported `g : E → ℝ` with `tsupport g ⊆ U`,

then `c = 0` (`TauCeti.eq_zero_of_integral_contDiff_smul_eq_apply_smul`). So a nonzero multiple
of a Dirac mass is not given by a locally integrable function, even locally. This is how one shows
that a function whose distributional Laplacian has a point mass, such as the Newtonian kernel, has
no Laplacian in `Lᵖ`.

The proof applies the fundamental lemma of the calculus of variations,
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, on the punctured neighbourhood: there `f`
pairs to zero with every test function, so `f` vanishes almost everywhere on `U ∖ {a}`, hence on
`U`, since `μ {a} = 0`. Testing against a bump function equal to `1` at `a` then gives `c = 0`.
-/

public section

namespace TauCeti

open MeasureTheory Set Topology

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [NullSingletonClass μ]

/-- **A Dirac mass is not a locally integrable function.** If a function `f`, locally integrable
on a neighbourhood `U` of `a`, satisfies `∫ g • f ∂μ = g a • c` for every smooth compactly
supported `g` with `tsupport g ⊆ U`, then `c = 0`. -/
theorem eq_zero_of_integral_contDiff_smul_eq_apply_smul {f : E → F} {a : E} {U : Set E}
    (hU : U ∈ 𝓝 a) (hf : LocallyIntegrableOn f U μ) {c : F}
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • f x ∂μ = g a • c) :
    c = 0 := by
  obtain ⟨V, hVU, hVo, haV⟩ := mem_nhds_iff.1 hU
  -- Away from `a`, `f` pairs to zero with every test function, so it vanishes there.
  have hzero : ∀ᵐ x ∂μ, x ∈ V \ {a} → f x = 0 :=
    (hVo.sdiff isClosed_singleton).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.mono_set hVU).mono_set sdiff_subset) fun g hg hgc hgs ↦ by
        rw [h g hg hgc (hgs.trans (sdiff_subset.trans hVU)),
          image_eq_zero_of_notMem_tsupport fun ha ↦ (hgs ha).2 rfl, zero_smul]
  have hzero' : ∀ᵐ x ∂μ, x ∈ V → f x = 0 := by
    filter_upwards [hzero, measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := μ) a)]
      with x hx hxa hxV using hx ⟨hxV, hxa⟩
  -- A bump function at `a` supported in `V` pairs to `c` with `f`, but `f` vanishes on `V`.
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hVo a haV
  let φ : ContDiffBump a := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hφV : tsupport φ ⊆ V := by
    rw [φ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrV
  have hint := h φ φ.contDiff φ.hasCompactSupport (hφV.trans hVU)
  rw [φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), one_smul] at hint
  rw [← hint]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hzero'] with x hx
  by_cases hxV : x ∈ V
  · simp [hx hxV]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hxV (hφV h)]

end TauCeti
