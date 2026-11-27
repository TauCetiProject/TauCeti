/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Total variation controls integrals of bounded functions

For finite measures `μ` and `ν` and a function `f` with `‖f‖ ≤ C`, the integrals of `f` differ by
at most `C * tvDist μ ν`:

```text
‖∫ f dμ - ∫ f dν‖ ≤ C * tvDist μ ν.
```

With Mathlib's normalization `tvDist` is the total mass of `|μ - ν|`, so the constant is `C` and not
`2 C`. The proof splits the space along a Hahn decomposition: on each side one measure dominates the
other, and the integrals against the two differ by the integral against their difference, whose
mass is the excess of the larger one.

## Main results

* `MeasureTheory.norm_integral_sub_integral_le_of_le`: for finite measures `μ ≤ ν`, the integrals of
  a function bounded by `C` differ by at most `C` times the mass of `ν` not carried by `μ`;
* `MeasureTheory.norm_integral_sub_integral_le_mul_tvDist`: the total variation bound above.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Lemma 2.1.
-/

public section

open Set

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ ν : Measure α} {f : α → E} {C : ℝ}

/-- If `μ ≤ ν` are finite measures, the integrals against them of a function bounded in norm by `C`
differ by at most `C` times the mass `ν univ - μ univ` of the difference. -/
theorem norm_integral_sub_integral_le_of_le [IsFiniteMeasure ν] (hμν : μ ≤ ν)
    (hf : AEStronglyMeasurable f ν) (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂ν - ∫ x, f x ∂μ‖ ≤ C * (ν.real univ - μ.real univ) := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_le ν hμν
  have hμ : Integrable f μ := .of_bound (hf.mono_measure hμν) C (.of_forall hC)
  have hD : Integrable f (ν - μ) := .of_bound (hf.mono_measure Measure.sub_le) C (.of_forall hC)
  calc ‖∫ x, f x ∂ν - ∫ x, f x ∂μ‖ = ‖∫ x, f x ∂(ν - μ)‖ := by
        conv_lhs => rw [← Measure.sub_add_cancel_of_le hμν, integral_add_measure hD hμ,
          add_sub_cancel_right]
    _ ≤ C * (ν - μ).real univ := norm_integral_le_of_norm_le_const (.of_forall hC)
    _ = C * (ν.real univ - μ.real univ) := by
        rw [measureReal_def, Measure.sub_apply MeasurableSet.univ hμν,
          ENNReal.toReal_sub_of_le (hμν univ) (measure_ne_top ν univ), measureReal_def,
          measureReal_def]

/-- **Total variation controls integrals.** For finite measures `μ` and `ν` and a function bounded
in norm by `C`, the integrals differ by at most `C * tvDist μ ν`. -/
theorem norm_integral_sub_integral_le_mul_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfμ : AEStronglyMeasurable f μ) (hfν : AEStronglyMeasurable f ν) (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂μ - ∫ x, f x ∂ν‖ ≤ C * tvDist μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h₁ := norm_integral_sub_integral_le_of_le hs.le_on hfν.restrict hC
  have h₂ := norm_integral_sub_integral_le_of_le hs.ge_on_compl hfμ.restrict hC
  simp only [measureReal_restrict_apply_univ] at h₁ h₂
  rw [hs.tvDist_eq, ← integral_add_compl hs.measurableSet (.of_bound hfμ C (.of_forall hC)),
    ← integral_add_compl hs.measurableSet (.of_bound hfν C (.of_forall hC))]
  calc ‖∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ - (∫ x in s, f x ∂ν + ∫ x in sᶜ, f x ∂ν)‖
      = ‖(∫ x in sᶜ, f x ∂μ - ∫ x in sᶜ, f x ∂ν) - (∫ x in s, f x ∂ν - ∫ x in s, f x ∂μ)‖ := by
        congr 1; abel
    _ ≤ ‖∫ x in sᶜ, f x ∂μ - ∫ x in sᶜ, f x ∂ν‖ + ‖∫ x in s, f x ∂ν - ∫ x in s, f x ∂μ‖ :=
        norm_sub_le _ _
    _ ≤ C * (μ.real sᶜ - ν.real sᶜ) + C * (ν.real s - μ.real s) := add_le_add h₂ h₁
    _ = C * (ν.real s - μ.real s + (μ.real sᶜ - ν.real sᶜ)) := by ring

end MeasureTheory
