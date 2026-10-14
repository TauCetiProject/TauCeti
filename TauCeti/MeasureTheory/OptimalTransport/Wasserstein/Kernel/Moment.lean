/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Kernel.Basic

/-!
# Finite moments of Markov-kernel mixtures

A mixture has finite `p`-moment exactly when its kernel's radial `Lᵖ` seminorms belong to
`Lᵖ` on the source, for a finite nonzero exponent. Consequently a Wasserstein-Lipschitz
Markov kernel preserves finite moments as soon as one of its laws has finite moment.
The anchor law is necessary: a constant kernel with an infinite-moment law is
Wasserstein-Lipschitz with constant zero.

These results discharge the output-moment hypotheses in the contraction estimate for
Markov kernels, allowing the kernel to act on finite-moment Wasserstein spaces.

## References

* Y. Ollivier, *Ricci curvature of Markov chains on metric spaces*, J. Funct. Anal.
  256 (2009), 810--864.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [PseudoMetricSpace Y] [OpensMeasurableSpace Y]
  {p : ℝ≥0∞} {μ : Measure X} {κ : Kernel X Y}

/-- A finite-kernel mixture has finite moment exactly when its radial seminorm profile
belongs to `Lᵖ` on the source. The source measure is finite and the exponent finite nonzero;
neither a topology on the source nor a standard-Borel hypothesis is needed. -/
theorem hasFiniteMoment_comp_iff_memLp (hp0 : p ≠ 0) (hp : p ≠ ∞)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] (y : Y) :
    HasFiniteMoment p (κ ∘ₘ μ) ↔
      MemLp (fun x ↦ eLpNorm (fun z ↦ edist y z) p (κ x)) p μ := by
  rw [hasFiniteMoment_iff_memLp_edist (x := y)
    measurable_edist_right.aestronglyMeasurable]
  simp only [MemLp, eLpNorm_eLpNorm_kernel hp0 hp κ μ measurable_edist_right]

variable [PseudoMetricSpace X] [OpensMeasurableSpace X] [StandardBorelSpace Y]
  [TopologicalSpace.SeparableSpace Y] [IsMarkovKernel κ]

/-- A Markov kernel with a Wasserstein bound from one anchor almost everywhere under the source
sends finite-moment finite measures to finite-moment measures, provided the anchor law has
finite moment. -/
theorem HasFiniteMoment.comp_kernel [IsFiniteMeasure μ] (hμ : HasFiniteMoment p μ)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) {L : ℝ≥0} {x₀ : X}
    (hκ : ∀ᵐ x ∂μ, wassersteinEDist p (κ x₀) (κ x) ≤ L * edist x₀ x)
    (hκ₀ : HasFiniteMoment p (κ x₀)) : HasFiniteMoment p (κ ∘ₘ μ) := by
  obtain ⟨y, hy⟩ := hasFiniteMoment_def.mp hκ₀
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hrad : Measurable (fun x ↦ eLpNorm (fun z ↦ edist y z) p (κ x)) :=
    measurable_eLpNorm_kernel hp0 hp κ measurable_edist_right
  have hdist : MemLp (fun x ↦ (L : ℝ≥0∞) * edist x₀ x) p μ :=
    (hμ.memLp (x := x₀) measurable_edist_right.aestronglyMeasurable).of_enorm_le_mul (c := L)
      (measurable_edist_right.const_mul _).aestronglyMeasurable
      (.of_forall fun _ ↦ by simp)
  have hconst : MemLp (fun _ : X ↦ eLpNorm (fun z ↦ edist y z) p (κ x₀)) p μ :=
    memLp_const_enorm (by simpa only [enorm_eq_self] using hy.eLpNorm_ne_top)
  refine (hasFiniteMoment_comp_iff_memLp hp0 hp y).2
    ((hconst.add hdist).of_le_enorm hrad.aestronglyMeasurable (hκ.mono fun x hx ↦ ?_))
  simp only [enorm_eq_self, Pi.add_apply]
  rw [← wassersteinEDist_dirac_left measurable_edist,
    ← wassersteinEDist_dirac_left measurable_edist]
  exact (wassersteinEDist_triangle measurable_edist hp1 (Measure.dirac y) (κ x₀) (κ x)).trans
    (add_le_add le_rfl hx)

end TauCeti
