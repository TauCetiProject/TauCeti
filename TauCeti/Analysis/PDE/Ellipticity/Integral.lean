/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Analysis.Convex.Integral
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.MeasureTheory.Integral.Average

/-!
# Integrability and averages of uniformly elliptic coefficient fields

A measurable coefficient field which is uniformly elliptic with constants `λ, Λ` has operators
bounded by `Λ`, so they are essentially bounded and locally integrable. Since the elliptic operators
form a closed convex set, the average of these operators over a set of positive finite measure is
again elliptic: freezing the field at this average gives a constant elliptic field, whose mean
deviation from the field is the mean oscillation of the operators.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.memLp_top_toEuclideanCLM`: the operators of a measurable field,
  uniformly elliptic on a measurable set, are essentially bounded there.
* `TauCeti.PDE.UniformlyEllipticOn.locallyIntegrable_toEuclideanCLM`: the operators of a
  measurable, uniformly elliptic field are locally integrable.
* `TauCeti.PDE.UniformlyEllipticOn.exists_uniformlyEllipticOn_const_and_setAverage_le`: freezing
  a uniformly elliptic field at the average of its operators over a set gives an elliptic constant
  matrix, whose mean deviation from the field is bounded by the mean oscillation of the operators.
-/

public section

open MeasureTheory Matrix Set
open scoped ENNReal

namespace TauCeti

namespace PDE

namespace UniformlyEllipticOn

variable {X n : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace X] {μ : Measure X}
  {s : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}

/-- The operators of a measurable coefficient field, uniformly elliptic on a measurable set `s`
with upper constant `Λ`, are essentially bounded on `s`. -/
theorem memLp_top_toEuclideanCLM (hell : UniformlyEllipticOn s a lam Lam) (hs : MeasurableSet s)
    (ha : AEStronglyMeasurable a (μ.restrict s)) :
    MemLp (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) ⊤ (μ.restrict s) :=
  memLp_top_of_bound (Matrix.aestronglyMeasurable_toEuclideanCLM_iff.2 ha) Lam
    (ae_restrict_of_forall_mem hs fun x hx => by
      rw [← norm_matrixBilinearForm_eq_norm_toEuclideanCLM]
      exact hell.opNorm_matrixBilinearForm_le hx)

/-- The operators of a measurable, uniformly elliptic coefficient field are locally integrable. -/
theorem locallyIntegrable_toEuclideanCLM [TopologicalSpace X] [IsLocallyFiniteMeasure μ]
    (hell : UniformlyEllipticOn univ a lam Lam) (ha : AEStronglyMeasurable a μ) :
    LocallyIntegrable (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) μ := by
  have h := hell.memLp_top_toEuclideanCLM MeasurableSet.univ (μ := μ)
    (by rwa [Measure.restrict_univ])
  rw [Measure.restrict_univ] at h
  exact h.locallyIntegrable le_top

/-- **Freezing at the average.** Let `a` be measurable and uniformly elliptic with constants
`λ, Λ` on a measurable set `s` of positive finite measure. If the mean oscillation of the operators
of `a` on `s` is at most `δ ≥ 0`, then there is a constant matrix `A`, elliptic with the same
constants, from which `a` deviates in mean on `s` by at most `δ`: the average of the operators
over `s`, which is elliptic since the elliptic operators form a closed convex set. -/
theorem exists_uniformlyEllipticOn_const_and_setAverage_le
    (hell : UniformlyEllipticOn s a lam Lam) (hs : MeasurableSet s)
    (ha : AEStronglyMeasurable a (μ.restrict s)) (h0 : μ s ≠ 0) (hfin : μ s ≠ ∞) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hosc : ⨍⁻ x in s, ‖toEuclideanCLM (𝕜 := ℝ) (a x) -
      ⨍ y in s, toEuclideanCLM (𝕜 := ℝ) (a y) ∂μ‖ₑ ∂μ ≤ ENNReal.ofReal δ) :
    ∃ A : Matrix n n ℝ, UniformlyEllipticOn s (fun _ => A) lam Lam ∧
      ⨍ x in s, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ∂μ ≤ δ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hfin
  have hint : IntegrableOn (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) s μ :=
    (hell.memLp_top_toEuclideanCLM hs ha).integrable le_top
  set κ := ⨍ y in s, toEuclideanCLM (𝕜 := ℝ) (a y) ∂μ
  have hκ : κ ∈ ellipticCLMSet lam Lam := Convex.set_average_mem (convex_ellipticCLMSet lam Lam)
    (isClosed_ellipticCLMSet lam Lam) h0 hfin
    (ae_restrict_of_forall_mem hs fun x hx => (toEuclideanCLM_mem_ellipticCLMSet_iff _).2
      ((uniformlyEllipticOn_iff.1 hell).2.2 hx)) hint
  refine ⟨(toEuclideanCLM (𝕜 := ℝ)).symm κ,
    uniformlyEllipticOn_of_forall_toEuclideanCLM_mem hell.pos hell.le
      fun _ _ => by rwa [StarAlgEquiv.apply_symm_apply], ?_⟩
  have hint' : IntegrableOn (fun x => toEuclideanCLM (𝕜 := ℝ) (a x) - κ) s μ :=
    hint.sub (integrableOn_const hfin)
  rw [setLAverage_enorm_eq_ofReal_setAverage_norm hint', ENNReal.ofReal_le_ofReal_iff hδ] at hosc
  simpa only [norm_matrixBilinearForm_sub_eq_norm_toEuclideanCLM_sub,
    StarAlgEquiv.apply_symm_apply] using hosc

end UniformlyEllipticOn

end PDE

end TauCeti
