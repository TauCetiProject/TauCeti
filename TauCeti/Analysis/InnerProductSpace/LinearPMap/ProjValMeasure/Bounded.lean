/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic

/-!
# Bounded spectral multipliers of a self-adjoint partial operator

A bounded symbol whose product with the real coordinate is also bounded has spectral integral
in the operator domain. On that vector the operator acts by multiplying the symbol by the
coordinate. This gives bounded spectral cuts and the inverse across a vector spectral gap.

## Provenance

Adapted from Kitware's DKPS formalization, `SpectralMeasure.lean`,
`SpectralCutOperator.lean` and `SpectralGapInverse.lean` at `797408205`.
The latter preserves Adam Bornemann's Spectra idea of a cut-off reciprocal
(`SpectralTheory/Calculus/SpectralGapInverse.lean`, Spectra commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`; Apache-2.0). The present proofs use
Tau Ceti's accepted projection-valued measure and bounded integral, rather than the donor's
separate Borel-calculus facade. No unbounded spectral-integral carrier is introduced.
-/

public section

noncomputable section

open Complex MeasureTheory TauCeti
open scoped InnerProductSpace

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

private theorem cayley_mul_integral (hA : IsSelfAdjoint A)
    (f g : BoundedBorelFunction ℝ) (hfg : ∀ s : ℝ, (s : ℂ) * f s = g s) :
    A.cayley * (A.spectralPVM hA).integral (g + I • f) =
      (A.spectralPVM hA).integral (g - I • f) := by
  have := hA.isStarNormal_cayley
  let κ (w : _root_.spectrum ℂ A.cayley) := inverseCayleyCoord (w : ℂ)
  have hκ : Measurable κ := by fun_prop
  let pull := BoundedBorelFunction.compStarAlgHom' κ hκ
  have hp (b : BoundedBorelFunction ℝ) :
      (A.spectralPVM hA).integral b = A.cayley.borelCalculus (pull b) := by
    rw [hA.spectralPVM_eq_map, ProjValMeasure.integral_map]
    rw [ContinuousLinearMap.integral_spectralPVM]
  let z : C(_root_.spectrum ℂ A.cayley, ℂ) :=
    (ContinuousMap.id ℂ).restrict (_root_.spectrum ℂ A.cayley)
  have hz : A.cayley = A.cayley.borelCalculus (BoundedBorelFunction.ofContinuousMap z) := by
    exact A.cayley.borelCalculus_restrict_id.symm
  rw [hp, hp]
  conv_lhs => arg 1; rw [hz]
  rw [← map_mul]
  apply ContinuousLinearMap.borelCalculus_congr_ae
  intro ξ
  have h1 : ∀ᵐ w : _root_.spectrum ℂ A.cayley ∂A.cayley.diagMeasure ξ, (w : ℂ) ≠ 1 := by
    apply ae_iff.mpr
    convert cayley_diagMeasure_singleton_one hA.neg_I_mem_resolventSet ξ using 1
    congr 1
    ext w
    simp
  filter_upwards [h1] with w hw
  simp only [BoundedBorelFunction.coe_mul, Pi.mul_apply,
    BoundedBorelFunction.ofContinuousMap_apply, pull,
    BoundedBorelFunction.compStarAlgHom'_apply, BoundedBorelFunction.coe_add,
    BoundedBorelFunction.coe_sub, BoundedBorelFunction.coe_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  -- Evaluate the continuous coordinate and the pulled-back symbols in the same scalar form.
  change (w : ℂ) * (g (κ w) + I * f (κ w)) = g (κ w) - I * f (κ w)
  rw [← hfg]
  have hk : (κ w : ℂ) = I * (1 + (w : ℂ)) / (1 - w) :=
    by simpa only [κ, inverseCayleyCoord_def] using
      (hA.ofReal_re_inverseCayley_eq_and_mem_spectrum w.property hw).1
  rw [hk]
  field_simp
  ring

/-- A bounded spectral multiplier with bounded coordinate product gives a vector in the graph
of the self-adjoint operator. -/
theorem _root_.IsSelfAdjoint.mem_graph_integral_spectralPVM (hA : IsSelfAdjoint A)
    (f g : BoundedBorelFunction ℝ) (hfg : ∀ s : ℝ, (s : ℂ) * f s = g s) (x : H) :
    ((A.spectralPVM hA).integral f x, (A.spectralPVM hA).integral g x) ∈ A.graph := by
  have h := cayley_mul_integral hA f g hfg
  rw [_root_.map_add, _root_.map_sub, _root_.map_smul] at h
  have hx := congrArg (fun T : H →L[ℂ] H => T x) h
  simp only [_root_.mul_apply_eq_comp, _root_.add_apply, _root_.sub_apply,
    _root_.smul_apply] at hx
  apply (mem_graph_iff_exists_cayley hA.neg_I_mem_resolventSet).2
  refine ⟨(2 * I)⁻¹ • ((A.spectralPVM hA).integral g x +
    I • (A.spectralPVM hA).integral f x), ?_⟩
  rw [ContinuousLinearMap.map_smul, hx, Prod.mk.injEq]
  constructor <;> match_scalars <;> norm_num [mul_inv_rev, inv_I] <;> linear_combination -I_sq


private def cutSymbol (B : Set ℝ) (hB : MeasurableSet B) (c r : ℝ)
    (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) : BoundedBorelFunction ℝ :=
  BoundedBorelFunction.ofFunction (B.indicator fun s => ((s - c : ℝ) : ℂ))
    (Measurable.indicator (by fun_prop) hB) ⟨r, hr, fun s => by
      by_cases hs : s ∈ B
      · rw [Set.indicator_of_mem hs, Complex.norm_real, Real.norm_eq_abs]
        exact hcr s hs
      · rw [Set.indicator_of_notMem hs, norm_zero]
        exact hr⟩

/-- The bounded spectral cut of `A - c` on a measurable set contained in the radius-r
interval around c. -/
def spectralCut (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) (c r : ℝ) (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) :
    H →L[ℂ] H := (A.spectralPVM hA).integral (cutSymbol B hB c r hr hcr)

/-- Characterization of the spectral cut by its bounded Borel symbol. -/
theorem _root_.IsSelfAdjoint.spectralCut_eq_integral (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) (c r : ℝ) (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r)
    (f : BoundedBorelFunction ℝ) (hf : ∀ s, f s = B.indicator (fun s => ((s - c : ℝ) : ℂ)) s) :
    A.spectralCut hA B hB c r hr hcr = (A.spectralPVM hA).integral f := by
  unfold spectralCut
  congr 1
  ext s
  simpa only [cutSymbol, BoundedBorelFunction.ofFunction_apply] using (hf s).symm

/-- The norm of a spectral cut is at most the radius of its spectral interval. -/
theorem _root_.IsSelfAdjoint.norm_spectralCut_le (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) (c r : ℝ) (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) :
    ‖A.spectralCut hA B hB c r hr hcr‖ ≤ r := by
  unfold spectralCut
  apply ProjValMeasure.norm_integral_le _ hr
  intro s
  simp only [cutSymbol, BoundedBorelFunction.ofFunction_apply]
  by_cases hs : s ∈ B
  · rw [Set.indicator_of_mem hs, Complex.norm_real, Real.norm_eq_abs]
    exact hcr s hs
  · rw [Set.indicator_of_notMem hs, norm_zero]
    exact hr

/-- The spectral projection onto a bounded spectral set lands in the domain, and on its
range the bounded spectral cut acts as `A - c`, expressed as membership in the graph. -/
theorem _root_.IsSelfAdjoint.mem_graph_spectralCut (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) (c r : ℝ) (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) (x : H) :
    ((A.spectralPVM hA).proj B hB x,
      A.spectralCut hA B hB c r hr hcr x + (c : ℂ) • (A.spectralPVM hA).proj B hB x)
        ∈ A.graph := by
  let f := BoundedBorelFunction.indicator B hB 1
  let g := cutSymbol B hB c r hr hcr + (c : ℂ) • f
  have hfg (s : ℝ) : (s : ℂ) * f s = g s := by
    simp only [g, BoundedBorelFunction.add_apply, BoundedBorelFunction.smul_apply,
      cutSymbol, BoundedBorelFunction.ofFunction_apply, f,
      BoundedBorelFunction.indicator_apply]
    by_cases hs : s ∈ B
    · simp only [Set.indicator_of_mem hs, BoundedBorelFunction.one_apply,
        Complex.ofReal_sub, mul_one]
      ring
    · simp only [Set.indicator_of_notMem hs, mul_zero, add_zero]
  have h := hA.mem_graph_integral_spectralPVM f g hfg x
  simpa only [g, f, _root_.map_add, _root_.map_smul, _root_.add_apply, _root_.smul_apply,
    ProjValMeasure.integral_indicator, spectralCut] using h

private def reciprocalSymbol (δ : ℝ) (hδ : 0 < δ) : BoundedBorelFunction ℝ :=
  BoundedBorelFunction.ofFunction (fun s => if δ ≤ |s| then (s : ℂ)⁻¹ else 0)
    (Measurable.ite (measurableSet_le measurable_const (by fun_prop))
      (by fun_prop) measurable_const) ⟨δ⁻¹, by positivity, fun s => by
      split_ifs with hs
      · simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, one_div] using
          one_div_le_one_div_of_le hδ hs
      · simp only [norm_zero]; positivity⟩

/-- The bounded reciprocal spectral multiplier outside `(-δ, δ)`, zero inside that interval. -/
def spectralGapInverse (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (δ : ℝ) (hδ : 0 < δ) :
    H →L[ℂ] H := (A.spectralPVM hA).integral (reciprocalSymbol δ hδ)

/-- Characterization of the gap inverse by the cut-off reciprocal symbol. -/
theorem _root_.IsSelfAdjoint.spectralGapInverse_eq_integral (hA : IsSelfAdjoint A)
    (δ : ℝ) (hδ : 0 < δ) (f : BoundedBorelFunction ℝ)
    (hf : ∀ s, f s = if δ ≤ |s| then (s : ℂ)⁻¹ else 0) :
    A.spectralGapInverse hA δ hδ = (A.spectralPVM hA).integral f := by
  unfold spectralGapInverse
  congr 1
  ext s
  simpa only [reciprocalSymbol, BoundedBorelFunction.ofFunction_apply] using (hf s).symm

/-- The spectral gap inverse has norm at most the reciprocal gap, without a support
hypothesis on the vector. -/
theorem _root_.IsSelfAdjoint.norm_spectralGapInverse_le (hA : IsSelfAdjoint A)
    (δ : ℝ) (hδ : 0 < δ) : ‖A.spectralGapInverse hA δ hδ‖ ≤ δ⁻¹ := by
  unfold spectralGapInverse
  apply ProjValMeasure.norm_integral_le _ (by positivity)
  intro s
  simp only [reciprocalSymbol, BoundedBorelFunction.ofFunction_apply]
  split_ifs with hs
  · simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, one_div] using
      one_div_le_one_div_of_le hδ hs
  · simp only [norm_zero]; positivity

/-- The spectral gap inverse satisfies the reciprocal-gap bound on every vector. -/
theorem _root_.IsSelfAdjoint.norm_spectralGapInverse_apply_le (hA : IsSelfAdjoint A)
    (δ : ℝ) (hδ : 0 < δ) (x : H) :
    ‖A.spectralGapInverse hA δ hδ x‖ ≤ δ⁻¹ * ‖x‖ :=
  (ContinuousLinearMap.le_opNorm _ x).trans (mul_le_mul_of_nonneg_right
    (hA.norm_spectralGapInverse_le δ hδ) (norm_nonneg x))

/-- The reciprocal cut-off solves `A y = x` whenever the diagonal spectral measure of x
gives no mass to the gap. In particular, y belongs to the actual domain of A. -/
theorem _root_.IsSelfAdjoint.mem_graph_spectralGapInverse (hA : IsSelfAdjoint A)
    (δ : ℝ) (hδ : 0 < δ) (x : H)
    (hgap : (A.spectralPVM hA).diag x (Set.Ioo (-δ) δ) = 0) :
    (A.spectralGapInverse hA δ hδ x, x) ∈ A.graph := by
  let B : Set ℝ := {s | δ ≤ |s|}
  have hB : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
  let g := BoundedBorelFunction.indicator B hB 1
  have hfg (s : ℝ) : (s : ℂ) * reciprocalSymbol δ hδ s = g s := by
    simp only [reciprocalSymbol, BoundedBorelFunction.ofFunction_apply]
    by_cases hs : δ ≤ |s|
    · have hs0 : (s : ℂ) ≠ 0 := by
        simpa using (ne_of_gt (lt_of_lt_of_le hδ hs) : |s| ≠ 0)
      simp [g, B, hs, hs0]
    · simp [g, B, hs]
  have hc : Bᶜ = Set.Ioo (-δ) δ := by
    ext s
    simp only [B, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Set.mem_Ioo, abs_lt]
  have hpx := ((A.spectralPVM hA).proj_apply_eq_self_iff hB x).2 (by rw [hc, hgap])
  have h := hA.mem_graph_integral_spectralPVM (reciprocalSymbol δ hδ) g hfg x
  simpa only [g, ProjValMeasure.integral_indicator, hpx, spectralGapInverse] using h

end LinearPMap
