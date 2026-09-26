/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Vitali's convergence theorem for maps into a pseudometric space

Let `μ` be a finite measure on `X` and let `T n, T₀ : X → Y` be almost-everywhere measurable
maps into a second-countable pseudometric space. Mathlib's Vitali convergence theorem
`MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite` characterises `Lᵖ` convergence of
vector-valued functions as convergence in measure together with uniform integrability. This file
transports it to `Y`-valued maps through the real-valued distances: for `1 ≤ p < ∞` and maps with
finite `p`-th moment about a basepoint `y₀`, the distances `dist (T n x) (T₀ x)` converge to `0`
in `Lᵖ(μ)` exactly when `T n` converges to `T₀` in measure and the family `dist (T n ·) y₀` is
uniformly integrable in `Lᵖ(μ)`.

The uniform integrability of `dist (T n ·) y₀` does not depend on the basepoint `y₀`: by the
triangle inequality, changing the basepoint changes each distance by at most the constant
`dist y₀ y₁`, and constants are uniformly integrable over a finite measure. Uniform integrability is
Mathlib's `MeasureTheory.UnifIntegrable`, the predicate its Vitali theorem uses. Mathlib's stronger
`MeasureTheory.UniformIntegrable` adds a uniform `Lᵖ` bound on the family; under the hypotheses of
the convergence theorem the two predicates coincide, because the `Lᵖ` convergence supplies the
bound: a convergent sequence of finite norms is bounded.

## Main statements

* `TauCeti.memLp_dist_of_memLp_dist` — two maps with finite `p`-th moment about a basepoint have
  a distance with finite `p`-th moment;
* `TauCeti.eLpNorm_dist_le_eLpNorm_dist_add`, `MeasureTheory.UnifIntegrable.dist_of_memLp_dist`
  and `MeasureTheory.UniformIntegrable.dist_of_memLp_dist` — the triangle inequality lifted to
  `Lᵖ` norms of distances and to uniform integrability, with and without the uniform `Lᵖ` bound;
* `TauCeti.unifIntegrable_dist_iff_dist` and `TauCeti.uniformIntegrable_dist_iff_dist` — uniform
  integrability of the distances to a basepoint does not depend on the basepoint;
* `TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable` — **Vitali's theorem
  for maps into a pseudometric space**: for `1 ≤ p < ∞`, `Lᵖ` convergence of `dist (T n ·) (T₀ ·)`
  to `0` is convergence in measure together with uniform integrability of `dist (T n ·) y₀`;
* `TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_uniformIntegrable` — the same with
  `MeasureTheory.UniformIntegrable`, which also records the uniform `Lᵖ` bound.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, second edition, Birkhäuser 2008, Lemma 5.4.1, whose `Lᵖ` refinement is
  the statement proved here.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [PseudoMetricSpace Y]

/-- The triangle inequality `dist a c ≤ dist a b + dist b c` between norms of real numbers, in
the form `MeasureTheory.eLpNorm_mono_ae` and `MeasureTheory.UnifIntegrable.ae_mono` consume. -/
private theorem norm_dist_le_norm_dist_add_dist (a b c : Y) :
    ‖dist a c‖ ≤ ‖dist a b + dist b c‖ := by
  rw [Real.norm_of_nonneg dist_nonneg, Real.norm_of_nonneg (by positivity)]
  exact dist_triangle a b c

/-- The triangle inequality `dist a b ≤ dist a c + dist b c` between norms of real numbers, in
the form `MeasureTheory.MemLp.of_le` and `MeasureTheory.UnifIntegrable.ae_mono` consume. -/
private theorem norm_dist_le_norm_dist_add_dist_right (a b c : Y) :
    ‖dist a b‖ ≤ ‖dist a c + dist b c‖ := by
  rw [Real.norm_of_nonneg dist_nonneg, Real.norm_of_nonneg (by positivity)]
  exact dist_triangle_right a b c

variable [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology Y] {μ : Measure X} {p : ℝ≥0∞}

section MemLp

variable {T T₀ : X → Y} {y₀ : Y}

/-- Two almost-everywhere measurable maps with finite `p`-th moment about a basepoint `y₀` have a
distance with finite `p`-th moment. -/
theorem memLp_dist_of_memLp_dist (hT : AEMeasurable T μ) (hT₀ : AEMeasurable T₀ μ)
    (hTp : MemLp (fun x ↦ dist (T x) y₀) p μ) (hT₀p : MemLp (fun x ↦ dist (T₀ x) y₀) p μ) :
    MemLp (fun x ↦ dist (T x) (T₀ x)) p μ :=
  (hTp.add hT₀p).of_le (hT.dist hT₀).aestronglyMeasurable <|
    ae_of_all _ fun x ↦ norm_dist_le_norm_dist_add_dist_right (T x) (T₀ x) y₀

/-- The triangle inequality for `Lᵖ` norms of distances: for `1 ≤ p`, a map `S : X → Y` and
almost-everywhere measurable maps `T S' : X → Y`, the `Lᵖ(μ)` norm of `dist (T ·) (S' ·)` is at
most the sum of those of `dist (T ·) (S ·)` and `dist (S ·) (S' ·)`. -/
theorem eLpNorm_dist_le_eLpNorm_dist_add {S S' : X → Y} (hp : 1 ≤ p) (hT : AEMeasurable T μ)
    (hS' : AEMeasurable S' μ) :
    eLpNorm (fun x ↦ dist (T x) (S' x)) p μ ≤
      eLpNorm (fun x ↦ dist (T x) (S x)) p μ + eLpNorm (fun x ↦ dist (S x) (S' x)) p μ :=
  (eLpNorm_add_le (f := fun x ↦ dist (T x) (S x)) (g := fun x ↦ dist (S x) (S' x)) hp).trans'
    (eLpNorm_mono_ae (hT.dist hS').aestronglyMeasurable <| ae_of_all _ fun x ↦
      norm_dist_le_norm_dist_add_dist (T x) (S x) (S' x))

/-- Uniform integrability in `Lᵖ(μ)` of the distances `dist (T i ·) (S ·)` to a reference map `S`
passes to any almost-everywhere measurable reference map `S'` with `dist (S ·) (S' ·)` of finite
`p`-th moment, for `1 ≤ p < ∞`: by the triangle inequality, changing the reference map changes
each distance by at most the fixed `Lᵖ` function `dist (S ·) (S' ·)`, and a single `Lᵖ` function
is uniformly integrable. -/
theorem _root_.MeasureTheory.UnifIntegrable.dist_of_memLp_dist {ι : Type*} {T : ι → X → Y}
    {S S' : X → Y} (h : UnifIntegrable (fun i x ↦ dist (T i x) (S x)) p μ) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hT : ∀ i, AEMeasurable (T i) μ) (hS' : AEMeasurable S' μ)
    (hSS' : MemLp (fun x ↦ dist (S x) (S' x)) p μ) :
    UnifIntegrable (fun i x ↦ dist (T i x) (S' x)) p μ :=
  (h.add (unifIntegrable_const hp hp' hSS') hp).ae_mono
    (fun i ↦ ((hT i).dist hS').aestronglyMeasurable) fun i ↦ ae_of_all _ fun x ↦
      enorm_le_iff_norm_le.2 (norm_dist_le_norm_dist_add_dist (T i x) (S x) (S' x))

/-- Uniform integrability in `Lᵖ(μ)` with a uniform `Lᵖ` bound of the distances `dist (T i ·) (S ·)`
to a reference map `S` passes to any almost-everywhere measurable reference map `S'` with
`dist (S ·) (S' ·)` of finite `p`-th moment, for `1 ≤ p < ∞`: the uniform bound grows by the
`Lᵖ` norm of `dist (S ·) (S' ·)`. -/
theorem _root_.MeasureTheory.UniformIntegrable.dist_of_memLp_dist {ι : Type*} {T : ι → X → Y}
    {S S' : X → Y} (h : UniformIntegrable (fun i x ↦ dist (T i x) (S x)) p μ) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hT : ∀ i, AEMeasurable (T i) μ) (hS' : AEMeasurable S' μ)
    (hSS' : MemLp (fun x ↦ dist (S x) (S' x)) p μ) :
    UniformIntegrable (fun i x ↦ dist (T i x) (S' x)) p μ := by
  obtain ⟨hui, C, hC⟩ := h
  refine ⟨hui.dist_of_memLp_dist hp hp' hT hS' hSS',
    C + (eLpNorm (fun x ↦ dist (S x) (S' x)) p μ).toNNReal, fun i ↦ ?_⟩
  rw [ENNReal.coe_add, ENNReal.coe_toNNReal hSS'.eLpNorm_ne_top]
  exact (eLpNorm_dist_le_eLpNorm_dist_add (S := S) hp (hT i) hS').trans (add_le_add_left (hC i) _)

end MemLp

section Basepoint

variable [IsFiniteMeasure μ] {ι : Type*} {T : ι → X → Y} {y₀ y₁ : Y}

/-- Uniform integrability in `Lᵖ(μ)` of the distances `dist (T i ·) y₀` does not depend on the
basepoint `y₀`, for `1 ≤ p < ∞` and a finite measure `μ`: changing the basepoint changes each
distance by at most the constant `dist y₀ y₁`. -/
theorem unifIntegrable_dist_iff_dist (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ i, AEMeasurable (T i) μ) :
    UnifIntegrable (fun i x ↦ dist (T i x) y₀) p μ ↔
      UnifIntegrable (fun i x ↦ dist (T i x) y₁) p μ := by
  suffices key : ∀ y₀ y₁ : Y, UnifIntegrable (fun i x ↦ dist (T i x) y₀) p μ →
      UnifIntegrable (fun i x ↦ dist (T i x) y₁) p μ from ⟨key y₀ y₁, key y₁ y₀⟩
  intro y₀ y₁ h
  exact h.dist_of_memLp_dist hp hp' hT aemeasurable_const (memLp_const (dist y₀ y₁))

/-- Uniform integrability in `Lᵖ(μ)` with a uniform `Lᵖ` bound of the distances `dist (T i ·) y₀`
does not depend on the basepoint `y₀`, for `1 ≤ p < ∞` and a finite measure `μ`. -/
theorem uniformIntegrable_dist_iff_dist (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ i, AEMeasurable (T i) μ) :
    UniformIntegrable (fun i x ↦ dist (T i x) y₀) p μ ↔
      UniformIntegrable (fun i x ↦ dist (T i x) y₁) p μ := by
  suffices key : ∀ y₀ y₁ : Y, UniformIntegrable (fun i x ↦ dist (T i x) y₀) p μ →
      UniformIntegrable (fun i x ↦ dist (T i x) y₁) p μ from ⟨key y₀ y₁, key y₁ y₀⟩
  intro y₀ y₁ h
  exact h.dist_of_memLp_dist hp hp' hT aemeasurable_const (memLp_const (dist y₀ y₁))

end Basepoint

section Vitali

variable [IsFiniteMeasure μ] {T : ℕ → X → Y} {T₀ : X → Y} {y₀ : Y}

/-- **Vitali's convergence theorem for maps into a pseudometric space.** Let `1 ≤ p < ∞`, let
`μ` be a finite measure, and let the almost-everywhere measurable maps `T n, T₀ : X → Y` have
finite `p`-th moment about a point `y₀`. Then `dist (T n x) (T₀ x)` tends to `0` in `Lᵖ(μ)` if
and only if `T n` converges to `T₀` in `μ`-measure and the family `dist (T n ·) y₀` is uniformly
integrable in `Lᵖ(μ)`. -/
theorem tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ n, AEMeasurable (T n) μ) (hT₀ : AEMeasurable T₀ μ)
    (hTp : ∀ n, MemLp (fun x ↦ dist (T n x) y₀) p μ) (hT₀p : MemLp (fun x ↦ dist (T₀ x) y₀) p μ) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ) atTop (𝓝 0) ↔
      TendstoInMeasure μ T atTop T₀ ∧ UnifIntegrable (fun n x ↦ dist (T n x) y₀) p μ := by
  -- convergence in measure of the maps is convergence in measure of their distances to `0`
  have key : TendstoInMeasure μ T atTop T₀ ↔
      TendstoInMeasure μ (fun n x ↦ dist (T n x) (T₀ x)) atTop 0 := by
    simp only [tendstoInMeasure_iff_dist, Pi.zero_apply, Real.dist_0_eq_abs, abs_dist]
  have hdp : ∀ n, MemLp (fun x ↦ dist (T n x) (T₀ x)) p μ := fun n ↦
    memLp_dist_of_memLp_dist (hT n) hT₀ (hTp n) hT₀p
  -- Vitali's theorem for the distances, then transport of uniform integrability between the
  -- reference maps `T₀` and `fun _ ↦ y₀`
  have hV := tendstoInMeasure_iff_tendsto_Lp_finite hp hp' hdp (MemLp.zero (p := p) (μ := μ))
  simp only [sub_zero] at hV
  rw [← hV, key]
  refine and_congr_right fun _ ↦ ⟨fun hui ↦ ?_, fun hui ↦ ?_⟩
  · exact hui.dist_of_memLp_dist hp hp' hT aemeasurable_const hT₀p
  · exact hui.dist_of_memLp_dist hp hp' hT hT₀ (by simpa only [dist_comm] using hT₀p)

/-- **Vitali's convergence theorem for maps into a pseudometric space**, with
`MeasureTheory.UniformIntegrable`: under the hypotheses of
`TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable`, `dist (T n x) (T₀ x)`
tends to `0` in `Lᵖ(μ)` if and only if `T n` converges to `T₀` in `μ`-measure and the family
`dist (T n ·) y₀` is uniformly integrable in `Lᵖ(μ)` with a uniform `Lᵖ` bound. -/
theorem tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_uniformIntegrable (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hT : ∀ n, AEMeasurable (T n) μ) (hT₀ : AEMeasurable T₀ μ)
    (hTp : ∀ n, MemLp (fun x ↦ dist (T n x) y₀) p μ) (hT₀p : MemLp (fun x ↦ dist (T₀ x) y₀) p μ) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ) atTop (𝓝 0) ↔
      TendstoInMeasure μ T atTop T₀ ∧ UniformIntegrable (fun n x ↦ dist (T n x) y₀) p μ := by
  refine ⟨fun hL ↦ ?_, fun ⟨hTm, hui⟩ ↦
    (tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable hp hp' hT hT₀ hTp hT₀p).2
      ⟨hTm, hui.unifIntegrable⟩⟩
  obtain ⟨hTm, hui⟩ :=
    (tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable hp hp' hT hT₀ hTp hT₀p).1 hL
  have hdp : ∀ n, MemLp (fun x ↦ dist (T n x) (T₀ x)) p μ := fun n ↦
    memLp_dist_of_memLp_dist (hT n) hT₀ (hTp n) hT₀p
  -- the convergent sequence of finite `Lᵖ` norms of the distances is bounded
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ n, eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ ≤ C := by
    have ht : Tendsto (fun n ↦ (eLpNorm (fun x ↦ dist (T n x) (T₀ x)) p μ).toNNReal) atTop
        (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.tendsto_toNNReal ENNReal.zero_ne_top).comp hL
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    exact ⟨C, fun n ↦ by
      rw [← ENNReal.coe_toNNReal (hdp n).eLpNorm_ne_top]
      exact ENNReal.coe_le_coe.2 (hC ⟨n, rfl⟩)⟩
  -- the distances to the reference map `T₀` are uniformly integrable with the bound `C`, and the
  -- reference map transports to the basepoint `y₀`
  have hui' : UniformIntegrable (fun n x ↦ dist (T n x) (T₀ x)) p μ :=
    ⟨hui.dist_of_memLp_dist hp hp' hT hT₀ (by simpa only [dist_comm] using hT₀p), C, hC⟩
  exact ⟨hTm, hui'.dist_of_memLp_dist hp hp' hT aemeasurable_const hT₀p⟩

end Vitali

end TauCeti
