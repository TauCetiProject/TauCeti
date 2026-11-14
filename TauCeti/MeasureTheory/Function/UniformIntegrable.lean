/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Uniform-integrability domination criteria and pseudometric Vitali convergence

For normed-group-valued families over arbitrary measures, this file supplies norm-domination
criteria for `MeasureTheory.UniformIntegrable`, including its uniform `Lᵖ` bound: domination by
another such family, by one `Lᵖ` function, or in `p`-th power by an integrable extended-real
majorant. A countable-supremum criterion follows from the last form.

For the Vitali convergence results, let `μ` be a finite measure on `X` and let `T n, T₀ : X → Y`
be almost-everywhere strongly measurable maps into a pseudometric space; no measurable structure
on `Y` is involved. Mathlib's Vitali convergence theorem
`MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite` characterises `Lᵖ` convergence of
vector-valued functions as convergence in measure together with uniform
integrability. This file transports it to `Y`-valued maps through the real-valued distances: for
`1 ≤ p < ∞` and maps with finite `p`-th moment about a basepoint `y₀`, the distances
`dist (T n x) (T₀ x)` converge to `0` in `Lᵖ(μ)` exactly when `T n` converges to `T₀` in measure
and the family `dist (T n ·) y₀` is uniformly integrable in `Lᵖ(μ)`.

The uniform integrability of `dist (T n ·) y₀` does not depend on the basepoint `y₀`: by the
triangle inequality, changing the basepoint changes each distance by at most the constant
`dist y₀ y₁`, and constants are uniformly integrable over a finite measure. Uniform integrability is
Mathlib's `MeasureTheory.UnifIntegrable`, the predicate its Vitali theorem uses. Mathlib's stronger
`MeasureTheory.UniformIntegrable` adds a uniform `Lᵖ` bound on the family. The convergence theorem
is stated with either predicate: when the `Lᵖ` convergence of the distances is assumed, the
convergent sequence of their finite `Lᵖ` norms is bounded, and this bound upgrades
`MeasureTheory.UnifIntegrable` to `MeasureTheory.UniformIntegrable`.

## Main statements

* `MeasureTheory.UniformIntegrable.ae_mono` — uniform integrability, including a uniform `Lᵖ`
  bound, passes to a family dominated almost everywhere in norm, even with a different codomain;
* `MeasureTheory.MemLp.uniformIntegrable_of_eNorm_le` — a family dominated almost everywhere
  in norm by one `Lᵖ` function is uniformly integrable, with a uniform `Lᵖ` bound;
* `TauCeti.uniformIntegrable_of_eNorm_rpow_le_of_lintegral_lt_top` — domination of `p`-th powers
  of norms by an integrable extended-real majorant gives uniform integrability and a uniform
  `Lᵖ` bound;
* `TauCeti.uniformIntegrable_of_lintegral_iSup_eNorm_rpow_lt_top` — a countable family with
  integrable supremum of its `p`-th powers of norms is uniformly integrable with a uniform
  `Lᵖ` bound;
* `TauCeti.memLp_dist_of_memLp_dist` — two maps whose distances to a common reference map have
  finite `p`-th moment have a distance with finite `p`-th moment;
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

/-- Uniform integrability, including a uniform `Lᵖ` bound, passes to an almost everywhere
norm-dominated family. The two families may take values in different normed groups. -/
theorem MeasureTheory.UniformIntegrable.ae_mono {α β γ ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup β] [NormedAddCommGroup γ]
    {μ : Measure α} {p : ℝ≥0∞} {D : ι → α → γ} {V : ι → α → β}
    (hUI : UniformIntegrable D p μ) (hV : ∀ i, AEStronglyMeasurable (V i) μ)
    (hle : ∀ i, ∀ᵐ x ∂μ, ‖V i x‖ₑ ≤ ‖D i x‖ₑ) : UniformIntegrable V p μ := by
  constructor
  · refine unifIntegrable_iff.2 fun ε hε ↦ ?_
    obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff.1 hUI.1 ε hε
    refine ⟨δ, hδ, fun i s hs ↦ ?_⟩
    exact (eLpNorm_mono_eNorm_ae (hV i).restrict
      ((hle i).filter_mono ae_restrict_le)).trans (hbound i s hs)
  · exact lt_of_le_of_lt (iSup_le fun i ↦ (eLpNorm_mono_eNorm_ae (hV i) (hle i)).trans
      (le_iSup (fun i ↦ eLpNorm (D i) p μ) i)) hUI.iSup_eLpNorm_lt

/-- A family dominated almost everywhere in norm by one `Lᵖ` function is uniformly integrable
in `Lᵖ`, including a uniform bound on its `Lᵖ` norms, for `1 ≤ p < ∞`. -/
theorem MeasureTheory.MemLp.uniformIntegrable_of_eNorm_le {α β γ ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup β] [NormedAddCommGroup γ]
    {μ : Measure α} {p : ℝ≥0∞} {D : α → γ} {V : ι → α → β}
    (hD : MemLp D p μ) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hV : ∀ i, AEStronglyMeasurable (V i) μ)
    (hle : ∀ i, ∀ᵐ x ∂μ, ‖V i x‖ₑ ≤ ‖D x‖ₑ) : UniformIntegrable V p μ :=
  (uniformIntegrable_const hp hp_top hD).ae_mono hV hle

namespace TauCeti

/-- A family whose `p`-th powers of norms are dominated almost everywhere by an integrable
extended-real majorant is uniformly integrable with a uniform `Lᵖ` bound, for `1 ≤ p < ∞`.
The measure need not be finite, and the index type may be arbitrary. -/
theorem uniformIntegrable_of_eNorm_rpow_le_of_lintegral_lt_top {α β ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup β] {μ : Measure α} {p : ℝ≥0∞}
    {V : ι → α → β} {G : α → ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hV : ∀ i, AEStronglyMeasurable (V i) μ) (hG : AEMeasurable G μ)
    (hfin : ∫⁻ x, G x ∂μ < ∞)
    (hle : ∀ i, ∀ᵐ x ∂μ, ‖V i x‖ₑ ^ p.toReal ≤ G x) : UniformIntegrable V p μ := by
  have hp_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
  have hfinite : ∀ᵐ x ∂μ, G x ^ p.toReal⁻¹ ≠ ∞ :=
    (ae_lt_top' hG hfin.ne).mono fun x hx ↦
      ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hp_pos.le) hx.ne
  have hD : MemLp (fun x ↦ (G x ^ p.toReal⁻¹).toReal) p μ := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp_zero hp_top
      (hG.pow_const _).ennreal_toReal.aestronglyMeasurable).2
    exact lt_of_eq_of_lt (lintegral_congr_ae <| hfinite.mono fun x hx ↦ by
      simp only [Real.eNorm_toReal hx, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp_pos.ne',
        ENNReal.rpow_one]) hfin
  exact hD.uniformIntegrable_of_eNorm_le hp hp_top hV fun i ↦ by
    filter_upwards [hfinite, hle i] with x hx hi
    rw [Real.eNorm_toReal hx]
    exact (ENNReal.le_rpow_inv_iff hp_pos).2 hi

/-- A countable family is uniformly integrable in `Lᵖ`, with a uniform `Lᵖ` bound, if the
supremum of the `p`-th powers of its norms has finite integral, for `1 ≤ p < ∞`.
The measure need not be finite. -/
theorem uniformIntegrable_of_lintegral_iSup_eNorm_rpow_lt_top {α β ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup β] [Countable ι] {μ : Measure α} {p : ℝ≥0∞}
    {V : ι → α → β} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hV : ∀ i, AEStronglyMeasurable (V i) μ)
    (hfin : ∫⁻ x, ⨆ i, ‖V i x‖ₑ ^ p.toReal ∂μ < ∞) : UniformIntegrable V p μ := by
  exact uniformIntegrable_of_eNorm_rpow_le_of_lintegral_lt_top hp hp_top hV
    (AEMeasurable.iSup fun i ↦ (hV i).eNorm.pow_const _) hfin
    fun i ↦ ae_of_all _ fun x ↦ le_iSup (fun j ↦ ‖V j x‖ₑ ^ p.toReal) i

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

variable [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

section MemLp

variable {T T₀ : X → Y}

/-- Two almost-everywhere strongly measurable maps `T T₀ : X → Y` whose distances to a common
reference map `S : X → Y` have finite `p`-th moment have a distance with finite `p`-th moment. For
a constant `S` this is finiteness of the `p`-th moments about a basepoint. -/
theorem memLp_dist_of_memLp_dist {S : X → Y} (hT : AEStronglyMeasurable T μ)
    (hT₀ : AEStronglyMeasurable T₀ μ) (hTp : MemLp (fun x ↦ dist (T x) (S x)) p μ)
    (hT₀p : MemLp (fun x ↦ dist (T₀ x) (S x)) p μ) :
    MemLp (fun x ↦ dist (T x) (T₀ x)) p μ :=
  (hTp.add hT₀p).of_le (hT.dist hT₀) <|
    ae_of_all _ fun x ↦ norm_dist_le_norm_dist_add_dist_right (T x) (T₀ x) (S x)

/-- The triangle inequality for `Lᵖ` norms of distances: for `1 ≤ p`, a map `S : X → Y` and
almost-everywhere strongly measurable maps `T S' : X → Y`, the `Lᵖ(μ)` norm of
`dist (T ·) (S' ·)` is at most the sum of those of `dist (T ·) (S ·)` and `dist (S ·) (S' ·)`. -/
theorem eLpNorm_dist_le_eLpNorm_dist_add {S S' : X → Y} (hp : 1 ≤ p)
    (hT : AEStronglyMeasurable T μ) (hS' : AEStronglyMeasurable S' μ) :
    eLpNorm (fun x ↦ dist (T x) (S' x)) p μ ≤
      eLpNorm (fun x ↦ dist (T x) (S x)) p μ + eLpNorm (fun x ↦ dist (S x) (S' x)) p μ :=
  (eLpNorm_add_le (f := fun x ↦ dist (T x) (S x)) (g := fun x ↦ dist (S x) (S' x)) hp).trans'
    (eLpNorm_mono_ae (hT.dist hS') <| ae_of_all _ fun x ↦
      norm_dist_le_norm_dist_add_dist (T x) (S x) (S' x))

/-- Uniform integrability in `Lᵖ(μ)` of the distances `dist (T i ·) (S ·)` from almost-everywhere
strongly measurable maps `T i` to a reference map `S` passes to any almost-everywhere strongly
measurable reference map `S'` with `dist (S ·) (S' ·)` of finite `p`-th moment, for `1 ≤ p < ∞`:
by the triangle inequality, changing the reference map changes each distance by at most the fixed
`Lᵖ` function `dist (S ·) (S' ·)`, and a single `Lᵖ` function is uniformly integrable. -/
theorem _root_.MeasureTheory.UnifIntegrable.dist_of_memLp_dist {ι : Type*} {T : ι → X → Y}
    {S S' : X → Y} (h : UnifIntegrable (fun i x ↦ dist (T i x) (S x)) p μ) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hT : ∀ i, AEStronglyMeasurable (T i) μ) (hS' : AEStronglyMeasurable S' μ)
    (hSS' : MemLp (fun x ↦ dist (S x) (S' x)) p μ) :
    UnifIntegrable (fun i x ↦ dist (T i x) (S' x)) p μ :=
  (h.add (unifIntegrable_const hp hp' hSS')).ae_mono
    (fun i ↦ (hT i).dist hS') fun i ↦ ae_of_all _ fun x ↦
      eNorm_le_iff_norm_le.2 (norm_dist_le_norm_dist_add_dist (T i x) (S x) (S' x))

/-- Uniform integrability in `Lᵖ(μ)` with a uniform `Lᵖ` bound of the distances `dist (T i ·) (S ·)`
from almost-everywhere strongly measurable maps `T i` to a reference map `S` passes to any
almost-everywhere strongly measurable reference map `S'` with `dist (S ·) (S' ·)` of finite `p`-th
moment, for `1 ≤ p < ∞`: the uniform bound grows by the `Lᵖ` norm of `dist (S ·) (S' ·)`. -/
theorem _root_.MeasureTheory.UniformIntegrable.dist_of_memLp_dist {ι : Type*} {T : ι → X → Y}
    {S S' : X → Y} (h : UniformIntegrable (fun i x ↦ dist (T i x) (S x)) p μ) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hT : ∀ i, AEStronglyMeasurable (T i) μ) (hS' : AEStronglyMeasurable S' μ)
    (hSS' : MemLp (fun x ↦ dist (S x) (S' x)) p μ) :
    UniformIntegrable (fun i x ↦ dist (T i x) (S' x)) p μ := by
  refine ⟨h.unifIntegrable.dist_of_memLp_dist hp hp' hT hS' hSS', ?_⟩
  refine lt_of_le_of_lt (iSup_le fun i ↦
    (eLpNorm_dist_le_eLpNorm_dist_add (S := S) hp (hT i) hS').trans
      (add_le_add (le_iSup (fun j ↦ eLpNorm (fun x ↦ dist (T j x) (S x)) p μ) i) le_rfl)) ?_
  exact ENNReal.add_lt_top.2 ⟨h.iSup_eLpNorm_lt, hSS'.eLpNorm_lt_top⟩

end MemLp

section Basepoint

variable [IsFiniteMeasure μ] {ι : Type*} {T : ι → X → Y} {y₀ y₁ : Y}

/-- Uniform integrability in `Lᵖ(μ)` of the distances `dist (T i ·) y₀` does not depend on the
basepoint `y₀`, for `1 ≤ p < ∞`, a finite measure `μ` and almost-everywhere strongly measurable
maps `T i`: changing the basepoint changes each distance by at most the constant `dist y₀ y₁`. -/
theorem unifIntegrable_dist_iff_dist (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ i, AEStronglyMeasurable (T i) μ) :
    UnifIntegrable (fun i x ↦ dist (T i x) y₀) p μ ↔
      UnifIntegrable (fun i x ↦ dist (T i x) y₁) p μ := by
  suffices key : ∀ y₀ y₁ : Y, UnifIntegrable (fun i x ↦ dist (T i x) y₀) p μ →
      UnifIntegrable (fun i x ↦ dist (T i x) y₁) p μ from ⟨key y₀ y₁, key y₁ y₀⟩
  intro y₀ y₁ h
  exact h.dist_of_memLp_dist hp hp' hT aestronglyMeasurable_const (memLp_const (dist y₀ y₁))

/-- Uniform integrability in `Lᵖ(μ)` with a uniform `Lᵖ` bound of the distances `dist (T i ·) y₀`
does not depend on the basepoint `y₀`, for `1 ≤ p < ∞`, a finite measure `μ` and
almost-everywhere strongly measurable maps `T i`. -/
theorem uniformIntegrable_dist_iff_dist (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ i, AEStronglyMeasurable (T i) μ) :
    UniformIntegrable (fun i x ↦ dist (T i x) y₀) p μ ↔
      UniformIntegrable (fun i x ↦ dist (T i x) y₁) p μ := by
  suffices key : ∀ y₀ y₁ : Y, UniformIntegrable (fun i x ↦ dist (T i x) y₀) p μ →
      UniformIntegrable (fun i x ↦ dist (T i x) y₁) p μ from ⟨key y₀ y₁, key y₁ y₀⟩
  intro y₀ y₁ h
  exact h.dist_of_memLp_dist hp hp' hT aestronglyMeasurable_const (memLp_const (dist y₀ y₁))

end Basepoint

section Vitali

variable [IsFiniteMeasure μ] {T : ℕ → X → Y} {T₀ : X → Y} {y₀ : Y}

/-- **Vitali's convergence theorem for maps into a pseudometric space.** Let `1 ≤ p < ∞`, let
`μ` be a finite measure, and let the almost-everywhere strongly measurable maps
`T n, T₀ : X → Y` have finite `p`-th moment about a point `y₀`. Then `dist (T n x) (T₀ x)` tends
to `0` in `Lᵖ(μ)` if and only if `T n` converges to `T₀` in `μ`-measure and the family
`dist (T n ·) y₀` is uniformly integrable in `Lᵖ(μ)`. -/
theorem tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hT : ∀ n, AEStronglyMeasurable (T n) μ) (hT₀ : AEStronglyMeasurable T₀ μ)
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
  · exact hui.dist_of_memLp_dist hp hp' hT aestronglyMeasurable_const hT₀p
  · exact hui.dist_of_memLp_dist hp hp' hT hT₀ (by simpa only [dist_comm] using hT₀p)

/-- **Vitali's convergence theorem for maps into a pseudometric space**, with
`MeasureTheory.UniformIntegrable`: under the hypotheses of
`TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable`, `dist (T n x) (T₀ x)`
tends to `0` in `Lᵖ(μ)` if and only if `T n` converges to `T₀` in `μ`-measure and the family
`dist (T n ·) y₀` is uniformly integrable in `Lᵖ(μ)` with a uniform `Lᵖ` bound. -/
theorem tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_uniformIntegrable (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hT : ∀ n, AEStronglyMeasurable (T n) μ) (hT₀ : AEStronglyMeasurable T₀ μ)
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
    ⟨hui.dist_of_memLp_dist hp hp' hT hT₀ (by simpa only [dist_comm] using hT₀p),
      (iSup_le hC).trans_lt ENNReal.coe_lt_top⟩
  exact ⟨hTm, hui'.dist_of_memLp_dist hp hp' hT aestronglyMeasurable_const hT₀p⟩

end Vitali

end TauCeti
