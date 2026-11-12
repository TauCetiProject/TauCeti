/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.MeasureTheory.Function.BoundedBorel
public import TauCeti.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Simultaneous continuous approximation for finitely many measures

Let `α` be a normal topological space with its Borel σ-algebra, for instance a compact Hausdorff
space, and let `μ i` be finitely many weakly regular measures on `α`. A function `f : α → E`
with values in a real normed space that is integrable for every `μ i` is approximated in
`L¹(μ i)`, simultaneously for all `i`, by a single continuous function `g`: approximate `f` in
`L¹` of the sum measure `∑ i, μ i`, which is again weakly regular, and use monotonicity of the
integral in the measure.

If the measures are finite and `‖f x‖ ≤ M` everywhere, the approximant can be chosen with the
same bound. Composing `g` with the radial retraction onto the closed ball of radius `M` keeps it
continuous, does not move the values of `f`, and at most doubles the distance from them, so it
costs only a factor of two in each `L¹` error. A sequence of such approximants then has `L¹`
errors tending to zero for every `μ i`.

This is the approximation step that extends a representation of the continuous functions on a
compact Hausdorff space to bounded Borel functions: the scalar measures of the representation are
finitely many finite regular measures at a time, and the uniform bound keeps the approximating
operators bounded.

## Main results

* `MeasureTheory.exists_continuous_forall_integral_norm_sub_le`: an integrable function is
  approximated in `L¹(μ i)` for all `i` at once by one continuous function.
* `MeasureTheory.exists_continuous_norm_le_forall_integral_norm_sub_le`: a function bounded by
  `M` is approximated in this way by a continuous function bounded by `M`.
* `MeasureTheory.exists_seq_continuous_norm_le_tendsto_integral_norm_sub`: a sequence of
  continuous functions bounded by `M` whose `L¹(μ i)` distances to `f` tend to zero for all `i`.
* `TauCeti.BoundedBorelFunction.eq_of_forall_ofContinuousMap_eq`: on a compact normal space, two
  maps on bounded Borel symbols that are Lipschitz for `L¹` distances against finite weakly
  regular measures and agree on continuous symbols are equal.

## Provenance

The sum-measure argument for a finite family is adapted from
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean` in the Kitware DKPS
formalization.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Theorem 3.14 (density of
  continuous functions in `L^p`) and Lusin's theorem 2.24 (radial truncation of approximants).
-/

public section

open Filter Topology

namespace MeasureTheory

variable {α : Type*} [TopologicalSpace α] [NormalSpace α] [MeasurableSpace α] [BorelSpace α]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Finite ι] {μ : ι → Measure α} [∀ i, (μ i).WeaklyRegular]

/-- **Simultaneous continuous approximation in `L¹`.** On a normal Borel space, a function that is
integrable for each of finitely many weakly regular measures `μ i` is approximated in
`L¹(μ i)`, for all `i` at once, by a single continuous function integrable for every `μ i`. -/
theorem exists_continuous_forall_integral_norm_sub_le {f : α → E}
    (hf : ∀ i, Integrable f (μ i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(α, E), ∀ i, Integrable g (μ i) ∧ ∫ x, ‖f x - g x‖ ∂μ i ≤ ε := by
  have := Fintype.ofFinite ι
  have hfμ : Integrable f (∑ i, μ i) := integrable_finsetSum_measure.2 fun i _ ↦ hf i
  -- Approximate in `L¹` of the sum measure, which dominates every `μ i`.
  obtain ⟨g, hfg, hg⟩ := hfμ.exists_boundedContinuous_integral_sub_le hε
  refine ⟨g.toContinuousMap, fun i ↦ ?_⟩
  have hle : μ i ≤ ∑ j, μ j :=
    Finset.single_le_sum (f := μ) (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ i)
  exact ⟨hg.mono_measure hle, (integral_mono_measure hle (.of_forall fun _ ↦ norm_nonneg _)
    (hfμ.sub hg).norm).trans hfg⟩

variable [∀ i, IsFiniteMeasure (μ i)]

/-- **Simultaneous bounded continuous approximation in `L¹`.** On a normal Borel space, a
function bounded by `M` and almost everywhere strongly measurable for each of finitely many finite
weakly regular measures `μ i` is approximated in `L¹(μ i)`, for all `i` at once, by a single
continuous function that is also bounded by `M` and integrable for every `μ i`. -/
theorem exists_continuous_norm_le_forall_integral_norm_sub_le {f : α → E}
    (hf : ∀ i, AEStronglyMeasurable f (μ i)) {M : ℝ} (hfM : ∀ x, ‖f x‖ ≤ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : C(α, E), (∀ x, ‖g x‖ ≤ M) ∧
      ∀ i, Integrable g (μ i) ∧ ∫ x, ‖f x - g x‖ ∂μ i ≤ ε := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · exact ⟨0, isEmptyElim, fun i ↦ by simp [Measure.eq_zero_of_isEmpty (μ i), hε.le]⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hfM x₀)
  have hfi i : Integrable f (μ i) := .of_bound (hf i) M (.of_forall hfM)
  obtain ⟨g, hg⟩ := exists_continuous_forall_integral_norm_sub_le hfi (half_pos hε)
  -- Retract `g` onto the closed ball of radius `M`, which contains every value of `f`.
  let r : C(E, E) :=
    ⟨TauCeti.radialRetraction M, continuous_const.radialRetraction (fun _ ↦ hM) continuous_id⟩
  have hrM x : ‖r x‖ ≤ M := (TauCeti.norm_radialRetraction hM x).trans_le (min_le_right _ _)
  refine ⟨r.comp g, fun x ↦ hrM (g x), fun i ↦ ⟨?_, ?_⟩⟩
  · exact .of_bound (r.continuous.comp_aestronglyMeasurable (hg i).1.1) M
      (.of_forall fun _ ↦ hrM _)
  -- Retraction fixes `f x` and is `2`-Lipschitz, so it at most doubles `‖f x - g x‖`.
  have hdist x : ‖f x - r (g x)‖ ≤ 2 * ‖f x - g x‖ := by
    have := (TauCeti.lipschitzWith_radialRetraction (E := E) hM).dist_le_mul (f x) (g x)
    rwa [TauCeti.radialRetraction_of_norm_le (hfM x), dist_eq_norm, dist_eq_norm,
      NNReal.coe_ofNat] at this
  calc ∫ x, ‖f x - r (g x)‖ ∂μ i ≤ ∫ x, 2 * ‖f x - g x‖ ∂μ i :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
          (((hfi i).sub (hg i).1).norm.const_mul 2) (.of_forall hdist)
    _ = 2 * ∫ x, ‖f x - g x‖ ∂μ i := integral_const_mul _ _
    _ ≤ ε := by linarith [(hg i).2]

/-- **Bounded continuous approximating sequences.** On a normal Borel space, a function bounded by
`M` and almost everywhere strongly measurable for each of finitely many finite weakly regular
measures `μ i` is the limit in `L¹(μ i)`, for all `i` at once, of a sequence of continuous
functions bounded by `M` and integrable for every `μ i`. -/
theorem exists_seq_continuous_norm_le_tendsto_integral_norm_sub {f : α → E}
    (hf : ∀ i, AEStronglyMeasurable f (μ i)) {M : ℝ} (hfM : ∀ x, ‖f x‖ ≤ M) :
    ∃ g : ℕ → C(α, E), (∀ n x, ‖g n x‖ ≤ M) ∧ (∀ n i, Integrable (g n) (μ i)) ∧
      ∀ i, Tendsto (fun n ↦ ∫ x, ‖f x - g n x‖ ∂μ i) atTop (𝓝 0) := by
  choose g hgM hg using fun n : ℕ ↦ exists_continuous_norm_le_forall_integral_norm_sub_le hf hfM
    (Nat.one_div_pos_of_nat (n := n))
  refine ⟨g, hgM, fun n i ↦ (hg n i).1, fun i ↦ ?_⟩
  exact squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun n ↦ (hg n i).2)
    tendsto_one_div_add_atTop_nhds_zero_nat

end MeasureTheory

namespace TauCeti.BoundedBorelFunction

open MeasureTheory

variable {α : Type*} [TopologicalSpace α] [NormalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {F : Type*} [MetricSpace F]

/-- **Extension from continuous symbols.** Let `ν₁` and `ν₂` be finite weakly regular measures on a
compact normal Borel space. If `Φ` is Lipschitz for the `L¹(ν₁)` distance of bounded Borel
symbols, `Ψ` is Lipschitz for the `L¹(ν₂)` distance, and `Φ` and `Ψ` agree on continuous symbols,
then they agree on every bounded Borel symbol: continuous symbols bounded by `‖f‖` approximate `f`
in `L¹(ν₁)` and `L¹(ν₂)` at once. -/
theorem eq_of_forall_ofContinuousMap_eq {ν₁ ν₂ : Measure α} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] [ν₁.WeaklyRegular] [ν₂.WeaklyRegular]
    {Φ Ψ : BoundedBorelFunction α → F} {C₁ C₂ : ℝ}
    (hΦ : ∀ f g, dist (Φ f) (Φ g) ≤ C₁ * ∫ x, ‖f x - g x‖ ∂ν₁)
    (hΨ : ∀ f g, dist (Ψ f) (Ψ g) ≤ C₂ * ∫ x, ‖f x - g x‖ ∂ν₂)
    (h : ∀ g : C(α, ℂ), Φ (ofContinuousMap g) = Ψ (ofContinuousMap g)) : Φ = Ψ := by
  funext f
  let ν : Bool → Measure α := fun b ↦ cond b ν₁ ν₂
  have : ∀ b, IsFiniteMeasure (ν b) := fun b ↦ by cases b <;> assumption
  have : ∀ b, (ν b).WeaklyRegular := fun b ↦ by cases b <;> assumption
  obtain ⟨g, -, -, hg⟩ := exists_seq_continuous_norm_le_tendsto_integral_norm_sub (μ := ν)
    (fun _ ↦ f.measurable.aestronglyMeasurable) f.norm_coe_le_norm
  -- A map that is Lipschitz for the `L¹(ν b)` distance sends the approximants to its value at `f`.
  have key {G : BoundedBorelFunction α → F} {C : ℝ} (b : Bool)
      (hG : ∀ f g, dist (G f) (G g) ≤ C * ∫ x, ‖f x - g x‖ ∂ν b) :
      Tendsto (fun n ↦ G (ofContinuousMap (g n))) atTop (𝓝 (G f)) := by
    refine tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ hG _ _) ?_
    simpa [norm_sub_rev] using (hg b).const_mul C
  exact tendsto_nhds_unique ((key true hΦ).congr fun n ↦ h (g n)) (key false hΨ)

end TauCeti.BoundedBorelFunction
