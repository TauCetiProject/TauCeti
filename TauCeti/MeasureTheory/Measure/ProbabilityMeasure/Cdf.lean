/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import TauCeti.Probability.Cdf
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Cumulative-distribution criteria for weak convergence on the real line

A family of probability measures on `ℝ` indexed by a countably generated filter converges weakly if
and only if the cumulative distribution functions converge pointwise at every continuity point of
the limiting cumulative distribution function (the Helly–Bray theorem). More generally, pointwise
convergence on any dense set of reals suffices: the half-open intervals `(a, b]` with endpoints in
that dense set form a π-system containing arbitrarily small neighborhoods of every point, and their
masses are differences of cumulative distribution functions, so Mathlib's portmanteau π-system
criterion `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` applies. Conversely, continuity
of `cdf ν` at `x` is equivalent to `ν {x} = 0`, which makes `Iic x` a `ν`-continuity set since its
boundary lies in `{x}`.

When the limiting law is atomless (`NullSingletonClass`), its cumulative distribution function is
continuous everywhere, so weak convergence and `MeasureTheory.TendstoInDistribution` are equivalent
to pointwise convergence of cumulative distribution functions at every real point.

## Main statements

* `MeasureTheory.ProbabilityMeasure.tendsto_cdf_of_tendsto_of_continuousAt` — weak convergence
  implies convergence of `cdf` at every continuity point of the limiting `cdf`.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_cdf_of_dense` — pointwise `cdf` convergence
  on a dense set implies weak convergence along any countably generated filter.
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_continuousAt_tendsto_cdf` — **Helly–Bray
  theorem**: weak convergence on `ℝ` is equivalent to `cdf` convergence at continuity points of the
  limiting `cdf`.
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_cdf` — for an atomless limit law, weak
  convergence is equivalent to pointwise `cdf` convergence everywhere.
* `MeasureTheory.tendsto_cdf_of_eventually_ae_le_iff_lt` — pointwise `cdf` convergence transferred
  across an eventual almost-everywhere sublevel equivalence `X i ω ≤ x ↔ Y i ω < α i` with
  `α i → x` at a continuity point of the limiting `cdf`.
* `MeasureTheory.tendstoInDistribution_iff_forall_continuousAt_tendsto_cdf` and
  `MeasureTheory.tendstoInDistribution_iff_tendsto_cdf` — counterparts for
  `MeasureTheory.TendstoInDistribution`.

## References

* Patrick Billingsley, *Convergence of Probability Measures*, 2nd edition, Wiley, 1999, §2.
* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter VIII, §1.
-/

public section

open Filter Function ProbabilityTheory Set
open scoped NNReal Topology

namespace MeasureTheory.ProbabilityMeasure

variable {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}

/-- Weak convergence of probability measures on `ℝ` implies convergence of cumulative distribution
functions at every continuity point of the limiting cumulative distribution function. -/
theorem tendsto_cdf_of_tendsto_of_continuousAt (h : Tendsto μs l (𝓝 μ)) {x : ℝ}
    (hx : ContinuousAt (cdf (μ : Measure ℝ)) x) :
    Tendsto (fun i ↦ cdf (μs i : Measure ℝ) x) l (𝓝 (cdf (μ : Measure ℝ) x)) := by
  have hnull : (μ : Measure ℝ) (frontier (Iic x)) = 0 :=
    measure_mono_null (frontier_Iic_subset x)
      ((Measure.continuousAt_cdf_iff (μ : Measure ℝ) x).1 hx)
  have hmeas := tendsto_measure_of_null_frontier_of_tendsto' h hnull
  simpa only [cdf_eq_real, Measure.real, Function.comp_def] using
    (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure ℝ) (Iic x))).comp hmeas

/-- Pointwise convergence of cumulative distribution functions on a dense subset of `ℝ` implies
weak convergence of probability measures along any countably generated filter. -/
theorem tendsto_of_tendsto_cdf_of_dense [l.IsCountablyGenerated] {D : Set ℝ} (hD : Dense D)
    (h : ∀ x ∈ D, Tendsto (fun i ↦ cdf (μs i : Measure ℝ) x) l (𝓝 (cdf (μ : Measure ℝ) x))) :
    Tendsto μs l (𝓝 μ) := by
  set S : Set (Set ℝ) := {s | ∃ a ∈ D, ∃ b ∈ D, s = Ioc a b}
  have hpi : IsPiSystem S := by
    rintro _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ _ ⟨a₂, ha₂, b₂, hb₂, rfl⟩ -
    exact ⟨max a₁ a₂, (max_choice a₁ a₂).elim (·.symm ▸ ha₁) (·.symm ▸ ha₂),
      min b₁ b₂, (min_choice b₁ b₂).elim (·.symm ▸ hb₁) (·.symm ▸ hb₂), Ioc_inter_Ioc⟩
  refine hpi.tendsto_probabilityMeasure_of_tendsto_of_mem ?_ ?_ ?_
  · rintro _ ⟨a, -, b, -, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨a', b', ⟨ha'x, hxb'⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hu.mem_nhds hx)
    obtain ⟨a, ⟨ha'a, hax⟩, haD⟩ := hD.inter_open_nonempty _ isOpen_Ioo (nonempty_Ioo.2 ha'x)
    obtain ⟨b, ⟨hxb, hbb'⟩, hbD⟩ := hD.inter_open_nonempty _ isOpen_Ioo (nonempty_Ioo.2 hxb')
    exact ⟨Ioc a b, ⟨a, haD, b, hbD, rfl⟩, Ioc_mem_nhds hax hxb,
      fun y hy ↦ hsub ⟨ha'a.trans hy.1, hy.2.trans_lt hbb'⟩⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    rcases le_or_gt a b with hab | hba
    · rw [← NNReal.tendsto_coe]
      have hcoe (ρ : ProbabilityMeasure ℝ) :
          (ρ (Ioc a b) : ℝ) = cdf (ρ : Measure ℝ) b - cdf (ρ : Measure ℝ) a := by
        rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn,
          (ρ : Measure ℝ).measureReal_Ioc_eq_cdf_sub hab]
      simpa only [hcoe] using (h b hb).sub (h a ha)
    · simp only [Ioc_eq_empty_of_le hba.le, coeFn_empty]
      exact tendsto_const_nhds

/-- **Helly–Bray theorem.** Along a countably generated filter, probability measures on `ℝ`
converge weakly if and only if their cumulative distribution functions converge pointwise at every
continuity point of the limiting cumulative distribution function. -/
theorem tendsto_iff_forall_continuousAt_tendsto_cdf [l.IsCountablyGenerated] :
    Tendsto μs l (𝓝 μ) ↔
      ∀ x, ContinuousAt (cdf (μ : Measure ℝ)) x →
        Tendsto (fun i ↦ cdf (μs i : Measure ℝ) x) l (𝓝 (cdf (μ : Measure ℝ) x)) where
  mp h _ hx := tendsto_cdf_of_tendsto_of_continuousAt h hx
  mpr h := by
    refine tendsto_of_tendsto_cdf_of_dense
      (((cdf (μ : Measure ℝ)).mono.countable_not_continuousAt).dense_compl ℝ) fun x hx ↦ ?_
    exact h x (not_not.1 hx)

/-- When the limiting law has no atoms, weak convergence of probability measures on `ℝ` along a
countably generated filter is equivalent to pointwise convergence of cumulative distribution
functions everywhere. -/
theorem tendsto_iff_tendsto_cdf [l.IsCountablyGenerated]
    [NullSingletonClass (μ : Measure ℝ)] :
    Tendsto μs l (𝓝 μ) ↔
      ∀ x, Tendsto (fun i ↦ cdf (μs i : Measure ℝ) x) l (𝓝 (cdf (μ : Measure ℝ) x)) := by
  rw [tendsto_iff_forall_continuousAt_tendsto_cdf]
  exact ⟨fun h x ↦ h x (Measure.continuous_cdf_of_noAtoms (μ : Measure ℝ)).continuousAt,
    fun h x _ ↦ h x⟩

end MeasureTheory.ProbabilityMeasure

namespace MeasureTheory

variable {ι Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ} {l : Filter ι}

/-- If `X i ω ≤ x` is eventually almost everywhere equivalent to `Y i ω < α i` with `α i → x`,
and the cumulative distribution functions of `Y i` converge pointwise to a function `Φ` continuous
at `x`, then `cdf ((μ i).map (X i)) x` converges to `Φ x`. -/
theorem tendsto_cdf_of_eventually_ae_le_iff_lt {Y : (i : ι) → Ω i → ℝ} {α : ι → ℝ}
    {Φ : ℝ → ℝ} {x : ℝ} (hX : ∀ i, AEMeasurable (X i) (μ i))
    (hY : ∀ i, AEMeasurable (Y i) (μ i)) (hΦ : ContinuousAt Φ x) (hα : Tendsto α l (𝓝 x))
    (hY_cdf : ∀ y, Tendsto (fun i ↦ cdf ((μ i).map (Y i)) y) l (𝓝 (Φ y)))
    (hinv : ∀ᶠ i in l, ∀ᵐ ω ∂μ i, X i ω ≤ x ↔ Y i ω < α i) :
    Tendsto (fun i ↦ cdf ((μ i).map (X i)) x) l (𝓝 (Φ x)) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨z, hzx, haΦz⟩ := (hΦ.eventually (lt_mem_nhds ha)).exists_lt
    filter_upwards [hinv, (tendsto_order.1 hα).1 z hzx,
      (tendsto_order.1 (hY_cdf z)).1 a haΦz] with i hi hαz hY_gt
    refine hY_gt.trans_le ?_
    rw [Measure.cdf_map (μ i) (Y i) (hY i) z, Measure.cdf_map (μ i) (X i) (hX i) x,
      measureReal_def, measureReal_def]
    refine ENNReal.toReal_mono (measure_ne_top (μ i) _) (measure_mono_ae ?_)
    filter_upwards [hi] with ω hω hYz
    exact hω.2 (lt_of_le_of_lt hYz hαz)
  · obtain ⟨y, hxy, hΦyb⟩ := (hΦ.eventually (gt_mem_nhds hb)).exists_gt
    filter_upwards [hinv, (tendsto_order.1 hα).2 y hxy,
      (tendsto_order.1 (hY_cdf y)).2 b hΦyb] with i hi hαy hY_lt
    refine lt_of_le_of_lt ?_ hY_lt
    rw [Measure.cdf_map (μ i) (X i) (hX i) x, Measure.cdf_map (μ i) (Y i) (hY i) y,
      measureReal_def, measureReal_def]
    refine ENNReal.toReal_mono (measure_ne_top (μ i) _) (measure_mono_ae ?_)
    filter_upwards [hi] with ω hω hXx
    exact (hω.1 hXx).le.trans hαy.le

/-- Convergence in distribution of real random variables implies convergence of cumulative
distribution functions at every continuity point of the limiting cumulative distribution
function. -/
protected theorem TendstoInDistribution.tendsto_cdf_of_continuousAt
    (h : TendstoInDistribution X l Z μ μ') {x : ℝ} (hx : ContinuousAt (cdf (μ'.map Z)) x) :
    Tendsto (fun i ↦ cdf ((μ i).map (X i)) x) l (𝓝 (cdf (μ'.map Z) x)) :=
  ProbabilityMeasure.tendsto_cdf_of_tendsto_of_continuousAt h.tendsto hx

/-- Pointwise convergence of the cumulative distribution functions of real random variables on a
dense set implies convergence in distribution along any countably generated filter. -/
protected theorem TendstoInDistribution.of_tendsto_cdf_of_dense [l.IsCountablyGenerated]
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') {D : Set ℝ} (hD : Dense D)
    (h : ∀ x ∈ D, Tendsto (fun i ↦ cdf ((μ i).map (X i)) x) l (𝓝 (cdf (μ'.map Z) x))) :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable := hX
  aemeasurable_limit := hZ
  tendsto := ProbabilityMeasure.tendsto_of_tendsto_cdf_of_dense hD h

/-- Along a countably generated filter, real random variables converge in distribution if and only
if their cumulative distribution functions converge at every continuity point of the limiting
cumulative distribution function. -/
theorem tendstoInDistribution_iff_forall_continuousAt_tendsto_cdf [l.IsCountablyGenerated]
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ x, ContinuousAt (cdf (μ'.map Z)) x →
        Tendsto (fun i ↦ cdf ((μ i).map (X i)) x) l (𝓝 (cdf (μ'.map Z) x)) where
  mp h _ hx := h.tendsto_cdf_of_continuousAt hx
  mpr h :=
    TendstoInDistribution.of_tendsto_cdf_of_dense hX hZ
      (((cdf (μ'.map Z)).mono.countable_not_continuousAt).dense_compl ℝ)
      fun x hx ↦ h x (not_not.1 hx)

/-- If a family of real random variables converges in distribution to a limit whose law has no
atoms, the cumulative distribution functions converge pointwise everywhere. -/
protected theorem TendstoInDistribution.tendsto_cdf [NullSingletonClass (μ'.map Z)]
    (h : TendstoInDistribution X l Z μ μ') (x : ℝ) :
    Tendsto (fun i ↦ cdf ((μ i).map (X i)) x) l (𝓝 (cdf (μ'.map Z) x)) :=
  h.tendsto_cdf_of_continuousAt (Measure.continuous_cdf_of_noAtoms (μ'.map Z)).continuousAt

/-- Pointwise convergence everywhere of cumulative distribution functions implies convergence in
distribution along any countably generated filter. -/
protected theorem TendstoInDistribution.of_tendsto_cdf [l.IsCountablyGenerated]
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ')
    (h : ∀ x, Tendsto (fun i ↦ cdf ((μ i).map (X i)) x) l (𝓝 (cdf (μ'.map Z) x))) :
    TendstoInDistribution X l Z μ μ' :=
  TendstoInDistribution.of_tendsto_cdf_of_dense hX hZ dense_univ fun x _ ↦ h x

/-- When the limiting law has no atoms, convergence in distribution of real random variables along
a countably generated filter is equivalent to pointwise convergence of their cumulative
distribution functions everywhere. -/
theorem tendstoInDistribution_iff_tendsto_cdf [l.IsCountablyGenerated]
    [NullSingletonClass (μ'.map Z)]
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ x, Tendsto (fun i ↦ cdf ((μ i).map (X i)) x) l (𝓝 (cdf (μ'.map Z) x)) where
  mp := TendstoInDistribution.tendsto_cdf
  mpr := TendstoInDistribution.of_tendsto_cdf hX hZ

end MeasureTheory
