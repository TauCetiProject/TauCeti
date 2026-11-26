/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
public import TauCeti.Analysis.Sobolev.W1p.Interval.Trace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Interval Sobolev functions vanishing on a set

On a bounded interval `(a, b)` every class of `W^{1,p}(a, b)` has a continuous representative on
`[a, b]`, and evaluation of it at a point is a continuous linear functional, for every
`1 ≤ p ≤ ∞`. Consequently, for an arbitrary set `Γ ⊆ ℝ`, every class of the space
`W^{1,p}_Γ(a, b)` of Sobolev functions vanishing on `Γ` (`TauCeti.w1pVanishingOnSubmodule`) has
continuous representative vanishing at every point of `[a, b] ∩ closure Γ`
(`TauCeti.W1p.intervalRepresentativeL_eq_zero_of_mem_w1pVanishingOnSubmodule`): the condition is
closed and holds for every generator, whose support misses `closure Γ`. The points of `Γ` may be
endpoints of the interval, as for a boundary part, or interior points.

Interior points really do constrain the space. On every open set `Ω`, `W^{1,p}_Γ(Ω)` contains
`W^{1,p}_0(Ω)` when `Γ` misses `Ω` (`TauCeti.w1p0Submodule_le_w1pVanishingOnSubmodule`). On an
interval the converse holds for every `p`
(`TauCeti.W1p.w1p0Submodule_Ioo_le_w1pVanishingOnSubmodule_iff`): if `t ∈ Γ ∩ (a, b)`, a smooth
bump supported in `(a, b)` and equal to `1` at `t` lies in `W^{1,p}_0(a, b)` but not in
`W^{1,p}_Γ(a, b)`, since its continuous representative does not vanish at `t`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.2 (the continuous representative of a one-dimensional Sobolev function).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Distributions

namespace TauCeti.W1p

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A class in `W^{1,p}_Γ(a, b)` has continuous representative vanishing at every point of `[a, b]`
in the closure of `Γ`, for every `1 ≤ p ≤ ∞` and every set `Γ`: the condition is closed and holds
for every generator, whose support misses `closure Γ`. -/
theorem intervalRepresentativeL_eq_zero_of_mem_w1pVanishingOnSubmodule (hab : a < b)
    {Γ : Set ℝ} {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p Γ) {t : Icc a b}
    (ht : (t : ℝ) ∈ closure Γ) :
    intervalRepresentativeL hab u t = 0 := by
  refine w1pVanishingOnSubmodule_subset_of_isClosed
    (isClosed_eq ((ContinuousMap.evalCLM ℝ t).comp (intervalRepresentativeL hab)).continuous
      continuous_const) (fun φ hφ ↦ ?_) hu
  rw [mem_ofPred_eq, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
    intervalRepresentativeL_restrictL_ofTestFunctionₗ]
  exact image_eq_zero_of_notMem_tsupport (hφ.notMem_of_mem_right ht)

/-- For every interior point `t` of `(a, b)` there is a class of `W^{1,p}_0(a, b)` whose continuous
representative is `1` at `t`: the restriction of a smooth bump centred at `t` and supported in
`(a, b)`. -/
private theorem exists_mem_w1p0Submodule_intervalRepresentativeL_eq_one {t : ℝ}
    (ht : t ∈ Ioo a b) :
    ∃ u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      intervalRepresentativeL (ht.1.trans ht.2) u ⟨t, Ioo_subset_Icc_self ht⟩ = 1 := by
  set r := min (t - a) (b - t)
  have hr0 : 0 < r := lt_min (sub_pos.2 ht.1) (sub_pos.2 ht.2)
  let f : ContDiffBump t := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsub : tsupport f ⊆ Ioo a b := by
    rw [f.tsupport_eq, Real.closedBall_eq_Icc]
    refine Icc_subset_Ioo ?_ ?_ <;> simp only [f] <;>
      linarith [min_le_left (t - a) (b - t), min_le_right (t - a) (b - t)]
  let φ : 𝓓((⊤ : Opens ℝ), ℝ) := ⟨f, f.contDiff, f.hasCompactSupport, subset_univ _⟩
  let ψ : 𝓓((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ), ℝ) := ⟨f, f.contDiff, f.hasCompactSupport, hsub⟩
  refine ⟨restrictL le_top (ofTestFunctionₗ volume ⊤ p φ), ?_, ?_⟩
  · rw [restrictL_ofTestFunctionₗ_eq_of_eqOn le_top (ψ := ψ) fun _ _ ↦ rfl]
    exact ofTestFunctionₗ_mem_w1p0Submodule ψ
  · rw [intervalRepresentativeL_restrictL_ofTestFunctionₗ]
    exact f.one_of_mem_closedBall (mem_closedBall_self f.rIn_pos.le)

/-- **`W^{1,p}_0(a, b) ≤ W^{1,p}_Γ(a, b)` exactly when `Γ` misses `(a, b)`**, for every
`1 ≤ p ≤ ∞`. One direction holds on every open set
(`TauCeti.w1p0Submodule_le_w1pVanishingOnSubmodule`). Conversely, at a point `t ∈ Γ ∩ (a, b)` a
smooth bump supported in `(a, b)` with value `1` at `t` lies in `W^{1,p}_0(a, b)`, while every class
of `W^{1,p}_Γ(a, b)` vanishes at `t`. -/
theorem w1p0Submodule_Ioo_le_w1pVanishingOnSubmodule_iff {Γ : Set ℝ} :
    w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p ≤
        w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p Γ ↔
      Disjoint Γ (Ioo a b) := by
  refine ⟨fun h ↦ not_not.1 fun hΓ ↦ ?_, fun hΓ ↦ w1p0Submodule_le_w1pVanishingOnSubmodule hΓ⟩
  obtain ⟨t, htΓ, ht⟩ := not_disjoint_iff.1 hΓ
  obtain ⟨u, hu0, hu1⟩ := exists_mem_w1p0Submodule_intervalRepresentativeL_eq_one (p := p) ht
  have := intervalRepresentativeL_eq_zero_of_mem_w1pVanishingOnSubmodule (ht.1.trans ht.2) (h hu0)
    (t := ⟨t, Ioo_subset_Icc_self ht⟩) (subset_closure htΓ)
  rw [hu1] at this
  exact one_ne_zero this

end TauCeti.W1p
