/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Normed.Operator.Holder

/-!
# Hölder bounds for local derivative fields

On an open convex set, bounds for a derivative field and its next derivative give a Hölder
bound for every exponent at most one. Thus local `C^{k,α}` data need a separate Hölder
hypothesis only at their top derivative. Currying preserves these bounds exactly.
-/

public section

open Set
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- A bounded Lipschitz map is Hölder for every exponent at most one, without a bounded-domain
assumption. The scale-one estimate uses the Lipschitz constant plus twice the value bound. -/
theorem LipschitzOnWith.holderOnWith_of_norm_le {X : Type*} [PseudoMetricSpace X]
    {s : Set X} {f : X → F}
    {L M α : ℝ≥0} (h : LipschitzOnWith L f s) (hb : ∀ x ∈ s, ‖f x‖ ≤ M) (hα : α ≤ 1) :
    HolderOnWith (L + 2 * M) α f s := by
  have hdiam : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ ((2 * M : ℝ≥0) : ℝ) := by
    intro x hx y hy
    rw [dist_eq_norm]
    exact (_root_.norm_sub_le _ _).trans (by push_cast; linarith [hb x hx, hb y hy])
  simpa using h.holderOnWith.of_le_of_dist_le (D := 2 * M) hdiam hα (by norm_num : (0 : ℝ≥0) < 1)

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace TauCeti

/-- Currying preserves the Hölder bound of the top derivative exactly. -/
theorem holderOnWith_iteratedFDeriv_succ_iff {f : E → F} {s : Set E} {j : ℕ}
    {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv ℝ (j + 1) f) s ↔
      HolderOnWith H α (iteratedFDeriv ℝ j (fderiv ℝ f)) s := by
  simp only [holderOnWith_iff_dist_le, iteratedFDeriv_succ_eq_comp_right,
    Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- The order-zero derivative field has the same Hölder constant as the original function. -/
theorem holderOnWith_iteratedFDeriv_zero_iff {f : E → F} {s : Set E} {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv ℝ 0 f) s ↔ HolderOnWith H α f s := by
  simp only [holderOnWith_iff_dist_le, iteratedFDeriv_zero_eq_comp,
    Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- Composing with linear isometries preserves a local Hölder bound on an actual derivative
field, including at points where the function need not be differentiable. -/
theorem _root_.LinearIsometryEquiv.holderOnWith_iteratedFDeriv_comp {E E' T Tu : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup Tu] [NormedSpace ℝ Tu]
    (e : E' ≃ₗᵢ[ℝ] E) (t : T ≃ₗᵢ[ℝ] Tu) (v : E → T)
    {C α : ℝ≥0} (j : ℕ) {S : Set E} (hv : HolderOnWith C α (iteratedFDeriv ℝ j v) S) :
    HolderOnWith C α (iteratedFDeriv ℝ j (t ∘ v ∘ e)) (e ⁻¹' S) := by
  rw [holderOnWith_iff_dist_le] at hv ⊢
  intro x hx y hy
  rw [dist_eq_norm, LinearIsometryEquiv.norm_iteratedFDeriv_sub_comp]
  have hxy := hv (e x) hx (e y) hy
  rw [e.dist_map] at hxy
  simpa only [dist_eq_norm] using hxy

/-- Every derivative field below the top order is Hölder, controlled by the uniform bound on
that field and its next derivative. No Hölder assumption on lower derivatives is needed. -/
theorem _root_.ContDiffOn.holderOnWith_iteratedFDeriv_of_lt {k j : ℕ} {s : Set E}
    {f : E → F} {M α : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : IsOpen s)
    (hconv : Convex ℝ s) (hj : j < k) (hα : α ≤ 1)
    (hb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M) :
    HolderOnWith (3 * M) α (iteratedFDeriv ℝ j f) s := by
  have hdiff : ∀ x ∈ s, DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x := fun x hx =>
    (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt_iteratedFDeriv (by exact_mod_cast hj)
  have hder : ∀ x ∈ s, ‖fderiv ℝ (iteratedFDeriv ℝ j f) x‖₊ ≤ M := by
    intro x hx
    exact_mod_cast (norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f) (n := j) (x := x)) ▸
      hb (j + 1) (by omega) x hx
  have hlip := Convex.lipschitzOnWith_of_nnnorm_fderiv_le hdiff hder hconv
  convert hlip.holderOnWith_of_norm_le (hb j hj.le) hα using 1
  ring

end TauCeti
