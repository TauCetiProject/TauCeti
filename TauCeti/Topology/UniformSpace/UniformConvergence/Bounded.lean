/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Boundedness on a strip from uniform convergence at both ends

A map `f` continuous on a strip `ℝ × T`, with `T` compact, that converges uniformly in the second
variable as the first tends to `-∞` and to `+∞` is bounded on the strip
(`TauCeti.exists_forall_norm_le_of_tendstoUniformlyOn`). No continuity of the limits is needed: far
enough out, `f (s, t)` is within `2` of the value at the end of a compact piece `[Rm, Rp] × T`,
on which `f` is bounded.

This is how the coefficients of linearized operators along Floer cylinders, whose loops converge
uniformly at both ends, are shown to be bounded.

Along a single end, a map `g` continuous on `α × β` is eventually bounded along the graphs
`x ↦ (x, F i x)` of a family converging uniformly on a compact set `s` to a limit continuous on `s`
(`IsCompact.exists_eventually_forall_norm_le_of_tendstoUniformlyOn`): the graphs converge uniformly
to the compact graph of the limit, near which `g` is bounded.
-/

public section

open Filter Set

namespace TauCeti

/-- A map continuous on a strip `ℝ × T`, with `T` compact, that converges uniformly on `T` as the
first variable tends to `-∞` and to `+∞` is bounded on the strip. -/
theorem exists_forall_norm_le_of_tendstoUniformlyOn {β E : Type*} [TopologicalSpace β]
    [SeminormedAddCommGroup E] {T : Set β} (hT : IsCompact T) {f : ℝ × β → E}
    (hf : ContinuousOn f (univ ×ˢ T))
    {gm gp : β → E} (hm : TendstoUniformlyOn (fun s t ↦ f (s, t)) gm atBot T)
    (hp : TendstoUniformlyOn (fun s t ↦ f (s, t)) gp atTop T) :
    ∃ C, ∀ s, ∀ t ∈ T, ‖f (s, t)‖ ≤ C := by
  obtain ⟨Rm, hRm⟩ := eventually_atBot.1 ((Metric.tendstoUniformlyOn_iff.1 hm) 1 one_pos)
  obtain ⟨Rp, hRp⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hp) 1 one_pos)
  set R := max Rm Rp
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := Rm) (b := R)).prod hT).exists_bound_of_continuousOn
    (hf.mono (prod_mono (subset_univ _) subset_rfl))
  refine ⟨C + 2, fun s t ht ↦ ?_⟩
  -- Near an end, `f (s, t)` is within `2` of `f (r, t)`, through the limit `g t`.
  have hnear : ∀ (g : β → E) (r : ℝ), r ∈ Icc Rm R → dist (g t) (f (s, t)) < 1 →
      dist (g t) (f (r, t)) < 1 → ‖f (s, t)‖ ≤ C + 2 := fun g r hr h₁ h₂ ↦ by
    have h := dist_triangle_left (f (s, t)) (f (r, t)) (g t)
    rw [dist_eq_norm] at h
    linarith [norm_le_insert' (f (s, t)) (f (r, t)), hC (r, t) ⟨hr, ht⟩]
  rcases le_or_gt s Rm with hs | hs
  · exact hnear gm Rm ⟨le_rfl, le_max_left _ _⟩ (hRm s hs t ht) (hRm Rm le_rfl t ht)
  rcases le_or_gt R s with hs' | hs'
  · exact hnear gp R ⟨le_max_left _ _, le_rfl⟩ (hRp s ((le_max_right _ _).trans hs') t ht)
      (hRp R (le_max_right _ _) t ht)
  · linarith [hC (s, t) ⟨⟨hs.le, hs'.le⟩, ht⟩]

end TauCeti

/-- If `F i → f` uniformly on a compact set `s`, with `f` continuous on `s`, then a continuous map
`g` is eventually bounded along the graphs `x ↦ (x, F i x)` over `s`. -/
theorem IsCompact.exists_eventually_forall_norm_le_of_tendstoUniformlyOn {ι α β E : Type*}
    [UniformSpace α] [UniformSpace β] [SeminormedAddCommGroup E] {F : ι → α → β} {f : α → β}
    {s : Set α} {p : Filter ι} (hs : IsCompact s) (hf : ContinuousOn f s) {g : α × β → E}
    (hg : Continuous g) (h : TendstoUniformlyOn F f p s) :
    ∃ C, ∀ᶠ i in p, ∀ x ∈ s, ‖g (x, F i x)‖ ≤ C := by
  have hK := hs.image_of_continuousOn ((continuousOn_id' s).prodMk hf)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C + 1, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    (hK.comp_tendstoUniformlyOn (fun _ _ ↦ hg.continuousAt) h.graph) 1 one_pos] with i hi x hx
  have h₁ := hi x hx
  rw [dist_eq_norm'] at h₁
  linarith [hC _ (mem_image_of_mem _ hx), norm_le_insert' (g (x, F i x)) (g (x, f x))]
