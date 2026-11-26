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

A sequence of maps continuous on a compact set `K` and converging uniformly on `K` is uniformly
bounded on `K` (`TendstoUniformlyOn.exists_forall_norm_le_of_isCompact`): far out, every term is
within `2` of one fixed term, and the finitely many remaining terms are bounded.

On the cylinder, a continuous map `f` of period one in `t` that, far out on each end, does not
depend on `s` is bounded (`TauCeti.exists_forall_norm_le_of_periodic_of_eventually_eq`).
-/

public section

open Filter Set Topology Function

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

/-- A continuous function on the cylinder, of period one in `t`, which far out on each end does not
depend on `s`, is bounded. -/
theorem exists_forall_norm_le_of_periodic_of_eventually_eq {E : Type*}
    [SeminormedAddCommGroup E] {f : ℝ × ℝ → E} (hf : Continuous f)
    (hper : ∀ s t, f (s, t + 1) = f (s, t)) {gm gp : ℝ → E}
    (hm : ∀ᶠ s in atBot, ∀ t, f (s, t) = gm t) (hp : ∀ᶠ s in atTop, ∀ t, f (s, t) = gp t) :
    ∃ C, ∀ z, ‖f z‖ ≤ C := by
  have hlim {l : Filter ℝ} {g : ℝ → E} (h : ∀ᶠ s in l, ∀ t, f (s, t) = g t) :
      TendstoUniformlyOn (fun s t ↦ f (s, t)) g l (Icc 0 1) :=
    (tendstoUniformlyOn_const g l _).congr (h.mono fun s hs t _ ↦ (hs t).symm)
  obtain ⟨C, hC⟩ := exists_forall_norm_le_of_tendstoUniformlyOn isCompact_Icc hf.continuousOn
    (hlim hm) (hlim hp)
  refine ⟨C, fun ⟨s, t⟩ ↦ ?_⟩
  -- Reduce `t` modulo `1` to `[0, 1)`.
  obtain ⟨t', ht', heq⟩ :=
    (show Periodic (fun t ↦ f (s, t)) 1 from hper s).exists_mem_Ico₀ one_pos t
  rw [show f (s, t) = f (s, t') from heq]
  exact hC s t' (Ico_subset_Icc_self ht')

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

/-- A sequence of maps continuous on a compact set `K` that converges uniformly on `K` is uniformly
bounded on `K`. No continuity of the limit is needed. -/
theorem TendstoUniformlyOn.exists_forall_norm_le_of_isCompact {α E : Type*} [TopologicalSpace α]
    [SeminormedAddCommGroup E] {F : ℕ → α → E} {f : α → E} {K : Set α}
    (h : TendstoUniformlyOn F f atTop K) (hK : IsCompact K) (hF : ∀ n, ContinuousOn (F n) K) :
    ∃ C, ∀ n, ∀ x ∈ K, ‖F n x‖ ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 h 1 one_pos)
  choose B hB using fun n => hK.exists_bound_of_continuousOn (hF n)
  set S := ∑ n ∈ Finset.range (N + 1), |B n|
  have hle (m : ℕ) (hm : m ≤ N) (x : α) (hx : x ∈ K) : ‖F m x‖ ≤ S :=
    (hB m x hx).trans ((le_abs_self _).trans (Finset.single_le_sum (fun n _ => abs_nonneg (B n))
      (Finset.mem_range.2 (by omega))))
  refine ⟨S + 2, fun n x hx => ?_⟩
  rcases le_or_gt n N with hn | hn
  · linarith [hle n hn x hx]
  -- Far out, `F n x` is within `2` of `F N x`, through the limit `f x`.
  have h₁ := hN n hn.le x hx
  have h₂ := hN N le_rfl x hx
  have h₃ := dist_triangle_left (F n x) (F N x) (f x)
  rw [dist_eq_norm] at h₃
  linarith [norm_le_insert' (F n x) (F N x), hle N le_rfl x hx]
