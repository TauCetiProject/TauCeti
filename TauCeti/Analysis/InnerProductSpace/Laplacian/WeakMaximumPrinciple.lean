/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.MaximumPrinciple

/-!
# The weak maximum principle for subharmonic functions

`TauCeti.Analysis.InnerProductSpace.Laplacian.MaximumPrinciple` proves the *strict* boundary
maximum principle: a `C²` function with `0 < Δ f` on the interior of a compact set attains its
maximum on the frontier. That strict hypothesis is only a warm-up; the theorem PDE theory
actually uses is the **weak maximum principle**, which relaxes `0 < Δ f` to the borderline
`0 ≤ Δ f` (subharmonic). This file supplies it, in bound form and in the extremum (`∃`) form.

## Main declarations

* `TauCeti.le_of_laplacian_nonneg_le_frontier`: **weak maximum principle**. A continuous function
  on a compact set that is `C²` and subharmonic (`0 ≤ Δ f`) on the interior is bounded on all of
  `K` by any bound it satisfies on `frontier K`.
* `TauCeti.ge_of_laplacian_nonpos_ge_frontier`: the dual weak minimum principle for superharmonic
  functions (`Δ f ≤ 0`).
* `TauCeti.exists_mem_frontier_isMaxOn_of_laplacian_nonneg` /
  `TauCeti.exists_mem_frontier_isMinOn_of_laplacian_nonpos`: on a nonempty compact set in a
  nontrivial finite-dimensional real inner product space, a subharmonic (resp. superharmonic)
  function attains a maximum (resp. minimum) on the frontier.
* `InnerProductSpace.HarmonicOnNhd.eq_zero_of_tendsto_cocompact`: a harmonic function on a
  nontrivial finite-dimensional space that tends to zero at infinity vanishes identically.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The `ε → 0` limit of a perturbation estimate: if `a ≤ m + ε * C` for every `ε > 0`, with a
nonnegative constant `C`, then `a ≤ m`. This packages the endgame of the perturbation arguments in
the weak maximum principles. -/
theorem le_of_forall_pos_mul_le {a m C : ℝ} (hC : 0 ≤ C) (h : ∀ ε : ℝ, 0 < ε → a ≤ m + ε * C) :
    a ≤ m := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · have := h 1 one_pos
    rw [← hC0] at this
    simpa using this
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hk := h (δ / C) (by positivity)
    have : δ / C * C = δ := by field_simp
    linarith

omit [FiniteDimensional ℝ E] in
/-- If every upper bound for a continuous function on the frontier of a nonempty compact set is
also an upper bound on the whole set, then the function attains a maximum on the frontier. -/
theorem exists_mem_frontier_isMaxOn_of_le_frontier {K : Set E} (hK : IsCompact K)
    [Nontrivial E] (hne : K.Nonempty) {f : E → ℝ} (hcont : ContinuousOn f K)
    (hbound : ∀ {m : ℝ}, (∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) →
      ∀ ⦃x⦄, x ∈ K → f x ≤ m) :
    ∃ x ∈ frontier K, IsMaxOn f K x := by
  have hfrsub : frontier K ⊆ K := hK.isClosed.frontier_subset
  have hfrcompact : IsCompact (frontier K) := hK.of_isClosed_subset isClosed_frontier hfrsub
  have hfrne : (frontier K).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rcases frontier_eq_empty_iff.mp hempty with h | h
    · exact hne.ne_empty h
    · exact noncompact_univ E (h ▸ hK)
  obtain ⟨z, hzfr, hzmax⟩ := hfrcompact.exists_isMaxOn hfrne (hcont.mono hfrsub)
  refine ⟨z, hzfr, isMaxOn_iff.mpr fun y hyK => ?_⟩
  exact hbound (fun w hw => isMaxOn_iff.mp hzmax w hw) hyK

/-- The Laplacian of the perturbation `f + ε‖·‖²` at a point where `f` is `C²`: it exceeds `Δ f` by
the contribution `ε * (2 * dim E)` of the strictly convex term `ε‖·‖²`. This is the computation the
bare-Laplacian and the `-Δ + c` weak maximum principles both run on the perturbed function. -/
theorem laplacian_add_const_smul_norm_sq {f : E → ℝ} {x : E} (ε : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    Δ (fun y : E => f y + ε • ‖y‖ ^ 2) x = Δ f x + ε * (2 * (Module.finrank ℝ E : ℝ)) := by
  have hεsq : ContDiffAt ℝ 2 (fun z : E => ε • ‖z‖ ^ 2) x :=
    ((contDiff_norm_sq ℝ).contDiffAt).const_smul ε
  have hadd : Δ (fun y : E => f y + ε • ‖y‖ ^ 2) x
      = Δ f x + Δ (fun z : E => ε • ‖z‖ ^ 2) x := hf.laplacian_add hεsq
  have hsmul : Δ (fun z : E => ε • ‖z‖ ^ 2) x = ε • Δ (fun z : E => ‖z‖ ^ 2) x :=
    laplacian_smul ε (contDiff_norm_sq ℝ).contDiffAt
  rw [hadd, hsmul, laplacian_norm_sq, smul_eq_mul]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The `ε → 0` perturbation engine of the weak maximum principles.** To bound `f x ≤ m` on a
bounded set `K`, it suffices to produce, for every `ε > 0`, a point `z ∈ K` at which the
perturbation `f + ε‖·‖²` attains its maximum over `K` and where `f z ≤ m`: bounding `‖·‖²` by a
constant on the bounded `K` and letting `ε → 0` then gives `f x ≤ m`. The bare-Laplacian and
`-Δ + c` weak maximum principles differ only in how they produce such a maximizer, so this lemma
packages everything they share. -/
theorem le_of_forall_pos_exists_isMaxOn_perturbation {K : Set E} (hK : Bornology.IsBounded K)
    {f : E → ℝ} {m : ℝ} {x : E} (hxK : x ∈ K)
    (H : ∀ ε : ℝ, 0 < ε → ∃ z ∈ K, IsMaxOn (fun y : E => f y + ε • ‖y‖ ^ 2) K z ∧ f z ≤ m) :
    f x ≤ m := by
  obtain ⟨M, hM⟩ := hK.exists_norm_le
  refine le_of_forall_pos_mul_le (sq_nonneg M) fun ε hε => ?_
  obtain ⟨z, hzK, hzmax, hfz⟩ := H ε hε
  have hxz : f x + ε * ‖x‖ ^ 2 ≤ f z + ε * ‖z‖ ^ 2 := by simpa [smul_eq_mul] using hzmax hxK
  have hzC : ‖z‖ ^ 2 ≤ M ^ 2 := by nlinarith [hM z hzK, norm_nonneg z]
  have hεzC : ε * ‖z‖ ^ 2 ≤ ε * M ^ 2 := mul_le_mul_of_nonneg_left hzC hε.le
  have hεx : 0 ≤ ε * ‖x‖ ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  linarith

section Nontrivial

variable [Nontrivial E]

/-- **Weak maximum principle for subharmonic functions.**

Let `K` be compact. If `f` is continuous on `K`, is `C²` on `interior K`, and is subharmonic
there (`0 ≤ Δ f`), then any bound `m` that `f` respects on `frontier K` bounds `f` on all of `K`. -/
theorem le_of_laplacian_nonneg_le_frontier {K : Set E} (hK : IsCompact K) {f : E → ℝ} {m : ℝ}
    (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ Δ f x) (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  -- Perturb `f` to the strictly subharmonic `f + ε‖·‖²`, whose maximum over `K` is forced onto the
  -- frontier by the strict boundary maximum principle; then let `ε → 0`.
  intro x hxK
  have hfrpos : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  refine le_of_forall_pos_exists_isMaxOn_perturbation hK.isBounded hxK fun ε hε => ?_
  have hεsq : ∀ y : E, ContDiffAt ℝ 2 (fun z : E => ε • ‖z‖ ^ 2) y :=
    fun y => ((contDiff_norm_sq ℝ).contDiffAt).const_smul ε
  have hgcont : ContinuousOn (fun y : E => f y + ε • ‖y‖ ^ 2) K := hcont.add (by fun_prop)
  have hgcd : ∀ ⦃y⦄, y ∈ interior K → ContDiffAt ℝ 2 (fun y : E => f y + ε • ‖y‖ ^ 2) y :=
    fun y hy => (hcd hy).add (hεsq y)
  have hglap : ∀ ⦃y⦄, y ∈ interior K → 0 < Δ (fun y : E => f y + ε • ‖y‖ ^ 2) y := by
    intro y hy
    rw [laplacian_add_const_smul_norm_sq ε (hcd hy)]
    have hpos : 0 < ε * (2 * (Module.finrank ℝ E : ℝ)) := mul_pos hε (mul_pos two_pos hfrpos)
    linarith [hlap hy]
  -- Strict boundary maximum principle: the maximizer lies on the frontier, where `f ≤ m`.
  obtain ⟨z, hzfr, hzmax⟩ :=
    exists_mem_frontier_isMaxOn_of_laplacian_pos hK ⟨x, hxK⟩ hgcont hgcd hglap
  exact ⟨z, hK.isClosed.frontier_subset hzfr, hzmax, hbdry hzfr⟩

/-- **Weak minimum principle for superharmonic functions.**

The dual of `le_of_laplacian_nonneg_le_frontier`: a continuous, `C²`, superharmonic (`Δ f ≤ 0`)
function on a compact set is bounded below on `K` by any lower bound it respects on `frontier K`.
-/
theorem ge_of_laplacian_nonpos_ge_frontier {K : Set E} (hK : IsCompact K) {f : E → ℝ} {m : ℝ}
    (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x ≤ 0) (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m ≤ f x := by
  intro x hxK
  have hle := le_of_laplacian_nonneg_le_frontier (f := -f) (m := -m) hK hcont.neg
    (fun y hy => (hcd hy).neg)
    (fun y hy => by
      rw [congrFun laplacian_neg y, Pi.neg_apply]; linarith [hlap hy])
    (fun y hy => neg_le_neg (hbdry hy)) hxK
  simp only [Pi.neg_apply] at hle
  linarith

/-- A subharmonic (`0 ≤ Δ f`) continuous function on a nonempty compact set in a nontrivial
finite-dimensional real inner product space attains a maximum on the frontier. This is the
`∃`-form of the weak maximum principle, mirroring
`exists_mem_frontier_isMaxOn_of_laplacian_pos` for the strict case. -/
theorem exists_mem_frontier_isMaxOn_of_laplacian_nonneg {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x) (hlap : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ Δ f x) :
    ∃ x ∈ frontier K, IsMaxOn f K x := by
  exact exists_mem_frontier_isMaxOn_of_le_frontier hK hne hcont fun hbdry =>
    le_of_laplacian_nonneg_le_frontier hK hcont hcd hlap hbdry

/-- A superharmonic (`Δ f ≤ 0`) continuous function on a nonempty compact set in a nontrivial
finite-dimensional real inner product space attains a minimum on the frontier. -/
theorem exists_mem_frontier_isMinOn_of_laplacian_nonpos {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x) (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x ≤ 0) :
    ∃ x ∈ frontier K, IsMinOn f K x := by
  obtain ⟨z, hzfr, hzmax⟩ := exists_mem_frontier_isMaxOn_of_laplacian_nonneg hK hne hcont.neg
    (fun y hy => (hcd hy).neg)
    (fun y hy => by
      rw [congrFun laplacian_neg y, Pi.neg_apply]; linarith [hlap hy])
  refine ⟨z, hzfr, isMinOn_iff.mpr fun y hyK => ?_⟩
  have := isMaxOn_iff.mp hzmax y hyK
  simpa using neg_le_neg this

/-- **A harmonic function on the whole space that vanishes at infinity is zero.** If `f` is
harmonic on a nontrivial finite-dimensional real inner product space and `f x → 0` as `x → ∞`,
then `f = 0`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.eq_zero_of_tendsto_cocompact {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : HarmonicOnNhd f Set.univ)
    (h : Filter.Tendsto f (Filter.cocompact E) (𝓝 0)) : f = 0 := by
  funext x
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ => ?_
  rw [Pi.zero_apply, map_zero]
  have hu : HarmonicOnNhd (φ ∘ f) Set.univ := hf.comp_CLM φ
  have hut : Filter.Tendsto (φ ∘ f) (Filter.cocompact E) (𝓝 0) := by
    simpa using (φ.continuous.tendsto 0).comp h
  -- By the weak maximum and minimum principles on a large ball, `|φ (f x)| ≤ ε` for every `ε > 0`.
  refine eq_of_forall_dist_le fun ε hε => ?_
  -- Off a compact set `K`, `|φ ∘ f| < ε`; take a ball around the origin containing `K` and `x`.
  obtain ⟨K, hK, hKε⟩ := Filter.mem_cocompact.1 (hut (Metric.ball_mem_nhds 0 hε))
  obtain ⟨R, hR⟩ := (hK.insert x).isBounded.subset_ball 0
  have hxR : x ∈ Metric.ball (0 : E) R := hR (Set.mem_insert x K)
  have hR0 : R ≠ 0 := by
    rintro rfl
    simp at hxR
  have hfr : ∀ ⦃y⦄, y ∈ frontier (Metric.closedBall (0 : E) R) → |(φ ∘ f) y| < ε := by
    intro y hy
    rw [frontier_closedBall (0 : E) hR0, mem_sphere_iff_norm, sub_zero] at hy
    have hyK : y ∉ K := fun hyK => by
      have := hR (Set.mem_insert_of_mem x hyK)
      rw [mem_ball_zero_iff, hy] at this
      exact lt_irrefl R this
    simpa [Real.dist_eq] using hKε hyK
  have hcb : IsCompact (Metric.closedBall (0 : E) R) := isCompact_closedBall 0 R
  have hcont : ContinuousOn (φ ∘ f) (Metric.closedBall (0 : E) R) :=
    hu.continuousOn.mono (Set.subset_univ _)
  have hcd : ∀ ⦃y⦄, y ∈ interior (Metric.closedBall (0 : E) R) → ContDiffAt ℝ 2 (φ ∘ f) y :=
    fun y _ => (hu y trivial).1
  have hΔ : ∀ y, Δ (φ ∘ f) y = 0 := fun y => (hu y trivial).2.self_of_nhds
  have hxB := Metric.ball_subset_closedBall hxR
  have hle := le_of_laplacian_nonneg_le_frontier hcb hcont hcd (fun y _ => (hΔ y).ge)
    (fun y hy => (abs_lt.1 (hfr hy)).2.le) hxB
  have hge := ge_of_laplacian_nonpos_ge_frontier hcb hcont hcd (fun y _ => (hΔ y).le)
    (fun y hy => (abs_lt.1 (hfr hy)).1.le) hxB
  rw [Real.dist_eq, sub_zero]
  exact abs_le.2 ⟨hge, hle⟩

end Nontrivial

end TauCeti

end
