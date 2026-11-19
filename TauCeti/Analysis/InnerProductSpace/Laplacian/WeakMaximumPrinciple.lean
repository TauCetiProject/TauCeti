/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Algebra.Order.Field.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.MaximumPrinciple
public import Mathlib.Analysis.Complex.ReImTopology

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
* `TauCeti.le_of_laplacian_nonneg_of_lt_le_frontier`: the same bound when `f` is only known to be
  `C²` and subharmonic at the interior points where it exceeds the bound.
* `TauCeti.ge_of_laplacian_nonpos_ge_frontier`: the dual weak minimum principle for superharmonic
  functions (`Δ f ≤ 0`).
* `TauCeti.ge_of_laplacian_nonpos_of_lt_ge_frontier`: the dual of the bound above a level, for
  `f` only known to be `C²` and superharmonic at the interior points where it is below the bound.
* `TauCeti.le_of_laplacian_nonneg_of_lt_le_strip`: the bound above a level on the closed strip
  `ℝ × [0, 1]` of the complex plane, for a function bounded on the two boundary lines and on the
  two ends of the strip.
* `TauCeti.exists_mem_frontier_isMaxOn_of_laplacian_nonneg` /
  `TauCeti.exists_mem_frontier_isMinOn_of_laplacian_nonpos`: on a nonempty compact set in a
  nontrivial finite-dimensional real inner product space, a subharmonic (resp. superharmonic)
  function attains a maximum (resp. minimum) on the frontier.
* `InnerProductSpace.HarmonicOnNhd.eq_zero_of_tendsto_cocompact`: a harmonic function on a
  nontrivial finite-dimensional space that tends to zero at infinity vanishes identically.
* `TauCeti.nonpos_of_tendsto_cocompact_of_laplacian_nonneg`,
  `TauCeti.eq_zero_of_tendsto_cocompact_of_mul_laplacian_nonneg`: the same Liouville argument for
  a real `C²` function satisfying only the sign condition `0 ≤ f · Δ f`, as differences of
  solutions of monotone semilinear equations do.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

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
  refine BddAbove.le_of_forall_pos_exists_add_mul_le
    (hK.bddAbove_image (f := fun y : E => ‖y‖ ^ 2) (by fun_prop)) fun ε hε => ?_
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
  exact ⟨z, hK.isClosed.frontier_subset hzfr,
    by simpa only [smul_eq_mul] using isMaxOn_iff.mp hzmax x hxK, hbdry hzfr⟩

/-- **Weak maximum principle above a level.**

Let `K` be compact and `f` continuous on `K`, with `f ≤ m` on `frontier K`. If `f` is `C²` and
subharmonic (`0 ≤ Δ f`) at the interior points of `K` where `m < f`, then `f ≤ m` on all of `K`.
Nothing is assumed about `f` at interior points where `f ≤ m`. -/
theorem le_of_laplacian_nonneg_of_lt_le_frontier {K : Set E} (hK : IsCompact K) {f : E → ℝ}
    {m : ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → m < f x → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → m < f x → 0 ≤ Δ f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  -- Apply the weak maximum principle to the compact superlevel set `K' = {f ≥ m + ε}`, on whose
  -- interior `f > m`, and on whose frontier `f ≤ m + ε`.
  intro x hx
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set K' := K ∩ f ⁻¹' Set.Ici (m + ε) with hK'
  have hK'c : IsClosed K' := hcont.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici
  by_cases hxK' : x ∈ K'
  swap
  · simp only [hK', Set.mem_inter_iff, hx, Set.mem_preimage, Set.mem_Ici, true_and,
      not_le] at hxK'
    exact hxK'.le
  -- Interior points of `K'` are interior points of `K` where `f > m`.
  have hint : ∀ ⦃y⦄, y ∈ interior K' → y ∈ interior K ∧ m < f y := fun y hy => by
    have h : m + ε ≤ f y := (interior_subset hy).2
    exact ⟨interior_mono Set.inter_subset_left hy, by linarith⟩
  refine le_of_laplacian_nonneg_le_frontier (hK.of_isClosed_subset hK'c Set.inter_subset_left)
    (hcont.mono Set.inter_subset_left) (fun y hy => hcd (hint hy).1 (hint hy).2)
    (fun y hy => hlap (hint hy).1 (hint hy).2) (fun y hy => ?_) hxK'
  have hyK' : y ∈ K' := hK'c.frontier_subset hy
  by_contra hlt
  rw [not_le] at hlt
  by_cases hyK : y ∈ frontier K
  · linarith [hbdry hyK]
  -- Otherwise `y` is an interior point of `K` with `f y > m + ε`, hence interior to `K'`.
  have hyint : y ∈ interior K := by
    by_contra hy'
    exact hyK (hK.isClosed.frontier_eq ▸ ⟨hyK'.1, hy'⟩)
  have hKy : K ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hyint
  exact hy.2 (mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hKy
    ((hcont.continuousAt hKy).preimage_mem_nhds (Ici_mem_nhds hlt))))

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

/-- **Weak minimum principle below a level.**

The dual of `le_of_laplacian_nonneg_of_lt_le_frontier`: let `K` be compact and `f` continuous on
`K`, with `m ≤ f` on `frontier K`. If `f` is `C²` and superharmonic (`Δ f ≤ 0`) at the interior
points of `K` where `f < m`, then `m ≤ f` on all of `K`. -/
theorem ge_of_laplacian_nonpos_of_lt_ge_frontier {K : Set E} (hK : IsCompact K) {f : E → ℝ}
    {m : ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → f x < m → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → f x < m → Δ f x ≤ 0)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m ≤ f x := by
  intro x hxK
  have hle := le_of_laplacian_nonneg_of_lt_le_frontier (f := -f) (m := -m) hK hcont.neg
    (fun y hy hlt => (hcd hy (by simpa using hlt)).neg)
    (fun y hy hlt => by
      rw [congrFun laplacian_neg y, Pi.neg_apply]; linarith [hlap hy (by simpa using hlt)])
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
  exact hK.exists_mem_frontier_isMaxOn_of_le_frontier hne
    (hcont.mono hK.isClosed.frontier_subset) fun hbdry =>
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

/-- **A function vanishing at infinity that is subharmonic where positive is nonpositive.** If a
`C²` function `f` on a nontrivial finite-dimensional real inner product space satisfies
`0 ≤ Δ f x` wherever `0 < f x`, and `f x → 0` as `x → ∞`, then `f ≤ 0` everywhere. -/
theorem nonpos_of_tendsto_cocompact_of_laplacian_nonneg {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x → 0 ≤ Δ f x) (h : Filter.Tendsto f (Filter.cocompact E) (𝓝 0))
    (x : E) : f x ≤ 0 := by
  by_contra! hx
  -- Apply the weak maximum principle on the compact superlevel set `{f ≥ f x / 2}`, where `f` is
  -- positive and hence subharmonic, and on whose frontier `f = f x / 2`.
  set K := {y | f x / 2 ≤ f y}
  have hKc : IsClosed K := isClosed_le continuous_const hf.continuous
  obtain ⟨t, ht, htK⟩ := Filter.mem_cocompact.1 (h (Iio_mem_nhds (half_pos hx)))
  have hK : IsCompact K := ht.of_isClosed_subset hKc fun y hy => by
    by_contra hyt
    exact (htK hyt : f y < f x / 2).not_ge hy
  have hle := le_of_laplacian_nonneg_le_frontier hK hf.continuous.continuousOn
    (fun _ _ => hf.contDiffAt)
    (fun y hy => hpos y ((half_pos hx).trans_le (interior_subset hy : f x / 2 ≤ f y)))
    (fun y hy => (frontier_le_subset_eq continuous_const hf.continuous hy).ge)
    (half_le_self hx.le : f x / 2 ≤ f x)
  linarith

/-- **Liouville theorem under the sign condition `f · Δ f ≥ 0`.** A `C²` function on a nontrivial
finite-dimensional real inner product space which tends to zero at infinity and satisfies
`0 ≤ f x * Δ f x` everywhere vanishes identically. The sign condition holds for solutions of
`Δ f = c f` with `c ≥ 0`, and for differences of solutions of semilinear equations `Δ u = F(x, u)`
with `F` nondecreasing in `u`. -/
theorem eq_zero_of_tendsto_cocompact_of_mul_laplacian_nonneg {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hsign : ∀ x, 0 ≤ f x * Δ f x) (h : Filter.Tendsto f (Filter.cocompact E) (𝓝 0)) :
    f = 0 := by
  funext x
  refine le_antisymm (nonpos_of_tendsto_cocompact_of_laplacian_nonneg hf
    (fun y hy => (mul_nonneg_iff_of_pos_left hy).1 (hsign y)) h x) ?_
  have hneg := nonpos_of_tendsto_cocompact_of_laplacian_nonneg (f := -f) hf.neg (fun y hy => by
    rw [laplacian_neg, Pi.neg_apply]
    have := hsign y
    rw [Pi.neg_apply, neg_pos] at hy
    nlinarith) (by rw [← neg_zero]; exact h.neg) x
  simpa using hneg

end Nontrivial

open Complex Set in
/-- **The weak maximum principle on a strip, above a level.** Let `f` be continuous on the closed
strip `ℝ × [0, 1]` of the complex plane and `C²` and subharmonic at the points of the open strip
where it exceeds `m`. If `f ≤ m` on the two boundary lines `ℑ z = 0` and `ℑ z = 1`, and also on
the two ends `|ℜ z| ≥ T` of the strip, then `f ≤ m` on the whole closed strip. The proof applies
`TauCeti.le_of_laplacian_nonneg_of_lt_le_frontier` on rectangles `[-S, S] × [0, 1]`. -/
theorem le_of_laplacian_nonneg_of_lt_le_strip {f : ℂ → ℝ} {m T : ℝ}
    (hcont : ContinuousOn f (univ ×ℂ Icc 0 1))
    (hcd : ∀ ⦃z : ℂ⦄, 0 < z.im → z.im < 1 → m < f z → ContDiffAt ℝ 2 f z)
    (hlap : ∀ ⦃z : ℂ⦄, 0 < z.im → z.im < 1 → m < f z → 0 ≤ Δ f z)
    (h₀ : ∀ z : ℂ, z.im = 0 → f z ≤ m) (h₁ : ∀ z : ℂ, z.im = 1 → f z ≤ m)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → f z ≤ m) {z : ℂ} (hz₀ : 0 ≤ z.im)
    (hz₁ : z.im ≤ 1) : f z ≤ m := by
  -- Apply the maximum principle on a rectangle `[-S, S] × [0, 1]` containing `z`, with `S ≥ T`.
  set S := max T |z.re|
  have hS : 0 ≤ S := (abs_nonneg _).trans (le_max_right _ _)
  have hsub : Icc (-S) S ×ℂ Icc 0 1 ⊆ univ ×ℂ Icc 0 1 := fun w hw ↦ ⟨mem_univ _, hw.2⟩
  have hint : interior (Icc (-S) S ×ℂ Icc (0 : ℝ) 1) = Ioo (-S) S ×ℂ Ioo 0 1 := by
    rw [interior_reProdIm, interior_Icc, interior_Icc]
  refine le_of_laplacian_nonneg_of_lt_le_frontier (isCompact_Icc.reProdIm isCompact_Icc)
    (hcont.mono hsub) (fun w hw ↦ ?_) (fun w hw ↦ ?_) (fun w hw ↦ ?_)
    ⟨abs_le.mp (le_max_right _ _), hz₀, hz₁⟩
  · rw [hint] at hw
    exact hcd hw.2.1 hw.2.2
  · rw [hint] at hw
    exact hlap hw.2.1 hw.2.2
  · rw [frontier_reProdIm, closure_Icc, closure_Icc, frontier_Icc zero_le_one,
      frontier_Icc (by linarith)] at hw
    rcases hw with ⟨-, hw | hw⟩ | ⟨hw, hw₀, hw₁⟩
    · exact h₀ w hw
    · exact h₁ w hw
    · refine hends w ?_ hw₀ hw₁
      rcases hw with hw | hw <;> rw [hw] <;> simp [S, abs_of_nonneg hS]

end TauCeti

end
