/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import TauCeti.Analysis.PDE.Perron.Basic

/-!
# Perron's method: barriers and boundary values

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space `E`, and let
`g` be bounded on `frontier Ω`. Perron's theorem (`TauCeti.harmonicOnNhd_perronSolution`) makes
the Perron solution `u = TauCeti.perronSolution Ω g` harmonic in `Ω`, but says nothing about its
boundary values. This file shows that `u` takes the value `g ξ` continuously at every point `ξ`
where `g` is continuous along `frontier Ω` and a **barrier** exists: a superharmonic function `w`,
continuous on `closure Ω`, vanishing at `ξ` and positive on the rest of `closure Ω`. A boundary
point admitting a barrier is called *regular*.

If every boundary point is regular, the Perron solution of continuous boundary data is
therefore continuous on `closure Ω` and equal to `g` on `frontier Ω`, and so solves the Dirichlet
problem `Δu = 0` in `Ω`, `u = g` on `frontier Ω`.

## Exterior sphere condition

If a closed ball `closedBall y R` meets `closure Ω` only at `ξ`, the function
`G(ξ - y) - G(x - y)`, built from the Newtonian kernel `G = TauCeti.newtonianKernel n` with pole
at `y`, is a barrier at `ξ`. In `ℝⁿ` with `n ≠ 2`, the Dirichlet problem is therefore solvable on
every bounded open set satisfying this exterior sphere condition at each boundary point.

## Main declarations

* `TauCeti.IsBarrier`: a barrier at a point relative to `Ω`.
* `TauCeti.tendsto_perronSolution_of_isBarrier`: at a point with a barrier where the boundary
  data is continuous, the Perron solution tends to the boundary value.
* `TauCeti.perronSolution_eq_of_isBarrier`: there the Perron solution equals the boundary value.
* `TauCeti.continuousOn_perronSolution`: if every boundary point admits a barrier, the Perron
  solution of continuous boundary data is continuous on `closure Ω`.
* `TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier`: **the Dirichlet problem**
  is solvable when every boundary point admits a barrier.
* `TauCeti.isBarrier_newtonianKernel_sub`: the exterior sphere barrier.
* `TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_sphere`: the
  Dirichlet problem is solvable on bounded open subsets of `ℝⁿ`, `n ≠ 2`, satisfying the exterior
  sphere condition.

## References

* O. Perron, *Eine neue Behandlung der ersten Randwertaufgabe für Δu = 0*, Math. Z. 18 (1923).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8, Lemma 2.13 and Theorem 2.14, and the exterior sphere barrier following it.
-/

public section

namespace TauCeti

open InnerProductSpace Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Set E} {g w : E → ℝ} {ξ : E}

variable [MeasurableSpace E] [BorelSpace E]

/-- A **barrier** at the point `ξ` relative to `Ω`: a function `w` that is superharmonic on `Ω`
(`-w` is subharmonic), continuous on `closure Ω`, zero at `ξ` and positive at every other point
of `closure Ω`. A point of `frontier Ω` admitting a barrier is a *regular* boundary point. -/
structure IsBarrier (Ω : Set E) (ξ : E) (w : E → ℝ) : Prop where
  /-- A barrier is superharmonic on `Ω`. -/
  subharmonicOn_neg : SubharmonicOn (-w) Ω
  /-- A barrier is continuous on `closure Ω`. -/
  continuousOn : ContinuousOn w (closure Ω)
  /-- A barrier vanishes at its point. -/
  apply_self : w ξ = 0
  /-- A barrier is positive on `closure Ω` away from its point. -/
  pos : ∀ x ∈ closure Ω, x ≠ ξ → 0 < w x

/-- The function `c + k w`, for `k ≥ 0` and a barrier `w`, is superharmonic on the open set
`Ω`. -/
private lemma IsBarrier.subharmonicOn_neg_const_add_mul (hΩ : IsOpen Ω) (hw : IsBarrier Ω ξ w)
    (c : ℝ) {k : ℝ} (hk : 0 ≤ k) : SubharmonicOn (-fun x ↦ c + k * w x) Ω := by
  have h := (hw.subharmonicOn_neg.const_smul hk).sub_harmonicOnNhd (harmonicOnNhd_const c) hΩ
  have heq : (k • -w) - (fun _ ↦ c) = -fun x ↦ c + k * w x := by
    ext x
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rwa [heq] at h

section Nontrivial

variable [Nontrivial E]

/-- Near a point `ξ` with a barrier `w`, where the boundary data `g` is continuous along
`frontier Ω`, the Perron solution is within `ε + k w` of `g ξ` on `closure Ω`, for some `k`. -/
private lemma exists_abs_perronSolution_sub_le (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Bornology.IsBounded (g '' frontier Ω)) (hw : IsBarrier Ω ξ w)
    (hgξ : ContinuousWithinAt g (frontier Ω) ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, ∀ x ∈ closure Ω, |perronSolution Ω g x - g ξ| ≤ ε + k * w x := by
  -- Choose `δ` with `|g x - g ξ| < ε` on boundary points within `δ` of `ξ`, and `k ≥ 0` with
  -- `k w ≥ |g ξ| + sup |g|` on `closure Ω` away from `ball ξ δ`. Then `g ξ - ε - k w` is a
  -- member of the Perron family, so lies below the Perron solution, while the superharmonic
  -- function `g ξ + ε + k w` lies above every member of the family by the comparison principle
  -- `SubharmonicOn.le_of_le_frontier_of_subharmonicOn_neg`, so above the Perron solution.
  obtain ⟨M, hM0, hM⟩ := hg.exists_pos_norm_le
  have hgM : ∀ x ∈ frontier Ω, |g x| ≤ M := fun x hx ↦ hM _ (mem_image_of_mem g hx)
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 hgξ ε hε
  -- On the compact set `closure Ω \ ball ξ δ`, the barrier is at least some `m > 0`.
  obtain ⟨m, hm, hmw⟩ :=
    (hb.isCompact_closure.diff (isOpen_ball (x := ξ) (ε := δ))).exists_forall_le'
    (hw.continuousOn.mono sdiff_subset) fun x hx ↦
      hw.pos x hx.1 fun h ↦ hx.2 (by rw [h]; exact mem_ball_self hδ)
  set k := (|g ξ| + M) / m
  have hk : 0 ≤ k := by positivity
  have hw0 : ∀ x ∈ closure Ω, 0 ≤ k * w x := fun x hx ↦ mul_nonneg hk <| by
    rcases eq_or_ne x ξ with rfl | hxξ
    · exact hw.apply_self.ge
    · exact (hw.pos x hx hxξ).le
  have hfar : ∀ x ∈ closure Ω, x ∉ ball ξ δ → |g ξ| + M ≤ k * w x := fun x hx hxδ ↦ by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    exact mul_le_mul_of_nonneg_left (hmw x ⟨hx, hxδ⟩) (by positivity)
  -- On `frontier Ω`, the boundary data lies within `ε + k w` of `g ξ`.
  have hfr : ∀ x ∈ frontier Ω, |g x - g ξ| ≤ ε + k * w x := fun x hx ↦ by
    have hxc : x ∈ closure Ω := frontier_subset_closure hx
    by_cases hxδ : x ∈ ball ξ δ
    · have := hδg hx hxδ
      rw [Real.dist_eq] at this
      linarith [hw0 x hxc]
    · have := hfar x hxc hxδ
      have := hgM x hx
      rw [abs_le] at *
      constructor <;> linarith [abs_nonneg (g ξ), le_abs_self (g ξ), neg_abs_le (g ξ)]
  -- The subharmonic function `g ξ - ε - k w` is a member of the Perron family.
  have hlow : (fun x ↦ (g ξ - ε) + -k * w x) ∈ perronFamily Ω g := by
    refine mem_perronFamily.2
      ⟨?_, continuousOn_const.add (hw.continuousOn.const_smul (-k)), fun x hx ↦ ?_⟩
    · have := hw.subharmonicOn_neg_const_add_mul hΩ (ε - g ξ) hk
      convert this using 2 with x
      simp only [Pi.neg_apply]
      ring
    · linarith [(abs_le.1 (hfr x hx)).1]
  refine ⟨k, fun x hx ↦ abs_le.2 ⟨?_, ?_⟩⟩
  · have := le_perronSolution hΩ hb hg.bddAbove hlow hx
    linarith
  -- The superharmonic function `g ξ + ε + k w` lies above every member of the Perron family.
  have hup : perronSolution Ω g x ≤ (g ξ + ε) + k * w x :=
    perronSolution_le_of_forall_le ⟨_, hlow⟩ fun v hv ↦
      have hv := mem_perronFamily.1 hv
      hv.1.le_of_le_frontier_of_subharmonicOn_neg hΩ hb hv.2.1
        (hw.subharmonicOn_neg_const_add_mul hΩ (g ξ + ε) hk)
        (continuousOn_const.add (hw.continuousOn.const_smul k))
        (fun y hy ↦ (hv.2.2 y hy).trans (by linarith [(abs_le.1 (hfr y hy)).2])) x hx
  linarith

/-- **Boundary values of the Perron solution.** Let `Ω` be a bounded open set and `g` bounded on
`frontier Ω`. At a point `ξ` admitting a barrier, where `g` is continuous along `frontier Ω`, the
Perron solution tends to `g ξ` as its argument tends to `ξ` within `closure Ω`. -/
theorem tendsto_perronSolution_of_isBarrier (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Bornology.IsBounded (g '' frontier Ω)) (hw : IsBarrier Ω ξ w)
    (hgξ : ContinuousWithinAt g (frontier Ω) ξ) :
    Tendsto (perronSolution Ω g) (𝓝[closure Ω] ξ) (𝓝 (g ξ)) := by
  by_cases hξ : ξ ∉ closure Ω
  · rw [notMem_closure_iff_nhdsWithin_eq_bot.1 (by rwa [closure_closure])]
    exact tendsto_bot
  rw [not_not] at hξ
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_abs_perronSolution_sub_le hΩ hb hg hw hgξ (half_pos hε)
  -- The barrier tends to `w ξ = 0` at `ξ`.
  have hw0 : Tendsto (fun x ↦ k * w x) (𝓝[closure Ω] ξ) (𝓝 0) := by
    simpa [hw.apply_self] using ((hw.continuousOn ξ hξ).tendsto).const_mul k
  filter_upwards [self_mem_nhdsWithin, hw0.eventually (gt_mem_nhds (half_pos hε))] with x hx hkx
  rw [Real.dist_eq]
  linarith [hk x hx]

/-- At a point `ξ ∈ closure Ω` admitting a barrier, where the boundary data `g` (bounded on
`frontier Ω`) is continuous along `frontier Ω`, the Perron solution equals `g ξ`. -/
theorem perronSolution_eq_of_isBarrier (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Bornology.IsBounded (g '' frontier Ω)) (hw : IsBarrier Ω ξ w)
    (hgξ : ContinuousWithinAt g (frontier Ω) ξ) (hξ : ξ ∈ closure Ω) :
    perronSolution Ω g ξ = g ξ :=
  tendsto_nhds_unique (tendsto_pure_nhds _ ξ)
    ((tendsto_perronSolution_of_isBarrier hΩ hb hg hw hgξ).mono_left (pure_le_nhdsWithin hξ))

/-- If every boundary point of the bounded open set `Ω` admits a barrier, the Perron solution of
boundary data `g` continuous on `frontier Ω` is continuous on `closure Ω`. -/
theorem continuousOn_perronSolution (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hreg : ∀ ξ ∈ frontier Ω, ∃ w, IsBarrier Ω ξ w) (hg : ContinuousOn g (frontier Ω)) :
    ContinuousOn (perronSolution Ω g) (closure Ω) := by
  have hgb : Bornology.IsBounded (g '' frontier Ω) :=
    ((hb.isCompact_closure.of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image_of_continuousOn hg).isBounded
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · exact ((harmonicOnNhd_perronSolution hΩ hb hgb.bddAbove (perronFamily_nonempty hgb.bddBelow)
      x hxΩ).1.continuousAt.continuousWithinAt)
  have hxf : x ∈ frontier Ω := hΩ.frontier_eq ▸ ⟨hx, hxΩ⟩
  obtain ⟨w, hw⟩ := hreg x hxf
  have hgx : ContinuousWithinAt g (frontier Ω) x := hg x hxf
  rw [ContinuousWithinAt, perronSolution_eq_of_isBarrier hΩ hb hgb hw hgx hx]
  exact tendsto_perronSolution_of_isBarrier hΩ hb hgb hw hgx

end Nontrivial

/-- **Perron's solution of the Dirichlet problem.** Let `Ω` be a bounded open set every boundary
point of which admits a barrier. For boundary data `g` continuous on `frontier Ω`, there is a
function harmonic in `Ω`, continuous on `closure Ω` and equal to `g` on `frontier Ω`. In a
nontrivial space it is the Perron solution `TauCeti.perronSolution Ω g`. -/
theorem exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hreg : ∀ ξ ∈ frontier Ω, ∃ w, IsBarrier Ω ξ w)
    (hg : ContinuousOn g (frontier Ω)) :
    ∃ u, HarmonicOnNhd u Ω ∧ ContinuousOn u (closure Ω) ∧ EqOn u g (frontier Ω) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space every function is constant, hence harmonic and continuous.
    refine ⟨g, fun x _ ↦ ?_, ?_, eqOn_refl g _⟩
    · have hconst : g = fun _ ↦ g x := funext fun y ↦ congrArg g (Subsingleton.elim y x)
      rw [hconst]
      exact harmonicAt_const _
    · exact (continuous_of_const fun a b ↦ congrArg g (Subsingleton.elim a b)).continuousOn
  have hgb : Bornology.IsBounded (g '' frontier Ω) :=
    ((hb.isCompact_closure.of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image_of_continuousOn hg).isBounded
  refine ⟨perronSolution Ω g, harmonicOnNhd_perronSolution hΩ hb hgb.bddAbove
    (perronFamily_nonempty hgb.bddBelow), continuousOn_perronSolution hΩ hb hreg hg,
    fun ξ hξ ↦ ?_⟩
  obtain ⟨w, hw⟩ := hreg ξ hξ
  exact perronSolution_eq_of_isBarrier hΩ hb hgb hw (hg ξ hξ) (frontier_subset_closure hξ)

/-! ### The exterior sphere condition -/

/-- **The exterior sphere barrier.** In `ℝⁿ` with `n ≠ 2`, suppose a closed ball centred at
`y ≠ ξ` meets `closure Ω` only at `ξ`, that is, every other point of `closure Ω` is farther from
`y` than `ξ`. Then `x ↦ G(ξ - y) - G(x - y)`, with `G = TauCeti.newtonianKernel n`, is a barrier
at `ξ` relative to `Ω`. -/
theorem isBarrier_newtonianKernel_sub {n : ℕ} (hn : n ≠ 2) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {ξ y : EuclideanSpace ℝ (Fin n)} (hξy : ξ ≠ y)
    (h : ∀ x ∈ closure Ω, x ≠ ξ → dist ξ y < dist x y) :
    IsBarrier Ω ξ fun x ↦ newtonianKernel n (ξ - y) - newtonianKernel n (x - y) := by
  -- The pole `y` lies outside `closure Ω`, where the kernel is harmonic.
  have hy : closure Ω ⊆ {y}ᶜ := fun x hx hxy ↦ by
    rcases eq_or_ne x ξ with rfl | hxξ
    · exact hξy hxy
    · have := h x hx hxξ
      rw [mem_singleton_iff.1 hxy, dist_self] at this
      exact dist_nonneg.not_gt this
  have hH := (harmonicOnNhd_newtonianKernel_sub n y).mono hy
  refine ⟨?_, continuousOn_const.sub hH.continuousOn, by simp, fun x hx hxξ ↦ sub_pos.2 ?_⟩
  · have heq : -(fun x ↦ newtonianKernel n (ξ - y) - newtonianKernel n (x - y)) =
        (fun x ↦ newtonianKernel n (x - y)) - fun _ ↦ newtonianKernel n (ξ - y) := by
      ext x
      simp
    rw [heq]
    exact ((hH.mono subset_closure).sub (harmonicOnNhd_const _)).subharmonicOn
  · have := h x hx hxξ
    rw [dist_eq_norm, dist_eq_norm] at this
    exact newtonianKernel_lt_newtonianKernel_of_norm_lt n hn (sub_ne_zero.2 hξy) this

/-- **The Dirichlet problem under the exterior sphere condition.** Let `Ω` be a bounded open
subset of `ℝⁿ`, `n ≠ 2`, such that at every boundary point `ξ` some closed ball centred at a point
`y ≠ ξ` meets `closure Ω` only at `ξ`. For boundary data `g` continuous on `frontier Ω`, there is
a function harmonic in `Ω`, continuous on `closure Ω` and equal to `g` on `frontier Ω`. -/
theorem exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_sphere {n : ℕ}
    (hn : n ≠ 2) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω)
    (hext : ∀ ξ ∈ frontier Ω, ∃ y ≠ ξ, ∀ x ∈ closure Ω, x ≠ ξ → dist ξ y < dist x y)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContinuousOn g (frontier Ω)) :
    ∃ u, HarmonicOnNhd u Ω ∧ ContinuousOn u (closure Ω) ∧ EqOn u g (frontier Ω) :=
  exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier hΩ hb (fun ξ hξ ↦
    let ⟨_, hyξ, hy⟩ := hext ξ hξ
    ⟨_, isBarrier_newtonianKernel_sub hn hyξ.symm hy⟩) hg

end TauCeti
