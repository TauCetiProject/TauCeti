/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Perron.Barrier
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Basic
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.Regularity.Hessian.Classical
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# The Dirichlet problem for Poisson's equation

Let `Ω ⊆ ℝ^{n+1}` be a bounded open set every boundary point of which admits a barrier, let
`0 < α < 1`, let `f` be bounded and locally `α`-Hölder in `Ω`, and let `g` be continuous on
`frontier Ω`. This file proves that the Dirichlet problem

`Δu = f` in `Ω`, `u = g` on `frontier Ω`

has a classical solution: a function `u` of class `C²` in `Ω` and continuous on `closure Ω`. Its
second derivatives are locally `α`-Hölder in `Ω`, so `u ∈ C^{2,α}(Ω) ∩ C⁰(closure Ω)`. No
continuity of `f` up to the boundary is assumed. The solution is unique on `closure Ω`, by the
comparison principle (`TauCeti.eqOn_closure_of_laplacian_eq_of_eqOn_frontier`). Barriers exist,
for instance, at every boundary point satisfying an exterior sphere condition
(`TauCeti.isBarrier_newtonianKernel_sub`, `TauCeti.isBarrier_log_norm_sub`), in particular on balls.

## The argument

The problem splits into a particular solution of `Δw = f` and a harmonic correction. For the
first, extend `f` by zero outside `Ω` and let `w` be the weak solution in `H¹₀(B)` of `Δw = f`
on a ball `B` containing `closure Ω`, given by Lax–Milgram
(`TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball`). The extended
right-hand side is bounded, so De Giorgi's theorem
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp`) makes the precise
representative of `w` Hölder continuous on `closure Ω`. In `Ω` the right-hand side is locally
Hölder, so the same precise representative is of class `C²` there and solves `Δw = f` pointwise
(`TauCeti.PDE.contDiffOn_preciseRepresentative_and_neg_laplacian_eq`). This replaces the
Newtonian potential of `f` in the classical proof.

Perron's method (`TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier`) then gives a
function `v`, harmonic in `Ω` and continuous on `closure Ω`, with boundary values `g - w`, and
`u = w + v` solves the problem. The local Hölder continuity of `D²u` is the interior Schauder
estimate (`TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian`).

## Main declarations

* `TauCeti.PDE.exists_contDiffOn_continuousOn_closure_laplacian_eq`: a particular solution of
  `Δw = f`, of class `C²` in `Ω` and continuous on `closure Ω`.
* `TauCeti.PDE.exists_contDiffOn_laplacian_eq_continuousOn_closure_eqOn_frontier`: the classical
  solvability of the Dirichlet problem for Poisson's equation.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.2, Theorem 4.3 and the remark following it (solvability on domains where the Dirichlet
  problem for Laplace's equation is solvable), and Theorem 6.13 (the case `L = Δ`).
-/

public section

noncomputable section

open InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **A particular solution of Poisson's equation.** Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be a
bounded open set, and let `f` be bounded and locally `α`-Hölder in `Ω`. Then there is a function
`w` of class `C²` in `Ω` and continuous on `closure Ω` with `Δw = f` in `Ω`. -/
theorem exists_contDiffOn_continuousOn_closure_laplacian_eq {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {f : E → ℝ}
    (hfb : Bornology.IsBounded (f '' Ω))
    (hfH : ∀ x ∈ Ω, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α f T) :
    ∃ w : E → ℝ, ContDiffOn ℝ 2 w Ω ∧ ContinuousOn w (closure Ω) ∧ ∀ x ∈ Ω, Δ w x = f x := by
  have hfc : ContinuousOn f Ω := fun x hx => by
    obtain ⟨T, hT, K, hK⟩ := hfH x hx
    exact ((hK.continuousOn hα).continuousAt hT).continuousWithinAt
  -- The right-hand side `h = -f` on `Ω`, extended by zero: `-Δw = h` is `Δw = f` in `Ω`.
  set h : E → ℝ := Ω.indicator fun x => -f x with hh
  -- A ball `B` containing the closed `1`-thickening of `closure Ω`.
  obtain ⟨R, hclB⟩ := hb.closure.cthickening.subset_ball (0 : E)
  let B : Opens E := ⟨ball 0 R, isOpen_ball⟩
  have hclB' : cthickening 1 (closure Ω) ⊆ (B : Set E) := hclB
  have hΩB : Ω ⊆ (B : Set E) :=
    subset_closure.trans ((self_subset_cthickening _).trans hclB')
  have hLp : ∀ p, MemLp h p (volume.restrict (B : Set E)) := fun p => by
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hfb
    have : IsFiniteMeasure (volume.restrict (B : Set E)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact memLp_indicator_of_continuousOn_of_norm_le hΩ.measurableSet (measure_ne_top _ _) hfc.neg
      (fun x hx => by simpa using hM _ (mem_image_of_mem f hx))
  -- The weak solution of `-Δw = h` in `H¹₀(B)`.
  obtain ⟨u, hu'⟩ := exists_energyFormH1_eq_integral_of_subset_ball (z := 0) (R := R) subset_rfl
    (hLp 2)
  -- De Giorgi's theorem: the precise representative `w` of the weak solution is Hölder
  -- continuous on `closure Ω`.
  obtain ⟨β, C, hβ, -, -, hDG⟩ := exists_holderOnWith_preciseRepresentative_of_memLp
    (ι := Fin (n + 1)) (mu := volume) (lam := 1) (Lam := 1) (r := n + 2)
    (by exact_mod_cast (show 1 < n + 2 by omega))
    (by simp only [Fintype.card_fin]; push_cast; linarith)
  have hwc : ContinuousOn (preciseRepresentative volume (W1p.value (u : W1p volume B 2)))
      (closure Ω) :=
    (hDG (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const (hLp _) hu' one_pos
      hclB').continuousOn hβ
  -- In `Ω`, where `h = -f` is locally Hölder, `w` is `C²` with `-Δw = h`.
  have hhH : ∀ x ∈ (⟨Ω, hΩ⟩ : Opens E), ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α h T :=
    fun x hx => by
      obtain ⟨T, hT, K, hK⟩ := hfH x hx
      refine ⟨T ∩ Ω, Filter.inter_mem hT (hΩ.mem_nhds hx), K, fun y hy z hz => ?_⟩
      rw [hh, indicator_of_mem hy.2, indicator_of_mem hz.2, edist_neg_neg]
      exact hK y hy.1 z hz.1
  have hΩ'B : (⟨Ω, hΩ⟩ : Opens E) ≤ B := hΩB
  obtain ⟨hw, hΔw⟩ := contDiffOn_preciseRepresentative_and_neg_laplacian_eq hα hα1 (hLp 2) hu'
    hΩ'B hhH
  refine ⟨_, hw, hwc, fun x hx => ?_⟩
  have := hΔw x hx
  rw [hh, indicator_of_mem hx] at this
  linarith

/-- **The Dirichlet problem for Poisson's equation.** Let `0 < α < 1`, and let `Ω ⊆ ℝ^{n+1}` be a
bounded open set every boundary point of which admits a barrier. Let `f` be bounded and locally
`α`-Hölder in `Ω`, and let `g` be continuous on `frontier Ω`. Then there is a function `u`, of
class `C²` in `Ω` and continuous on `closure Ω`, with

`Δu = f` in `Ω`, `u = g` on `frontier Ω`,

whose second derivatives are locally `α`-Hölder in `Ω`. It is unique on `closure Ω`
(`TauCeti.eqOn_closure_of_laplacian_eq_of_eqOn_frontier`). -/
theorem exists_contDiffOn_laplacian_eq_continuousOn_closure_eqOn_frontier {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hreg : ∀ ξ ∈ frontier Ω, ∃ w, IsBarrier Ω ξ w) {f g : E → ℝ}
    (hfb : Bornology.IsBounded (f '' Ω))
    (hfH : ∀ x ∈ Ω, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α f T)
    (hg : ContinuousOn g (frontier Ω)) :
    ∃ u : E → ℝ, ContDiffOn ℝ 2 u Ω ∧ ContinuousOn u (closure Ω) ∧ (∀ x ∈ Ω, Δ u x = f x) ∧
      EqOn u g (frontier Ω) ∧
      ∀ x ∈ Ω, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ 2 u) T := by
  obtain ⟨w, hw, hwc, hΔw⟩ :=
    exists_contDiffOn_continuousOn_closure_laplacian_eq hα hα1 hΩ hb hfb hfH
  -- The harmonic correction `v` with boundary values `g - w`.
  obtain ⟨v, hv, hvc, hvg⟩ := exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier hΩ hb hreg
    (hg.sub (hwc.mono frontier_subset_closure))
  have hu : ContDiffOn ℝ 2 (w + v) Ω := hw.add hv.contDiffOn
  have hΔ : ∀ x ∈ Ω, Δ (w + v) x = f x := fun x hx => by
    rw [(hw.contDiffAt (hΩ.mem_nhds hx)).laplacian_add (hv x hx).1, hΔw x hx,
      (hv x hx).2.self_of_nhds, Pi.zero_apply, add_zero]
  refine ⟨w + v, hu, hwc.add hvc, hΔ, fun x hx => ?_, fun x hx =>
    exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian hα hα1 hΩ hu (fun y hy => ?_) hx⟩
  · rw [Pi.add_apply, hvg hx, Pi.sub_apply, add_sub_cancel]
  · obtain ⟨T, hT, K, hK⟩ := hfH y hy
    refine ⟨T ∩ Ω, Filter.inter_mem hT (hΩ.mem_nhds hy), K, fun a ha b hb => ?_⟩
    rw [hΔ a ha.2, hΔ b hb.2]
    exact hK a ha.1 b hb.1

end PDE

end TauCeti
