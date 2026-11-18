/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import TauCeti.Topology.Algebra.Polynomial.Basic

/-!
# Roots and factorizations at a puncture

Let `F y` be complex polynomials of bounded degree whose coefficients are continuous at a point
`c`. A root of `F y`, continuous on a punctured ball about `c` in a real normed space of dimension
greater than one, converges at `c` to a root of `F c`
(`TauCeti.Polynomial.exists_isRoot_tendsto_of_continuousOn`): near `c` the roots of `F y` lie close
to the finitely many roots of `F c` (`Polynomial.eventually_rel_roots_norm_sub_lt`), and the
connected punctured ball cannot be split between two of them
(`TauCeti.exists_mem_tendsto_of_forall_eventually_exists_dist_lt`). A splitting of `F y` into
linear factors with roots continuous at `c` passes to the limit
(`TauCeti.Polynomial.eq_prod_X_sub_C_of_continuousAt`).
-/

public section

open Filter Metric Polynomial Set Topology

namespace TauCeti.Polynomial

/-- **A continuous root extends across a puncture.** Let `F y` be polynomials of degree `d` near
`c`, a point of a real normed space of dimension greater than one, with coefficients continuous at
`c`. A root `v` of `F`, continuous on a punctured ball about `c`, converges at `c` to a root of
`F c`. -/
theorem exists_isRoot_tendsto_of_continuousOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) {F : E → ℂ[X]} {c : E} {d : ℕ}
    (hF : ∀ i ≤ d, ContinuousAt (fun y => (F y).coeff i) c)
    (hdeg : ∀ᶠ y in 𝓝 c, (F y).degree = d) {δ : ℝ} (hδ : 0 < δ) {v : E → ℂ}
    (hv : ContinuousOn v (ball c δ \ {c})) (hroot : ∀ z ∈ ball c δ \ {c}, (F z).IsRoot (v z)) :
    ∃ w, (F c).IsRoot w ∧ Tendsto v (𝓝[≠] c) (𝓝 w) := by
  classical
  -- near `c`, every root of `F y` lies close to a root of `F c`
  have hclose (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ z in 𝓝[≠] c, ∃ s ∈ (F c).roots.toFinset, dist (v z) s < ε := by
    filter_upwards [nhdsWithin_le_nhds (eventually_rel_roots_norm_sub_lt hF hdeg hε),
      nhdsWithin_le_nhds hdeg, self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds c hδ)] with
      z hrel hzd hzc hzb
    have hvz : v z ∈ (F z).roots :=
      (mem_roots (ne_zero_of_coe_le_degree hzd.ge)).2 (hroot z ⟨hzb, hzc⟩)
    obtain ⟨s, hs, hsv⟩ := Multiset.exists_mem_of_rel_of_mem (Multiset.rel_flip.2 hrel) hvz
    exact ⟨s, Multiset.mem_toFinset.2 hs, by rwa [dist_eq_norm, norm_sub_rev]⟩
  obtain ⟨w, hw, hlim⟩ := exists_mem_tendsto_of_forall_eventually_exists_dist_lt hE hδ hv hclose
  exact ⟨w, isRoot_of_mem_roots (Multiset.mem_toFinset.1 hw), hlim⟩

/-- **Splitting passes to the limit.** Let `F y` be complex polynomials of degree at most `d` near
`c`, with coefficients continuous at `c`, that split into linear factors `X - u_i(y)` on a
punctured neighbourhood of `c`, the roots `u_i` being continuous at `c`. Then `F c` splits into the
limiting factors `X - u_i(c)`. -/
theorem eq_prod_X_sub_C_of_continuousAt {B : Type*} [TopologicalSpace B] {F : B → ℂ[X]} {c : B}
    [(𝓝[≠] c).NeBot] {d : ℕ} {u : Fin d → B → ℂ}
    (hF : ∀ i ≤ d, ContinuousAt (fun y => (F y).coeff i) c)
    (hdeg : ∀ᶠ y in 𝓝 c, (F y).natDegree ≤ d) (hu : ∀ i, ContinuousAt (u i) c)
    (hsplit : ∀ᶠ y in 𝓝[≠] c, F y = ∏ i, (X - C (u i y))) :
    F c = ∏ i, (X - C (u i c)) := by
  refine Polynomial.funext fun z => tendsto_nhds_unique (f := fun y => (F y).eval z)
    (l := 𝓝[≠] c) ?_ ?_
  · exact (continuousAt_eval hF hdeg continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
  · have hprod : Tendsto (fun y => (∏ i, (X - C (u i y))).eval z) (𝓝[≠] c)
        (𝓝 ((∏ i, (X - C (u i c))).eval z)) := by
      simp only [eval_prod, eval_sub, eval_X, eval_C]
      exact tendsto_finsetProd _ fun i _ =>
        tendsto_const_nhds.sub ((hu i).tendsto.mono_left nhdsWithin_le_nhds)
    exact hprod.congr' (hsplit.mono fun y hy => by simp only [hy])

end TauCeti.Polynomial
