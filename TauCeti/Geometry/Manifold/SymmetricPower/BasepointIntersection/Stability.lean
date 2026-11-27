/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Number
import TauCeti.Analysis.Analytic.ZeroCount
import TauCeti.Analysis.Complex.Conformal.Hurwitz
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.MetricSpace.SeparatedBalls
import TauCeti.Topology.Sym.Cons
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Stability of the basepoint intersection number in families

Let `F : P → ℂ → Sym α n` be a family of curves in a symmetric power of a complex curve `α`,
parametrized by a topological space `P`, with analytic symmetric-chart coordinates on a bounded
connected open set `U ⊆ ℂ`. If the curve `F p₀` sends the frontier of `U` off the basepoint divisor
`V_z`, and the family is jointly continuous along `{p₀} × closure U`, then the basepoint
intersection number of `F p` on `U` equals that of `F p₀` for every `p` near `p₀`
(`TauCeti.eventually_basepointIntersectionNumber_eq`). For a family that is jointly continuous on
`P × closure U` and sends the frontier of `U` off `V_z` at every parameter, the intersection number
is therefore a locally constant function of the parameter
(`TauCeti.isLocallyConstant_basepointIntersectionNumber`), and so it is constant along any path of
such curves.

For holomorphic disks in `Sym^g(Σ)` with boundary on the Heegaard tori `T_α ∪ T_β`, and a basepoint
`z` off the attaching curves, this says that the multiplicity `n_z` of Ozsváth--Szabó, counted
analytically as the sum of the positive local intersection orders with `V_z`, does not jump under
deformations of the disk: it is constant on the connected components of a moduli space of disks
and is preserved under limits that converge uniformly on the closed parameter domain.

The proof is Hurwitz's theorem. Near each of the finitely many intersections of `F p₀` with `V_z`,
choose a disc whose closure `F p₀` maps into one elementary-symmetric chart, in which `V_z` is an
affine hyperplane `ℓ = b`. On that disc the intersection orders of `F p` are the orders of vanishing
of the holomorphic function `ℓ ∘ C ∘ F p - b`, which converges uniformly to `ℓ ∘ C ∘ F p₀ - b` on
the bounding circle, so its zero count with multiplicity is eventually that of the limit
(`TauCeti.eventually_finsum_analyticOrderNatAt_ball_eq`). This is
`TauCeti.eventually_basepointIntersectionNumber_ball_eq_and_finite`. Away from these discs `F p₀`
misses the closed set `V_z` on a compact set, and so does `F p` for `p` near `p₀`.

## Main results

* `TauCeti.eventually_basepointIntersectionNumber_ball_eq_and_finite`: Hurwitz stability on a
  disc whose closure is mapped into a single chart and whose bounding circle is mapped off the
  divisor.
* `TauCeti.eventually_basepointIntersectionNumber_eq`: stability on a bounded connected domain
  whose frontier is mapped off the divisor.
* `TauCeti.isLocallyConstant_basepointIntersectionNumber`: the intersection number of a continuous
  family of such curves is locally constant in the parameter.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), Section 2 (the multiplicity `n_z`).
* L. Ahlfors, *Complex Analysis*, Ch. 5 (Hurwitz's theorem).
-/

public section

open Filter Function Metric Set
open scoped Manifold Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] [IsManifold 𝓘(ℂ) 1 α]
  {n : ℕ} {P : Type*} [TopologicalSpace P] {z : α} {F : P → ℂ → Sym α n} {p₀ : P}

/-- On a disc whose closure a curve `f` maps into the chart `C` of `s`, with analytic chart
coordinates, and whose bounding circle `f` maps off the basepoint divisor, the intersection orders
of `f` with the divisor are the orders of vanishing of `ℓ ∘ C ∘ f - b`, for an affine equation
`ℓ = b` of the divisor in `C`. So the basepoint intersection number of `f` on the disc is the zero
count of this function, and `f` meets the divisor at finitely many parameters of the disc. -/
private theorem basepointIntersectionNumber_ball_eq_finsum_analyticOrderNatAt {f : ℂ → Sym α n}
    {s : Sym α n} {c : ℂ} {r : ℝ} (hr : 0 < r) {ℓ : (Fin n → ℂ) →L[ℂ] ℂ} {b : ℂ}
    (hℓ : ∀ x ∈ (symChartAt (K := ℂ) s).source,
      x ∈ Sym.basepointDivisor z ↔ ℓ (symChartAt (K := ℂ) s x) = b)
    (hc : ∀ t ∈ closedBall c r, ContinuousAt f t)
    (ha : ∀ t ∈ closedBall c r, AnalyticAt ℂ (fun t' => symChartAt (K := ℂ) (f t) (f t')) t)
    (hs : ∀ t ∈ closedBall c r, f t ∈ (symChartAt (K := ℂ) s).source)
    (hsph : ∀ t ∈ sphere c r, f t ∉ Sym.basepointDivisor z) :
    basepointIntersectionNumber z f (ball c r) =
        ↑(∑ᶠ t ∈ ball c r, analyticOrderNatAt (fun t => ℓ (symChartAt (K := ℂ) s (f t)) - b) t) ∧
      (ball c r ∩ f ⁻¹' Sym.basepointDivisor z).Finite := by
  set g : ℂ → ℂ := fun t => ℓ (symChartAt (K := ℂ) s (f t)) - b
  have hC : ∀ t ∈ closedBall c r, AnalyticAt ℂ (fun t' => symChartAt (K := ℂ) s (f t')) t :=
    fun t ht => analyticAt_symChartAt_comp_of_analyticAt (hc t ht) (mem_symChartAt_source _)
      (hs t ht) (ha t ht)
  have hg : AnalyticOnNhd ℂ g (closedBall c r) := fun t ht =>
    ((ℓ.analyticAt _).comp (hC t ht)).sub analyticAt_const
  -- `g` does not vanish on the bounding circle, so it has finite order on the whole closed disc
  obtain ⟨t₀, ht₀⟩ := (NormedSpace.sphere_nonempty (x := c) (r := r)).2 hr.le
  have htop : ∀ t ∈ closedBall c r, analyticOrderAt g t ≠ ⊤ := fun t ht =>
    hg.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c r).isPreconnected
      (sphere_subset_closedBall ht₀) ht <| by
        have h₀ : analyticOrderAt g t₀ = 0 := analyticOrderAt_eq_zero.2 <| Or.inr fun h =>
          hsph t₀ ht₀ ((hℓ _ (hs t₀ (sphere_subset_closedBall ht₀))).2 (sub_eq_zero.1 h))
        rw [h₀]
        exact ENat.zero_ne_top
  have hord : ∀ t ∈ ball c r, basepointIntersectionOrder z f t = analyticOrderNatAt g t :=
    fun t ht => by
      have ht' := ball_subset_closedBall ht
      rw [basepointIntersectionOrder_eq_analyticOrderAt_sub (hc t ht') (hs t ht') (hC t ht') hℓ,
        Nat.cast_analyticOrderNatAt (htop t ht')]
  have hfin := hg.meromorphicOn.finite_ball_inter_support_analyticOrderNatAt
  refine ⟨?_, hfin.subset fun t ⟨ht, htV⟩ => ⟨ht, fun h0 => ?_⟩⟩
  · rw [basepointIntersectionNumber_def, finsum_mem_congr rfl hord]
    exact ((Nat.castAddMonoidHom ℕ∞).map_finsum_mem' hfin).symm
  · have h := hord t ht
    rw [h0, Nat.cast_zero,
      basepointIntersectionOrder_eq_zero_iff (ha t (ball_subset_closedBall ht))] at h
    exact h htV

/-- **Hurwitz stability of the basepoint intersection number on a disc.** Let `F` be a family of
curves in `Sym α n`, jointly continuous at every point of `{p₀} × closedBall c r`, such that the
curves `F p` for `p` near `p₀` are continuous on the closed disc with analytic symmetric-chart
coordinates there. If `F p₀` maps the closed disc into the chart of a tuple `s` and its bounding
circle off the basepoint divisor, then for `p` near `p₀` the curve `F p` meets the divisor at only
finitely many parameters of the open disc, and its basepoint intersection number on the open disc
is that of `F p₀`. -/
theorem eventually_basepointIntersectionNumber_ball_eq_and_finite {s : Sym α n} {c : ℂ} {r : ℝ}
    (hF : ∀ t ∈ closedBall c r, ContinuousAt (uncurry F) (p₀, t))
    (hFc : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ closedBall c r, ContinuousAt (F p) t)
    (hFa : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ closedBall c r,
      AnalyticAt ℂ (fun t' => symChartAt (K := ℂ) (F p t) (F p t')) t)
    (hs : ∀ t ∈ closedBall c r, F p₀ t ∈ (symChartAt (K := ℂ) s).source)
    (hsph : ∀ t ∈ sphere c r, F p₀ t ∉ Sym.basepointDivisor z) :
    ∀ᶠ p in 𝓝 p₀, basepointIntersectionNumber z (F p) (ball c r) =
        basepointIntersectionNumber z (F p₀) (ball c r) ∧
      (ball c r ∩ F p ⁻¹' Sym.basepointDivisor z).Finite := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  set C := symChartAt (K := ℂ) s
  -- for `p` near `p₀`, `F p` still maps the closed disc into the chart and the circle off `V_z`
  have hsrc : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ closedBall c r, F p t ∈ C.source :=
    (isCompact_closedBall c r).eventually_forall_of_forall_eventually fun t ht =>
      hF t ht (C.open_source.mem_nhds (hs t ht))
  have hsph' : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ sphere c r, F p t ∉ Sym.basepointDivisor z :=
    (isCompact_sphere c r).eventually_forall_of_forall_eventually fun t ht =>
      hF t (sphere_subset_closedBall ht)
        ((Sym.isClosed_basepointDivisor z).isOpen_compl.mem_nhds (hsph t ht))
  by_cases hV : ∃ x ∈ C.source, x ∈ Sym.basepointDivisor z
  swap
  · -- the chart misses the divisor, so no curve meets it on the disc
    push Not at hV
    have h0 : ∀ q, (∀ t ∈ closedBall c r, F q t ∈ C.source) →
        ∀ t ∈ ball c r, F q t ∉ Sym.basepointDivisor z :=
      fun q hq t ht => hV _ (hq t (ball_subset_closedBall ht))
    filter_upwards [hsrc] with p hp
    rw [basepointIntersectionNumber_eq_zero_of_forall_notMem (h0 p hp),
      basepointIntersectionNumber_eq_zero_of_forall_notMem (h0 p₀ hsrc.self_of_nhds)]
    exact ⟨rfl, (finite_empty).subset fun t ⟨ht, htV⟩ => h0 p hp t ht htV⟩
  obtain ⟨ℓ, b, -, hℓ⟩ := exists_continuousLinearMap_ne_zero_mem_iff_symChartAt (K := ℂ) z s hV
  -- the local equations `g p = ℓ ∘ C ∘ F p - b` of the divisor along the curves
  set g : P → ℂ → ℂ := fun p t => ℓ (C (F p t)) - b
  have hga : ∀ᶠ p in 𝓝 p₀, AnalyticOnNhd ℂ (g p) (closedBall c r) := by
    filter_upwards [hFc, hFa, hsrc] with p hc ha hp t ht
    exact ((ℓ.analyticAt _).comp (analyticAt_symChartAt_comp_of_analyticAt (hc t ht)
      (mem_symChartAt_source _) (hp t ht) (ha t ht))).sub analyticAt_const
  have hconv : TendstoUniformlyOn g (g p₀) (𝓝 p₀) (sphere c r) :=
    (isCompact_sphere c r).tendstoUniformlyOn_of_continuousAt fun t ht => by
      have h : ContinuousAt (fun x => ℓ (C x) - b) (uncurry F (p₀, t)) :=
        (ℓ.continuous.continuousAt.comp (C.continuousAt (hs t (sphere_subset_closedBall ht)))).sub
          continuousAt_const
      exact h.comp (hF t (sphere_subset_closedBall ht))
  have hne : ∀ t ∈ sphere c r, g p₀ t ≠ 0 := fun t ht h =>
    hsph t ht ((hℓ _ (hs t (sphere_subset_closedBall ht))).2 (sub_eq_zero.1 h))
  have h₀ := basepointIntersectionNumber_ball_eq_finsum_analyticOrderNatAt hr hℓ
    hFc.self_of_nhds hFa.self_of_nhds hsrc.self_of_nhds hsph
  filter_upwards [hFc, hFa, hsrc, hsph', eventually_finsum_analyticOrderNatAt_ball_eq
    hga.self_of_nhds hga hconv hne] with p hc ha hp hp' hH
  obtain ⟨hp₁, hp₂⟩ := basepointIntersectionNumber_ball_eq_finsum_analyticOrderNatAt hr hℓ hc ha
    hp hp'
  refine ⟨?_, hp₂⟩
  rw [hp₁, h₀.1]
  exact congrArg _ hH

omit [IsManifold 𝓘(ℂ) 1 α] in
/-- Around the finitely many intersections of `f` with the basepoint divisor in a bounded
connected open set `U` whose frontier `f` maps off the divisor, there are closed discs of a common
radius `r > 0` that lie in `U`, are mapped by `f` into the chart at the image of their centres and
meet the divisor only at their centres, and whose interiors are pairwise disjoint. -/
private theorem exists_pos_forall_closedBall_basepointDivisor {f : ℂ → Sym α n} {U : Set ℂ}
    (hUo : IsOpen U) (hU : IsPreconnected U) (hUc : IsCompact (closure U))
    (hf : ContinuousOn f (closure U))
    (ha : ∀ w ∈ U, AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (hfr : ∀ t ∈ frontier U, f t ∉ Sym.basepointDivisor z) :
    ∃ r > 0, (U ∩ f ⁻¹' Sym.basepointDivisor z).PairwiseDisjoint (ball · r) ∧
      ∀ w ∈ U ∩ f ⁻¹' Sym.basepointDivisor z, ∀ t ∈ closedBall w r, t ∈ U ∧
        f t ∈ (symChartAt (K := ℂ) (f w)).source ∧ (t ≠ w → f t ∉ Sym.basepointDivisor z) := by
  set S := U ∩ f ⁻¹' Sym.basepointDivisor z
  have hfc : ∀ t ∈ U, ContinuousAt f t := fun t ht =>
    hf.continuousAt (mem_of_superset (hUo.mem_nhds ht) subset_closure)
  have hS : S.Finite := finite_basepointDivisor_intersections_of_frontier z hUo hU hUc hf
    (fun w hw _ => ha w hw) hfr
  have hnhds : ∀ w ∈ S, U ∩ f ⁻¹' (symChartAt (K := ℂ) (f w)).source ∩
      {t | t ≠ w → f t ∉ Sym.basepointDivisor z} ∈ 𝓝 w := fun w hw => by
    have hiso := eventually_nhdsWithin_iff.1 <|
      eventually_notMem_basepointDivisor_of_isPreconnected z hU hfc (fun w hw _ => ha w hw)
        (exists_mem_notMem_basepointDivisor_of_frontier ⟨w, hw.1⟩ hUc hf hfr) hw.1 hw.2
    exact inter_mem (inter_mem (hUo.mem_nhds hw.1) ((hfc w hw.1).preimage_mem_nhds
      ((symChartAt (K := ℂ) (f w)).open_source.mem_nhds (mem_symChartAt_source _)))) hiso
  obtain ⟨r, hr, hrS, hsep⟩ := (eventually_mem_nhdsWithin.and
    (nhdsWithin_le_nhds (eventually_closedBall_subset_and_lt_dist hS hnhds))).exists
    (f := 𝓝[>] (0 : ℝ))
  refine ⟨r, hr, fun w hw w' hw' hww' => ball_disjoint_ball ?_, fun w hw t ht => ?_⟩
  · linarith [hsep w hw w' hw' hww']
  · obtain ⟨⟨htU, hts⟩, hiso⟩ := hrS w hw ht
    exact ⟨htU, hts, hiso⟩

/-- **Stability of the basepoint intersection number.** Let `U ⊆ ℂ` be a bounded connected open
set and `F` a family of curves in `Sym α n` that is jointly continuous within
`P × closure U` at every point of `{p₀} × closure U`, such that the curves `F p` for `p` near `p₀`
are continuous on `U` with analytic symmetric-chart coordinates there. If `F p₀` sends the frontier
of `U` off the basepoint divisor, then for `p` near `p₀` the basepoint intersection number of
`F p` on `U` is that of `F p₀`. -/
theorem eventually_basepointIntersectionNumber_eq {U : Set ℂ} (hUo : IsOpen U)
    (hU : IsPreconnected U) (hUc : IsCompact (closure U))
    (hF : ∀ t ∈ closure U, ContinuousWithinAt (uncurry F) (univ ×ˢ closure U) (p₀, t))
    (hFc : ∀ᶠ p in 𝓝 p₀, ContinuousOn (F p) U)
    (hFa : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ U,
      AnalyticAt ℂ (fun t' => symChartAt (K := ℂ) (F p t) (F p t')) t)
    (hfr : ∀ t ∈ frontier U, F p₀ t ∉ Sym.basepointDivisor z) :
    ∀ᶠ p in 𝓝 p₀, basepointIntersectionNumber z (F p) U =
      basepointIntersectionNumber z (F p₀) U := by
  set V := Sym.basepointDivisor (n := n) z
  set f := F p₀
  have hf : ContinuousOn f (closure U) := fun t ht =>
    (hF t ht).comp (continuousWithinAt_const.prodMk continuousWithinAt_id)
      fun t ht => ⟨mem_univ _, ht⟩
  -- small disjoint discs around the finitely many intersections of `f` with `V` in `U`
  set S := U ∩ f ⁻¹' V
  have hS : S.Finite := finite_basepointDivisor_intersections_of_frontier z hUo hU hUc hf
    (fun w hw _ => hFa.self_of_nhds w hw) hfr
  obtain ⟨r, hr, hdisj, hrS⟩ :=
    exists_pos_forall_closedBall_basepointDivisor hUo hU hUc hf hFa.self_of_nhds hfr
  have hball : ∀ w ∈ S, closedBall w r ⊆ U := fun w hw t ht => (hrS w hw t ht).1
  -- on each disc, the intersection number is stable by Hurwitz's theorem
  have hloc : ∀ᶠ p in 𝓝 p₀, ∀ w ∈ S,
      basepointIntersectionNumber z (F p) (ball w r) = basepointIntersectionNumber z f (ball w r) ∧
        (ball w r ∩ F p ⁻¹' V).Finite :=
    hS.eventually_all.2 fun w hw =>
      eventually_basepointIntersectionNumber_ball_eq_and_finite (s := f w)
      (fun t ht => (hF t (subset_closure (hball w hw ht))).continuousAt <| prod_mem_nhds univ_mem <|
        mem_of_superset (hUo.mem_nhds (hball w hw ht)) subset_closure)
      (hFc.mono fun p hp t ht => hp.continuousAt (hUo.mem_nhds (hball w hw ht)))
      (hFa.mono fun p hp t ht => hp t (hball w hw ht)) (fun t ht => (hrS w hw t ht).2.1)
      fun t ht => (hrS w hw t (sphere_subset_closedBall ht)).2.2 (ne_of_mem_sphere ht hr.ne')
  -- off the discs, `f` misses `V` on a compact set, and so does `F p` for `p` near `p₀`
  set K := closure U \ ⋃ w ∈ S, ball w r
  have hoff : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ K, F p t ∉ V := by
    refine IsCompact.eventually_forall_mem_of_continuousWithinAt
      (hUc.diff (isOpen_biUnion fun _ _ => isOpen_ball)) sdiff_subset
      (Sym.isClosed_basepointDivisor z).isOpen_compl (fun t ht => hF t ht.1) ?_
    rintro t ⟨htU, htB⟩ htV
    by_cases ht : t ∈ U
    · exact htB (mem_biUnion ⟨ht, htV⟩ (mem_ball_self hr))
    · exact hfr t ⟨htU, by rwa [hUo.interior_eq]⟩ htV
  -- so the intersection number on `U` is the sum of those on the discs
  have hdec : ∀ q, (∀ w ∈ S, (ball w r ∩ F q ⁻¹' V).Finite) → (∀ t ∈ K, F q t ∉ V) →
      basepointIntersectionNumber z (F q) U =
        ∑ᶠ w ∈ S, basepointIntersectionNumber z (F q) (ball w r) := fun q hq hqK => by
    rw [basepointIntersectionNumber_eq_of_subset (W := ⋃ w ∈ S, ball w r)
      (iUnion₂_subset fun w hw => ball_subset_closedBall.trans (hball w hw))
      fun t ht htV => by_contra fun htB => hqK t ⟨subset_closure ht, htB⟩ htV,
      basepointIntersectionNumber_biUnion hS hdisj hq]
  filter_upwards [hloc, hoff] with p hp hpK
  rw [hdec p (fun w hw => (hp w hw).2) hpK,
    hdec p₀ (fun w hw => (hloc.self_of_nhds w hw).2) hoff.self_of_nhds]
  exact finsum_mem_congr rfl fun w hw => (hp w hw).1

/-- **The basepoint intersection number is locally constant in families.** Let `U ⊆ ℂ` be a bounded
connected open set and `F` a family of curves in `Sym α n`, jointly continuous on `P × closure U`,
with analytic symmetric-chart coordinates on `U`, each sending the frontier of `U` off the basepoint
divisor. Then the basepoint intersection number of `F p` on `U` is a locally constant function of
`p`; in particular it is constant when `P` is preconnected. -/
theorem isLocallyConstant_basepointIntersectionNumber {U : Set ℂ} (hUo : IsOpen U)
    (hU : IsPreconnected U) (hUc : IsCompact (closure U))
    (hF : ContinuousOn (uncurry F) (univ ×ˢ closure U))
    (hFa : ∀ p, ∀ t ∈ U, AnalyticAt ℂ (fun t' => symChartAt (K := ℂ) (F p t) (F p t')) t)
    (hfr : ∀ p, ∀ t ∈ frontier U, F p t ∉ Sym.basepointDivisor z) :
    IsLocallyConstant fun p => basepointIntersectionNumber z (F p) U :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun p₀ =>
    eventually_basepointIntersectionNumber_eq hUo hU hUc
      (fun _ ht => hF _ ⟨mem_univ _, ht⟩)
      (Eventually.of_forall fun _ =>
        (hF.comp (continuousOn_const.prodMk continuousOn_id) fun _ ht => ⟨mem_univ _, ht⟩).mono
          subset_closure)
      (Eventually.of_forall hFa) (hfr p₀)

end TauCeti

end
