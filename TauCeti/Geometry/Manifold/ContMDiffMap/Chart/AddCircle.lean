/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.Equicontinuity
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Topology.Instances.AddCircle.Lift
import TauCeti.Topology.MetricSpace.Pseudo.Basic

/-!
# The weak Whitney topology on functions on a circle

The charts of the circle `AddCircle p` are local real lifts: on the target of the chart at `x`,
the inverse chart is the quotient map `ℝ → AddCircle p`. So the coordinate derivatives of a
vector-valued `C^n` map `f` on the circle, which define the weak Whitney topology, are the
derivatives of its periodic lift `f ∘ (↑)` on `ℝ`, restricted to the chart targets
(`ContMDiffMap.chartIteratedFDeriv_addCircle_apply`).

Consequently a family of `C^n` maps on the circle converges in the weak Whitney topology as soon
as the derivatives of order at most `n` of their lifts converge locally uniformly on `ℝ`
(`ContMDiffMap.tendsto_addCircle_of_tendstoLocallyUniformly`). In particular lifts of periodic
functions converge when, for each order `m ≤ n`, the `m`-th derivatives of their differences are
bounded uniformly by constants tending to `0`
(`ContMDiffMap.tendsto_addCircle_of_norm_iteratedDeriv_sub_le`). This is how explicit families of
functions on the circle, given by periodic formulas, are shown to converge in the `C^n` topology.

The same description holds for maps between circles `AddCircle p → AddCircle q`, through their
continuous real lifts `F`, `f [x] = [F x]`. Read in charts, such a map is near each point its lift
plus an integer multiple of the period `q`
(`AddCircle.exists_extChartAt_comp_eventuallyEq_add_zsmul`), so its coordinate derivatives of
positive order are those of the lift. The lift itself is only
defined up to adding a multiple of `q`; normalized to vanish at `0` it is unique. For `1 ≤ n`, a
family of `C^n` maps of circles converges in the weak Whitney topology exactly when the values at
`0` converge and the normalized lifts converge in every `C^m`, `m ≤ n`, locally uniformly on `ℝ`
(`ContMDiffMap.tendsto_addCircle_addCircle_iff_lift`). The two directions are
`ContMDiffMap.tendsto_addCircle_addCircle_of_lift` and
`ContMDiffMap.tendstoLocallyUniformly_iteratedFDeriv_lift`,
`ContMDiffMap.tendstoLocallyUniformly_lift_sub_lift_zero`. This is what makes constructions on
diffeomorphisms of the circle through their lifts continuous on the diffeomorphism group.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

/-! ### Charts of the circle along the quotient map -/

namespace AddCircle

variable {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]

/-- Read in charts, a map of circles with a continuous lift `F` has the iterated derivatives of
positive order of `F`. -/
theorem iteratedFDerivWithin_extChartAt_comp_of_lift {f : AddCircle p → AddCircle q}
    {F : ℝ → ℝ} (hF : Continuous F) (hfF : ∀ x : ℝ, f x = F x) {x : AddCircle p}
    {y : AddCircle q} {z : ℝ} (hz : z ∈ (extChartAt 𝓘(ℝ) x).target)
    (hy : f z ∈ (extChartAt 𝓘(ℝ) y).source) {m : ℕ} (hm : m ≠ 0) :
    iteratedFDerivWithin ℝ m (extChartAt 𝓘(ℝ) y ∘ f ∘ (extChartAt 𝓘(ℝ) x).symm)
      (extChartAt 𝓘(ℝ) x).target z = iteratedFDeriv ℝ m F z := by
  obtain ⟨k, hk⟩ := exists_extChartAt_comp_eventuallyEq_add_zsmul hF hfF hz hy
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [iteratedFDerivWithin_of_isOpen _ (isOpen_extChartAt_target x) hz,
    (Filter.EventuallyEq.iteratedFDeriv ℝ hk _).eq_of_nhds,
    TauCeti.iteratedFDeriv_succ_add_const]

omit [Fact (0 < p)] [Fact (0 < q)] in
/-- The iterated derivatives of positive order of a continuous lift `F` of a circle map are
periodic: `F (· + j • p)` differs from `F` by a constant. -/
theorem iteratedFDeriv_lift_add_zsmul {f : AddCircle p → AddCircle q} {F : ℝ → ℝ}
    (hF : Continuous F) (hfF : ∀ x : ℝ, f x = F x) {m : ℕ} (hm : m ≠ 0) (j : ℤ) (v : ℝ) :
    iteratedFDeriv ℝ m F (v + j • p) = iteratedFDeriv ℝ m F v := by
  obtain ⟨c, hc⟩ := exists_forall_eq_add_of_lift (T := q) (F₁ := fun v ↦ F (v + j • p))
    (by fun_prop) hF fun v ↦ by rw [← hfF, ← hfF, coe_add, coe_zsmul, coe_period, smul_zero,
      add_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hshift : (fun v ↦ F (v + j • p)) = fun v ↦ F v + c := funext hc
  rw [← iteratedFDeriv_comp_add_right, hshift, TauCeti.iteratedFDeriv_succ_add_const]

end AddCircle

namespace ContMDiffMap

variable {p : ℝ} [Fact (0 < p)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞ω}

/-- The coordinate derivatives of a map on the circle are the derivatives of its periodic lift. -/
theorem chartIteratedFDeriv_addCircle_apply (f : C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯)
    (x : AddCircle p) (m : ℕ) (hm : m ≤ n) (y : (extChartAt 𝓘(ℝ) x).target) :
    chartIteratedFDeriv f x m hm y = iteratedFDeriv ℝ m (f ∘ ((↑) : ℝ → AddCircle p)) y := by
  have hT : IsOpen (extChartAt 𝓘(ℝ) x).target := isOpen_extChartAt_target x
  rw [chartIteratedFDeriv_self_target_apply, iteratedFDerivWithin_of_isOpen m hT y.property]
  -- Near `y`, the map read in the chart is the lift, since the inverse chart is the quotient map.
  refine (Filter.EventuallyEq.iteratedFDeriv ℝ ?_ m).eq_of_nhds
  filter_upwards [hT.mem_nhds y.property] with u hu
  simp only [Function.comp_apply, AddCircle.extChartAt_symm_apply x hu]

/-- A family of `C^n` maps on the circle converges in the weak Whitney topology when the
derivatives of order at most `n` of their lifts to `ℝ` converge locally uniformly. -/
theorem tendsto_addCircle_of_tendstoLocallyUniformly {ι : Type*} {l : Filter ι}
    {f : ι → C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯} {g : C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯}
    (h : ∀ m : ℕ, m ≤ n → TendstoLocallyUniformly
      (fun i ↦ iteratedFDeriv ℝ m (f i ∘ ((↑) : ℝ → AddCircle p)))
      (iteratedFDeriv ℝ m (g ∘ ((↑) : ℝ → AddCircle p))) l) :
    Tendsto f l (𝓝 g) := by
  refine tendsto_manifoldWeakWhitney_iff_chartIteratedFDeriv.2 fun x m hm ↦ ?_
  refine ContinuousMap.tendsto_of_tendstoLocallyUniformly ?_
  have hφ (φ : C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯) : ⇑(chartIteratedFDeriv φ x m hm) =
      iteratedFDeriv ℝ m (φ ∘ ((↑) : ℝ → AddCircle p)) ∘ Subtype.val :=
    funext (chartIteratedFDeriv_addCircle_apply φ x m hm)
  simp only [hφ]
  exact (h m hm).comp _ continuous_subtypeVal

/-- Lifts of `p`-periodic `C^n` functions `f i` converge to the lift of `g` in the weak Whitney
topology when, for each order `m ≤ n`, eventually `‖(f i - g)⁽ᵐ⁾ t‖ ≤ b m i` for all `t`, with
bounds `b m i` tending to `0`. -/
theorem tendsto_addCircle_of_norm_iteratedDeriv_sub_le {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → F} {g : ℝ → F} (hf : ∀ i, Function.Periodic (f i) p)
    (hg : Function.Periodic g p) (hfn : ∀ i, ContDiff ℝ n (f i)) (hgn : ContDiff ℝ n g)
    {b : ℕ → ι → ℝ} (hb : ∀ m : ℕ, m ≤ n → Tendsto (b m) l (𝓝 0))
    (h : ∀ m : ℕ, m ≤ n → ∀ᶠ i in l, ∀ t, ‖iteratedDeriv m (f i - g) t‖ ≤ b m i) :
    Tendsto (β := C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ, F), F⟯)
      (fun i ↦ ⟨(hf i).lift, (hf i).contMDiff_lift (hfn i)⟩) l
      (𝓝 ⟨hg.lift, hg.contMDiff_lift hgn⟩) := by
  refine tendsto_addCircle_of_tendstoLocallyUniformly fun m hm ↦ ?_
  simp only [coeFn_mk, Function.Periodic.lift_comp_coe]
  refine (tendstoUniformlyOn_univ.1 (TauCeti.tendstoUniformlyOn_of_dist_le (hb m hm)
    ((h m hm).mono fun i hi t _ ↦ ?_))).tendstoLocallyUniformly
  rw [dist_eq_norm, ← iteratedFDeriv_sub_apply ((hfn i).contDiffAt.of_le hm)
    (hgn.contDiffAt.of_le hm), norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hi t

/-! ### Maps between circles -/

section CircleMaps

open Metric

variable {q : ℝ} [Fact (0 < q)] {ι : Type*} {l : Filter ι}
  {f : ι → C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ), AddCircle q⟯}
  {g : C^n⟮𝓘(ℝ), AddCircle p; 𝓘(ℝ), AddCircle q⟯} {F : ι → ℝ → ℝ} {G : ℝ → ℝ}

/-- Near a point `w₀` of the chart target, where `g` is read in the charts at `x` and `y` as its
lift `G` plus `k • q`, so are the maps `f i`, with their lifts `F i` and the same `k`, eventually,
as soon as the lifts converge locally uniformly. -/
private theorem exists_eventually_extChartAt_comp_eventuallyEq (hG : Continuous G)
    (hfF : ∀ i (x : ℝ), f i x = F i x) (hgG : ∀ x : ℝ, g x = G x)
    (h₀ : TendstoLocallyUniformly F G l) {x : AddCircle p} {y : AddCircle q} {w₀ : ℝ}
    (hw₀ : w₀ ∈ (extChartAt 𝓘(ℝ) x).target) (hgs : g w₀ ∈ (extChartAt 𝓘(ℝ) y).source) :
    ∃ k : ℤ, (extChartAt 𝓘(ℝ) y ∘ g ∘ (extChartAt 𝓘(ℝ) x).symm =ᶠ[𝓝 w₀]
        fun v ↦ G v + k • q) ∧
      ∀ᶠ z in l ×ˢ 𝓝 w₀, f z.1 ((extChartAt 𝓘(ℝ) x).symm z.2) ∈ (extChartAt 𝓘(ℝ) y).source ∧
        extChartAt 𝓘(ℝ) y ∘ f z.1 ∘ (extChartAt 𝓘(ℝ) x).symm =ᶠ[𝓝 z.2]
          fun v ↦ F z.1 v + k • q := by
  rw [hgG] at hgs
  -- On a ball around `G w₀`, the chart at `y` read along the quotient map is `· + k • q`.
  obtain ⟨k, hk⟩ := AddCircle.exists_eventually_extChartAt_coe_eq_add_zsmul y hgs
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hk.and
    (continuous_quotient_mk'.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source y).mem_nhds hgs)))
  -- Wherever a lift stays in that ball, its map read in charts is the lift plus `k • q`.
  have hread {φ : AddCircle p → AddCircle q} {Φ : ℝ → ℝ} (hφ : ∀ x : ℝ, φ x = Φ x) {v : ℝ}
      (hv : v ∈ (extChartAt 𝓘(ℝ) x).target) (hΦ : dist (Φ v) (G w₀) < ε) :
      (extChartAt 𝓘(ℝ) y ∘ φ ∘ (extChartAt 𝓘(ℝ) x).symm) v = Φ v + k • q ∧
        φ ((extChartAt 𝓘(ℝ) x).symm v) ∈ (extChartAt 𝓘(ℝ) y).source := by
    rw [Function.comp_apply, Function.comp_apply, AddCircle.extChartAt_symm_apply x hv, hφ]
    exact hball hΦ
  obtain ⟨t, ht, hFt⟩ := Metric.tendstoLocallyUniformly_iff.1 h₀ (ε / 2) (half_pos hε) w₀
  have hS : ∀ᶠ v in 𝓝 w₀, v ∈ t ∧ dist (G v) (G w₀) < ε / 2 ∧
      v ∈ (extChartAt 𝓘(ℝ) x).target :=
    (Filter.eventually_mem_set.2 ht).and ((hG.continuousAt.eventually
      (ball_mem_nhds _ (half_pos hε))).and ((isOpen_extChartAt_target x).mem_nhds hw₀))
  refine ⟨k, hS.mono fun v ⟨_, hvG, hvT⟩ ↦ (hread hgG hvT (hvG.trans (half_lt_self hε))).1,
    (hFt.prod_mk hS.eventually_nhds).mono fun ⟨i, v⟩ ⟨hi, hSv⟩ ↦ ?_⟩
  have hFv {v' : ℝ} (hv' : v' ∈ t ∧ dist (G v') (G w₀) < ε / 2 ∧
      v' ∈ (extChartAt 𝓘(ℝ) x).target) : dist (F i v') (G w₀) < ε :=
    calc dist (F i v') (G w₀) ≤ dist (G v') (F i v') + dist (G v') (G w₀) :=
          dist_triangle_left _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hi v' hv'.1) hv'.2.1
      _ = ε := add_halves ε
  exact ⟨(hread (hfF i) hSv.self_of_nhds.2.2 (hFv hSv.self_of_nhds)).2,
    hSv.mono fun v' hv' ↦ (hread (hfF i) hv'.2.2 (hFv hv')).1⟩

/-- The pointwise step of `tendsto_addCircle_addCircle_of_lift`: near a point `w₀` of the chart
target where `g` passes a chart derivative test, the maps `f i` eventually pass it too. -/
private theorem eventually_chartJetSet_of_lift (hG : Continuous G)
    (hfF : ∀ i (x : ℝ), f i x = F i x) (hgG : ∀ x : ℝ, g x = G x)
    (h₀ : TendstoLocallyUniformly F G l) {x : AddCircle p} {y : AddCircle q} {m : ℕ}
    (hm : m ≤ n) (hFm : TendstoLocallyUniformly (fun i ↦ iteratedFDeriv ℝ m (F i))
      (iteratedFDeriv ℝ m G) l) {V : Set (ℝ [×m]→L[ℝ] ℝ)} (hV : IsOpen V) {w₀ : ℝ}
    (hw₀ : w₀ ∈ (extChartAt 𝓘(ℝ) x).target)
    (hg₀ : g ((extChartAt 𝓘(ℝ) x).symm w₀) ∈ (extChartAt 𝓘(ℝ) y).source ∧
      iteratedFDerivWithin ℝ m (extChartAt 𝓘(ℝ) y ∘ g ∘ (extChartAt 𝓘(ℝ) x).symm)
        (extChartAt 𝓘(ℝ) x).target w₀ ∈ V) :
    ∀ᶠ z in l ×ˢ 𝓝 w₀, z.2 ∈ (extChartAt 𝓘(ℝ) x).target →
      f z.1 ((extChartAt 𝓘(ℝ) x).symm z.2) ∈ (extChartAt 𝓘(ℝ) y).source ∧
      iteratedFDerivWithin ℝ m (extChartAt 𝓘(ℝ) y ∘ f z.1 ∘ (extChartAt 𝓘(ℝ) x).symm)
        (extChartAt 𝓘(ℝ) x).target z.2 ∈ V := by
  have hGs : ContDiff ℝ n G := AddCircle.contDiff_of_comp_coe_eq (funext hgG) hG g.contMDiff
  obtain ⟨hgs, hgV⟩ := hg₀
  rw [AddCircle.extChartAt_symm_apply x hw₀] at hgs
  obtain ⟨k, hψg, hψ⟩ := exists_eventually_extChartAt_comp_eventuallyEq hG hfF hgG h₀ hw₀ hgs
  -- A margin around the chart derivative of `g` at `w₀` inside `V`.
  set A := fun v ↦ iteratedFDeriv ℝ m (fun v' ↦ G v' + k • q) v
  have hA₀ : A w₀ ∈ V := by
    rwa [iteratedFDerivWithin_of_isOpen _ (isOpen_extChartAt_target x) hw₀,
      (hψg.iteratedFDeriv ℝ m).eq_of_nhds] at hgV
  obtain ⟨δ, hδ, hδV⟩ := isOpen_iff.1 hV _ hA₀
  have hAc : ∀ᶠ v in 𝓝 w₀, dist (A v) (A w₀) < δ / 2 :=
    ((hGs.add contDiff_const).continuous_iteratedFDeriv hm).continuousAt.eventually
      (ball_mem_nhds _ (half_pos hδ))
  obtain ⟨t', ht', hFt'⟩ := Metric.tendstoLocallyUniformly_iff.1 hFm (δ / 2) (half_pos hδ) w₀
  filter_upwards [hψ, hFt'.prod_mk (hAc.and ht')] with ⟨i, v⟩ ⟨hfs, hψv⟩ ⟨hi, hAv, hvt'⟩ hvT
  refine ⟨hfs, ?_⟩
  rw [iteratedFDerivWithin_of_isOpen _ (isOpen_extChartAt_target x) hvT,
    (hψv.iteratedFDeriv ℝ m).eq_of_nhds]
  refine hδV (mem_ball.2 ?_)
  calc dist (iteratedFDeriv ℝ m (fun v' ↦ F i v' + k • q) v) (A w₀)
      ≤ dist (iteratedFDeriv ℝ m (fun v' ↦ F i v' + k • q) v) (A v) + dist (A v) (A w₀) :=
        dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := by
        rw [TauCeti.dist_iteratedFDeriv_add_const, dist_comm]
        exact add_lt_add (hi v hvt') hAv
    _ = δ := add_halves δ

/-- **Convergence of circle maps from their lifts.** A family `f i` of `C^n` maps
`AddCircle p → AddCircle q` converges to `g` in the weak Whitney topology when lifts `F i` of the
`f i` and a continuous lift `G` of `g` have iterated derivatives of each order `m ≤ n` converging
locally uniformly on `ℝ`. -/
theorem tendsto_addCircle_addCircle_of_lift (hG : Continuous G)
    (hfF : ∀ i (x : ℝ), f i x = F i x) (hgG : ∀ x : ℝ, g x = G x)
    (h : ∀ m : ℕ, m ≤ n → TendstoLocallyUniformly (fun i ↦ iteratedFDeriv ℝ m (F i))
      (iteratedFDeriv ℝ m G) l) :
    Tendsto f l (𝓝 g) := by
  -- The lifts themselves converge locally uniformly.
  have h₀ : TendstoLocallyUniformly F G l :=
    TauCeti.tendstoLocallyUniformly_iteratedFDeriv_zero_iff.1 (h 0 (by simp))
  refine tendsto_manifoldWeakWhitney_iff.2 fun x y m hm K hK V hV hgK ↦ ?_
  rw [mem_chartJetSet] at hgK
  simp only [mem_chartJetSet]
  -- Near each point of `K` the maps `f i` eventually pass the test; `K` is compact.
  have key := (hK.image continuous_subtypeVal).mem_prod_nhdsSet_of_forall
    (l := l) fun w₀ ⟨z, hz, hzw⟩ ↦ hzw ▸
      eventually_chartJetSet_of_lift hG hfF hgG h₀ hm (h m hm) hV z.property (hgK z hz)
  filter_upwards [Filter.Eventually.curry key] with i hi z hz
  exact hi.self_of_nhdsSet z ⟨z, hz, rfl⟩ z.property

/-- The chart derivative test behind `tendstoLocallyUniformly_iteratedFDeriv_lift`: on a closed
ball of a chart target where `g` lands in the chart at `y` and the `m`-th derivative of its lift
`G` stays within `c` of its value at the centre, the `m`-th derivatives of the lifts `F i` of the
`f i` eventually do so too. -/
private theorem eventually_forall_closedBall_dist_iteratedFDeriv_lt (hF : ∀ i, Continuous (F i))
    (hG : Continuous G) (hfF : ∀ i (x : ℝ), f i x = F i x) (hgG : ∀ x : ℝ, g x = G x)
    (hfg : Tendsto f l (𝓝 g)) {m : ℕ} (hm : m ≤ n) (hm₀ : m ≠ 0) {x : AddCircle p}
    {y : AddCircle q} {z₀ ρ c : ℝ}
    (hρ : closedBall z₀ ρ ⊆ {v | v ∈ (extChartAt 𝓘(ℝ) x).target ∧
      g v ∈ (extChartAt 𝓘(ℝ) y).source ∧
      dist (iteratedFDeriv ℝ m G v) (iteratedFDeriv ℝ m G z₀) < c}) :
    ∀ᶠ i in l, ∀ v ∈ closedBall z₀ ρ,
      dist (iteratedFDeriv ℝ m (F i) v) (iteratedFDeriv ℝ m G z₀) < c := by
  set K : Set (extChartAt 𝓘(ℝ) x).target := Subtype.val ⁻¹' closedBall z₀ ρ
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 fun v hv ↦ (hρ hv).1]
    exact isCompact_closedBall z₀ ρ
  have hgK : g ∈ chartJetSet x y m K (ball (iteratedFDeriv ℝ m G z₀) c) := by
    refine mem_chartJetSet.2 fun v hv ↦ ?_
    obtain ⟨hvT, hvs, hvd⟩ := hρ hv
    rw [AddCircle.extChartAt_symm_apply x hvT]
    exact ⟨hvs, by
      rwa [AddCircle.iteratedFDerivWithin_extChartAt_comp_of_lift hG hgG hvT hvs hm₀, mem_ball]⟩
  filter_upwards [tendsto_manifoldWeakWhitney_iff.1 hfg x y m hm K hK _ isOpen_ball hgK]
    with i hi v hv
  obtain ⟨hfs, hfd⟩ := (mem_chartJetSet.1 hi) ⟨v, (hρ hv).1⟩ hv
  rw [AddCircle.extChartAt_symm_apply x (hρ hv).1] at hfs
  rwa [AddCircle.iteratedFDerivWithin_extChartAt_comp_of_lift (hF i) (hfF i) (hρ hv).1 hfs hm₀,
    mem_ball] at hfd

/-- **Lifts of convergent circle maps.** If `C^n` maps `f i : AddCircle p → AddCircle q` converge
to `g` in the weak Whitney topology, then for each positive order `m ≤ n` the iterated derivatives
of continuous lifts of the `f i` converge locally uniformly on `ℝ` to those of a continuous lift
of `g`. -/
theorem tendstoLocallyUniformly_iteratedFDeriv_lift (hF : ∀ i, Continuous (F i))
    (hG : Continuous G) (hfF : ∀ i (x : ℝ), f i x = F i x) (hgG : ∀ x : ℝ, g x = G x)
    (hfg : Tendsto f l (𝓝 g)) {m : ℕ} (hm : m ≤ n) (hm₀ : m ≠ 0) :
    TendstoLocallyUniformly (fun i ↦ iteratedFDeriv ℝ m (F i)) (iteratedFDeriv ℝ m G) l := by
  have hGs : ContDiff ℝ n G := AddCircle.contDiff_of_comp_coe_eq (funext hgG) hG g.contMDiff
  refine Metric.tendstoLocallyUniformly_iff.2 fun ε hε w ↦ ?_
  -- The chart at `w` sends it to a representative `z₀ = w + j • p`.
  obtain ⟨j, hj⟩ := AddCircle.exists_extChartAt_coe_self_eq_add_zsmul (p := p) w
  set x : AddCircle p := ((w : ℝ) : AddCircle p)
  set z₀ := extChartAt 𝓘(ℝ) x x
  set y := g x
  -- A closed ball around `z₀` on which `g` passes a chart derivative test with margin `ε / 2`.
  obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ > 0, closedBall z₀ ρ ⊆ {v | v ∈ (extChartAt 𝓘(ℝ) x).target ∧
      g v ∈ (extChartAt 𝓘(ℝ) y).source ∧
      dist (iteratedFDeriv ℝ m G v) (iteratedFDeriv ℝ m G z₀) < ε / 2} := by
    refine nhds_basis_closedBall.mem_iff.1 ?_
    have hy : g z₀ ∈ (extChartAt 𝓘(ℝ) y).source := by
      rw [AddCircle.coe_extChartAt_self]
      exact mem_extChartAt_source y
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x),
      (g.contMDiff.continuous.comp continuous_quotient_mk').continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source y).mem_nhds hy),
      (hGs.continuous_iteratedFDeriv hm).continuousAt.eventually
        (ball_mem_nhds _ (half_pos hε))] with v hvT hvs hvd
    exact ⟨hvT, hvs, hvd⟩
  refine ⟨closedBall w ρ, closedBall_mem_nhds w hρ, ?_⟩
  filter_upwards [eventually_forall_closedBall_dist_iteratedFDeriv_lt hF hG hfF hgG hfg hm hm₀
    hρU] with i hi v hv
  -- Compare at the representative `v + j • p` in the tested ball, using periodicity.
  have hv' : v + j • p ∈ closedBall z₀ ρ := by
    rwa [hj, mem_closedBall, dist_add_right]
  have hvd := (hρU hv').2.2
  have hfd := hi _ hv'
  rw [AddCircle.iteratedFDeriv_lift_add_zsmul hG hgG hm₀] at hvd
  rw [AddCircle.iteratedFDeriv_lift_add_zsmul (hF i) (hfF i) hm₀] at hfd
  calc dist (iteratedFDeriv ℝ m G v) (iteratedFDeriv ℝ m (F i) v)
      ≤ dist (iteratedFDeriv ℝ m G v) (iteratedFDeriv ℝ m G z₀) +
          dist (iteratedFDeriv ℝ m (F i) v) (iteratedFDeriv ℝ m G z₀) :=
        dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hvd hfd
    _ = ε := add_halves ε

/-- **Normalized lifts of convergent circle maps.** If `C^n` maps `f i : AddCircle p → AddCircle q`,
`1 ≤ n`, converge to `g` in the weak Whitney topology, then continuous lifts of the `f i`,
normalized to vanish at `0`, converge locally uniformly on `ℝ` to the normalized continuous lift
of `g`. -/
theorem tendstoLocallyUniformly_lift_sub_lift_zero (hn : 1 ≤ n) (hF : ∀ i, Continuous (F i))
    (hG : Continuous G) (hfF : ∀ i (x : ℝ), f i x = F i x) (hgG : ∀ x : ℝ, g x = G x)
    (hfg : Tendsto f l (𝓝 g)) :
    TendstoLocallyUniformly (fun i x ↦ F i x - F i 0) (fun x ↦ G x - G 0) l := by
  have hGs : ContDiff ℝ 1 G :=
    (AddCircle.contDiff_of_comp_coe_eq (funext hgG) hG g.contMDiff).of_le hn
  have hFs (i : ι) : ContDiff ℝ 1 (F i) :=
    (AddCircle.contDiff_of_comp_coe_eq (funext (hfF i)) (hF i) (f i).contMDiff).of_le hn
  have h₁ := tendstoLocallyUniformly_iff_forall_isCompact.1
    (tendstoLocallyUniformly_iteratedFDeriv_lift hF hG hfF hgG hfg (m := 1) (by exact_mod_cast hn)
      one_ne_zero)
  refine Metric.tendstoLocallyUniformly_iff.2 fun ε hε w ↦ ?_
  set R := |w| + 1
  have hR : 0 < R := by positivity
  -- By the mean value theorem on `[-R, R]`, from the uniform convergence of the derivatives.
  refine ⟨closedBall 0 R, closedBall_mem_nhds_of_mem (by simp [R]), ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (h₁ _ (isCompact_closedBall 0 R)) (ε / (R + 1))
    (by positivity)] with i hi v hv
  have hd : ∀ u ∈ closedBall (0 : ℝ) R, DifferentiableAt ℝ (fun x ↦ G x - F i x) u :=
    fun u _ ↦ (hGs.differentiable one_ne_zero u).sub ((hFs i).differentiable one_ne_zero u)
  have hb : ∀ u ∈ closedBall (0 : ℝ) R, ‖fderiv ℝ (fun x ↦ G x - F i x) u‖ ≤ ε / (R + 1) :=
    fun u hu ↦ by
      rw [← norm_iteratedFDeriv_one, ← Pi.sub_def,
        iteratedFDeriv_sub_apply hGs.contDiffAt (hFs i).contDiffAt,
        ← dist_eq_norm]
      exact (hi u hu).le
  have hmv := (convex_closedBall (0 : ℝ) R).norm_image_sub_le_of_norm_fderiv_le hd hb
    (mem_closedBall_self hR.le) hv
  have hsub : G v - G 0 - (F i v - F i 0) = (G v - F i v) - (G 0 - F i 0) := by ring
  rw [Real.dist_eq, hsub]
  rw [mem_closedBall_zero_iff] at hv
  calc |(G v - F i v) - (G 0 - F i 0)| ≤ ε / (R + 1) * ‖v - 0‖ := hmv
    _ ≤ ε / (R + 1) * R := by gcongr; simpa using hv
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- **The weak Whitney topology on circle maps, through lifts.** For `1 ≤ n`, `C^n` maps
`f i : AddCircle p → AddCircle q` with continuous lifts `F i` converge to `g`, with continuous lift
`G`, exactly when their values at `0` converge and, for each order `m ≤ n`, the iterated
derivatives of the lifts normalized to vanish at `0` converge locally uniformly on `ℝ`. The
normalized lift `x ↦ F x - F 0` does not depend on the choice of the lift. -/
theorem tendsto_addCircle_addCircle_iff_lift (hn : 1 ≤ n) (hF : ∀ i, Continuous (F i))
    (hG : Continuous G) (hfF : ∀ i (x : ℝ), f i x = F i x) (hgG : ∀ x : ℝ, g x = G x) :
    Tendsto f l (𝓝 g) ↔ Tendsto (fun i ↦ f i 0) l (𝓝 (g 0)) ∧ ∀ m : ℕ, m ≤ n →
      TendstoLocallyUniformly (fun i ↦ iteratedFDeriv ℝ m (fun x ↦ F i x - F i 0))
        (iteratedFDeriv ℝ m (fun x ↦ G x - G 0)) l := by
  have hsub (Φ : ℝ → ℝ) (m : ℕ) : iteratedFDeriv ℝ (m + 1) (fun x ↦ Φ x - Φ 0) =
      iteratedFDeriv ℝ (m + 1) Φ := by
    simp_rw [sub_eq_add_neg]
    exact TauCeti.iteratedFDeriv_succ_add_const Φ _ m
  constructor
  · refine fun hfg ↦ ⟨((continuous_eval_const_manifoldWeakWhitney (0 : AddCircle p)).tendsto g).comp
      hfg, fun m hm ↦ ?_⟩
    rcases m with _ | m
    · exact TauCeti.tendstoLocallyUniformly_iteratedFDeriv_zero_iff.2
        (tendstoLocallyUniformly_lift_sub_lift_zero hn hF hG hfF hgG hfg)
    · simp only [hsub]
      exact tendstoLocallyUniformly_iteratedFDeriv_lift hF hG hfF hgG hfg hm (Nat.succ_ne_zero m)
  · rintro ⟨h₀, h⟩
    -- Shift the lifts so that their values at `0` converge to `G 0`, through the representatives
    -- of the differences `f i 0 - g 0` in `[-q / 2, q / 2)`.
    have hq : (0 : ℝ) < q := Fact.out
    obtain ⟨r, hr, hr₀, hrc⟩ : ∃ r : AddCircle q → ℝ, ContinuousAt r 0 ∧ r 0 = 0 ∧
        ∀ a, (r a : AddCircle q) = a := by
      have h0 : (0 : ℝ) ∈ Ioo (-(q / 2)) (-(q / 2) + q) := ⟨by linarith, by linarith⟩
      set e := AddCircle.openPartialHomeomorphCoe q (-(q / 2))
      refine ⟨e.symm, ?_, e.left_inv h0, fun a ↦ by
        rw [AddCircle.openPartialHomeomorphCoe_symm_apply, AddCircle.coe_equivIco]⟩
      simpa [e] using e.continuousAt_symm (e.map_source h0)
    have hdiff : Tendsto (fun i ↦ r (f i 0 - g 0)) l (𝓝 0) := by
      have h' := h₀.sub_const (g 0)
      rw [sub_self] at h'
      exact (by simpa only [hr₀] using hr.tendsto : Tendsto r (𝓝 0) (𝓝 0)).comp h'
    refine tendsto_addCircle_addCircle_of_lift
      (F := fun i x ↦ F i x - F i 0 + (G 0 + r (f i 0 - g 0))) hG (fun i x ↦ ?_) hgG fun m hm ↦ ?_
    · simp only [AddCircle.coe_add, AddCircle.coe_sub, ← hfF, ← hgG, hrc, QuotientAddGroup.mk_zero]
      abel
    · rcases m with _ | m
      · refine TauCeti.tendstoLocallyUniformly_iteratedFDeriv_zero_iff.2 ?_
        have h0 := TauCeti.tendstoLocallyUniformly_iteratedFDeriv_zero_iff.1 (h 0 (by simp))
        have hc : TendstoLocallyUniformly (fun i (_ : ℝ) ↦ G 0 + r (f i 0 - g 0))
            (fun _ ↦ G 0 + 0) l :=
          (tendsto_const_nhds.add hdiff).tendstoUniformly_const.tendstoLocallyUniformly
        convert h0.add hc using 1
        funext x
        simp only [Pi.add_apply, add_zero, sub_add_cancel]
      · simp only [TauCeti.iteratedFDeriv_succ_add_const, ← hsub G m]
        simpa only [hsub] using h (m + 1) hm

end CircleMaps

end ContMDiffMap
