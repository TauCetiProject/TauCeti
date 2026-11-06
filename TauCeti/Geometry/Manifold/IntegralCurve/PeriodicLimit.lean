/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.IntegralCurve.Flow
import TauCeti.Topology.Homotopy.AddCircle

/-!
# Limits of periodic orbits

Let `v` be a `C¹` vector field on a finite-dimensional boundaryless manifold `M`, and let `γₙ`
be global integral curves of `v` which are `Tₙ`-periodic, with `Tₙ > 0`. Suppose that the initial
points `γₙ(0)` converge to a point `x` and the periods `Tₙ` converge to `T`, and that the maximal
integral curve `φ_x` of `v` through `x` is defined for all time. This file describes what the
orbits converge to.

* The limit returns: `φ_x(T) = x`, so `φ_x` is `T`-periodic
  (`TauCeti.maximalIntegralCurve_eq_of_tendsto`,
  `TauCeti.periodic_maximalIntegralCurve_of_tendsto`). This is the continuity of the maximal flow
  at `(x, T)`.
* If the periods shrink to `T = 0`, then `x` is a zero of `v`
  (`TauCeti.eq_zero_of_tendsto_of_tendsto_zero`): every `t > 0` is a limit of multiples
  `kₙ Tₙ`, at which `γₙ` returns to its initial point, so `φ_x(t) = x` for all `t > 0`.
* If `T > 0` and the loops `ℝ/Tₙℤ → M` traced by the `γₙ` are null-homotopic, then so is the
  loop `ℝ/Tℤ → M` traced by `φ_x` (`TauCeti.exists_nullhomotopic_of_tendsto`). For `n` large,
  the orbit segments `t ↦ φ(y, S t)`, `t ∈ [0, 1]`, for `(y, S)` on the segment, in a chart at
  `x`, from `(γₙ(0), Tₙ)` to `(x, T)`, start and end in a convex chart neighbourhood of `x`, so
  closing each of them by a straight arc in the chart gives a free homotopy between the two
  loops (`ContinuousMap.homotopic_of_forall_ofUnitInterval_of_convex`).

Together these are the compactness step that produces periodic orbits as limits of periodic orbits
of bounded period, as in the proof of the almost existence theorem of Hofer, Zehnder and Struwe.
A rest point is the only degenerate limit, so the limit of nonconstant orbits through points where
`v` does not vanish is a nonconstant periodic orbit.

## Main results

* `TauCeti.maximalIntegralCurve_eq_of_tendsto`, `TauCeti.periodic_maximalIntegralCurve_of_tendsto`:
  a limit of periodic orbits returns after the limit period.
* `TauCeti.eq_zero_of_tendsto_of_tendsto_zero`: periodic orbits with periods tending to `0`
  accumulate only at zeros of the field.
* `TauCeti.exists_nullhomotopic_of_tendsto`: a limit of null-homotopic periodic orbits with a
  positive limit period traces a null-homotopic loop.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. 20 (1990), 49–58.
-/

public section

noncomputable section

open Filter Function Manifold Set
open scoped ContDiff Manifold Topology

local notation "𝕀" => unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {x : M} [T2Space M] [IsManifold I 1 M]
  [BoundarylessManifold I M]

namespace TauCeti

variable [FiniteDimensional ℝ E] {γ : ℕ → ℝ → M} {T : ℕ → ℝ} {T₀ : ℝ}

/-- **A limit of periodic orbits returns after the limit period.** If `Tₙ`-periodic global
integral curves `γₙ` have initial points converging to `x` and periods converging to `T₀`, and the
maximal integral curve through `x` is defined at `T₀`, then it is back at `x` at time `T₀`. -/
theorem maximalIntegralCurve_eq_of_tendsto
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ n, IsMIntegralCurve (γ n) v) (hper : ∀ n, Periodic (γ n) (T n))
    (hx : Tendsto (fun n ↦ γ n 0) atTop (𝓝 x)) (hT : Tendsto T atTop (𝓝 T₀))
    (hT₀ : T₀ ∈ maximalIntegralCurveInterval v x) : maximalIntegralCurve v x T₀ = x := by
  refine tendsto_nhds_unique ((continuousAt_maximalIntegralCurve hv (p := (x, T₀)) hT₀).tendsto.comp
    (hx.prodMk_nhds hT)) (hx.congr fun n ↦ ?_)
  simp only [comp_apply, (hγ n).maximalIntegralCurve_eq hv, (hper n).eq]

/-- **A limit of periodic orbits is periodic.** If `Tₙ`-periodic global integral curves `γₙ` have
initial points converging to `x` and periods converging to `T₀`, and the maximal integral curve
through `x` is defined for all time, then it is `T₀`-periodic. -/
theorem periodic_maximalIntegralCurve_of_tendsto
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ n, IsMIntegralCurve (γ n) v) (hper : ∀ n, Periodic (γ n) (T n))
    (hx : Tendsto (fun n ↦ γ n 0) atTop (𝓝 x)) (hT : Tendsto T atTop (𝓝 T₀))
    (hglob : maximalIntegralCurveInterval v x = univ) :
    Periodic (maximalIntegralCurve v x) T₀ := fun t ↦ by
  rw [add_comm, maximalIntegralCurve_add hv (hglob ▸ mem_univ _) (hglob ▸ mem_univ _),
    maximalIntegralCurve_eq_of_tendsto hv hγ hper hx hT (hglob ▸ mem_univ _)]

/-- **Periodic orbits with periods tending to zero accumulate at zeros of the field.** If
`Tₙ`-periodic global integral curves `γₙ`, with `Tₙ > 0` and `Tₙ → 0`, have initial points
converging to `x`, and the maximal integral curve through `x` is defined for all positive time,
then `v x = 0`. -/
theorem eq_zero_of_tendsto_of_tendsto_zero
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ n, IsMIntegralCurve (γ n) v) (hper : ∀ n, Periodic (γ n) (T n))
    (hTpos : ∀ n, 0 < T n) (hx : Tendsto (fun n ↦ γ n 0) atTop (𝓝 x))
    (hT : Tendsto T atTop (𝓝 0)) (hglob : Ioi 0 ⊆ maximalIntegralCurveInterval v x) :
    v x = 0 := by
  -- Every positive time `t` is the limit of the multiples `⌊t / Tₙ⌋ Tₙ` of the periods, at which
  -- `γₙ` is back at `γₙ(0)`, so the maximal curve through `x` is at `x` at time `t`.
  have hfix (t : ℝ) (ht : 0 < t) : maximalIntegralCurve v x t = x := by
    have hle (n : ℕ) : (⌊t / T n⌋₊ : ℝ) * T n ≤ t :=
      (le_div_iff₀ (hTpos n)).1 (Nat.floor_le (div_nonneg ht.le (hTpos n).le))
    have hge (n : ℕ) : t - T n ≤ (⌊t / T n⌋₊ : ℝ) * T n := by
      have := (div_lt_iff₀ (hTpos n)).1 (Nat.lt_floor_add_one (t / T n))
      linarith
    have hk : Tendsto (fun n ↦ (⌊t / T n⌋₊ : ℝ) * T n) atTop (𝓝 t) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using tendsto_const_nhds.sub hT)
        tendsto_const_nhds hge hle
    refine tendsto_nhds_unique ((continuousAt_maximalIntegralCurve hv (p := (x, t))
      (hglob ht)).tendsto.comp (hx.prodMk_nhds hk)) (hx.congr fun n ↦ ?_)
    simp only [comp_apply, (hγ n).maximalIntegralCurve_eq hv, (hper n).nat_mul_eq]
  have : Nonempty M := ⟨x⟩
  have hc : EventuallyConst (maximalIntegralCurve v x) (𝓝 1) :=
    eventuallyConst_iff_exists_eventuallyEq.2
      ⟨x, eventually_of_mem (Ioi_mem_nhds one_pos) fun t ht ↦ hfix t ht⟩
  exact hfix 1 one_pos ▸ ((isMIntegralCurveOn_maximalIntegralCurve hv).isMIntegralCurveAt
    (isOpen_maximalIntegralCurveInterval.mem_nhds (hglob one_pos))).eq_zero_of_eventuallyConst hc

/-- Near a periodic orbit through `x` of period `T₀ > 0`, defined for all time, the orbit segments
`t ↦ φ(e⁻¹ q₁, q₂ t)`, `t ∈ [0, 1]`, for `q` in a ball around `(e x, T₀)` in the chart `e` at `x`,
depend continuously on `(q, t)` and start and end in the preimage of a convex ball of the chart. -/
private theorem exists_ball_continuousAt
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hT₀ : 0 < T₀)
    (hglob : maximalIntegralCurveInterval v x = univ) (hret : maximalIntegralCurve v x T₀ = x) :
    ∃ r > 0, Metric.ball (extChartAt I x x) r ⊆ (extChartAt I x).target ∧ ∃ ρ > 0,
      ∀ q ∈ Metric.ball ((extChartAt I x x, T₀) : E × ℝ) ρ,
        q.1 ∈ Metric.ball (extChartAt I x x) r ∧
        maximalIntegralCurve v ((extChartAt I x).symm q.1) q.2 ∈
          (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) r ∧
        ∀ t : 𝕀, ContinuousAt (fun z : (E × ℝ) × 𝕀 ↦
          maximalIntegralCurve v ((extChartAt I x).symm z.1.1) (z.1.2 * z.2)) (q, t) := by
  set e := extChartAt I x with he
  have htgt : e.target ∈ 𝓝 (e x) :=
    mem_interior_iff_mem_nhds.1 (I.isInteriorPoint_iff.1 BoundarylessManifold.isInteriorPoint)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 htgt
  have hU : e.source ∩ e ⁻¹' Metric.ball (e x) r ∈ 𝓝 x :=
    inter_mem (extChartAt_source_mem_nhds x)
      ((continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  -- A tube `V × W` around the orbit segment `{x} × [0, T₀ + 1]` in the domain of the flow.
  obtain ⟨V, W, hVo, -, hxV, hW, hVW⟩ := generalized_tube_lemma (isCompact_singleton (x := x))
    (isCompact_Icc (a := (0 : ℝ)) (b := T₀ + 1)) (isOpen_maximalIntegralCurveFlowDomain hv)
    (fun p hp ↦ by simp [(mem_singleton_iff.1 hp.1), hglob])
  have hsymm : ContinuousAt e.symm (e x) := continuousAt_extChartAt_symm x
  have hex : e.symm (e x) = x := extChartAt_to_inv x
  have hend : ContinuousAt (fun q : E × ℝ ↦ maximalIntegralCurve v (e.symm q.1) q.2)
      (e x, T₀) :=
    (continuousAt_maximalIntegralCurve hv (p := (x, T₀)) (hglob ▸ mem_univ _)).comp_of_eq
      ((hsymm.comp (f := Prod.fst) continuousAt_fst).prodMk continuousAt_snd)
      (by simp [hex])
  have hval : maximalIntegralCurve v (e.symm (e x)) T₀ = x := by rw [hex, hret]
  have hN : {q : E × ℝ | q.1 ∈ Metric.ball (e x) r ∧ e.symm q.1 ∈ V ∧ q.2 ∈ Ioo 0 (T₀ + 1) ∧
      maximalIntegralCurve v (e.symm q.1) q.2 ∈ e.source ∩ e ⁻¹' Metric.ball (e x) r} ∈
        𝓝 (e x, T₀) := by
    refine inter_mem (continuousAt_fst.preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
      (inter_mem ((hsymm.comp (f := Prod.fst) continuousAt_fst).preimage_mem_nhds
        (hVo.mem_nhds (by simpa [hex] using hxV rfl)))
        (inter_mem (continuousAt_snd.preimage_mem_nhds
          (Ioo_mem_nhds (a := 0) (b := T₀ + 1) hT₀ (by linarith)))
          (hend.preimage_mem_nhds (by rw [hval]; exact hU))))
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨r, hr, hrt, ρ, hρ, fun q hq ↦ ?_⟩
  obtain ⟨hq₁, hqV, hq₂, hqU⟩ := hρN hq
  refine ⟨hq₁, hqU, fun t ↦ ?_⟩
  -- The orbit segment through `e⁻¹ q₁` stays in the tube up to time `q₂ < T₀ + 1`.
  have hdom : (e.symm q.1, q.2 * t) ∈ V ×ˢ W :=
    ⟨hqV, hW ⟨mul_nonneg hq₂.1.le t.2.1, (mul_le_of_le_one_right hq₂.1.le t.2.2).trans hq₂.2.le⟩⟩
  have hsymm' : ContinuousAt e.symm q.1 := (continuousOn_extChartAt_symm x).continuousAt
    (mem_of_superset (Metric.isOpen_ball.mem_nhds hq₁) hrt)
  have hfst : ContinuousAt (fun z : (E × ℝ) × 𝕀 ↦ e.symm z.1.1) (q, t) :=
    hsymm'.comp_of_eq (continuous_fst.comp continuous_fst).continuousAt rfl
  exact (continuousAt_maximalIntegralCurve hv (p := (e.symm q.1, q.2 * t))
    (mem_maximalIntegralCurveFlowDomain.1 (hVW hdom))).comp (f := fun z : (E × ℝ) × 𝕀 ↦
      (e.symm z.1.1, z.1.2 * z.2))
      (hfst.prodMk (by fun_prop : Continuous fun z : (E × ℝ) × 𝕀 ↦ z.1.2 * (z.2 : ℝ)).continuousAt)

/-- **A limit of null-homotopic periodic orbits is null-homotopic.** If `Tₙ`-periodic global
integral curves `γₙ`, `Tₙ > 0`, trace null-homotopic loops `ℝ/Tₙℤ → M`, their initial points
converge to `x` and their periods converge to `T₀ > 0`, and the maximal integral curve through `x`
is defined for all time, then it traces a null-homotopic loop `ℝ/T₀ℤ → M`. -/
theorem exists_nullhomotopic_of_tendsto
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ n, IsMIntegralCurve (γ n) v) (hper : ∀ n, Periodic (γ n) (T n))
    (hTpos : ∀ n, 0 < T n)
    (hnull : ∀ n, ∃ g : C(AddCircle (T n), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ n t)
    (hx : Tendsto (fun n ↦ γ n 0) atTop (𝓝 x)) (hT : Tendsto T atTop (𝓝 T₀)) (hT₀ : 0 < T₀)
    (hglob : maximalIntegralCurveInterval v x = univ) :
    ∃ g : C(AddCircle T₀, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = maximalIntegralCurve v x t := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  set e := extChartAt I x with he
  have hφ0 (y : M) : maximalIntegralCurve v y 0 = y :=
    maximalIntegralCurve_zero (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt)
  have hex : e.symm (e x) = x := extChartAt_to_inv x
  have hret := maximalIntegralCurve_eq_of_tendsto hv hγ hper hx hT (hglob ▸ mem_univ _)
  have hperx := periodic_maximalIntegralCurve_of_tendsto hv hγ hper hx hT hglob
  have hcx : Continuous (maximalIntegralCurve v x) :=
    (isMIntegralCurve_maximalIntegralCurve_of_eq_univ hv hglob).continuous
  -- The limit loop, as a map from the circle `ℝ/T₀ℤ`.
  let g : C(AddCircle T₀, M) :=
    ⟨hperx.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hcx⟩
  have hg (t : ℝ) : g t = maximalIntegralCurve v x t := hperx.lift_coe t
  refine ⟨g, ?_, hg⟩
  obtain ⟨r, hr, hrt, ρ, hρ, hball⟩ := exists_ball_continuousAt hv hT₀ hglob hret
  -- Pick an orbit `γₙ` whose initial point and period are close to those of the limit.
  have hlim : Tendsto (fun n ↦ ((e (γ n 0), T n) : E × ℝ)) atTop (𝓝 (e x, T₀)) :=
    ((continuousAt_extChartAt (I := I) x).tendsto.comp hx).prodMk_nhds hT
  obtain ⟨n, hn, hns⟩ := ((hlim.eventually (Metric.ball_mem_nhds ((e x, T₀) : E × ℝ) hρ)).and
    (hx.eventually (extChartAt_source_mem_nhds (I := I) x))).exists
  obtain ⟨gₙ, hgₙ, hgγ⟩ := hnull n
  -- The segment of parameters from `(e (γₙ 0), Tₙ)` to `(e x, T₀)`.
  let q : 𝕀 → E × ℝ := fun u ↦ (1 - (u : ℝ)) • ((e (γ n 0), T n) : E × ℝ) + (u : ℝ) • (e x, T₀)
  have hq (u : 𝕀) : q u ∈ Metric.ball ((e x, T₀) : E × ℝ) ρ :=
    convex_ball _ _ hn (Metric.mem_ball_self hρ) (sub_nonneg.2 u.2.2) u.2.1 (by ring)
  have hqc : Continuous q := by fun_prop
  -- The family of orbit segments, whose ends lie in a convex ball of the chart.
  let L : C(𝕀 × 𝕀, M) := ⟨fun z ↦ maximalIntegralCurve v (e.symm (q z.1).1) ((q z.1).2 * z.2),
    continuous_iff_continuousAt.2 fun z ↦ ((hball _ (hq z.1)).2.2 z.2).comp
      (f := fun z : 𝕀 × 𝕀 ↦ (q z.1, z.2)) (by fun_prop)⟩
  have hL0 (u : 𝕀) : L (u, 0) = e.symm (q u).1 := by
    simp [L, hφ0]
  have hL1 (u : 𝕀) : L (u, 1) = maximalIntegralCurve v (e.symm (q u).1) (q u).2 := by
    simp [L]
  have hsrc0 (u : 𝕀) : L (u, 0) ∈ e.source ∧ e (L (u, 0)) ∈ Metric.ball (e x) r := by
    rw [hL0]
    refine ⟨e.map_target (hrt (hball _ (hq u)).1), ?_⟩
    rw [e.right_inv (hrt (hball _ (hq u)).1)]
    exact (hball _ (hq u)).1
  have hsrc1 (u : 𝕀) : L (u, 1) ∈ e.source ∧ e (L (u, 1)) ∈ Metric.ball (e x) r := by
    rw [hL1]
    exact (hball _ (hq u)).2.1
  -- The values of the two families at the ends of the parameter segment.
  have hq0 : q 0 = (e (γ n 0), T n) := by simp [q]
  have hq1 : q 1 = (e x, T₀) := by simp [q]
  have hLn (t : 𝕀) : L (0, t) = γ n (T n * t) := by
    simp only [L, ContinuousMap.coe_mk, hq0, e.left_inv hns, (hγ n).maximalIntegralCurve_eq hv]
  have hLx (t : 𝕀) : L (1, t) = maximalIntegralCurve v x (T₀ * t) := by
    simp only [L, ContinuousMap.coe_mk, hq1, hex]
  have hn0 : L (0, 1) = L (0, 0) := by
    rw [hLn, hLn]
    simp [(hper n).eq]
  have hx0 : L (1, 1) = L (1, 0) := by
    rw [hLx, hLx]
    simp [hret, hφ0]
  -- The two loops, read on the circle `ℝ/ℤ`.
  let hn' := AddCircle.homeomorphAddCircle (1 : ℝ) (T n) one_ne_zero (hTpos n).ne'
  let hx' := AddCircle.homeomorphAddCircle (1 : ℝ) T₀ one_ne_zero hT₀.ne'
  have hhom : (gₙ.comp ⟨hn', hn'.continuous⟩).Homotopic (g.comp ⟨hx', hx'.continuous⟩) :=
    ContinuousMap.homotopic_of_forall_ofUnitInterval_of_convex e (continuousOn_extChartAt x)
      (continuousOn_extChartAt_symm x) (convex_ball _ _) hrt L hsrc0 hsrc1 hn0 hx0
      (fun t ↦ by simp [hn', AddCircle.homeomorphAddCircle_apply_mk, hgγ, hLn, mul_comm])
      (fun t ↦ by simp [hx', AddCircle.homeomorphAddCircle_apply_mk, hg, hLx, mul_comm])
  obtain ⟨c, hc⟩ := hgₙ.comp_left ⟨hn', hn'.continuous⟩
  have hgx : (g.comp ⟨hx', hx'.continuous⟩).comp ⟨hx'.symm, hx'.symm.continuous⟩ = g := by
    ext θ
    simp
  exact hgx ▸ ContinuousMap.Nullhomotopic.comp_left ⟨c, hhom.symm.trans hc⟩ _

end TauCeti
