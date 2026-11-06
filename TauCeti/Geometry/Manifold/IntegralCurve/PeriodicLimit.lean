/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Geometry.Manifold.IntegralCurve.Flow
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Topology.Homotopy.AddCircle

/-!
# Limits of periodic integral curves

Let `v` be a `C¹` vector field on a finite-dimensional boundaryless manifold `M`, and let `γ i` be
a family of global integral curves of `v`, indexed along a filter `l`, which eventually stay in a
fixed compact set and whose initial points converge to `x`. Each `γ i` is the maximal integral
curve through its initial point, and the maximal flow is continuous on its open domain. So the
curves `γ i` converge pointwise to the maximal integral curve through `x`, which never leaves the
compact set and is therefore itself a global integral curve
(`TauCeti.tendsto_maximalIntegralCurve_of_tendsto`,
`TauCeti.isMIntegralCurve_maximalIntegralCurve_of_tendsto`).

If moreover `γ i` is `T i`-periodic and `T i → T₀`, the limit curve is `T₀`-periodic
(`TauCeti.periodic_maximalIntegralCurve_of_tendsto`). When the periods tend to `0`, the limit curve
is constant (`TauCeti.maximalIntegralCurve_eq_of_tendsto_zero`), so it sits at a zero of `v`
(`IsMIntegralCurve.eq_zero_of_forall_eq`). Hence if `v x ≠ 0`, the periods cannot shrink to `0`:
a limit of periodic orbits of bounded period near a nonzero of the field is a nonconstant periodic
orbit, with period the limit of the periods.

**Contractibility passes to the limit.** If the loops `ℝ / (T i)ℤ → M` traced by the `γ i` are
frequently null-homotopic and `T₀ > 0`, then so is the loop `ℝ / T₀ℤ → M` traced by the limit
(`TauCeti.exists_nullhomotopic_of_tendsto`). Fix a chart `e` at `x`. For an initial point `y` and
a time `τ` near `(x, T₀)`, let `b = φ(y, -τ)` be the point flowing to `y` in time `τ`, and let
`w(θ)` run along the straight segment from `y` to `b` in the chart. The loop
`θ ↦ φ(w(θ), θτ)`, `θ ∈ [0, 1]`, starts and ends at `y`, depends continuously on `(y, τ)`, and is
the orbit loop itself when `y` is `τ`-periodic, since then `b = y`. Moving `(y, τ)` along a
straight path from `(γ i 0, T i)` to `(x, T₀)` gives a free homotopy between the two orbit loops,
which descends to the circle by `ContinuousMap.homotopic_of_comp_ofUnitInterval`.

These are the compactness statements by which closed orbits of bounded period on nearby levels of
a function produce a closed orbit on the limiting level, the last step of the Hofer–Zehnder–Struwe
almost existence argument.

## Main results

* `TauCeti.isMIntegralCurve_maximalIntegralCurve_of_tendsto`,
  `TauCeti.tendsto_maximalIntegralCurve_of_tendsto`: confined global integral curves with
  converging initial points converge pointwise to a global integral curve.
* `TauCeti.periodic_maximalIntegralCurve_of_tendsto`: the limit of periodic curves is periodic
  with the limit period.
* `TauCeti.maximalIntegralCurve_eq_of_tendsto_zero`: when the periods tend to `0` the limit is
  constant.
* `TauCeti.exists_nullhomotopic_of_tendsto`: a limit of contractible periodic orbits is
  contractible.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2 (the limit of periodic solutions in the proof of the almost existence theorem).
-/

public section

noncomputable section

open Filter Function Metric Set Topology
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x}
  {ι : Type*} {l : Filter ι} {γ : ι → ℝ → M} {T : ι → ℝ} {T₀ : ℝ} {x : M} {K : Set M}

/-- Global integral curves confined to a compact set, with converging initial points, converge
pointwise to the maximal integral curve through the limit point, which is a global integral
curve. -/
private theorem isMIntegralCurve_maximalIntegralCurve_and_tendsto [l.NeBot]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ i, IsMIntegralCurve (γ i) v) (hK : IsCompact K) (hmem : ∀ᶠ i in l, ∀ t, γ i t ∈ K)
    (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x)) :
    IsMIntegralCurve (maximalIntegralCurve v x) v ∧
      ∀ t, Tendsto (fun i ↦ γ i t) l (𝓝 (maximalIntegralCurve v x t)) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hglob (i : ι) : maximalIntegralCurve v (γ i 0) = γ i := (hγ i).maximalIntegralCurve_eq hv
  -- Where the maximal curve through `x` is defined, it is the limit by continuity of the flow.
  have hconv : ∀ t ∈ maximalIntegralCurveInterval v x,
      Tendsto (fun i ↦ γ i t) l (𝓝 (maximalIntegralCurve v x t)) := fun t ht ↦ by
    have h := (continuousAt_maximalIntegralCurve hv (p := (x, t)) ht).tendsto.comp
      (hx.prodMk_nhds tendsto_const_nhds)
    simpa only [comp_def, hglob] using h
  -- So it stays in `K`, and is defined for all time.
  have huniv : maximalIntegralCurveInterval v x = univ :=
    maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
      (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt) hK fun t ht ↦
        hK.isClosed.mem_of_tendsto (hconv t ht) (hmem.mono fun i hi ↦ hi t)
  refine ⟨?_, fun t ↦ hconv t (huniv ▸ mem_univ t)⟩
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, ← huniv]
  exact isMIntegralCurveOn_maximalIntegralCurve hv

/-- **Limits of confined integral curves are integral curves.** Let `γ i` be global integral
curves of a `C¹` vector field which eventually stay in a compact set `K`, and whose initial points
converge to `x`. Then the maximal integral curve through `x` is a global integral curve. -/
theorem isMIntegralCurve_maximalIntegralCurve_of_tendsto [l.NeBot]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ i, IsMIntegralCurve (γ i) v) (hK : IsCompact K) (hmem : ∀ᶠ i in l, ∀ t, γ i t ∈ K)
    (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x)) : IsMIntegralCurve (maximalIntegralCurve v x) v :=
  (isMIntegralCurve_maximalIntegralCurve_and_tendsto hv hγ hK hmem hx).1

/-- **Pointwise convergence of confined integral curves.** Under the hypotheses of
`isMIntegralCurve_maximalIntegralCurve_of_tendsto`, the curves `γ i` converge pointwise to the
maximal integral curve through `x`. -/
theorem tendsto_maximalIntegralCurve_of_tendsto [l.NeBot]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ i, IsMIntegralCurve (γ i) v) (hK : IsCompact K) (hmem : ∀ᶠ i in l, ∀ t, γ i t ∈ K)
    (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x)) (t : ℝ) :
    Tendsto (fun i ↦ γ i t) l (𝓝 (maximalIntegralCurve v x t)) :=
  (isMIntegralCurve_maximalIntegralCurve_and_tendsto hv hγ hK hmem hx).2 t

/-- Under the hypotheses of `isMIntegralCurve_maximalIntegralCurve_of_tendsto`, the maximal
integral curve through `x` is defined for all time. -/
private theorem mem_maximalIntegralCurveInterval_of_tendsto [l.NeBot]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ i, IsMIntegralCurve (γ i) v) (hK : IsCompact K) (hmem : ∀ᶠ i in l, ∀ t, γ i t ∈ K)
    (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x)) (t : ℝ) : t ∈ maximalIntegralCurveInterval v x := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [(maximalIntegralCurveInterval_eq_univ_iff hv).2 ⟨_, maximalIntegralCurve_zero
    (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt),
    isMIntegralCurve_maximalIntegralCurve_of_tendsto hv hγ hK hmem hx⟩]
  exact mem_univ t

/-- **Limits of periodic integral curves are periodic.** Under the hypotheses of
`isMIntegralCurve_maximalIntegralCurve_of_tendsto`, if each `γ i` is `T i`-periodic and
`T i → T₀`, the limit curve is `T₀`-periodic. -/
theorem periodic_maximalIntegralCurve_of_tendsto [l.NeBot]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ i, IsMIntegralCurve (γ i) v) (hper : ∀ i, Periodic (γ i) (T i)) (hK : IsCompact K)
    (hmem : ∀ᶠ i in l, ∀ t, γ i t ∈ K) (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x))
    (hT : Tendsto T l (𝓝 T₀)) : Periodic (maximalIntegralCurve v x) T₀ := by
  have hglob (i : ι) : maximalIntegralCurve v (γ i 0) = γ i := (hγ i).maximalIntegralCurve_eq hv
  intro t
  -- `γ i (t + T i) = γ i t` converges both to the value at `t + T₀` and to the value at `t`.
  have h := (continuousAt_maximalIntegralCurve hv (p := (x, t + T₀))
    (mem_maximalIntegralCurveInterval_of_tendsto hv hγ hK hmem hx _)).tendsto.comp
      (hx.prodMk_nhds (tendsto_const_nhds.add hT))
  simp only [comp_def, hglob, fun i ↦ hper i t] at h
  exact tendsto_nhds_unique h (tendsto_maximalIntegralCurve_of_tendsto hv hγ hK hmem hx t)

/-- **Limits of periodic integral curves with shrinking periods are constant.** Under the
hypotheses of `isMIntegralCurve_maximalIntegralCurve_of_tendsto`, if each `γ i` is periodic with a
positive period `T i` and `T i → 0`, the limit curve stays at `x`. Combined with
`IsMIntegralCurve.eq_zero_of_forall_eq`, this bounds the periods away from `0` near a point where
the field does not vanish. -/
theorem maximalIntegralCurve_eq_of_tendsto_zero [l.NeBot]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ i, IsMIntegralCurve (γ i) v) (hper : ∀ i, Periodic (γ i) (T i))
    (hT_pos : ∀ i, 0 < T i) (hK : IsCompact K) (hmem : ∀ᶠ i in l, ∀ t, γ i t ∈ K)
    (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x)) (hT : Tendsto T l (𝓝 0)) (t : ℝ) :
    maximalIntegralCurve v x t = x := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hglob (i : ι) : maximalIntegralCurve v (γ i 0) = γ i := (hγ i).maximalIntegralCurve_eq hv
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x :=
    zero_mem_maximalIntegralCurveInterval hv.contMDiffAt
  -- Reduce `t` modulo the period: `γ i t = γ i (r i)` with `0 ≤ r i < T i`, so `r i → 0`.
  set r : ι → ℝ := fun i ↦ toIcoMod (hT_pos i) 0 t with hr_def
  have hr : Tendsto r l (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
    (fun i ↦ (toIcoMod_mem_Ico (hT_pos i) 0 t).1)
    (fun i ↦ by simpa using (toIcoMod_mem_Ico (hT_pos i) 0 t).2.le)
  have hγr (i : ι) : γ i (r i) = γ i t := by
    conv_rhs => rw [← toIcoMod_add_toIcoDiv_zsmul (hT_pos i) 0 t]
    exact ((hper i).zsmul _ _).symm
  have h := (continuousAt_maximalIntegralCurve hv (p := (x, 0)) h0).tendsto.comp
    (hx.prodMk_nhds hr)
  simp only [comp_def, hglob, hγr, maximalIntegralCurve_zero h0] at h
  exact tendsto_nhds_unique (tendsto_maximalIntegralCurve_of_tendsto hv hγ hK hmem hx t) h

/-- **A limit of contractible periodic orbits is contractible.** Under the hypotheses of
`periodic_maximalIntegralCurve_of_tendsto`, with positive periods `T i → T₀ > 0`, if frequently
along `l` the loop `ℝ / (T i)ℤ → M` traced by `γ i` is null-homotopic, then so is the loop
`ℝ / T₀ℤ → M` traced by the limit curve. -/
theorem exists_nullhomotopic_of_tendsto [l.NeBot]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : ∀ i, IsMIntegralCurve (γ i) v) (hper : ∀ i, Periodic (γ i) (T i))
    (hT_pos : ∀ i, 0 < T i) (hK : IsCompact K) (hmem : ∀ᶠ i in l, ∀ t, γ i t ∈ K)
    (hx : Tendsto (fun i ↦ γ i 0) l (𝓝 x)) (hT : Tendsto T l (𝓝 T₀)) (hT₀ : 0 < T₀)
    (hnull : ∃ᶠ i in l, ∃ g : C(AddCircle (T i), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ i t) :
    ∃ g : C(AddCircle T₀, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = maximalIntegralCurve v x t := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : Fact (0 < T₀) := ⟨hT₀⟩
  set φ : M × ℝ → M := fun q ↦ maximalIntegralCurve v q.1 q.2 with hφ
  have hglob (i : ι) : maximalIntegralCurve v (γ i 0) = γ i := (hγ i).maximalIntegralCurve_eq hv
  have hpx : Periodic (maximalIntegralCurve v x) T₀ :=
    periodic_maximalIntegralCurve_of_tendsto hv hγ hper hK hmem hx hT
  have hJx := mem_maximalIntegralCurveInterval_of_tendsto hv hγ hK hmem hx
  have h0 (y : M) : (0 : ℝ) ∈ maximalIntegralCurveInterval v y :=
    zero_mem_maximalIntegralCurveInterval hv.contMDiffAt
  have hcont : ContinuousOn φ (maximalIntegralCurveFlowDomain v) :=
    (contMDiffOn_maximalIntegralCurve le_rfl hv).continuousOn
  have hD : IsOpen (maximalIntegralCurveFlowDomain v) := isOpen_maximalIntegralCurveFlowDomain hv
  set e := extChartAt I x with he
  -- The chart target is a neighbourhood of `e x`, since `x` is an interior point.
  have htgt : e.target ∈ 𝓝 (e x) := by
    have h := extChartAt_target_mem_nhdsWithin (I := I) x
    rwa [nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x)))] at h
  /- For `q = ((y, τ), θ)`, the point `b q = φ(y, -τ)` flows to `y` in time `τ`, the point `w q`
  runs along the chart segment from `y` to `b q` as `θ` goes from `0` to `1`, and
  `L q = φ(w q, θτ)`. For fixed `(y, τ)`, `θ ↦ L q` is a loop at `y`. -/
  let b : (M × ℝ) × ℝ → M := fun q ↦ φ (q.1.1, -q.1.2)
  let c : (M × ℝ) × ℝ → E := fun q ↦ (1 - q.2) • e q.1.1 + q.2 • e (b q)
  let w : (M × ℝ) × ℝ → M := fun q ↦ e.symm (c q)
  let L : (M × ℝ) × ℝ → M := fun q ↦ φ (w q, q.2 * q.1.2)
  -- An open set `A₄` on which `L` is continuous.
  let A₁ : Set ((M × ℝ) × ℝ) := (fun q ↦ q.1.1) ⁻¹' e.source ∩
    (fun q ↦ (q.1.1, -q.1.2)) ⁻¹' maximalIntegralCurveFlowDomain v
  have hA₁ : IsOpen A₁ :=
    ((isOpen_extChartAt_source x).preimage (by fun_prop)).inter (hD.preimage (by fun_prop))
  have hb : ContinuousOn b A₁ :=
    hcont.comp (by fun_prop : Continuous fun q : (M × ℝ) × ℝ ↦ (q.1.1, -q.1.2)).continuousOn
      fun _ hq ↦ hq.2
  let A₂ : Set ((M × ℝ) × ℝ) := A₁ ∩ b ⁻¹' e.source
  have hA₂ : IsOpen A₂ := hb.isOpen_inter_preimage hA₁ (isOpen_extChartAt_source x)
  have hc : ContinuousOn c A₂ := by
    refine ContinuousOn.add ?_ ?_
    · exact (continuousOn_const.sub continuous_snd.continuousOn).smul
        ((continuousOn_extChartAt x).comp (by fun_prop : Continuous fun q :
          (M × ℝ) × ℝ ↦ q.1.1).continuousOn fun _ hq ↦ hq.1.1)
    · exact continuous_snd.continuousOn.smul
        ((continuousOn_extChartAt x).comp (hb.mono inter_subset_left) fun _ hq ↦ hq.2)
  let A₃ : Set ((M × ℝ) × ℝ) := A₂ ∩ c ⁻¹' interior e.target
  have hA₃ : IsOpen A₃ := hc.isOpen_inter_preimage hA₂ isOpen_interior
  have hw : ContinuousOn w A₃ :=
    (continuousOn_extChartAt_symm x).comp (hc.mono inter_subset_left)
      fun _ hq ↦ interior_subset hq.2
  have hwτ : ContinuousOn (fun q ↦ (w q, q.2 * q.1.2)) A₃ :=
    hw.prodMk (by fun_prop : Continuous fun q : (M × ℝ) × ℝ ↦ q.2 * q.1.2).continuousOn
  let A₄ : Set ((M × ℝ) × ℝ) := A₃ ∩ (fun q ↦ (w q, q.2 * q.1.2)) ⁻¹'
    maximalIntegralCurveFlowDomain v
  have hA₄ : IsOpen A₄ := hwτ.isOpen_inter_preimage hA₃ hD
  have hL : ContinuousOn L A₄ := hcont.comp (hwτ.mono inter_subset_left) fun _ hq ↦ hq.2
  -- Each `θ ↦ L ((y, τ), θ)` is a loop at `y`.
  have hL0 {q : (M × ℝ) × ℝ} (hq : q ∈ A₂) (hθ : q.2 = 0) : L q = q.1.1 := by
    simp only [L, w, c, hθ, sub_zero, one_smul, zero_smul, add_zero, zero_mul, hφ,
      e.left_inv hq.1.1, maximalIntegralCurve_zero (h0 _)]
  have hL1 {q : (M × ℝ) × ℝ} (hq : q ∈ A₂) (hθ : q.2 = 1) : L q = q.1.1 := by
    have hb' : maximalIntegralCurve v q.1.1 (-q.1.2) ∈ e.source := hq.2
    have hneg : -q.1.2 ∈ maximalIntegralCurveInterval v q.1.1 :=
      mem_maximalIntegralCurveFlowDomain.1 (mem_preimage.1 hq.1.2)
    simp only [L, w, c, hθ, sub_self, zero_smul, one_smul, zero_add, one_mul, hφ, b,
      e.left_inv hb']
    rw [← maximalIntegralCurve_add hv hneg (by simpa using h0 q.1.1), neg_add_cancel,
      maximalIntegralCurve_zero (h0 _)]
  -- At a periodic point the loop is the orbit loop.
  have hLper {y : M} {τ : ℝ} (hy : y ∈ e.source) (hyper : maximalIntegralCurve v y (-τ) = y)
      (θ : ℝ) : w ((y, τ), θ) = y := by
    simp only [w, c, b, hφ, hyper, ← add_smul, sub_add_cancel, one_smul, e.left_inv hy]
  have hxx : maximalIntegralCurve v x (-T₀) = x := by
    rw [(hpx.neg).eq, maximalIntegralCurve_zero (h0 x)]
  -- The loops at `(x, T₀)` lie in `A₄`, hence so do those at nearby parameters.
  have hxA (θ : ℝ) : ((x, T₀), θ) ∈ A₄ := by
    have hxs : x ∈ e.source := mem_extChartAt_source x
    refine ⟨⟨⟨⟨hxs, mem_preimage.2 (mem_maximalIntegralCurveFlowDomain.2 (hJx _))⟩, ?_⟩, ?_⟩,
      mem_preimage.2 (mem_maximalIntegralCurveFlowDomain.2 ?_)⟩
    · exact mem_preimage.2 (by simpa only [b, hφ, hxx] using hxs)
    · refine mem_preimage.2 ?_
      simp only [c, b, hφ, hxx, ← add_smul, sub_add_cancel, one_smul]
      exact mem_interior_iff_mem_nhds.2 htgt
    · simpa only [hLper hxs hxx] using hJx _
  obtain ⟨u, V, hu, -, hxu, hIV, huV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := ((x, T₀) : M × ℝ))) isCompact_Icc hA₄
    (by rintro ⟨p, θ⟩ ⟨hp, -⟩; obtain rfl : p = (x, T₀) := hp; exact hxA θ)
  obtain ⟨U₁, hU₁, U₂, hU₂, hU⟩ := mem_nhds_prod_iff.1 (hu.mem_nhds (hxu rfl))
  obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhds_iff.1 (inter_mem (interior_mem_nhds.2 htgt)
    ((continuousAt_extChartAt_symm x).preimage_mem_nhds (by rwa [extChartAt_to_inv])))
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.1 hU₂
  -- Choose `i` with a null-homotopic orbit loop and parameters close to `(x, T₀)`.
  have hev₁ : ∀ᶠ i in l, γ i 0 ∈ e.source := hx (extChartAt_source_mem_nhds x)
  have hev₂ : ∀ᶠ i in l, e (γ i 0) ∈ ball (e x) r :=
    ((continuousAt_extChartAt x).tendsto.comp hx) (ball_mem_nhds _ hr)
  have hev₃ : ∀ᶠ i in l, T i ∈ ball T₀ ε := hT (ball_mem_nhds _ hε)
  obtain ⟨i, ⟨g, hg, hgγ⟩, hi₁, hi₂, hi₃⟩ :=
    (hnull.and_eventually (hev₁.and (hev₂.and hev₃))).exists
  have hiper : maximalIntegralCurve v (γ i 0) (-T i) = γ i 0 := by
    rw [hglob, (hper i).neg.eq]
  -- The straight path `P` from `(γ i 0, T i)` to `(x, T₀)` in the chart.
  let P : unitInterval → M × ℝ := fun s ↦ (e.symm ((1 - (s : ℝ)) • e (γ i 0) + (s : ℝ) • e x),
    (1 - (s : ℝ)) * T i + s * T₀)
  have hPe (s : unitInterval) : (1 - (s : ℝ)) • e (γ i 0) + (s : ℝ) • e x ∈ ball (e x) r :=
    convex_ball _ _ hi₂ (mem_ball_self hr) (sub_nonneg.2 s.2.2) s.2.1 (sub_add_cancel 1 _)
  have hPT (s : unitInterval) : (1 - (s : ℝ)) * T i + s * T₀ ∈ ball T₀ ε :=
    convex_ball _ _ hi₃ (mem_ball_self hε) (sub_nonneg.2 s.2.2) s.2.1 (sub_add_cancel 1 _)
  have hPu (s : unitInterval) : P s ∈ u := hU (mk_mem_prod (hr_sub (hPe s)).2 (hε_sub (hPT s)))
  have hP : Continuous P :=
    ((continuousOn_extChartAt_symm x).comp_continuous (by fun_prop)
      fun s ↦ interior_subset (hr_sub (hPe s)).1).prodMk (by fun_prop)
  have hPA (s t : unitInterval) : (P s, (t : ℝ)) ∈ A₄ := huV (mk_mem_prod (hPu s) (hIV t.2))
  -- The free homotopy of loops `G (s, t) = L (P s, t)`.
  let G : C(unitInterval × unitInterval, M) :=
    ⟨fun p ↦ L (P p.1, (p.2 : ℝ)), hL.comp_continuous (by fun_prop) fun p ↦ hPA p.1 p.2⟩
  have hGapply (p : unitInterval × unitInterval) : G p = L (P p.1, (p.2 : ℝ)) := rfl
  have hG (s : unitInterval) : G (s, 0) = G (s, 1) := by
    rw [hGapply, hGapply, hL0 (hPA s 0).1.1 (by simp), hL1 (hPA s 1).1.1 (by simp)]
  have hP0 : P 0 = (γ i 0, T i) := by
    simp [P, e.left_inv hi₁]
  have hP1 : P 1 = (x, T₀) := by
    simp [P, he]
  -- The orbit loop of `γ i`, reparametrized to period `T₀`, and that of the limit curve.
  let scale : C(AddCircle T₀, AddCircle (T i)) :=
    ⟨_, (AddCircle.homeomorphAddCircle T₀ (T i) hT₀.ne' (hT_pos i).ne').continuous⟩
  have hscale (θ : AddCircle T₀) :
      scale θ = AddCircle.homeomorphAddCircle T₀ (T i) hT₀.ne' (hT_pos i).ne' θ := rfl
  let g₀ : C(AddCircle T₀, M) :=
    ⟨hpx.lift, (isMIntegralCurve_maximalIntegralCurve_of_tendsto hv hγ hK hmem
      hx).continuous.quotient_liftOn' _⟩
  have hg₀ (t : ℝ) : g₀ t = maximalIntegralCurve v x t := hpx.lift_coe t
  have h₀ (t : unitInterval) : (g.comp scale) (AddCircle.ofUnitInterval T₀ t) = G (0, t) := by
    rw [hGapply, ContinuousMap.comp_apply, hP0, AddCircle.ofUnitInterval_apply]
    rw [hscale, AddCircle.homeomorphAddCircle_apply_mk, hgγ]
    simp only [L, hφ, hLper hi₁ hiper, hglob]
    congr 1
    field_simp
  have h₁ (t : unitInterval) : g₀ (AddCircle.ofUnitInterval T₀ t) = G (1, t) := by
    rw [hGapply, hP1, AddCircle.ofUnitInterval_apply, hg₀]
    simp only [L, hφ, hLper (mem_extChartAt_source x) hxx]
  obtain ⟨z, hz⟩ := hg.comp_left scale
  exact ⟨g₀, ⟨z, (ContinuousMap.homotopic_of_comp_ofUnitInterval G hG h₀ h₁).symm.trans hz⟩, hg₀⟩

end TauCeti
