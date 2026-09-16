/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
import TauCeti.Geometry.Manifold.IntegralCurve.SmoothDependence
import Mathlib.Topology.Connected.Clopen

/-!
# The flow law for maximal integral curves

The maximal integral curve of an autonomous vector field can be restarted at any time in its
interval of existence. Its new maximal interval is the translate of the original interval, and
the restarted curve is the corresponding translate of the original curve. These are the domain
and value laws that turn the family `maximalIntegralCurve v` into a partial flow.

The domain statement is essential: `maximalIntegralCurve` is total only by assigning its initial
point as a junk value outside the interval of existence, so an unconditional flow equation would
be false. The results below always carry the precise membership hypotheses.

## Main results

* `mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff`: the maximal interval after
  restarting at `t` is exactly the translate by `-t` of the original interval.
* `maximalIntegralCurve_add`: the domain-aware flow law
  `φ x (t + s) = φ (φ x t) s`.
* `maximalIntegralCurveFlowDomain`: the natural domain of the maximal flow.
* `isOpen_maximalIntegralCurveFlowDomain`: the natural domain is open.
* `contMDiffOn_maximalIntegralCurve`: the maximal flow of a smooth vector field is smooth on its
  natural domain.

## References

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012],
  Chapter 9, especially Theorem 9.12.
-/

public section

open Function Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {s t : ℝ} {x : M}

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- Any two times in the maximal interval lie in a common open subinterval on which the maximal
curve is an integral curve. -/
private theorem exists_common_Ioo_maximalIntegralCurveInterval
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x)
    (hs : s ∈ maximalIntegralCurveInterval v x) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Ioo a b ∧ t ∈ Ioo a b ∧ s ∈ Ioo a b ∧
      IsMIntegralCurveOn (maximalIntegralCurve v x) v (Ioo a b) := by
  obtain ⟨γ, a₁, b₁, hγ, hγx, hγ0, ht, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
  obtain ⟨δ, a₂, b₂, hδ, hδx, hδ0, hs, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq hs
  refine ⟨min a₁ a₂, max b₁ b₂,
    ⟨(min_le_left _ _).trans_lt hγ0.1, hγ0.2.trans_le (le_max_left _ _)⟩,
    ⟨lt_of_le_of_lt (min_le_left _ _) ht.1, ht.2.trans_le (le_max_left _ _)⟩,
    ⟨lt_of_le_of_lt (min_le_right _ _) hs.1, hs.2.trans_le (le_max_right _ _)⟩, ?_⟩
  refine (isMIntegralCurveOn_maximalIntegralCurve hv).mono fun r hr ↦ ?_
  rcases lt_or_ge r 0 with hr0 | hr0
  · rcases min_choice a₁ a₂ with hmin | hmin
    · exact hγ.subset_maximalIntegralCurveInterval hγ0 hγx
        ⟨hmin ▸ hr.1, hr0.trans hγ0.2⟩
    · exact hδ.subset_maximalIntegralCurveInterval hδ0 hδx
        ⟨hmin ▸ hr.1, hr0.trans hδ0.2⟩
  · rcases max_choice b₁ b₂ with hmax | hmax
    · exact hγ.subset_maximalIntegralCurveInterval hγ0 hγx
        ⟨hγ0.1.trans_le hr0, hmax ▸ hr.2⟩
    · exact hδ.subset_maximalIntegralCurveInterval hδ0 hδx
        ⟨hδ0.1.trans_le hr0, hmax ▸ hr.2⟩

/-- If `s` and `t` belong to the maximal interval through `x`, then `s - t` belongs to the
maximal interval through the point reached at time `t`. This is the domain half of restarting an
autonomous integral curve at time `t`. -/
private theorem sub_mem_maximalIntegralCurveInterval
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x)
    (hs : s ∈ maximalIntegralCurveInterval v x) :
    s - t ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v x t) := by
  obtain ⟨a, b, h0, ht', hs', hγ⟩ :=
    exists_common_Ioo_maximalIntegralCurveInterval hv ht hs
  have hshift : IsMIntegralCurveOn (maximalIntegralCurve v x ∘ (· + t)) v
      (Ioo (a - t) (b - t)) := by
    convert hγ.comp_add t using 1
    ext r
    simp only [mem_Ioo, mem_ofPred_eq, sub_lt_iff_lt_add, lt_sub_iff_add_lt]
  exact hshift.subset_maximalIntegralCurveInterval
    ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ (by simp)
    ⟨by linarith [hs'.1], by linarith [hs'.2]⟩

/-- **The flow law for the maximal integral curve.** If both `t` and `t + s` lie in the maximal
interval through `x`, restarting the curve at time `t` and running it for time `s` gives its value
at time `t + s`. -/
theorem maximalIntegralCurve_add
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x)
    (hts : t + s ∈ maximalIntegralCurveInterval v x) :
    maximalIntegralCurve v x (t + s) =
      maximalIntegralCurve v (maximalIntegralCurve v x t) s := by
  obtain ⟨a, b, h0, ht', hst', hγ⟩ :=
    exists_common_Ioo_maximalIntegralCurveInterval hv ht hts
  have hshift : IsMIntegralCurveOn (maximalIntegralCurve v x ∘ (· + t)) v
      (Ioo (a - t) (b - t)) := by
    convert hγ.comp_add t using 1
    ext r
    simp only [mem_Ioo, mem_ofPred_eq, sub_lt_iff_lt_add, lt_sub_iff_add_lt]
  have h0shift : (0 : ℝ) ∈ Ioo (a - t) (b - t) :=
    ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have hsshift : s ∈ Ioo (a - t) (b - t) :=
    ⟨by linarith [hst'.1], by linarith [hst'.2]⟩
  symm
  simpa only [comp_apply, add_comm] using
    hshift.eqOn_maximalIntegralCurve hv h0shift (by simp) hsshift

/-- Restarting a maximal integral curve at time `t` translates its maximal interval by `-t`.
This characterizes the domain of the partial flow without reference to the chosen integral-curve
witnesses. -/
@[simp] theorem mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x) :
    s ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v x t) ↔
      t + s ∈ maximalIntegralCurveInterval v x := by
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x := by
    obtain ⟨γ, a, b, hγ, hγx, hγ0, -, -⟩ :=
      exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
    exact hγ.subset_maximalIntegralCurveInterval hγ0 hγx hγ0
  have hneg : -t ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v x t) := by
    simpa only [zero_sub] using sub_mem_maximalIntegralCurveInterval hv ht h0
  have hback : maximalIntegralCurve v (maximalIntegralCurve v x t) (-t) = x := by
    rw [← maximalIntegralCurve_add hv ht]
    · simpa only [add_neg_cancel] using maximalIntegralCurve_zero h0
    · simpa using h0
  constructor
  · intro hs
    have := sub_mem_maximalIntegralCurveInterval hv hneg hs
    rw [hback] at this
    simpa only [sub_neg_eq_add, add_comm] using this
  · intro hst
    simpa only [add_sub_cancel_left] using
      sub_mem_maximalIntegralCurveInterval hv ht hst

/-- Set form of `mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff`: the maximal interval
after restarting at `t` is the preimage of the original interval under translation by `t`. -/
theorem maximalIntegralCurveInterval_maximalIntegralCurve_eq_preimage
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : t ∈ maximalIntegralCurveInterval v x) :
    maximalIntegralCurveInterval v (maximalIntegralCurve v x t) =
      (fun s : ℝ ↦ t + s) ⁻¹' maximalIntegralCurveInterval v x := by
  ext s
  exact mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff hv ht

/-! ### The domain and regularity of the maximal flow -/

/-- The natural domain of the maximal flow of `v`, consisting of the pairs `(x, t)` for which the
maximal integral curve through `x` is defined at time `t`. -/
def maximalIntegralCurveFlowDomain (v : (x : M) → TangentSpace I x) : Set (M × ℝ) :=
  {p | p.2 ∈ maximalIntegralCurveInterval v p.1}

omit [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
/-- Membership in the natural domain of the maximal flow. -/
@[simp] theorem mem_maximalIntegralCurveFlowDomain {p : M × ℝ} :
    p ∈ maximalIntegralCurveFlowDomain v ↔ p.2 ∈ maximalIntegralCurveInterval v p.1 :=
  Iff.rfl

/-- A point is good for the order-`n + 1` maximal flow if the natural domain is a neighbourhood
of that point and the total, junk-extended flow is `C^(n+1)` there. -/
private def IsMaximalIntegralCurveFlowPoint (n : ℕ) (v : (x : M) → TangentSpace I x)
    (p : M × ℝ) : Prop :=
  maximalIntegralCurveFlowDomain v ∈ 𝓝 p ∧
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I (n + 1 : ℕ)
      (fun q : M × ℝ ↦ maximalIntegralCurve v q.1 q.2) p

omit [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
/-- For finite differentiability order, being a regular point of the maximal flow is an open
condition. -/
private theorem isOpen_isMaximalIntegralCurveFlowPoint (n : ℕ)
    [IsManifold I (n + 1 : ℕ) M]
    (v : (x : M) → TangentSpace I x) :
    IsOpen {p | IsMaximalIntegralCurveFlowPoint (I := I) n v p} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨u, hup, hu, hud⟩ := mem_nhds_iff.mp hp.1
  have hsmooth :
      {q | ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I (n + 1 : ℕ)
        (fun r : M × ℝ ↦ maximalIntegralCurve v r.1 r.2) q} ∈ 𝓝 p :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hp.2
  refine Filter.mem_of_superset (Filter.inter_mem (hu.mem_nhds hud) hsmooth) ?_
  rintro q ⟨hqu, hq⟩
  refine ⟨Filter.mem_of_superset (hu.mem_nhds hqu) hup, hq⟩

/-- Every initial state at time zero is a regular point of the finite-order maximal flow. -/
private theorem isMaximalIntegralCurveFlowPoint_zero [CompleteSpace E] [FiniteDimensional ℝ E]
    (n : ℕ) (hv : CMDiff (n + 1 : ℕ) (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (x : M) :
    IsMaximalIntegralCurveFlowPoint (I := I) n v (x, 0) := by
  have hvone : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num)
  refine ⟨eventually_mem_maximalIntegralCurveInterval hvone.contMDiffAt, ?_⟩
  apply contMDiffAt_maximalIntegralCurve (n := (n : ℕ∞))
  simpa using hv.contMDiffAt

/-- Regular points compose according to the flow law. -/
private theorem IsMaximalIntegralCurveFlowPoint.add [CompleteSpace E]
    [FiniteDimensional ℝ E] (n : ℕ) [IsManifold I (n + 1 : ℕ) M]
    (hv : CMDiff (n + 1 : ℕ) (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {x : M} {s u : ℝ}
    (hs : IsMaximalIntegralCurveFlowPoint (I := I) n v (x, s))
    (hu : IsMaximalIntegralCurveFlowPoint (I := I) n v
      (maximalIntegralCurve v x s, u)) :
    IsMaximalIntegralCurveFlowPoint (I := I) n v (x, s + u) := by
  let F : M × ℝ → M := fun p ↦ maximalIntegralCurve v p.1 p.2
  let G : M × ℝ → M × ℝ := fun p ↦ (maximalIntegralCurve v p.1 s, -s + p.2)
  have hslice : ContMDiffAt I I (n + 1 : ℕ) (fun y ↦ maximalIntegralCurve v y s) x :=
    hs.2.comp x (contMDiffAt_id.prodMk contMDiffAt_const)
  have hsub : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (n + 1 : ℕ)
      (fun p : M × ℝ ↦ -s + p.2) (x, s + u) := by
    have haff : ContDiff ℝ (n + 1 : ℕ) (fun r : ℝ ↦ -s + r) :=
      contDiff_const.add contDiff_id
    exact haff.contMDiff.contMDiffAt.comp (x, s + u) contMDiffAt_snd
  have hG : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (n + 1 : ℕ) G
      (x, s + u) := by
    exact (hslice.comp (x, s + u) contMDiffAt_fst).prodMk hsub
  have hGvalue : G (x, s + u) = (maximalIntegralCurve v x s, u) := by
    simp [G]
  have hfixed : ∀ᶠ p in 𝓝 ((x, s + u) : M × ℝ),
      s ∈ maximalIntegralCurveInterval v p.1 := by
    have hbase : ∀ᶠ y in 𝓝 x, s ∈ maximalIntegralCurveInterval v y := by
      have h := (continuousAt_id.prodMk continuousAt_const).eventually hs.1
      filter_upwards [h] with y hy
      simpa only [id_eq, mem_maximalIntegralCurveFlowDomain] using hy
    filter_upwards [(continuousAt_fst :
      ContinuousAt (fun p : M × ℝ ↦ p.1) (x, s + u)).eventually hbase] with p hp
    exact hp
  have hinner : ∀ᶠ p in 𝓝 ((x, s + u) : M × ℝ),
      -s + p.2 ∈ maximalIntegralCurveInterval v (maximalIntegralCurve v p.1 s) := by
    have h := hG.continuousAt.eventually (hGvalue ▸ hu.1)
    simpa only [G, mem_maximalIntegralCurveFlowDomain] using h
  have hdomain : ∀ᶠ p in 𝓝 ((x, s + u) : M × ℝ),
      p ∈ maximalIntegralCurveFlowDomain v := by
    have hvone : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) :=
      hv.of_le (by norm_num)
    filter_upwards [hfixed, hinner] with p hps hpinner
    rw [mem_maximalIntegralCurveFlowDomain]
    have := (mem_maximalIntegralCurveInterval_maximalIntegralCurve_iff
      (v := v) (x := p.1) (t := s) (s := -s + p.2) hvone hps).mp hpinner
    ring_nf at this
    exact this
  -- On this neighbourhood the domain identity supplies the hypotheses of the flow law, so the
  -- maximal flow agrees with a composition of its time-`s` slice and the restarted flow.
  refine ⟨hdomain, ?_⟩
  have hcomp : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I (n + 1 : ℕ) (F ∘ G) (x, s + u) :=
    hu.2.comp_of_eq hG hGvalue
  refine hcomp.congr_of_eventuallyEq ?_
  have hvone : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num)
  filter_upwards [hfixed, hdomain] with p hps hp
  have hp' : s + (-s + p.2) ∈ maximalIntegralCurveInterval v p.1 := by
    convert mem_maximalIntegralCurveFlowDomain.mp hp using 1
    ring
  have hadd := maximalIntegralCurve_add (v := v) (x := p.1) (t := s) (s := -s + p.2)
    hvone hps hp'
  ring_nf at hadd
  simpa only [F, G, Function.comp_apply] using hadd

/-- Every point in the natural domain is a regular point of the finite-order maximal flow. The
proof propagates the time-zero result along the connected maximal interval. -/
private theorem isMaximalIntegralCurveFlowPoint_of_mem [CompleteSpace E]
    [FiniteDimensional ℝ E] (n : ℕ) [IsManifold I (n + 1 : ℕ) M]
    (hv : CMDiff (n + 1 : ℕ) (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {x : M} {t : ℝ} (ht : t ∈ maximalIntegralCurveInterval v x) :
    IsMaximalIntegralCurveFlowPoint (I := I) n v (x, t) := by
  let P : Set (M × ℝ) := {p | IsMaximalIntegralCurveFlowPoint (I := I) n v p}
  let S : Set ℝ := {s | (x, s) ∈ P}
  let K : Set ℝ := Icc (min 0 t) (max 0 t)
  have hvone : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num)
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x :=
    zero_mem_maximalIntegralCurveInterval hvone.contMDiffAt
  have hKsub : K ⊆ maximalIntegralCurveInterval v x := by
    intro r hr
    dsimp only [K] at hr
    rcases le_total 0 t with h | h
    · rw [min_eq_left h, max_eq_right h] at hr
      exact ordConnected_maximalIntegralCurveInterval.out h0 ht hr
    · rw [min_eq_right h, max_eq_left h] at hr
      exact ordConnected_maximalIntegralCurveInterval.out ht h0 hr
  have hPopen : IsOpen P :=
    isOpen_isMaximalIntegralCurveFlowPoint (I := I) n v
  have hSopen : IsOpen S := by
    exact hPopen.preimage (continuous_const.prodMk continuous_id)
  have hcurve : ContinuousOn (maximalIntegralCurve v x) K :=
    (isMIntegralCurveOn_maximalIntegralCurve hvone).continuousOn.mono hKsub
  -- A limit of regular times is regular: restart at a nearby regular time and use continuity of
  -- the fixed maximal trajectory to make the remaining time lie in the regular time-zero germ.
  have hSKclosed : IsClosed (S ∩ K) := by
    rw [← closure_subset_iff_isClosed]
    intro r hr
    have hrK : r ∈ K := by
      apply (isClosed_Icc.closure_subset_iff.mpr inter_subset_right) hr
    have hgr : ContinuousWithinAt
        (fun s : ℝ ↦ (maximalIntegralCurve v x s, r - s)) K r := by
      exact (hcurve r hrK).prodMk
        ((continuousAt_const.sub continuousAt_id).continuousWithinAt)
    have hzero :
        (maximalIntegralCurve v x r, (0 : ℝ)) ∈ P :=
      isMaximalIntegralCurveFlowPoint_zero (I := I) n hv _
    have hpre : {s : ℝ | (maximalIntegralCurve v x s, r - s) ∈ P} ∈ 𝓝[K] r := by
      have hzero' : (maximalIntegralCurve v x r, r - r) ∈ P := by
        simpa only [sub_self] using hzero
      exact hgr.eventually (hPopen.mem_nhds hzero')
    obtain ⟨w, hwr, hw⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
    obtain ⟨s, hsw, hsS, hsK⟩ :=
      (mem_closure_iff_nhds.mp hr w hwr)
    have hs : IsMaximalIntegralCurveFlowPoint (I := I) n v (x, s) := hsS
    have hsr : IsMaximalIntegralCurveFlowPoint (I := I) n v
        (maximalIntegralCurve v x s, r - s) :=
      hw ⟨hsw, hsK⟩
    have hadd := hs.add n hv hsr
    ring_nf at hadd
    exact ⟨hadd, hrK⟩
  have h0K : (0 : ℝ) ∈ K := by
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have htK : t ∈ K := by
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  let T : Set K := {r | (r : ℝ) ∈ S}
  have hTopen : IsOpen T :=
    hSopen.preimage continuous_subtype_val
  have hTclosed : IsClosed T := by
    have h : IsClosed ((fun r : K ↦ (r : ℝ)) ⁻¹' (S ∩ K)) :=
      hSKclosed.preimage continuous_subtype_val
    have heq : (fun r : K ↦ (r : ℝ)) ⁻¹' (S ∩ K) = T := by
      ext r
      constructor
      · exact fun hr ↦ hr.1
      · exact fun hr ↦ ⟨hr, r.property⟩
    rwa [heq] at h
  -- The regular times form a nonempty clopen subset of the connected compact interval from
  -- `0` to `t`, so they fill that interval.
  let _ : PreconnectedSpace K := Subtype.preconnectedSpace isPreconnected_Icc
  have h0S : (0 : ℝ) ∈ S :=
    isMaximalIntegralCurveFlowPoint_zero (I := I) n hv x
  have hKT : (Set.univ : Set K) ⊆ T :=
    isPreconnected_univ.subset_isClopen ⟨hTclosed, hTopen⟩
      (by
        have hz : (⟨0, h0K⟩ : K) ∈ T := h0S
        exact ⟨_, mem_inter (mem_univ _) hz⟩)
  exact hKT (mem_univ (⟨t, htK⟩ : K))

/-- **The natural domain of the maximal flow is open.** This is openness jointly in the initial
point and time, not merely openness of each individual maximal interval. -/
theorem isOpen_maximalIntegralCurveFlowDomain [FiniteDimensional ℝ E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    IsOpen (maximalIntegralCurveFlowDomain v) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I (0 + 1 : ℕ) M := IsManifold.of_le (n := 1) (by norm_num)
  rw [isOpen_iff_mem_nhds]
  intro p hp
  exact (isMaximalIntegralCurveFlowPoint_of_mem (I := I) 0 hv hp).1

/-- **Smoothness of the maximal flow.** The maximal flow of a smooth vector field on a
finite-dimensional boundaryless manifold is jointly smooth in its initial point and time on its
natural domain. -/
theorem contMDiffOn_maximalIntegralCurve [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (hv : CMDiff ∞ (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : M × ℝ ↦ maximalIntegralCurve v p.1 p.2)
      (maximalIntegralCurveFlowDomain v) := by
  rw [contMDiffOn_infty]
  intro n
  let _ : IsManifold I (n + 1 : ℕ) M := IsManifold.of_le (n := ∞)
    (by exact_mod_cast le_top)
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro p hp
  exact (isMaximalIntegralCurveFlowPoint_of_mem (I := I) n
    (hv.of_le (by exact_mod_cast le_top)) hp).2.contMDiffWithinAt.of_le
    (by exact_mod_cast Nat.le_succ n)

end TauCeti
