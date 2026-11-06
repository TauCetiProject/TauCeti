/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.Monotonicity
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
import TauCeti.Geometry.Manifold.Flow.Straightening
import TauCeti.Geometry.Manifold.LocallyContractible
import TauCeti.Geometry.Symplectic.Hamiltonian.Characteristic
import TauCeti.Topology.Homotopy.AddCircle

/-!
# Almost existence from a finite relative capacity

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless manifold `M`, and
`F : M → ℝ` a smooth function. This file completes the argument of Hofer, Zehnder and Struwe which
turns finiteness of a `π₁`-sensitive Hofer–Zehnder capacity into closed characteristics on almost
every level of `F`.

**The limit step.** Let `F⁻¹[a, b]` be compact and let `s ∈ (a, b)` be a regular value of `F`. If
levels `F⁻¹(c)` with `c` arbitrarily close to `s` carry closed characteristics, contractible in
`M`, of period at most `K`, then so does `F⁻¹(s)`
(`IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`).
The Hamiltonian flow of `F` is defined for all time on `F⁻¹[a, b]`, so by compactness the periods
and initial points of the closed characteristics accumulate at some `(T, p)` with `F p = s`, and
the trajectory of `p` returns to `p` at time `T`. The limit period `T` is positive, because no
point near a point where the Hamiltonian vector field does not vanish returns to itself in a short
time (`TauCeti.exists_pos_eventually_forall_flowOf_ne`), and `X_F` does not vanish on a regular
level. The loops of the closed characteristics, read on the unit interval, converge to that of the
limit trajectory in the compact-open topology, and a limit of null-homotopic loops in a manifold
is null-homotopic (`Path.Homotopic.refl_of_tendsto`).

**Almost existence.** Combined with the monotonicity argument
(`IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`),
this gives the relative form of the Hofer–Zehnder–Struwe theorem: if the relative capacity
`c°_HZ({F < b}, Z)` is finite for some `Z ⊆ {F ≤ a}`, and `F` has compact sublevel sets below `b`
and takes every value in `(a, b)`, then every level `F⁻¹(c)`, `c ∈ (a, b)`, has the contractible
almost existence property in `M`
(`IsNondegenerate.hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top`).

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm`.

* `IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`:
  closed characteristics of bounded period on levels accumulating at a regular level give one on
  that level.
* `IsNondegenerate.hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top`:
  finiteness of the relative capacity gives contractible almost existence.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. 20 (1990), 49–58.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.3.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {Z : Set M}
  {F : M → ℝ}

namespace IsNondegenerate

/-- If `F⁻¹[a, b]` is compact, the Hamiltonian flow of `F` through a point of `F⁻¹[a, b]` is
defined for all time: its trajectory stays in the compact level of the point. -/
private theorem mem_flowDomain_hamiltonianVectorField (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : IsCompact (F ⁻¹' Icc a b)) {x : M}
    (hx : F x ∈ Icc a b) (t : ℝ) : (t, x) ∈ flowDomain (σ.hamiltonianVectorField F) := by
  have hX : ContMDiff I I.tangent 1
      (fun y ↦ (⟨y, σ.hamiltonianVectorField F y⟩ : TangentBundle I M)) :=
    hσ.contMDiff_hamiltonianVectorField (by simp) (hF.of_le (by simp))
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x) hX.contMDiffAt
  have hK : IsCompact (F ⁻¹' {F x}) :=
    hcpt.of_isClosed_subset (isClosed_singleton.preimage hF.continuous)
      fun y (hy : F y = F x) ↦ by rw [mem_preimage, hy]; exact hx
  rw [TauCeti.mem_flowDomain, maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hX h0 hK
    fun t ht ↦ ?_]
  · exact mem_univ t
  rw [mem_preimage, mem_singleton_iff,
    (hσ.isHamiltonianVectorField_hamiltonianVectorField F).apply_eq_of_isMIntegralCurveOn
      isOpen_maximalIntegralCurveInterval isPreconnected_maximalIntegralCurveInterval
      (isMIntegralCurveOn_maximalIntegralCurve hX) (fun _ _ ↦ hF.mdifferentiableAt (by simp)) h0 ht,
    maximalIntegralCurve_zero h0]

/-- **The loop of a limit of trajectories is null-homotopic.** Let `F⁻¹[a, b]` be compact, and
let `p ∈ F⁻¹(a, b)` return to itself at time `T₀ > 0` under the Hamiltonian flow of `F`. If the
null-homotopic loops `g i` of period `T i > 0`, traced by the trajectories through points `q i`,
have periods and initial points converging to `(T₀, p)`, then the loop of period `T₀` traced by the
trajectory through `p` is null-homotopic. -/
private theorem exists_nullhomotopic_of_tendsto (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : IsCompact (F ⁻¹' Icc a b)) {T₀ : ℝ} {p : M}
    (hT₀ : 0 < T₀) (hp : F p ∈ Ioo a b)
    (hper : Periodic (fun t ↦ flowOf (σ.hamiltonianVectorField F) t p) T₀) {ι : Type*}
    {u : Filter ι} [u.NeBot] {T : ι → ℝ} {q : ι → M} (hT : ∀ i, 0 < T i)
    (g : ∀ i, C(AddCircle (T i), M)) (hg : ∀ i, (g i).Nullhomotopic)
    (hgq : ∀ i (t : ℝ), g i t = flowOf (σ.hamiltonianVectorField F) t (q i))
    (hu : Tendsto (fun i ↦ (T i, q i)) u (𝓝 (T₀, p))) :
    ∃ g₀ : C(AddCircle T₀, M), g₀.Nullhomotopic ∧
      ∀ t : ℝ, g₀ t = flowOf (σ.hamiltonianVectorField F) t p := by
  classical
  set X := σ.hamiltonianVectorField F
  have hX : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
    hσ.contMDiff_hamiltonianVectorField (by simp) (hF.of_le (by simp))
  have : Fact (0 < T₀) := ⟨hT₀⟩
  have := I.stronglyLocallyContractibleSpace
  have := ChartedSpace.stronglyLocallyContractibleSpace H M
  -- The loops `t ↦ flowOf X (t * τ) z` depend continuously on `(τ, z) ∈ W = ℝ × F⁻¹(a, b)`.
  set W : Set (ℝ × M) := univ ×ˢ (F ⁻¹' Ioo a b)
  have hW : IsOpen W := isOpen_univ.prod (isOpen_Ioo.preimage hF.continuous)
  have hΦ : ContinuousOn (fun q : ℝ × M ↦ flowOf X q.1 q.2) W :=
    (contMDiffOn_flowOf le_rfl hX).continuousOn.mono fun q hq ↦
      hσ.mem_flowDomain_hamiltonianVectorField hF hcpt (Ioo_subset_Icc_self hq.2) _
  let G : C(W × unitInterval, M) := ⟨fun q : W × unitInterval ↦ flowOf X (q.2 * q.1.1.1) q.1.1.2,
    hΦ.comp_continuous (f := fun q : W × unitInterval ↦ ((q.2 : ℝ) * q.1.1.1, q.1.1.2))
      (by fun_prop) fun q ↦ ⟨mem_univ _, q.1.2.2⟩⟩
  have hW₀ : (T₀, p) ∈ W := ⟨mem_univ _, hp⟩
  let w (i : ι) : W := if hi : (T i, q i) ∈ W then ⟨_, hi⟩ else ⟨_, hW₀⟩
  have hwev : ∀ᶠ i in u, ((w i : W) : ℝ × M) = (T i, q i) := by
    filter_upwards [hu.eventually (hW.mem_nhds hW₀)] with i hi
    simp only [w]
    split_ifs with h'
    · rfl
    · exact absurd hi h'
  have hw : Tendsto w u (𝓝 ⟨_, hW₀⟩) :=
    tendsto_subtype_rng.2 (hu.congr' (hwev.mono fun _ h ↦ h.symm))
  -- The limit loop, and the convergence of the based loops of the `g i` to its based loop.
  let g₀ : C(AddCircle T₀, M) :=
    ⟨hper.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
      (hΦ.comp_continuous (f := fun t : ℝ ↦ (t, p)) (by fun_prop) fun _ ↦ ⟨mem_univ _, hp⟩)⟩
  have hg₀ (t : ℝ) : g₀ t = flowOf X t p := hper.lift_coe t
  refine ⟨g₀, (ContinuousMap.nullhomotopic_iff_addCircleLoop_homotopic g₀).2 ?_, hg₀⟩
  refine Path.Homotopic.refl_of_tendsto (L := u) (c := fun i ↦ (g i).addCircleLoop) ?_
    (Eventually.of_forall fun i ↦ ?_)
  · refine ((G.curry.continuous.tendsto _).comp hw).congr' ?_ |>.trans (le_of_eq ?_)
    · filter_upwards [hwev] with i hi
      ext t
      simp only [Function.comp_apply, ContinuousMap.curry_apply, ContinuousMap.coe_mk, G,
        Path.coe_toContinuousMap]
      rw [ContinuousMap.addCircleLoop_apply, hi, hgq]
    · congr 1
      ext t
      simp only [ContinuousMap.curry_apply, ContinuousMap.coe_mk, G, Path.coe_toContinuousMap,
        ContinuousMap.addCircleLoop_apply, hg₀]
  · have : Fact (0 < T i) := ⟨hT i⟩
    exact (ContinuousMap.nullhomotopic_iff_addCircleLoop_homotopic (g i)).1 (hg i)

/-- **Closed characteristics on a limit level.** Let `F⁻¹[a, b]` be compact and let `s ∈ (a, b)`
be a regular value of `F`. If levels `F⁻¹(c)` with `c` arbitrarily close to `s` carry closed
characteristics, contractible in `M`, of period at most `K`, then so does the level `F⁻¹(s)`. -/
theorem hasContractibleClosedCharacteristicOfPeriodLE_of_frequently (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b s K : ℝ} (hs : s ∈ Ioo a b)
    (hcpt : IsCompact (F ⁻¹' Icc a b)) (hreg : IsRegularValue I 𝓘(ℝ) F s)
    (h : ∃ᶠ c in 𝓝 s, σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K) :
    σ.HasContractibleClosedCharacteristicOfPeriodLE univ F s K := by
  set X := σ.hamiltonianVectorField F
  have hX : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
    hσ.contMDiff_hamiltonianVectorField (by simp) (hF.of_le (by simp))
  have hFc : Continuous F := hF.continuous
  -- Choose a closed characteristic `γ c` of period `T c ≤ K` on each level `c` of `S`.
  set S := {c | σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K}
  choose T γ hT hTK hγ hper hne hlev g hg hgγ using
    fun c : S ↦ hasContractibleClosedCharacteristicOfPeriodLE_iff.1 c.2
  have hγD (c : S) (t : ℝ) : (t, γ c 0) ∈ flowDomain X := by
    rw [TauCeti.mem_flowDomain, (maximalIntegralCurveInterval_eq_univ_iff hX).2 ⟨γ c, rfl, hγ c⟩]
    exact mem_univ t
  have hret (c : S) : flowOf X (T c) (γ c 0) = γ c 0 := by
    rw [flowOf_eq_of_isMIntegralCurve hX (hγ c), ← zero_add (T c), hper c 0]
  -- Along an ultrafilter of levels tending to `s`, the periods and initial points converge to
  -- some `(T₀, p)`, by compactness of `[0, K] × F⁻¹[a, b]`.
  let L : Filter S := comap Subtype.val (𝓝 s)
  have : L.NeBot := comap_neBot_iff.2 fun t ht ↦ by
    obtain ⟨c, hct, hc⟩ := frequently_iff.1 h ht
    exact ⟨⟨c, hc⟩, hct⟩
  have hLs : Tendsto (Subtype.val : S → ℝ) L (𝓝 s) := tendsto_comap
  have hLmem : ∀ᶠ c in L, (T c, γ c 0) ∈ Icc 0 K ×ˢ (F ⁻¹' Icc a b) := by
    filter_upwards [hLs.eventually (Icc_mem_nhds hs.1 hs.2)] with c hc
    exact ⟨⟨(hT c).le, hTK c⟩, by rw [mem_preimage, hlev c 0]; exact hc⟩
  obtain ⟨⟨T₀, p⟩, ⟨hT₀, -⟩, hcl⟩ := (isCompact_Icc.prod hcpt).exists_clusterPt
    (f := map (fun c ↦ (T c, γ c 0)) L) (le_principal_iff.2 hLmem)
  obtain ⟨u, huL, hu⟩ := mapClusterPt_iff_ultrafilter.1 hcl
  have hTu : Tendsto T u (𝓝 T₀) := (continuous_fst.tendsto _).comp hu
  have hqu : Tendsto (fun c ↦ γ c 0) u (𝓝 p) := (continuous_snd.tendsto _).comp hu
  have hFp : F p = s := tendsto_nhds_unique ((hFc.tendsto p).comp hqu)
    ((hLs.mono_left huL).congr fun c ↦ (hlev c 0).symm)
  have hpab : F p ∈ Ioo a b := hFp ▸ hs
  have hpD (t : ℝ) : (t, p) ∈ flowDomain X :=
    hσ.mem_flowDomain_hamiltonianVectorField hF hcpt (Ioo_subset_Icc_self hpab) t
  -- The trajectory of `p` returns to `p` at time `T₀`, by continuity of the flow at `(T₀, p)`.
  have hTp : flowOf X T₀ p = p := by
    have hΦ : ContinuousAt (fun q : ℝ × M ↦ flowOf X q.1 q.2) (T₀, p) :=
      (contMDiffOn_flowOf le_rfl hX).continuousOn.continuousAt
        ((isOpen_flowDomain hX).mem_nhds (hpD T₀))
    exact tendsto_nhds_unique (hΦ.tendsto.comp hu) (hqu.congr fun c ↦ (hret c).symm)
  -- `X_F` does not vanish at the regular point `p`, so points near `p` do not return to
  -- themselves before some time `τ > 0`; hence `T₀ > 0`.
  obtain ⟨τ, hτ, hnear⟩ := exists_pos_eventually_forall_flowOf_ne hX
    (hσ.hamiltonianVectorField_ne_zero (isRegularValue_iff.1 hreg p hFp))
  have hT₀pos : 0 < T₀ := by
    refine hT₀.1.lt_of_ne fun h0 ↦ ?_
    obtain ⟨c, hc, hcτ⟩ := ((hqu.eventually hnear).and
      (hTu.eventually (gt_mem_nhds (lt_of_eq_of_lt h0.symm hτ)))).exists
    exact hc (T c) ⟨hT c, hcτ⟩ (hγD c _) (hret c)
  -- The trajectory of `p` is a closed characteristic of period `T₀` on the level `s`.
  set γ₀ : ℝ → M := fun t ↦ flowOf X t p
  have hγ₀ : IsMIntegralCurve γ₀ X := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn]
    simpa only [hpD, ofPred_true] using isMIntegralCurveOn_flowOf hX p
  have hγ₀0 : γ₀ 0 = p := flowOf_zero hX p
  have hper₀ : Periodic γ₀ T₀ := fun t ↦ by
    simp only [γ₀]
    rw [add_comm, ← (flowOf_add hX (hpD T₀) (by rw [hTp]; exact hpD t)).2, hTp]
  -- Its loop is null-homotopic, as a limit of the null-homotopic loops of the `γ c`.
  obtain ⟨g₀, hg₀, hg₀γ⟩ := hσ.exists_nullhomotopic_of_tendsto hF hcpt hT₀pos hpab hper₀ hT
    (fun c ↦ (⟨Subtype.val, continuous_subtype_val⟩ : C(univ, M)).comp (g c))
    (fun c ↦ (hg c).comp_right _)
    (fun c t ↦ (hgγ c t).trans (flowOf_eq_of_isMIntegralCurve hX (hγ c) t).symm) hu
  refine hasContractibleClosedCharacteristicOfPeriodLE_iff.2 ⟨T₀, γ₀, hT₀pos, hT₀.2, hγ₀, hper₀,
    ⟨τ / 2, by rw [hγ₀0]; exact hnear.self_of_nhds _ ⟨by positivity, by linarith⟩ (hpD _)⟩,
    fun t ↦ by
      rw [(hσ.isHamiltonianVectorField_hamiltonianVectorField F).apply_eq_of_isMIntegralCurve hγ₀
        (fun _ ↦ hF.mdifferentiableAt (by simp)) 0 t, hγ₀0, hFp],
    (⟨fun q ↦ ⟨q, trivial⟩, by fun_prop⟩ : C(M, univ)).comp g₀, hg₀.comp_right _, hg₀γ⟩

/-- **Almost existence from a finite relative capacity** (Hofer–Zehnder, Struwe). Let `F` have
compact sublevel sets `{F ≤ s}` for `s < b` and take every value in `(a, b)`, and let
`Z ⊆ {F ≤ a}`. If the relative `π₁`-sensitive Hofer–Zehnder capacity `c°_HZ({F < b}, Z)` is
finite, then every level `F⁻¹(c)` with `c ∈ (a, b)` has the contractible almost existence property
in `M`: almost every regular level near it carries a closed characteristic contractible in `M`. -/
theorem hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b c : ℝ}
    (hcpt : ∀ s < b, IsCompact {x | F x ≤ s}) (hrange : Ioo a b ⊆ range F)
    (hZ : Z ⊆ {x | F x ≤ a}) (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞))
    (hc : c ∈ Ioo a b) : σ.HasContractibleAlmostExistence univ F c := by
  refine hasContractibleAlmostExistence_iff.2
    ⟨min (c - a) (b - c), lt_min (sub_pos.2 hc.1) (sub_pos.2 hc.2), ?_⟩
  filter_upwards [hσ.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE hF hcpt
    (by rw [ModelWithCorners.interior_eq_univ]; exact subset_univ _) hrange hZ hcap]
    with s hs hsc hreg
  have hsab : s ∈ Ioo a b := ⟨by linarith [hsc.1, min_le_left (c - a) (b - c)],
    by linarith [hsc.2, min_le_right (c - a) (b - c)]⟩
  obtain ⟨K, hK⟩ := hs hsab
  -- The levels in `[a, (s + b) / 2]` form a compact set.
  have hcpt' : IsCompact (F ⁻¹' Icc a ((s + b) / 2)) :=
    (hcpt _ (by linarith [hsab.2])).of_isClosed_subset (isClosed_Icc.preimage hF.continuous)
      fun x hx ↦ hx.2
  refine (hσ.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently (K := K) hF
    ⟨hsab.1, by linarith [hsab.2]⟩ hcpt' hreg (frequently_iff.2 fun hU ↦ ?_)
    ).hasContractibleClosedCharacteristic
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨c', hc', hchar⟩ := hK (δ / 2) (by positivity)
  refine ⟨c', hball ?_, hchar⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hc'.1, hc'.2]

end IsNondegenerate

end SmoothTwoForm

end TauCeti
