/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.Monotonicity
import TauCeti.Geometry.Manifold.Flow.OrbitLimit
import TauCeti.Geometry.Manifold.RegularValue.Factorization
import TauCeti.Geometry.Symplectic.Hamiltonian.Characteristic

/-!
# Almost existence of closed characteristics from a finite capacity

Let `σ` be a symplectic form on a boundaryless finite-dimensional manifold `M`, and `F : M → ℝ` a
smooth function with compact sublevel sets near the levels under consideration. This file proves
the almost existence theorem of Hofer, Zehnder and Struwe for the `π₁`-sensitive capacities:

* if the relative capacity `c°_HZ({F < b}, Z)` is finite, where `Z ⊆ {F ≤ a}`, then almost every
  regular level `F⁻¹(s)`, `s ∈ (a, b)`, carries a closed characteristic contractible in `M`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`), so that every
  level in `(a, b)` has the contractible almost existence property
  (`IsNondegenerate.hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top`);
* if the capacity `c°_HZ(M)` of the manifold is finite, every nonempty regular level of `F` with
  compact sublevel sets has the contractible almost existence property
  (`IsNondegenerate.hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top`).

The monotonicity argument
(`IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`) gives, for
almost every `s`, closed characteristics of a fixed bounded period on levels arbitrarily close
above `s`. The remaining step is a limit
(`IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`): on a regular
level the Hamiltonian vector field does not vanish, so by the compactness of the nearby levels and
the continuity of the flow these orbits converge, along a subnet, to a closed characteristic of
the level `F⁻¹(s)` itself, of the same bounded period and still contractible in `M`.

## Main results

* `IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`: closed
  characteristics of bounded period on levels converging to a regular level give one on that
  level.
* `TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`: a finite relative
  capacity gives closed characteristics on almost every regular level.
* `IsNondegenerate.hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top`: the
  relative almost existence theorem.
* `IsNondegenerate.hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top`: finiteness of
  `c°_HZ(M)` implies the contractible almost existence property of every nonempty regular level
  with compact sublevel sets.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.3 and §5.
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. 20 (1990), 49–58.
-/

public section

noncomputable section

open Filter Function Metric Set Topology
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {Z : Set M} {F : M → ℝ}

/-- **Closed characteristics on a limit level.** Let `σ` be nondegenerate and `F` smooth, with
`F⁻¹[a, b]` compact, and let `s ∈ (a, b)` be a regular value of `F`. If levels of `F` arbitrarily
close to `s` carry closed characteristics contractible in `M` of period at most `K`, then so does
the level `F⁻¹(s)`. -/
theorem hasContractibleClosedCharacteristicOfPeriodLE_of_frequently (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b s K : ℝ} (hcpt : IsCompact (F ⁻¹' Icc a b))
    (hs : s ∈ Ioo a b) (hreg : IsRegularValue I 𝓘(ℝ) F s)
    (h : ∃ᶠ c in 𝓝 s, σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K) :
    σ.HasContractibleClosedCharacteristicOfPeriodLE univ F s K := by
  have : IsManifold I 2 M := .of_le (n := ∞) (by norm_num)
  have : IsManifold I 1 M := .of_le (n := ∞) (by norm_num)
  set X := σ.hamiltonianVectorField F
  have hX : CMDiff 1 (T% X) :=
    hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (hF.of_le (by norm_num))
  have hXH := hσ.isHamiltonianVectorField_hamiltonianVectorField F
  have hFd (y : M) : MDifferentiableAt I 𝓘(ℝ) F y := (hF y).mdifferentiableAt (by simp)
  -- Index the closed characteristics by their levels, which converge to `s`.
  set S := {c | σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K}
  set l : Filter S := comap Subtype.val (𝓝 s)
  have : l.NeBot := mem_closure_iff_comap_neBot.1 (mem_closure_iff_frequently.2 h)
  have hl : Tendsto (fun i : S ↦ (i : ℝ)) l (𝓝 s) := tendsto_comap
  have hP (i : S) := hasContractibleClosedCharacteristicOfPeriodLE_iff.1 i.2
  choose T γ hT hTK hγ hper hne hlev g hg hgγ using hP
  -- Eventually the initial points lie in `F⁻¹[a, b]` and the periods in `[0, K]`: extract a
  -- convergent subnet.
  have hmem : ∀ᶠ i in l, (γ i 0, T i) ∈ (F ⁻¹' Icc a b) ×ˢ Icc 0 K := by
    filter_upwards [hl.eventually (Icc_mem_nhds hs.1 hs.2)] with i hi
    exact ⟨by rwa [mem_preimage, hlev i 0], (hT i).le, hTK i⟩
  obtain ⟨⟨x, T₀⟩, ⟨-, hT₀K⟩, hclus⟩ :=
    (hcpt.prod isCompact_Icc).exists_mapClusterPt (tendsto_principal.2 hmem)
  set u := fun i ↦ (γ i 0, T i)
  set l' := l ⊓ comap u (𝓝 (x, T₀))
  have : l'.NeBot := inf_neBot_iff.2 fun {p} hp {q} hq ↦ by
    obtain ⟨t, ht, htq⟩ := mem_comap.1 hq
    obtain ⟨i, hit, hip⟩ :=
      ((hclus.frequently (p := (· ∈ t)) ht).and_eventually hp).exists
    exact ⟨i, hip, htq hit⟩
  have hu : Tendsto u l' (𝓝 (x, T₀)) := tendsto_comap.mono_left inf_le_right
  have hx : Tendsto (fun i ↦ γ i 0) l' (𝓝 x) := (continuous_fst.tendsto _).comp hu
  have hTl : Tendsto T l' (𝓝 T₀) := (continuous_snd.tendsto _).comp hu
  -- The limit point lies on the regular level `F⁻¹(s)`, where `X_F` does not vanish.
  have hFx : F x = s := tendsto_nhds_unique ((hF.continuous.tendsto x).comp hx)
    ((hl.mono_left inf_le_left).congr fun i ↦ (hlev i 0).symm)
  have hX0 : X x ≠ 0 := hσ.hamiltonianVectorField_ne_zero (hreg.isRegularPoint hFx)
  -- Its trajectory stays in the compact level `F⁻¹(s)`, so it is defined for all time.
  have hdom (t : ℝ) : (t, x) ∈ flowDomain X := by
    have h0 := zero_mem_maximalIntegralCurveInterval (v := X) (x := x) hX.contMDiffAt
    have hlevel : IsCompact (F ⁻¹' {s}) := hcpt.of_isClosed_subset
      (isClosed_singleton.preimage hF.continuous)
      (preimage_mono (singleton_subset_iff.2 (Ioo_subset_Icc_self hs)))
    have huniv := maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hX h0 hlevel
      fun t ht ↦ by
        rw [mem_preimage, mem_singleton_iff, hXH.apply_eq_of_isMIntegralCurveOn
          isOpen_maximalIntegralCurveInterval isPreconnected_maximalIntegralCurveInterval
          (isMIntegralCurveOn_maximalIntegralCurve hX) (fun _ _ ↦ hFd _) h0 ht,
          maximalIntegralCurve_zero h0, hFx]
    rw [mem_flowDomain, huniv]
    exact mem_univ t
  have hcurve : IsMIntegralCurve (fun t ↦ flowOf X t x) X := by
    have h := isMIntegralCurveOn_flowOf hX x
    rwa [show {t | (t, x) ∈ flowDomain X} = univ from eq_univ_of_forall hdom,
      ← isMIntegralCurve_iff_isMIntegralCurveOn] at h
  -- The limit orbit: positive period, periodic, nonconstant, null-homotopic.
  have hT₀ := pos_of_tendsto_period hX hX0 hγ hper hT hx hTl
  obtain ⟨g₀, hg₀, hg₀x⟩ := exists_nullhomotopic_of_tendsto_period hX hT₀ hdom hγ hper hT hx hTl
    (Eventually.of_forall fun i ↦
      ⟨(⟨Subtype.val, continuous_subtype_val⟩ : C(univ, M)).comp (g i), (hg i).comp_right _,
        hgγ i⟩)
  obtain ⟨δ, hδ, hev⟩ := exists_pos_eventually_flowOf_ne hX hX0
  refine hasContractibleClosedCharacteristicOfPeriodLE_iff.2
    ⟨T₀, fun t ↦ flowOf X t x, hT₀, hT₀K.2, hcurve,
    periodic_flowOf_of_tendsto_period hX hdom hγ hper hx hTl, ⟨δ / 2, ?_⟩, fun t ↦ ?_,
    (⟨fun y ↦ ⟨y, mem_univ y⟩, by fun_prop⟩ : C(M, univ)).comp g₀, hg₀.comp_right _, hg₀x⟩
  · exact fun h ↦ (hev.self_of_nhds (δ / 2) ⟨half_pos hδ, half_lt_self hδ⟩).2
      (h.trans (flowOf_zero hX x))
  · rw [hXH.apply_eq_of_isMIntegralCurve hcurve (fun _ ↦ hFd _) 0 t, flowOf_zero hX, hFx]

/-- **Closed characteristics on almost every level.** Let `σ` be nondegenerate and `F` smooth,
with compact sublevel sets `{F ≤ s}` for `s < b`, let every value in `(a, b)` be attained by `F`,
and let `Z ⊆ {F ≤ a}`. If the relative capacity `c°_HZ({F < b}, Z)` is finite, then almost every
regular level `F⁻¹(s)`, `s ∈ (a, b)`, carries a closed characteristic contractible in `M`. -/
theorem ae_hasContractibleClosedCharacteristic (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s})
    (hrange : Ioo a b ⊆ range F) (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) :
    ∀ᵐ s, s ∈ Ioo a b → IsRegularValue I 𝓘(ℝ) F s →
      σ.HasContractibleClosedCharacteristic univ F s := by
  filter_upwards [hσ.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE hF hcpt
    (by rw [I.interior_eq_univ]; exact subset_univ _) hrange hZ hcap] with s hs hsI hreg
  obtain ⟨K, hK⟩ := hs hsI
  refine (hσ.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently hF (a := a) (K := K)
    (b := (s + b) / 2) ((hcpt _ (by linarith [hsI.2])).of_isClosed_subset
      (isClosed_Icc.preimage hF.continuous) fun _ hx ↦ hx.2)
    ⟨hsI.1, by linarith [hsI.2]⟩ hreg (frequently_iff.2 fun {U} hU ↦ ?_)
    ).hasContractibleClosedCharacteristic
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨c, hc, hcK⟩ := hK (ε / 2) (half_pos hε)
  refine ⟨c, hεU ?_, hcK⟩
  rw [mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hc.1, hc.2]

/-- **The relative almost existence theorem.** Under the hypotheses of
`ae_hasContractibleClosedCharacteristic`, in particular finiteness of `c°_HZ({F < b}, Z)` with
`Z ⊆ {F ≤ a}`, every level `F⁻¹(c)` with `c ∈ (a, b)` has the contractible almost existence
property in `M`. -/
theorem hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b c : ℝ}
    (hcpt : ∀ s < b, IsCompact {x | F x ≤ s}) (hrange : Ioo a b ⊆ range F)
    (hZ : Z ⊆ {x | F x ≤ a}) (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞))
    (hc : c ∈ Ioo a b) : σ.HasContractibleAlmostExistence univ F c := by
  refine hasContractibleAlmostExistence_iff.2
    ⟨min (c - a) (b - c), lt_min (sub_pos.2 hc.1) (sub_pos.2 hc.2), ?_⟩
  filter_upwards [hσ.ae_hasContractibleClosedCharacteristic hF hcpt hrange hZ hcap]
    with c' h hc' hreg
  exact h ⟨by linarith [hc'.1, min_le_left (c - a) (b - c)],
    by linarith [hc'.2, min_le_right (c - a) (b - c)]⟩ hreg

/-- **Finite capacity implies contractible almost existence** (Barraud–Damian–Humilière–Oancea,
Proposition 6.3, after Hofer–Zehnder and Struwe). Let `σ` be nondegenerate, with finite
`π₁`-sensitive Hofer–Zehnder capacity `c°_HZ(M)`, and let `F` be smooth. Every nonempty regular
level `F⁻¹(c)` such that `{F ≤ b}` is compact for some `b > c` has the contractible almost
existence property in `M`. -/
theorem hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (hcap : σ.contractibleHZCapacity univ ≠ (∞ : ℝ≥0∞)) {b c : ℝ} (hcb : c < b)
    (hcpt : IsCompact {x | F x ≤ b}) (hreg : IsRegularValue I 𝓘(ℝ) F c) (hne : ∃ x, F x = c) :
    σ.HasContractibleAlmostExistence univ F c := by
  -- `F` is open at a point of the regular level, so its range contains a neighbourhood of `c`.
  obtain ⟨x, hx⟩ := hne
  have hrange : range F ∈ 𝓝 c := by
    rw [← hx, ← (hreg.isRegularPoint hx).map_nhds_eq (hF x) (by simp)]
    exact mem_of_superset (image_mem_map univ_mem) (image_subset_range F univ)
  obtain ⟨ε, hε, hεr⟩ := Metric.mem_nhds_iff.1 hrange
  set ε' := min ε (b - c)
  have hε' : 0 < ε' := lt_min hε (sub_pos.2 hcb)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'b : ε' ≤ b - c := min_le_right _ _
  have hball : Ioo (c - ε') (c + ε') ⊆ range F := fun r hr ↦ hεr (by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2])
  -- Apply the relative theorem on `(c - ε' / 2, c + ε')` with `Z = {F < c - ε' / 2}`.
  obtain ⟨y, hy⟩ := hball (show c - 3 * ε' / 4 ∈ Ioo (c - ε') (c + ε') from
    ⟨by linarith, by linarith⟩)
  refine hσ.hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top hF
    (a := c - ε' / 2) (b := c + ε') (Z := {y | F y < c - ε' / 2})
    (fun s hs ↦ hcpt.of_isClosed_subset (isClosed_le hF.continuous continuous_const)
      fun z hz ↦ by rw [mem_ofPred_eq] at hz ⊢; linarith)
    ((Ioo_subset_Ioo_left (by linarith)).trans hball)
    (fun _ hz ↦ by rw [mem_ofPred_eq] at hz ⊢; exact hz.le)
    (ne_top_of_le_ne_top hcap (relContractibleHZCapacity_le_contractibleHZCapacity_univ
      (isOpen_lt hF.continuous continuous_const) ⟨y, by rw [mem_ofPred_eq]; linarith⟩))
    ⟨by linarith, by linarith⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
