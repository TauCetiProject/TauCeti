/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.Monotonicity
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.IntegralCurve.PeriodicLimit
import TauCeti.Geometry.Symplectic.Hamiltonian.Characteristic

/-!
# Almost existence of closed characteristics from a finite relative capacity

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless manifold `M`, let
`F : M → ℝ` be smooth with compact sublevel sets `{F ≤ s}` for `s < b`, and let `Z ⊆ {F ≤ a}`. If
the relative `π₁`-sensitive Hofer–Zehnder capacity `c°_HZ({F < b}, Z)` is finite, then almost
every regular level `F⁻¹(s)`, `s ∈ (a, b)`, carries a closed characteristic contractible in `M`
(`TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`). Every level in
`(a, b)` therefore has the contractible almost existence property in `M`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence`). This is the
Hofer–Zehnder–Struwe almost existence theorem in the relative form in which
Barraud–Damian–Humilière–Oancea apply it near a hypersurface (their Proposition 6.3), where
contractibility is tested in the ambient manifold.

The monotonicity argument gives, for almost every `s ∈ (a, b)`, a bound `K` such that every
interval `[s, s + δ]` contains a level carrying a closed characteristic contractible in `M` of
period at most `K`
(`IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`).
What remains is a compactness argument, carried out here in
`IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`: if levels
arbitrarily close to a regular level `F⁻¹(s)` carry closed characteristics, contractible in `M`, of
period at most `K`, then so does `F⁻¹(s)`. The closed characteristics lie in a compact
sublevel set, so their initial points and periods have a limit `(x, T₀)`, along which they converge
to the integral curve of `X_F` through `x` (`TauCeti.tendsto_maximalIntegralCurve_of_tendsto`).
That curve lies in `F⁻¹(s)`, is `T₀`-periodic, and its loop is contractible
(`TauCeti.exists_nullhomotopic_of_tendsto`). Since `s` is regular, `X_F` does not vanish at `x`,
which rules out a constant limit, and with it the limit period `T₀ = 0`
(`TauCeti.maximalIntegralCurve_eq_of_tendsto_zero`).

## Main results

* `IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`: closed
  characteristics of bounded period on nearby levels give one on a regular level.
* `TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`: a finite
  relative capacity gives closed characteristics on almost every regular level.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence`: a finite relative
  capacity gives the contractible almost existence property.

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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] {σ : SmoothTwoForm I M} {Z : Set M}
  {F : M → ℝ}

namespace IsNondegenerate

/-- **Closed characteristics on a limit level.** Let `F⁻¹(s)` be a regular level of a smooth
function, with `{F ≤ s'}` compact for some `s' > s`. If levels of `F` arbitrarily close to `s`
carry closed characteristics, contractible in `M`, of period at most `K`, then so does
`F⁻¹(s)`. -/
theorem hasContractibleClosedCharacteristicOfPeriodLE_of_frequently (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {s s' K : ℝ} (hss' : s < s') (hcpt : IsCompact {x | F x ≤ s'})
    (hreg : IsRegularValue I 𝓘(ℝ) F s)
    (h : ∃ᶠ c in 𝓝 s, σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K) :
    σ.HasContractibleClosedCharacteristicOfPeriodLE univ F s K := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  set v := σ.hamiltonianVectorField F
  have hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) :=
    hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (hF.of_le (by norm_cast))
  -- Index the closed characteristics by the levels carrying them, approaching `s`.
  let ι := {c : ℝ // σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K}
  let l : Filter ι := comap Subtype.val (𝓝 s)
  have : l.NeBot := comap_neBot_iff_frequently.2 (h.mono fun c hc ↦ ⟨⟨c, hc⟩, rfl⟩)
  have hlim : Tendsto (Subtype.val : ι → ℝ) l (𝓝 s) := tendsto_comap
  choose T γ hT hTK hγ hper hne hlev g hg hgγ using fun i : ι ↦
    hasContractibleClosedCharacteristicOfPeriodLE_iff.1 i.2
  -- They eventually lie in the compact set `{F ≤ s'}`.
  have hmem : ∀ᶠ i in l, ∀ t, γ i t ∈ {x | F x ≤ s'} :=
    (hlim.eventually (eventually_le_nhds hss')).mono fun i hi t ↦ by
      simpa only [mem_ofPred_eq, hlev i t] using hi
  -- Choose a limit `(x, T₀)` of their initial points and periods.
  obtain ⟨⟨x, T₀⟩, -, hclus⟩ := (hcpt.prod (isCompact_Icc (a := 0) (b := K))).exists_mapClusterPt
    (f := l) (u := fun i ↦ (γ i 0, T i)) (le_principal_iff.2 (hmem.mono fun i hi ↦
      ⟨hi 0, (hT i).le, hTK i⟩))
  obtain ⟨U, hUl, hU⟩ := mapClusterPt_iff_ultrafilter.1 hclus
  have hx : Tendsto (fun i ↦ γ i 0) (U : Filter ι) (𝓝 x) := (continuous_fst.tendsto _).comp hU
  have hTU : Tendsto T (U : Filter ι) (𝓝 T₀) := (continuous_snd.tendsto _).comp hU
  have hmemU := hmem.filter_mono hUl
  have hglobal := isMIntegralCurve_maximalIntegralCurve_of_tendsto hv hγ hcpt hmemU hx
  have hconv := tendsto_maximalIntegralCurve_of_tendsto hv hγ hcpt hmemU hx
  set γ₀ := maximalIntegralCurve v x
  have hγ₀ : γ₀ 0 = x :=
    maximalIntegralCurve_zero (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt)
  -- The limit curve lies in the level `F⁻¹(s)`, where `X_F` does not vanish.
  have hlev₀ (t : ℝ) : F (γ₀ t) = s := tendsto_nhds_unique
    ((hF.continuous.tendsto _).comp (hconv t)) ((hlim.mono_left hUl).congr fun i ↦ (hlev i t).symm)
  have hvx : v x ≠ 0 :=
    hσ.hamiltonianVectorField_ne_zero (isRegularValue_iff.1 hreg x (hγ₀ ▸ hlev₀ 0))
  have hnonconst : ∃ t, γ₀ t ≠ γ₀ 0 := by
    by_contra! hcon
    exact hvx (hglobal.eq_zero_of_forall_eq fun t ↦ (hcon t).trans hγ₀)
  -- The limit period is positive, since a vanishing one would make the limit curve constant.
  have hT₀ : 0 < T₀ := by
    refine (ge_of_tendsto hTU (Eventually.of_forall fun i ↦ (hT i).le)).lt_of_ne fun h0 ↦ hvx ?_
    exact hglobal.eq_zero_of_forall_eq
      (maximalIntegralCurve_eq_of_tendsto_zero hv hγ hper hT hcpt hmemU hx (h0 ▸ hTU))
  obtain ⟨g₀, hg₀, hg₀γ⟩ := exists_nullhomotopic_of_tendsto hv hγ hper hT hcpt hmemU hx hTU hT₀
    (Frequently.of_forall fun i ↦ ⟨(ContinuousMap.mk Subtype.val continuous_subtype_val).comp
      (g i), (hg i).comp_right _, hgγ i⟩)
  exact hasContractibleClosedCharacteristicOfPeriodLE_iff.2 ⟨T₀, γ₀, hT₀,
    le_of_tendsto hTU (Eventually.of_forall hTK), hglobal,
    periodic_maximalIntegralCurve_of_tendsto hv hγ hper hcpt hmemU hx hTU, hnonconst, hlev₀,
    (ContinuousMap.mk (fun y : M ↦ (⟨y, mem_univ y⟩ : (univ : Set M)))
      (continuous_id.subtype_mk _)).comp g₀,
    hg₀.comp_right _, hg₀γ⟩

/-- **Closed characteristics on almost every level.** Let `F` be smooth, with compact sublevel
sets `{F ≤ s}` for `s < b`, let every value in `(a, b)` be attained by `F`, and let
`Z ⊆ {F ≤ a}`. If the relative capacity `c°_HZ({F < b}, Z)` is finite, then almost every regular
level `F⁻¹(s)`, `s ∈ (a, b)`, carries a closed characteristic contractible in `M`. -/
theorem ae_hasContractibleClosedCharacteristic (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s})
    (hrange : Ioo a b ⊆ range F) (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) :
    ∀ᵐ s, s ∈ Ioo a b → IsRegularValue I 𝓘(ℝ) F s →
      σ.HasContractibleClosedCharacteristic univ F s := by
  filter_upwards [hσ.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE hF hcpt
    (by simp [ModelWithCorners.interior_eq_univ]) hrange hZ hcap] with s hs hsI hreg
  obtain ⟨K, hK⟩ := hs hsI
  refine (hσ.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently hF
    (s' := (s + b) / 2) (K := K) (by linarith [hsI.2]) (hcpt _ (by linarith [hsI.2])) hreg
    ?_).hasContractibleClosedCharacteristic
  -- Every neighbourhood of `s` contains some `[s, s + δ]`, hence such a level.
  refine frequently_nhds_iff.2 fun V hsV hV ↦ ?_
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hV s hsV
  obtain ⟨c, hc, hP⟩ := hK (δ / 2) (half_pos hδ)
  refine ⟨c, hδV ?_, hP⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hc.1, hc.2]

/-- **Almost existence from a finite relative capacity.** Under the hypotheses of
`ae_hasContractibleClosedCharacteristic`, every level `F⁻¹(c)`, `c ∈ (a, b)`, has the contractible
almost existence property in `M`. -/
theorem hasContractibleAlmostExistence (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s}) (hrange : Ioo a b ⊆ range F)
    (hZ : Z ⊆ {x | F x ≤ a}) (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞))
    {c : ℝ} (hc : c ∈ Ioo a b) : σ.HasContractibleAlmostExistence univ F c := by
  refine hasContractibleAlmostExistence_iff.2
    ⟨min (c - a) (b - c), lt_min (by linarith [hc.1]) (by linarith [hc.2]), ?_⟩
  filter_upwards [hσ.ae_hasContractibleClosedCharacteristic hF hcpt hrange hZ hcap] with s hs hmem
  exact hs ⟨by linarith [hmem.1, min_le_left (c - a) (b - c)],
    by linarith [hmem.2, min_le_right (c - a) (b - c)]⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
