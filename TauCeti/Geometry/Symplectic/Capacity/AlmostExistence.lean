/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.Monotonicity
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.IntegralCurve.PeriodicLimit
import TauCeti.Geometry.Symplectic.Hamiltonian.Characteristic
import TauCeti.Geometry.Symplectic.Hamiltonian.Complete

/-!
# The Hofer–Zehnder–Struwe almost existence theorem

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless manifold `M` and let
`F : M → ℝ` be smooth.

**Closed characteristics pass to the limit.** If the levels `F⁻¹(c)` carrying a closed
characteristic contractible in `M` of period at most `τ` accumulate at a regular value `s`, and
`F⁻¹([a, b])` is compact for some `a < s < b`, then `F⁻¹(s)` carries such a closed characteristic
(`IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`).
A subsequence of the orbits on the nearby levels has initial points and periods converging, by
compactness of `F⁻¹([a, b]) × [0, τ]`. The limit point `x` lies on `F⁻¹(s)`, where `X_F` does not
vanish since `s` is a regular value, so the limit period is positive and the orbit of `X_F`
through `x` is a nonconstant periodic orbit, whose loop is contractible in `M` as a limit of
contractible loops (`TauCeti.exists_nullhomotopic_of_tendsto`).

**Almost existence.** Let `{F ≤ s}` be compact for `s < b`, let `F` attain every value in
`(a, b)`, and let `Z ⊆ {F ≤ a}`. If the relative `π₁`-sensitive Hofer–Zehnder capacity
`c°_HZ({F < b}, Z)` (`TauCeti.SmoothTwoForm.relContractibleHZCapacity`) is finite, then almost every
regular level of `F` in `(a, b)` carries a closed characteristic contractible in `M`
(`TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`), so every level
in `(a, b)` has the contractible almost existence property
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence`). The Hofer–Zehnder
monotonicity argument gives, near almost every level `s`, closed characteristics of a bounded
period on levels in `[s, s + δ]` for every `δ > 0`
(`IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`); at a regular
level the limit above turns them into a closed characteristic on `F⁻¹(s)` itself. This is the
relative version, on a family of levels, of the almost existence theorem of Hofer–Zehnder and
Struwe (Barraud–Damian–Humilière–Oancea, Proposition 6.3), with contractibility tested in the
ambient manifold.

## Main results

* `IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`: closed
  characteristics of bounded period on levels accumulating at a regular value give one on that
  level.
* `TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`: finiteness of
  the relative capacity gives closed characteristics on almost every regular level.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence`: finiteness of the
  relative capacity gives the contractible almost existence property of every level in `(a, b)`.

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
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {Z : Set M} {F : M → ℝ}

namespace IsNondegenerate

/-- The orbit of the Hamiltonian vector field through a point of a compact level is defined for
all time. -/
private theorem maximalIntegralCurveInterval_eq_univ (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {x : M} (hK : IsCompact {y | F y = F x}) :
    maximalIntegralCurveInterval (σ.hamiltonianVectorField F) x = univ := by
  have hv := hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (hF.of_le (by simp))
  exact maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt) hK fun t ht ↦
      (isFirstIntegral_iff.2 fun y ↦ σ.poissonBracket_self F y).apply_maximalIntegralCurve hσ
        (hF.of_le (by simp)) (hF.mdifferentiable (by simp)) ht

/-- A limit of closed characteristics of period at most `τ`, contractible in `M`, through a regular
point `x` of the level `F⁻¹(s)` whose orbit is defined for all time, is a closed characteristic of
`F⁻¹(s)` of period at most `τ`, contractible in `M`. -/
private theorem hasContractibleClosedCharacteristicOfPeriodLE_of_tendsto
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F) {γ : ℕ → ℝ → M} {T : ℕ → ℝ} {x : M}
    {T₀ s τ : ℝ} (hγ : ∀ n, IsMIntegralCurve (γ n) (σ.hamiltonianVectorField F))
    (hper : ∀ n, Periodic (γ n) (T n)) (hT : ∀ n, 0 < T n)
    (hnull : ∀ n, ∃ g : C(AddCircle (T n), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ n t)
    (hx : Tendsto (fun n ↦ γ n 0) atTop (𝓝 x)) (hTl : Tendsto T atTop (𝓝 T₀))
    (hT₀ : T₀ ∈ Icc 0 τ) (hFx : F x = s) (hreg : IsRegularPoint I 𝓘(ℝ) F x)
    (hglob : maximalIntegralCurveInterval (σ.hamiltonianVectorField F) x = univ) :
    σ.HasContractibleClosedCharacteristicOfPeriodLE univ F s τ := by
  have hv := hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (hF.of_le (by simp))
  have hX := hσ.hamiltonianVectorField_ne_zero hreg
  -- The limit period is positive, since otherwise `x` would be a zero of `X_F`.
  have hpos : 0 < T₀ := hT₀.1.lt_of_ne fun h0 ↦ hX <|
    eq_zero_of_tendsto_of_tendsto_zero hv hγ hper hT hx (h0 ▸ hTl) (by simp [hglob])
  have hint : IsMIntegralCurve (maximalIntegralCurve (σ.hamiltonianVectorField F) x)
      (σ.hamiltonianVectorField F) := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn, ← hglob]
    exact isMIntegralCurveOn_maximalIntegralCurve hv
  have h0 : maximalIntegralCurve (σ.hamiltonianVectorField F) x 0 = x :=
    maximalIntegralCurve_zero (hglob ▸ mem_univ _)
  obtain ⟨g', hg', hg'γ⟩ := exists_nullhomotopic_of_tendsto hv hγ hper hT hnull hx hTl hpos hglob
  rw [hasContractibleClosedCharacteristicOfPeriodLE_iff]
  refine ⟨T₀, _, hpos, hT₀.2, hint, periodic_maximalIntegralCurve_of_tendsto hv hγ hper hx hTl
      hglob, ?_, fun t ↦ ?_, (⟨fun y ↦ ⟨y, mem_univ y⟩, by fun_prop⟩ : C(M, univ)).comp g',
    hg'.comp_right _, fun t ↦ by simp [hg'γ]⟩
  · -- A constant orbit would pass through a zero of `X_F`.
    by_contra! hcon
    have : Nonempty M := ⟨x⟩
    have hz := ((hint.isMIntegralCurveOn univ).isMIntegralCurveAt (t₀ := 0) univ_mem)
      |>.eq_zero_of_eventuallyConst
        (eventuallyConst_iff_exists_eventuallyEq.2 ⟨_, Eventually.of_forall hcon⟩)
    exact hX (h0 ▸ hz)
  · rw [(isFirstIntegral_iff.2 fun y ↦ σ.poissonBracket_self F y).apply_maximalIntegralCurve hσ
      (hF.of_le (by simp)) (hF.mdifferentiable (by simp)) (hglob ▸ mem_univ t), hFx]

/-- **Closed characteristics pass to the limit at a regular level.** Let `F` be smooth with
`F⁻¹([a, b])` compact and let `s ∈ (a, b)` be a regular value of `F`. If levels of `F` carrying a
closed characteristic contractible in `M` of period at most `τ` accumulate at `s`, then the level
`F⁻¹(s)` carries such a closed characteristic. -/
theorem hasContractibleClosedCharacteristicOfPeriodLE_of_frequently (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b s τ : ℝ} (hs : s ∈ Ioo a b)
    (hcpt : IsCompact (F ⁻¹' Icc a b)) (hreg : IsRegularValue I 𝓘(ℝ) F s)
    (h : ∃ᶠ c in 𝓝 s, σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c τ) :
    σ.HasContractibleClosedCharacteristicOfPeriodLE univ F s τ := by
  have : FirstCountableTopology H := I.isClosedEmbedding.isEmbedding.firstCountableTopology
  have : FirstCountableTopology M := ChartedSpace.firstCountableTopology (H := H)
  obtain ⟨c, hc, hcc⟩ := exists_seq_forall_of_frequently h
  simp only [hasContractibleClosedCharacteristicOfPeriodLE_iff] at hcc
  choose T γ hT hTτ hγ hper _ hlev g hg hgγ using hcc
  -- Extract a subsequence whose initial points and periods converge, to `x` and `T₀`.
  have hfreq : ∃ᶠ n in atTop, (γ n 0, T n) ∈ (F ⁻¹' Icc a b) ×ˢ Icc 0 τ :=
    ((hc.eventually (Ioo_mem_nhds hs.1 hs.2)).mono fun n hn ↦
      ⟨by simp [hlev n 0, hn.1.le, hn.2.le], (hT n).le, hTτ n⟩).frequently
  obtain ⟨⟨x, T₀⟩, ⟨-, hT₀⟩, φ, hφ, hlim⟩ := (hcpt.prod isCompact_Icc).tendsto_subseq' hfreq
  have hx : Tendsto (fun k ↦ γ (φ k) 0) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hlim
  have hFx : F x = s := tendsto_nhds_unique ((hF.continuous.tendsto x).comp hx)
    ((hc.comp hφ.tendsto_atTop).congr fun k ↦ (hlev _ 0).symm)
  -- The orbit through `x` stays in the compact level `F⁻¹(s)`, so it is defined for all time.
  have hglob := hσ.maximalIntegralCurveInterval_eq_univ hF (x := x) (hcpt.of_isClosed_subset
    (isClosed_eq hF.continuous continuous_const) fun y (hy : F y = F x) ↦ by
      simp [hy.trans hFx, hs.1.le, hs.2.le])
  exact hσ.hasContractibleClosedCharacteristicOfPeriodLE_of_tendsto hF (fun k ↦ hγ (φ k))
    (fun k ↦ hper (φ k)) (fun k ↦ hT (φ k))
    (fun k ↦ ⟨(ContinuousMap.mk Subtype.val continuous_subtype_val).comp (g (φ k)),
      (hg (φ k)).comp_right _, hgγ (φ k)⟩) hx ((continuous_snd.tendsto _).comp hlim) hT₀ hFx
    (hreg.isRegularPoint hFx) hglob

/-- **Closed characteristics on almost every regular level.** Let `F` be smooth, with compact
sublevel sets `{F ≤ s}` for `s < b`, let every value in `(a, b)` be attained by `F`, and let
`Z ⊆ {F ≤ a}`. If the relative capacity `c°_HZ({F < b}, Z)` is finite, then almost every regular
level of `F` in `(a, b)` carries a closed characteristic contractible in `M`. -/
theorem ae_hasContractibleClosedCharacteristic (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s})
    (hrange : Ioo a b ⊆ range F) (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) :
    ∀ᵐ s, s ∈ Ioo a b → IsRegularValue I 𝓘(ℝ) F s →
      σ.HasContractibleClosedCharacteristic univ F s := by
  filter_upwards [hσ.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE hF hcpt
    (by simp [ModelWithCorners.interior_eq_univ]) hrange hZ hcap] with s hs hsI hreg
  obtain ⟨K, hK⟩ := hs hsI
  -- The levels carrying short closed characteristics accumulate at `s` from above.
  have hfreq : ∃ᶠ c in 𝓝 s, σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K := by
    refine frequently_iff.2 fun hU ↦ ?_
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨c, hc, hcK⟩ := hK (δ / 2) (half_pos hδ)
    refine ⟨c, hδU ?_, hcK⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hc.1, hc.2]
  -- `F⁻¹([a, b'])` is compact for `b' = (s + b) / 2 < b`.
  have hb' : (s + b) / 2 < b := by linarith [hsI.2]
  have hcpt' : IsCompact (F ⁻¹' Icc a ((s + b) / 2)) :=
    (hcpt _ hb').of_isClosed_subset (isClosed_Icc.preimage hF.continuous) fun x hx ↦ hx.2
  exact (hσ.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently hF
    ⟨hsI.1, by linarith [hsI.2]⟩ hcpt' hreg hfreq).hasContractibleClosedCharacteristic

/-- **The Hofer–Zehnder–Struwe almost existence theorem.** Let `F` be smooth, with compact
sublevel sets `{F ≤ s}` for `s < b`, let every value in `(a, b)` be attained by `F`, and let
`Z ⊆ {F ≤ a}`. If the relative capacity `c°_HZ({F < b}, Z)` is finite, then every level `F⁻¹(c)`,
`c ∈ (a, b)`, has the contractible almost existence property in `M`. -/
theorem hasContractibleAlmostExistence (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    {a b c : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s}) (hrange : Ioo a b ⊆ range F)
    (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) (hc : c ∈ Ioo a b) :
    σ.HasContractibleAlmostExistence univ F c := by
  rw [hasContractibleAlmostExistence_iff]
  refine ⟨min (c - a) (b - c), lt_min (by linarith [hc.1]) (by linarith [hc.2]), ?_⟩
  filter_upwards [hσ.ae_hasContractibleClosedCharacteristic hF hcpt hrange hZ hcap] with c' hc'
    hmem
  refine hc' ⟨?_, ?_⟩
  · linarith [hmem.1, min_le_left (c - a) (b - c)]
  · linarith [hmem.2, min_le_right (c - a) (b - c)]

end IsNondegenerate

end SmoothTwoForm

end TauCeti
