/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Schwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Delta
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LowPass
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The little Besov spaces

Schwartz functions lie in every inhomogeneous Besov space `B^s_{p,q}`, `q ≠ 0`
(`SchwartzMap.memBesov`, with the inclusion `SchwartzMap.toBesovSpaceCLM`). Their closure in
`B^s_{p,∞}` is the **little Besov space** `b^s_{p,∞}` (`TauCeti.BesovSpace.littleBesov` as a closed
`ℂ`-submodule of `B^s_{p,∞}(E, F)`, and `TemperedDistribution.MemLittleBesov` as an unbundled
predicate on `𝓢'(E, F)`); at `p = ∞` it is the little Hölder–Zygmund space `c^s`, the closure of
the Schwartz functions in `𝒞^s = B^s_{∞,∞}`.

A general element of `B^s_{p,∞}` only has bounded weighted blocks `2^{js} ‖Δⱼ u‖_p`; the elements
of `b^s_{p,∞}` are characterised through their Littlewood–Paley blocks `Δⱼ u`
(`TauCeti.BesovSpace.mem_littleBesov_iff`): `u ∈ b^s_{p,∞}` exactly when

* the weighted blocks vanish at high frequency, `2^{js} ‖Δⱼ u‖_p → 0`, and
* every block `Δⱼ u` lies in the `Lᵖ` closure of the Schwartz functions.

For `p < ∞` the Schwartz functions are dense in `Lᵖ`, so the second condition is automatic:
`b^s_{p,∞}` is cut out by the decay of the weighted blocks alone
(`TauCeti.BesovSpace.mem_littleBesov_iff_tendsto`), equivalently by norm convergence of the dyadic
partial sums `S_N u → u` (`TauCeti.BesovSpace.mem_littleBesov_iff_tendsto_partialSumCLM`), contains
the Bessel-potential space `H^{s,p}` (`BesselPotentialSpace.toBesovSpace_mem_littleBesov`), and
equals the closure in `B^s_{p,∞}` of any higher-regularity space `B^{s'}_{p,q}` with `s < s'`
(`TauCeti.BesovSpace.littleBesov_eq_closure_range_inclusionOfLT`). At `p = ∞` the `L^∞` closure of
the Schwartz functions consists of the classes of the continuous functions vanishing at infinity,
and the second condition is not automatic: the constant function `1` has `Δⱼ 1 = 0` for `j ≥ 1`,
but its block `Δ₀ 1 = 1` does not vanish at infinity.

Because `b^s_{p,∞}` is the closure of compactly supported smooth functions for *all* `1 ≤ p ≤ ∞`
(including `p = ∞`), any continuous semilinear operator between spaces `B^s_{p,∞}` (possibly over
different base spaces) that maps compactly supported Schwartz functions into the target little Besov
space preserves `b^s_{p,∞}` (`TauCeti.BesovSpace.map_mem_littleBesov_of_hasCompactSupport`). In
particular, across the full range `1 ≤ p ≤ ∞`:

* compactly supported smooth functions are dense in `b^s_{p,∞}(E, F)`, and continuous semilinear
  maps out of `b^s_{p,∞}(E, F)` are determined by their values on (compactly supported) Schwartz
  functions (`SchwartzMap.denseRange_toLittleBesovCLM`,
  `TauCeti.BesovSpace.littleBesov_continuousLinearMap_ext`);
* `b^s_{p,∞}` is independent of the Littlewood–Paley bump `φ` up to Banach-space isomorphism
  (`TauCeti.BesovSpace.littleBesovBumpEquiv`), and is preserved by dyadic partial sums
  (`TauCeti.BesovSpace.partialSumCLM_mem_littleBesov_of_mem`), the Besov and Bernstein inclusions,
  fiberwise continuous linear maps (`TauCeti.BesovSpace.postcomp_mem_littleBesov`,
  `TauCeti.BesovSpace.littleBesovPostcompEquiv`), Fourier multipliers and Bessel-potential lifting
  (`TauCeti.BesovSpace.fourierMultiplierCLM_mem_littleBesov`,
  `TauCeti.BesovSpace.littleBesovBesselPotentialEquiv`), and multiplication by smooth functions of
  temperate growth with bounded derivatives up to order `⌊|s|⌋₊ + 1`
  (`TauCeti.BesovSpace.smulLeftCLM_mem_littleBesov`);
* in positive dimension `n ≥ 1`, the Dirac mass satisfies `δ₀ ∈ b^s_{p,∞} ↔ s < -n (1 - 1/p)`
  (`TemperedDistribution.memLittleBesov_delta_zero_iff`), failing at the critical regularity
  `s = -n (1 - 1/p)` where `δ₀ ∈ B^s_{p,∞}`; hence for every `s ∈ ℝ`, `1 ≤ p ≤ ∞` and nontrivial
  `F`, `b^s_{p,∞}(E, F)` is a proper closed subspace of `B^s_{p,∞}(E, F)`
  (`TauCeti.BesovSpace.littleBesov_ne_top`) and `𝓢(E, F)` is not dense in `B^s_{p,∞}(E, F)`
  (`SchwartzMap.not_denseRange_toBesovSpaceCLM_top`).

## Main declarations

* `TauCeti.BesovSpace.littleBesov` and `TemperedDistribution.MemLittleBesov`: the little Besov
  space `b^s_{p,∞}` as a closed `ℂ`-submodule of `B^s_{p,∞}`
  (`TauCeti.BesovSpace.isClosed_littleBesov`, `CompleteSpace`) and as an unbundled predicate on
  `𝓢'(E, F)`.
* `TauCeti.BesovSpace.mem_littleBesov_iff`, `TauCeti.BesovSpace.mem_littleBesov_iff_tendsto`,
  `TauCeti.BesovSpace.mem_littleBesov_iff_tendsto_partialSumCLM`,
  `BesselPotentialSpace.toBesovSpace_mem_littleBesov`, and
  `TauCeti.BesovSpace.littleBesov_eq_closure_range_inclusionOfLT`: characterizations by blocks,
  dyadic partial sums, Sobolev embeddings, and higher-regularity Besov closures.
* `TauCeti.BesovSpace.mem_littleBesov_of_toDistr_eq`: an `Lᵖ` limit of Schwartz functions whose
  blocks vanish from some index on lies in `b^s_{p,∞}`.
* `TauCeti.BesovSpace.block_mem_closure_of_mem_closure_range_toBesovSpaceCLM` and
  `TauCeti.BesovSpace.map_mem_closure_range_toBesovSpaceCLM`: the blocks of a limit of Schwartz
  functions in any `B^s_{p,q}` are `Lᵖ` limits of Schwartz functions, and these limits are stable
  under the maps of the Besov scale that keep the tempered distribution.
* `SchwartzMap.toLittleBesovCLM`, `SchwartzMap.denseRange_toLittleBesovCLM`,
  `SchwartzMap.dense_image_toLittleBesovCLM_hasCompactSupport`, and
  `TauCeti.BesovSpace.littleBesov_continuousLinearMap_ext`: smooth and `C_c^∞` density in
  `b^s_{p,∞}(E, F)` (`1 ≤ p ≤ ∞`).
* `TauCeti.BesovSpace.map_mem_littleBesov_of_hasCompactSupport`,
  `TauCeti.BesovSpace.map_mem_littleBesov_of_toBesovSpaceCLM`,
  `TauCeti.BesovSpace.partialSumCLM_mem_littleBesov_of_mem`,
  `TauCeti.BesovSpace.littleBesovBumpEquiv`, `TauCeti.BesovSpace.littleBesovPostcompEquiv`,
  `TauCeti.BesovSpace.fourierMultiplierCLM_mem_littleBesov`,
  `TauCeti.BesovSpace.littleBesovBesselPotentialEquiv`, and
  `TauCeti.BesovSpace.smulLeftCLM_mem_littleBesov`: invariance and Banach-space isomorphisms across
  the full range `1 ≤ p ≤ ∞`.
* `TemperedDistribution.memLittleBesov_delta_zero_iff`, `TauCeti.BesovSpace.littleBesov_ne_top`,
  and `SchwartzMap.not_denseRange_toBesovSpaceCLM_top`: critical non-membership of `δ₀`, properness
  of `b^s_{p,∞}`, and non-density of `𝓢(E, F)` in `B^s_{p,∞}(E, F)`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2 (Theorem 6.2.3;
  compare Theorem 3.4.2(c) for the real-interpolation closure analogue).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Sections 2.3.2 and 2.3.3.
-/

public section

noncomputable section

open Filter Topology MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

namespace TauCeti.BesovSpace

section Submodule

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The little Besov space -/

variable (F φ s p) in
/-- The **little Besov space** `b^s_{p,∞}`: the closure of the Schwartz functions in
`B^s_{p,∞}`. At `p = ∞` it is the little Hölder–Zygmund space `c^s`. Its isometric inclusion into
`B^s_{p,∞}(E, F)` is `(littleBesov F φ s p).subtypeₗᵢ`. -/
def littleBesov : Submodule ℂ (BesovSpace F φ s p ∞) :=
  (LinearMap.range (SchwartzMap.toBesovSpaceCLM F φ s p ∞).toLinearMap).topologicalClosure

/-- The little Besov space is closed in `B^s_{p,∞}`. -/
instance isClosed_littleBesov : IsClosed (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) :=
  Submodule.isClosed_topologicalClosure _

/-- The little Besov space is complete, as a closed subspace of `B^s_{p,∞}`. -/
instance : CompleteSpace (littleBesov F φ s p) :=
  isClosed_littleBesov.completeSpace_coe

/-- As a set, the little Besov space is the closure of the image of the Schwartz functions. -/
theorem coe_littleBesov : (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) =
    closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p ∞)) := by
  rw [littleBesov, Submodule.topologicalClosure_coe, LinearMap.coe_range,
    ContinuousLinearMap.coe_coe]

/-- **For all `1 ≤ p ≤ ∞`, `b^s_{p,∞}(E, F)` is the closure of compactly supported smooth functions
in `B^s_{p,∞}(E, F)`.** -/
theorem littleBesov_eq_closure_image_hasCompactSupport :
    (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) =
      closure (SchwartzMap.toBesovSpaceCLM F φ s p ∞ ''
        {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) := by
  rw [closure_image_toBesovSpaceCLM_hasCompactSupport, coe_littleBesov]

/-- Schwartz functions lie in the little Besov space. -/
@[simp]
theorem toBesovSpaceCLM_mem_littleBesov (f : 𝓢(E, F)) :
    SchwartzMap.toBesovSpaceCLM F φ s p ∞ f ∈ littleBesov F φ s p :=
  Submodule.le_topologicalClosure _ ⟨f, rfl⟩

/-- **Minimality from compactly supported smooth functions.** The little Besov space is contained in
every closed subspace of `B^s_{p,∞}` containing the compactly supported Schwartz functions. -/
theorem littleBesov_le_of_hasCompactSupport {S : Submodule ℂ (BesovSpace F φ s p ∞)}
    (hS : IsClosed (S : Set (BesovSpace F φ s p ∞)))
    (h : ∀ f : 𝓢(E, F), HasCompactSupport (f : E → F) →
      SchwartzMap.toBesovSpaceCLM F φ s p ∞ f ∈ S) :
    littleBesov F φ s p ≤ S := by
  rw [← SetLike.coe_subset_coe, littleBesov_eq_closure_image_hasCompactSupport]
  refine closure_minimal ?_ hS
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

/-- **Minimality.** The little Besov space is contained in every closed subspace of `B^s_{p,∞}`
containing the Schwartz functions. -/
theorem littleBesov_le {S : Submodule ℂ (BesovSpace F φ s p ∞)}
    (hS : IsClosed (S : Set (BesovSpace F φ s p ∞)))
    (h : ∀ f : 𝓢(E, F), SchwartzMap.toBesovSpaceCLM F φ s p ∞ f ∈ S) :
    littleBesov F φ s p ≤ S :=
  littleBesov_le_of_hasCompactSupport hS fun f _ ↦ h f

/-- **The weighted blocks of an element of `b^s_{p,∞}` vanish at high frequency:**
`2^{js} ‖Δⱼ u‖_p → 0`. -/
theorem tendsto_rpow_mul_norm_block_of_mem_littleBesov {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) :
    Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) := by
  rw [← SetLike.mem_coe, coe_littleBesov] at hu
  refine closure_minimal ?_ isClosed_setOf_tendsto_rpow_mul_norm_block hu
  rintro _ ⟨f, rfl⟩
  simpa only [Set.mem_ofPred_eq, block_toBesovSpaceCLM] using
    tendsto_rpow_mul_norm_block ENNReal.one_ne_top (SchwartzMap.toBesovSpaceCLM F φ s p 1 f)

/-- **The blocks of a limit of Schwartz functions in `B^s_{p,q}` are limits of Schwartz functions
in `Lᵖ`.** -/
theorem block_mem_closure_of_mem_closure_range_toBesovSpaceCLM {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {u : BesovSpace F φ s p q}
    (hu : u ∈ closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p q))) (j : ℕ) :
    u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) := by
  refine map_mem_closure (f := fun x : BesovSpace F φ s p q ↦ x.block j) (continuous_block j) hu ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨_, (block_toBesovSpaceCLM f j).symm⟩

/-- **The blocks of an element of `b^s_{p,∞}` are limits of Schwartz functions in `Lᵖ`.** -/
theorem block_mem_closure_of_mem_littleBesov {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) (j : ℕ) :
    u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) := by
  rw [← SetLike.mem_coe, coe_littleBesov] at hu
  exact block_mem_closure_of_mem_closure_range_toBesovSpaceCLM hu j

/-- **Band-limited limits of Schwartz functions.** Let `v ∈ B^s_{p,∞}` have as tempered
distribution an `Lᵖ` function `w`. If `w` is an `Lᵖ` limit of Schwartz functions and its blocks
`Δₖ w` vanish for `k ≥ M`, then `v` lies in the little Besov space `b^s_{p,∞}`. -/
theorem mem_littleBesov_of_toDistr_eq {v : BesovSpace F φ s p ∞}
    {w : Lp F p (volume : Measure E)} (hvw : v.toDistr = w)
    (hw : w ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p)) {M : ℕ}
    (hM : ∀ k, M ≤ k → littlewoodPaleyBlock F φ k (w : 𝓢'(E, F)) = 0) :
    v ∈ littleBesov F φ s p := by
  obtain ⟨L, hL⟩ := exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock (F := F) φ
  set K : ℝ := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  have hK := exists_littlewoodPaleyLowPass_succ_eq_and_norm_le (F := F) φ (p := p)
  obtain ⟨C, hC0, hC⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq_zero F φ
  -- For a Schwartz function `g` close to `w` in `Lᵖ`, the cut-off `S_{M+1} g` is a Schwartz
  -- function, `S_{M+1} w = w`, and `S_{M+1} (w - g)` has finitely many nonzero blocks, so its
  -- Besov norm is controlled by `‖w - g‖_p`.
  -- `S_{M+1}` fixes `w`.
  have hSw : ∑ j ∈ Finset.range (M + 1), littlewoodPaleyBlock F φ j (w : 𝓢'(E, F)) = w :=
    sum_littlewoodPaleyBlock_eq_self φ _ fun j hj ↦ hM j (Nat.le_of_lt (by simpa using hj))
  rw [← SetLike.mem_coe, coe_littleBesov]
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  set A := 2 ^ (|s| * ((M + L : ℕ) : ℝ)) * C * K
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := Metric.mem_closure_iff.1 hw (ε / (A + 1)) (by positivity)
  rw [dist_eq_norm] at hg
  -- The cut-off `h = S_{M+1} g` is a Schwartz function, and `w - h = S_{M+1} (w - g)`.
  set h : 𝓢(E, F) := ∑ j ∈ Finset.range (M + 1),
    SchwartzMap.fourierMultiplierCLM F (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) g
  obtain ⟨r, hr, hrw⟩ := hK M (w - g.toLp p (volume : Measure E))
  rw [littlewoodPaleyLowPass_apply] at hr
  have hrh : (r : 𝓢'(E, F)) = w - h := by
    rw [← hr, Lp.toTemperedDistribution_sub, Lp.toTemperedDistribution_toLp_eq]
    simp only [map_sub, Finset.sum_sub_distrib, h, map_sum,
      littlewoodPaleyBlock_toTemperedDistributionCLM_eq, hSw]
  obtain ⟨x, hxr, hx⟩ := hC s (M + L) r fun k hk ↦ by
    rw [← hr]
    exact (hL k M).2 hk _
  have hxv : x = v - SchwartzMap.toBesovSpaceCLM F φ s p ∞ h := ext <| by
    rw [hxr, hrh, toDistr_sub, hvw, SchwartzMap.toDistr_toBesovSpaceCLM]
  refine ⟨_, ⟨h, rfl⟩, ?_⟩
  rw [dist_eq_norm, ← hxv]
  calc ‖x‖ ≤ 2 ^ (|s| * ((M + L : ℕ) : ℝ)) * C * ‖r‖ := hx
    _ ≤ 2 ^ (|s| * ((M + L : ℕ) : ℝ)) * C * (K * (ε / (A + 1))) := by
        gcongr
        exact hrw.trans (by gcongr)
    _ = A * (ε / (A + 1)) := by ring
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **The converse.** If the weighted blocks of `u ∈ B^s_{p,∞}` vanish at high frequency and every
block is a limit of Schwartz functions in `Lᵖ`, then `u` lies in the little Besov space. -/
theorem mem_littleBesov_of_tendsto {u : BesovSpace F φ s p ∞}
    (hdecay : Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0))
    (hblock : ∀ j, u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p)) :
    u ∈ littleBesov F φ s p := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_lowPass_eq_zero (F := F) (φ := φ)
  rw [← SetLike.mem_coe]
  refine isClosed_littleBesov.mem_of_tendsto (tendsto_partialSumCLM_top_of_tendsto hdecay)
    (Eventually.of_forall fun N ↦ ?_)
  -- `S_N u` is a band-limited `Lᵖ` limit of Schwartz functions.
  have hvw : (partialSumCLM F φ s p ∞ N u).toDistr = (u.lowPass N : 𝓢'(E, F)) := by
    rw [toDistr_partialSumCLM, coe_lowPass, littlewoodPaleyLowPass_apply]
  exact mem_littleBesov_of_toDistr_eq hvw (lowPass_mem_closure_range_toLp hblock N)
    fun k hk ↦ hL u N k hk

/-- **The little Besov space `b^s_{p,∞}` is cut out by its blocks:** `u` lies in the closure of
the Schwartz functions in `B^s_{p,∞}` exactly when `2^{js} ‖Δⱼ u‖_p → 0` and every block `Δⱼ u` is
a limit of Schwartz functions in `Lᵖ`. -/
theorem mem_littleBesov_iff {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔
      Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) ∧
        ∀ j, u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) :=
  ⟨fun hu ↦ ⟨tendsto_rpow_mul_norm_block_of_mem_littleBesov hu,
    block_mem_closure_of_mem_littleBesov hu⟩, fun h ↦ mem_littleBesov_of_tendsto h.1 h.2⟩

/-- **For `p < ∞`, the little Besov space `b^s_{p,∞}` is cut out by the decay of the weighted
blocks:** `u ∈ b^s_{p,∞}` exactly when `2^{js} ‖Δⱼ u‖_p → 0`, since the Schwartz functions are
dense in `Lᵖ`. -/
theorem mem_littleBesov_iff_tendsto (hp : p ≠ ∞) {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔ Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (F := F) (μ := (volume : Measure E)) hp
  have hcoe : ⇑(SchwartzMap.toLpCLM ℝ F p (volume : Measure E)) = fun f : 𝓢(E, F) ↦ f.toLp p :=
    funext fun _ ↦ SchwartzMap.toLpCLM_apply
  rw [mem_littleBesov_iff, ← hcoe, and_iff_left_iff_imp]
  exact fun _ j ↦ hdense (u.block j)

/-- For every `1 ≤ p ≤ ∞` and `u ∈ b^s_{p,∞}(E, F)`, the dyadic partial sums `S_N u` converge to
`u` in the `B^s_{p,∞}` norm as `N → ∞`. -/
theorem tendsto_partialSumCLM_of_mem_littleBesov {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) :
    Tendsto (fun N ↦ partialSumCLM F φ s p ∞ N u) atTop (𝓝 u) :=
  tendsto_partialSumCLM_top_of_tendsto (tendsto_rpow_mul_norm_block_of_mem_littleBesov hu)

/-- For every `1 ≤ p ≤ ∞` (including `p = ∞`), each dyadic partial sum `S_N` maps
`b^s_{p,∞}(E, F)` into itself. -/
theorem partialSumCLM_mem_littleBesov_of_mem {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) (N : ℕ) :
    partialSumCLM F φ s p ∞ N u ∈ littleBesov F φ s p :=
  littleBesov_le (S := (littleBesov F φ s p).comap (partialSumCLM F φ s p ∞ N).toLinearMap)
    (isClosed_littleBesov.preimage (partialSumCLM F φ s p ∞ N).continuous)
    (fun f ↦ by
      rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe,
        SchwartzMap.partialSumCLM_toBesovSpaceCLM]
      exact toBesovSpaceCLM_mem_littleBesov _) hu

/-- For `1 ≤ p < ∞`, every dyadic partial sum `S_N u` lies in `b^s_{p,∞}(E, F)`. -/
theorem partialSumCLM_mem_littleBesov (hp : p ≠ ∞) (N : ℕ) (u : BesovSpace F φ s p ∞) :
    partialSumCLM F φ s p ∞ N u ∈ littleBesov F φ s p := by
  rw [← SetLike.mem_coe, coe_littleBesov]
  exact partialSumCLM_mem_closure_range_toBesovSpaceCLM hp N u

/-- **Dyadic partial-sum characterization of `b^s_{p,∞}` for `1 ≤ p < ∞`.** An element
`u ∈ B^s_{p,∞}(E, F)` lies in `b^s_{p,∞}(E, F)` if and only if its dyadic partial sums `S_N u`
converge to `u` in the `B^s_{p,∞}` norm as `N → ∞`. -/
theorem mem_littleBesov_iff_tendsto_partialSumCLM (hp : p ≠ ∞) {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔ Tendsto (fun N ↦ partialSumCLM F φ s p ∞ N u) atTop (𝓝 u) := by
  rw [mem_littleBesov_iff_tendsto hp, tendsto_partialSumCLM_top_iff]

end Submodule

section SmoothClosure

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Compactly supported smooth density in `b^s_{p,∞}` -/

/-- Explicit norm approximation in `b^s_{p,∞}(E, F)` (`1 ≤ p ≤ ∞`) by compactly supported Schwartz
functions. -/
theorem exists_hasCompactSupport_norm_sub_lt_of_mem_littleBesov
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(E, F), HasCompactSupport (f : E → F) ∧
      ‖u - SchwartzMap.toBesovSpaceCLM F φ s p ∞ f‖ < ε := by
  rw [← SetLike.mem_coe, littleBesov_eq_closure_image_hasCompactSupport] at hu
  obtain ⟨_, ⟨f, hf, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hu ε hε
  exact ⟨f, hf, by rwa [dist_eq_norm] at hdist⟩

variable (F) in
/-- The continuous linear inclusion of Schwartz functions into the little Besov space
`b^s_{p,∞}(E, F)`. -/
def _root_.SchwartzMap.toLittleBesovCLM (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : 𝓢(E, F) →L[ℂ] littleBesov F φ s p :=
  (SchwartzMap.toBesovSpaceCLM F φ s p ∞).codRestrict (littleBesov F φ s p)
    toBesovSpaceCLM_mem_littleBesov

@[simp]
theorem _root_.SchwartzMap.coe_toLittleBesovCLM_apply (f : 𝓢(E, F)) :
    (SchwartzMap.toLittleBesovCLM F φ s p f : BesovSpace F φ s p ∞) =
      SchwartzMap.toBesovSpaceCLM F φ s p ∞ f :=
  (rfl)

/-- **Schwartz functions are dense in `b^s_{p,∞}(E, F)`** for every `1 ≤ p ≤ ∞` (including the
little Hölder–Zygmund space `c^s` at `p = ∞`). -/
theorem _root_.SchwartzMap.denseRange_toLittleBesovCLM (φ : ContDiffBump (0 : E)) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    DenseRange (SchwartzMap.toLittleBesovCLM (E := E) F φ s p) := by
  rw [SchwartzMap.toLittleBesovCLM]
  exact (SchwartzMap.toBesovSpaceCLM F φ s p ∞).denseRange_codRestrict_topologicalClosure

/-- **Compactly supported smooth functions are dense in `b^s_{p,∞}(E, F)`** for every
`1 ≤ p ≤ ∞`. -/
theorem _root_.SchwartzMap.dense_image_toLittleBesovCLM_hasCompactSupport
    (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Dense (SchwartzMap.toLittleBesovCLM F φ s p ''
      {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) :=
  (SchwartzMap.denseRange_toLittleBesovCLM φ s p).dense_image (map_continuous _)
    SchwartzMap.dense_hasCompactSupport

/-- Continuous semilinear maps out of `b^s_{p,∞}(E, F)` (`1 ≤ p ≤ ∞`) into a Hausdorff space are
determined by their values on compactly supported Schwartz functions. -/
theorem littleBesov_continuousLinearMap_ext_hasCompactSupport {R : Type*} [Semiring R]
    {σ : ℂ →+* R} {Z : Type*} [AddCommMonoid Z] [Module R Z] [TopologicalSpace Z] [T2Space Z]
    {T T' : littleBesov F φ s p →SL[σ] Z}
    (h : ∀ f : 𝓢(E, F), HasCompactSupport (f : E → F) →
      T (SchwartzMap.toLittleBesovCLM F φ s p f) =
        T' (SchwartzMap.toLittleBesovCLM F φ s p f)) :
    T = T' := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  refine (SchwartzMap.dense_image_toLittleBesovCLM_hasCompactSupport φ s p).induction ?_
    (isClosed_eq T.continuous T'.continuous) u
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

/-- Continuous semilinear maps out of `b^s_{p,∞}(E, F)` (`1 ≤ p ≤ ∞`) into a Hausdorff space are
determined by their values on Schwartz functions. -/
theorem littleBesov_continuousLinearMap_ext {R : Type*} [Semiring R] {σ : ℂ →+* R}
    {Z : Type*} [AddCommMonoid Z] [Module R Z] [TopologicalSpace Z] [T2Space Z]
    {T T' : littleBesov F φ s p →SL[σ] Z}
    (h : ∀ f : 𝓢(E, F),
      T (SchwartzMap.toLittleBesovCLM F φ s p f) =
        T' (SchwartzMap.toLittleBesovCLM F φ s p f)) :
    T = T' :=
  littleBesov_continuousLinearMap_ext_hasCompactSupport fun f _ ↦ h f

end SmoothClosure

section Invariance

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The little Besov spaces under embeddings and operators -/

/-- A continuous semilinear map between spaces `B^s_{p,∞}` (possibly over different base spaces)
that sends compactly supported Schwartz functions into the target little Besov space maps
`b^s_{p,∞}(E, F)` into `b^{s'}_{p',∞}(E', G)`. -/
theorem map_mem_littleBesov_of_hasCompactSupport
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E'] {φ' : ContDiffBump (0 : E')} {s' : ℝ} {p' : ℝ≥0∞}
    [Fact (1 ≤ p')] {σ : ℂ →+* ℂ} (T : BesovSpace F φ s p ∞ →SL[σ] BesovSpace G φ' s' p' ∞)
    (hT : ∀ f : 𝓢(E, F), HasCompactSupport (f : E → F) →
      T (SchwartzMap.toBesovSpaceCLM F φ s p ∞ f) ∈ littleBesov G φ' s' p')
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    T u ∈ littleBesov G φ' s' p' := by
  rw [← SetLike.mem_coe, littleBesov_eq_closure_image_hasCompactSupport] at hu
  exact (Set.MapsTo.closure_left (by rintro _ ⟨f, hf, rfl⟩; exact hT f hf)
    T.continuous isClosed_littleBesov) hu

/-- A continuous semilinear map between spaces `B^s_{p,∞}` (possibly over different base spaces)
that sends Schwartz functions into the target little Besov space maps `b^s_{p,∞}(E, F)` into
`b^{s'}_{p',∞}(E', G)`. -/
theorem map_mem_littleBesov_of_toBesovSpaceCLM
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E'] {φ' : ContDiffBump (0 : E')} {s' : ℝ} {p' : ℝ≥0∞}
    [Fact (1 ≤ p')] {σ : ℂ →+* ℂ} (T : BesovSpace F φ s p ∞ →SL[σ] BesovSpace G φ' s' p' ∞)
    (hT : ∀ f : 𝓢(E, F), T (SchwartzMap.toBesovSpaceCLM F φ s p ∞ f) ∈ littleBesov G φ' s' p')
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    T u ∈ littleBesov G φ' s' p' :=
  map_mem_littleBesov_of_hasCompactSupport T (fun f _ ↦ hT f) hu

/-- A continuous linear map between Besov spaces that keeps the underlying tempered distribution
maps limits of Schwartz functions to limits of Schwartz functions. -/
theorem map_mem_closure_range_toBesovSpaceCLM {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {φ' : ContDiffBump (0 : E)} {s' : ℝ} {p' q' : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    (T : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ' s' p' q') (hT : ∀ u, (T u).toDistr = u.toDistr)
    {u : BesovSpace F φ s p q}
    (hu : u ∈ closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p q))) :
    T u ∈ closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ' s' p' q')) := by
  refine map_mem_closure T.continuous hu ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨f, ext (by simp only [hT, SchwartzMap.toDistr_toBesovSpaceCLM])⟩

/-- A continuous linear map between spaces `B^s_{p,∞}` that keeps the underlying tempered
distribution maps the little Besov space into the little Besov space. -/
theorem map_mem_littleBesov {φ' : ContDiffBump (0 : E)} {s' : ℝ} {p' : ℝ≥0∞} [Fact (1 ≤ p')]
    (T : BesovSpace F φ s p ∞ →L[ℂ] BesovSpace F φ' s' p' ∞) (hT : ∀ u, (T u).toDistr = u.toDistr)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) : T u ∈ littleBesov F φ' s' p' := by
  rw [← SetLike.mem_coe, coe_littleBesov] at hu ⊢
  exact map_mem_closure_range_toBesovSpaceCLM T hT hu

/-- `bumpEquiv` maps `b^s_{p,∞}` into `b^s_{p,∞}` for any other bump `φ'`. -/
theorem bumpEquiv_mem_littleBesov (φ' : ContDiffBump (0 : E)) {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) :
    bumpEquiv F φ φ' s p ∞ u ∈ littleBesov F φ' s p := by
  have := map_mem_littleBesov
    (bumpEquiv F φ φ' s p ∞ : BesovSpace F φ s p ∞ →L[ℂ] BesovSpace F φ' s p ∞)
    (fun _ ↦ by simp) hu
  rwa [ContinuousLinearEquiv.coe_coe] at this

/-- **The little Besov space does not depend on the bump function.** -/
@[simp]
theorem bumpEquiv_mem_littleBesov_iff (φ' : ContDiffBump (0 : E)) {u : BesovSpace F φ s p ∞} :
    bumpEquiv F φ φ' s p ∞ u ∈ littleBesov F φ' s p ↔ u ∈ littleBesov F φ s p := by
  refine ⟨fun h ↦ ?_, bumpEquiv_mem_littleBesov φ'⟩
  have h' := bumpEquiv_mem_littleBesov φ h
  rwa [← bumpEquiv_symm, ContinuousLinearEquiv.symm_apply_apply] at h'

variable (F) in
/-- **Equivalence of little Besov norms across Littlewood–Paley partitions.** Two smooth bump
functions `φ` and `φ'` define canonically isomorphic Banach spaces `b^s_{p,∞}`. -/
def littleBesovBumpEquiv (φ φ' : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    littleBesov F φ s p ≃L[ℂ] littleBesov F φ' s p :=
  (bumpEquiv F φ φ' s p ∞).ofSubmodules _ _ <| by
    ext v
    simp [Submodule.mem_map_equiv]

@[simp]
theorem coe_littleBesovBumpEquiv_apply (φ' : ContDiffBump (0 : E)) (u : littleBesov F φ s p) :
    (littleBesovBumpEquiv F φ φ' s p u : BesovSpace F φ' s p ∞) = bumpEquiv F φ φ' s p ∞ u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

@[simp]
theorem _root_.SchwartzMap.littleBesovBumpEquiv_toLittleBesovCLM (φ' : ContDiffBump (0 : E))
    (f : 𝓢(E, F)) :
    littleBesovBumpEquiv F φ φ' s p (SchwartzMap.toLittleBesovCLM F φ s p f) =
      SchwartzMap.toLittleBesovCLM F φ' s p f :=
  Subtype.ext (by simp)

@[simp]
theorem littleBesovBumpEquiv_symm (φ' : ContDiffBump (0 : E)) :
    (littleBesovBumpEquiv F φ φ' s p).symm = littleBesovBumpEquiv F φ' φ s p :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦ Subtype.ext <| by simp [littleBesovBumpEquiv]

/-- **Monotonicity in the smoothness:** `b^s_{p,∞} ⊆ b^{s'}_{p,∞}` for `s' ≤ s`. -/
theorem inclusion_mem_littleBesov {s' : ℝ} (hs : s' ≤ s) {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) : inclusion F φ p hs le_rfl u ∈ littleBesov F φ s' p :=
  map_mem_littleBesov _ (toDistr_inclusion hs le_rfl) hu

/-- For `1 ≤ p < ∞`, `s' ≤ s` and `q < ∞`, the inclusion `B^s_{p,q} → B^{s'}_{p,∞}` lands in
`b^{s'}_{p,∞}`. -/
theorem inclusion_le_top_mem_littleBesov (hp : p ≠ ∞) {s' : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : s' ≤ s) (hq : q ≠ ∞) (u : BesovSpace F φ s p q) :
    inclusion F φ p hs le_top u ∈ littleBesov F φ s' p := by
  rw [mem_littleBesov_iff_tendsto hp]
  simpa only [block_inclusion] using tendsto_rpow_mul_norm_block hq (inclusion F φ p hs le_rfl u)

open scoped BesselPotentialSpace in
/-- **For `1 ≤ p < ∞`, `H^{s,p}(E, F) ⊆ b^s_{p,∞}(E, F)`.** Since Schwartz functions are dense in
`H^{s,p}(E, F)` for `p < ∞` and `BesselPotentialSpace.toBesovSpace φ` is continuous, its range lies
in `b^s_{p,∞}(E, F)`. -/
theorem _root_.BesselPotentialSpace.toBesovSpace_mem_littleBesov (φ : ContDiffBump (0 : E))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (u : H^{s, p}(E, F)) :
    BesselPotentialSpace.toBesovSpace φ u ∈ littleBesov F φ s p := by
  have hu : u ∈ closure (Set.range (SchwartzMap.toBesselPotentialSpaceCLM s p)) :=
    SchwartzMap.denseRange_toBesselPotentialSpaceCLM s hp u
  exact (Set.MapsTo.closure_left
    (by rintro _ ⟨f, rfl⟩; simp [SchwartzMap.toBesovSpace_toBesselPotentialSpaceCLM])
    (BesselPotentialSpace.toBesovSpace φ).continuous isClosed_littleBesov) hu

/-- **The Bernstein embedding of the little Besov spaces:**
`b^s_{p,∞} ⊆ b^{s - n (1/p - 1/r)}_{r,∞}` for `p ≤ r`. -/
theorem inclusionOfExponentLE_mem_littleBesov {r : ℝ≥0∞} [Fact (1 ≤ r)] (hpr : p ≤ r)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    inclusionOfExponentLE F φ ∞ hpr u ∈
      littleBesov F φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r :=
  map_mem_littleBesov _ (toDistr_inclusionOfExponentLE hpr) hu

/-- **A loss of smoothness lands in the little space for `p < ∞`:** `B^s_{p,q} ⊆ b^{s'}_{p,∞}` for
`s' < s`, since the weighted blocks of `B^{s'}_{p,1}` vanish at high frequency. -/
theorem inclusionOfLT_mem_littleBesov (hp : p ≠ ∞) {s' : ℝ} (hs : s' < s) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (u : BesovSpace F φ s p q) :
    inclusionOfLT F φ p q ∞ hs u ∈ littleBesov F φ s' p := by
  rw [mem_littleBesov_iff_tendsto hp]
  simpa only [block_inclusionOfLT] using
    tendsto_rpow_mul_norm_block ENNReal.one_ne_top (inclusionOfLT F φ p q 1 hs u)

/-- **Closure of higher-regularity Besov spaces** (compare Bergh–Löfström, Theorem 3.4.2(c)). For
`1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `s < s'`, the little Besov space `b^s_{p,∞}(E, F)` is the closure in
`B^s_{p,∞}(E, F)` of the image of `B^{s'}_{p,q}(E, F)`. -/
theorem littleBesov_eq_closure_range_inclusionOfLT (hp : p ≠ ∞) {s' : ℝ} (hs : s < s')
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) =
      closure (Set.range (inclusionOfLT F φ p q ∞ hs)) := by
  refine Set.Subset.antisymm (fun u hu ↦ ?_) ?_
  · exact mem_closure_of_tendsto (tendsto_partialSumCLM_of_mem_littleBesov hu)
      (Eventually.of_forall fun N ↦ partialSumCLM_mem_range_inclusionOfLT hs q N u)
  · refine closure_minimal ?_ isClosed_littleBesov
    rintro _ ⟨v, rfl⟩
    exact inclusionOfLT_mem_littleBesov hp hs v

/-- `BesovSpace.postcomp` maps `b^s_{p,∞}(E, F)` into `b^s_{p,∞}(E, G)`. -/
theorem postcomp_mem_littleBesov (L : F →L[ℂ] G) {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) :
    postcomp φ s p ∞ L u ∈ littleBesov G φ s p :=
  map_mem_littleBesov_of_toBesovSpaceCLM (postcomp φ s p ∞ L) (fun f ↦ by
    rw [← SchwartzMap.toBesovSpaceCLM_postcompCLM]
    exact toBesovSpaceCLM_mem_littleBesov _) hu

/-- On Schwartz functions, post-composition in `b^s_{p,∞}` agrees with `SchwartzMap.postcompCLM`. -/
theorem _root_.SchwartzMap.toLittleBesovCLM_postcompCLM (L : F →L[ℂ] G) (f : 𝓢(E, F)) :
    (SchwartzMap.toLittleBesovCLM G φ s p (f.postcompCLM L) : BesovSpace G φ s p ∞) =
      postcomp φ s p ∞ L (SchwartzMap.toLittleBesovCLM F φ s p f) :=
  SchwartzMap.toBesovSpaceCLM_postcompCLM L f

theorem postcompEquiv_mem_littleBesov_iff (e : F ≃L[ℂ] G) {u : BesovSpace F φ s p ∞} :
    postcompEquiv φ s p ∞ e u ∈ littleBesov G φ s p ↔ u ∈ littleBesov F φ s p := by
  refine ⟨fun h ↦ ?_, fun hu ↦ by
    rw [postcompEquiv_apply]; exact postcomp_mem_littleBesov (e : F →L[ℂ] G) hu⟩
  have h' := postcomp_mem_littleBesov (e.symm : G →L[ℂ] F) h
  rwa [← postcompEquiv_apply, ← postcompEquiv_symm, ContinuousLinearEquiv.symm_apply_apply] at h'

@[simp]
theorem postcomp_coe_equiv_mem_littleBesov_iff (e : F ≃L[ℂ] G) {u : BesovSpace F φ s p ∞} :
    postcomp φ s p ∞ (e : F →L[ℂ] G) u ∈ littleBesov G φ s p ↔ u ∈ littleBesov F φ s p := by
  rw [← postcompEquiv_apply, postcompEquiv_mem_littleBesov_iff]

variable (φ s p) in
/-- A continuous linear equivalence `e : F ≃L[ℂ] G` on the fiber induces an isomorphism of little
Besov spaces `b^s_{p,∞}(E, F) ≃L[ℂ] b^s_{p,∞}(E, G)`. -/
def littleBesovPostcompEquiv (e : F ≃L[ℂ] G) :
    littleBesov F φ s p ≃L[ℂ] littleBesov G φ s p :=
  (postcompEquiv φ s p ∞ e).ofSubmodules (littleBesov F φ s p) (littleBesov G φ s p) <| by
    ext v
    simp [Submodule.mem_map_equiv]

@[simp]
theorem coe_littleBesovPostcompEquiv_apply (e : F ≃L[ℂ] G) (u : littleBesov F φ s p) :
    (littleBesovPostcompEquiv φ s p e u : BesovSpace G φ s p ∞) = postcompEquiv φ s p ∞ e u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

@[simp]
theorem _root_.SchwartzMap.littleBesovPostcompEquiv_toLittleBesovCLM (e : F ≃L[ℂ] G)
    (f : 𝓢(E, F)) :
    littleBesovPostcompEquiv φ s p e (SchwartzMap.toLittleBesovCLM F φ s p f) =
      SchwartzMap.toLittleBesovCLM G φ s p (f.postcompCLM (e : F →L[ℂ] G)) :=
  Subtype.ext (by simp [SchwartzMap.toBesovSpaceCLM_postcompCLM])

@[simp]
theorem littleBesovPostcompEquiv_symm (e : F ≃L[ℂ] G) :
    (littleBesovPostcompEquiv φ s p e).symm = littleBesovPostcompEquiv φ s p e.symm :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦ Subtype.ext <| by simp [littleBesovPostcompEquiv]

open scoped ContDiff in
/-- **Fourier multipliers on little Besov spaces.** A smooth symbol `g` of order `m` maps
`b^s_{p,∞}` into `b^{s - m}_{p,∞}` for every `1 ≤ p ≤ ∞`. -/
theorem fourierMultiplierCLM_mem_littleBesov {g : E → ℂ} {m s' : ℝ} (hg : ContDiff ℝ ∞ g)
    (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    (hs : s' = s - m) {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    fourierMultiplierCLM F φ p ∞ hg hgm hs u ∈ littleBesov F φ s' p :=
  map_mem_littleBesov_of_toBesovSpaceCLM (fourierMultiplierCLM F φ p ∞ hg hgm hs)
    (fun f ↦ by simp) hu

/-- `besselPotentialEquiv` maps `b^s_{p,∞}` into `b^{s - t}_{p,∞}` for every `1 ≤ p ≤ ∞`. -/
theorem besselPotentialEquiv_mem_littleBesov (t : ℝ) {s' : ℝ} (hs : s' = s - t)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    besselPotentialEquiv F φ p ∞ t hs u ∈ littleBesov F φ s' p :=
  map_mem_littleBesov_of_toBesovSpaceCLM (besselPotentialEquiv F φ p ∞ t hs).toContinuousLinearMap
    (fun f ↦ by simp) hu

@[simp]
theorem besselPotentialEquiv_mem_littleBesov_iff (t : ℝ) {s' : ℝ} (hs : s' = s - t)
    {u : BesovSpace F φ s p ∞} :
    besselPotentialEquiv F φ p ∞ t hs u ∈ littleBesov F φ s' p ↔ u ∈ littleBesov F φ s p := by
  refine ⟨fun h ↦ ?_, besselPotentialEquiv_mem_littleBesov t hs⟩
  have h' := besselPotentialEquiv_mem_littleBesov (-t)
    (by rw [hs, sub_neg_eq_add, sub_add_cancel]) h
  rwa [← besselPotentialEquiv_symm t hs, ContinuousLinearEquiv.symm_apply_apply] at h'

variable (F φ p) in
/-- **Bessel-potential lifting isomorphism on little Besov spaces.** For `s' = s - t`, `J^t`
restricts to a continuous linear equivalence `b^s_{p,∞}(E, F) ≃L[ℂ] b^{s'}_{p,∞}(E, F)`. -/
def littleBesovBesselPotentialEquiv (t : ℝ) {s s' : ℝ} (hs : s' = s - t) :
    littleBesov F φ s p ≃L[ℂ] littleBesov F φ s' p :=
  (besselPotentialEquiv F φ p ∞ t hs).ofSubmodules _ _ <| by
    ext v
    simp [Submodule.mem_map_equiv]

@[simp]
theorem coe_littleBesovBesselPotentialEquiv_apply (t : ℝ) {s' : ℝ} (hs : s' = s - t)
    (u : littleBesov F φ s p) :
    (littleBesovBesselPotentialEquiv F φ p t hs u : BesovSpace F φ s' p ∞) =
      besselPotentialEquiv F φ p ∞ t hs u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

@[simp]
theorem _root_.SchwartzMap.littleBesovBesselPotentialEquiv_toLittleBesovCLM (t : ℝ) {s' : ℝ}
    (hs : s' = s - t) (f : 𝓢(E, F)) :
    littleBesovBesselPotentialEquiv F φ p t hs (SchwartzMap.toLittleBesovCLM F φ s p f) =
      SchwartzMap.toLittleBesovCLM F φ s' p
        (SchwartzMap.fourierMultiplierCLM F
          (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) f) :=
  Subtype.ext (by simp)

@[simp]
theorem littleBesovBesselPotentialEquiv_symm (t : ℝ) {s' : ℝ} (hs : s' = s - t) :
    (littleBesovBesselPotentialEquiv F φ p t hs).symm =
      littleBesovBesselPotentialEquiv F φ p (-t) (by rw [hs, sub_neg_eq_add, sub_add_cancel]) :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦
    Subtype.ext <| by simp [littleBesovBesselPotentialEquiv]

/-- **Smooth multipliers of little Besov spaces.** Multiplication by a function `g : E → ℂ` of
temperate growth with bounded derivatives up to order `⌊|s|⌋₊ + 1` maps `b^s_{p,∞}(E, F)` into
itself for every `1 ≤ p ≤ ∞`. -/
theorem smulLeftCLM_mem_littleBesov {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    smulLeftCLM F φ s p ∞ g hg hbd u ∈ littleBesov F φ s p :=
  map_mem_littleBesov_of_toBesovSpaceCLM (smulLeftCLM F φ s p ∞ g hg hbd) (fun f ↦ by simp) hu

end Invariance

end TauCeti.BesovSpace

namespace TemperedDistribution

section Predicate

variable (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A tempered distribution `u` lies in the **little Besov space** `b^s_{p,∞}` built from the
Littlewood–Paley partition of `φ` if `u` is the underlying distribution of an element of
`TauCeti.BesovSpace.littleBesov F φ s p` (equivalently, every block `Δⱼ u` is an `Lᵖ` function in
the `Lᵖ` closure of `𝓢(E, F)` and `2^{js} ‖Δⱼ u‖_p → 0`; for `p < ∞` the decay condition alone
suffices). -/
def MemLittleBesov (u : 𝓢'(E, F)) : Prop :=
  ∃ v ∈ TauCeti.BesovSpace.littleBesov F φ s p, v.toDistr = u

variable {φ s p}

@[simp]
theorem _root_.TauCeti.BesovSpace.memLittleBesov_toDistr_iff
    {u : TauCeti.BesovSpace F φ s p ∞} :
    u.toDistr.MemLittleBesov φ s p ↔ u ∈ TauCeti.BesovSpace.littleBesov F φ s p :=
  ⟨fun ⟨_, hv, hvu⟩ ↦ TauCeti.BesovSpace.ext hvu ▸ hv, fun hu ↦ ⟨u, hu, rfl⟩⟩

/-- A tempered distribution `u ∈ B^s_{p,∞}` bundled into `BesovSpace` lies in `littleBesov` if and
only if `u` satisfies `MemLittleBesov`. -/
@[simp]
theorem MemBesov.toBesovSpace_mem_littleBesov_iff {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p ∞) :
    hu.toBesovSpace ∈ TauCeti.BesovSpace.littleBesov F φ s p ↔ u.MemLittleBesov φ s p := by
  rw [← TauCeti.BesovSpace.memLittleBesov_toDistr_iff, hu.toDistr_toBesovSpace]

/-- Every element of the little Besov space `b^s_{p,∞}` lies in `B^s_{p,∞}`. -/
theorem MemLittleBesov.memBesov {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) :
    u.MemBesov φ s p ∞ := by
  obtain ⟨v, -, rfl⟩ := hu
  exact v.memBesov_toDistr

/-- **Block characterization of `MemLittleBesov`.** For every `1 ≤ p ≤ ∞`, `u ∈ b^s_{p,∞}` if and
only if every block `Δⱼ u` is an `Lᵖ` function `fⱼ` in the `Lᵖ` closure of `𝓢(E, F)` and
`2^{js} ‖fⱼ‖_p → 0`. -/
theorem memLittleBesov_iff {u : 𝓢'(E, F)} :
    u.MemLittleBesov φ s p ↔ ∃ f : ℕ → Lp F p (volume : Measure E),
      (∀ j, littlewoodPaleyBlock F φ j u = f j) ∧
        Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) atTop (𝓝 0) ∧
          ∀ j, f j ∈ closure (Set.range fun g : 𝓢(E, F) ↦ g.toLp p) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hdecay, hblock⟩ := TauCeti.BesovSpace.mem_littleBesov_iff.1 hv
    exact ⟨v.block, fun j ↦ (TauCeti.BesovSpace.coe_block v j).symm, hdecay, hblock⟩
  · rintro ⟨f, hf, hdecay, hblock⟩
    have hu : u.MemBesov φ s p ∞ := memBesov_iff.2 ⟨f, hf, memℓp_infty hdecay.norm.bddAbove_range⟩
    have hblk (j : ℕ) : hu.toBesovSpace.block j = f j :=
      Lp.toTemperedDistribution_injective <| by
        simp only [TauCeti.BesovSpace.coe_block, hu.toDistr_toBesovSpace, hf]
    refine hu.toBesovSpace_mem_littleBesov_iff.1
      (TauCeti.BesovSpace.mem_littleBesov_iff.2 ⟨?_, ?_⟩)
    · simpa only [hblk] using hdecay
    · simpa only [hblk] using hblock

/-- **For `1 ≤ p < ∞`, `MemLittleBesov` is cut out by high-frequency decay of the blocks.** -/
theorem memLittleBesov_iff_tendsto (hp : p ≠ ∞) {u : 𝓢'(E, F)} :
    u.MemLittleBesov φ s p ↔ ∃ f : ℕ → Lp F p (volume : Measure E),
      (∀ j, littlewoodPaleyBlock F φ j u = f j) ∧
        Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) atTop (𝓝 0) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (F := F) (μ := (volume : Measure E)) hp
  have hcoe : ⇑(SchwartzMap.toLpCLM ℝ F p (volume : Measure E)) = fun g : 𝓢(E, F) ↦ g.toLp p :=
    funext fun _ ↦ SchwartzMap.toLpCLM_apply
  rw [memLittleBesov_iff, ← hcoe]
  exact exists_congr fun f ↦ and_congr_right fun _ ↦ and_iff_left fun j ↦ hdense (f j)

@[simp]
theorem MemLittleBesov.zero : (0 : 𝓢'(E, F)).MemLittleBesov φ s p :=
  ⟨0, Submodule.zero_mem _, TauCeti.BesovSpace.toDistr_zero⟩

theorem MemLittleBesov.add {u v : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p)
    (hv : v.MemLittleBesov φ s p) : (u + v).MemLittleBesov φ s p := by
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  exact ⟨u' + v', Submodule.add_mem _ hu' hv', TauCeti.BesovSpace.toDistr_add u' v'⟩

theorem MemLittleBesov.smul {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) (c : ℂ) :
    (c • u).MemLittleBesov φ s p := by
  obtain ⟨u', hu', rfl⟩ := hu
  exact ⟨c • u', Submodule.smul_mem _ c hu', TauCeti.BesovSpace.toDistr_smul c u'⟩

theorem MemLittleBesov.neg {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) :
    (-u).MemLittleBesov φ s p := by
  simpa using hu.smul (-1)

theorem MemLittleBesov.sub {u v : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p)
    (hv : v.MemLittleBesov φ s p) : (u - v).MemLittleBesov φ s p := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- Every dyadic partial sum `∑_{j < N} Δⱼ u` of `u ∈ b^s_{p,∞}(E, F)` (`1 ≤ p ≤ ∞`) lies in
`b^s_{p,∞}(E, F)`. -/
theorem MemLittleBesov.sum_littlewoodPaleyBlock {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p)
    (N : ℕ) : (∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u).MemLittleBesov φ s p := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, TauCeti.BesovSpace.partialSumCLM_mem_littleBesov_of_mem hv N,
    TauCeti.BesovSpace.toDistr_partialSumCLM N v⟩

/-- **Monotonicity of little Besov spaces.** For `s' ≤ s`, `b^s_{p,∞} ⊆ b^{s'}_{p,∞}`. -/
theorem MemLittleBesov.mono {u : 𝓢'(E, F)} {s' : ℝ} (hu : u.MemLittleBesov φ s p) (hs : s' ≤ s) :
    u.MemLittleBesov φ s' p := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, TauCeti.BesovSpace.inclusion_mem_littleBesov hs hv,
    TauCeti.BesovSpace.toDistr_inclusion hs le_rfl v⟩

/-- **Independence of the bump function.** A tempered distribution in `b^s_{p,∞}` built from `φ`
lies in `b^s_{p,∞}` built from any other bump function `φ'`. -/
theorem MemLittleBesov.of_bump {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p)
    (φ' : ContDiffBump (0 : E)) : u.MemLittleBesov φ' s p := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, TauCeti.BesovSpace.bumpEquiv_mem_littleBesov φ' hv,
    TauCeti.BesovSpace.toDistr_bumpEquiv φ' v⟩

/-- **Unbundled Bernstein embedding on `MemLittleBesov`.** -/
theorem MemLittleBesov.mono_exponent {u : 𝓢'(E, F)} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hu : u.MemLittleBesov φ s p) (hpr : p ≤ r) :
    u.MemLittleBesov φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, TauCeti.BesovSpace.inclusionOfExponentLE_mem_littleBesov hpr hv,
    TauCeti.BesovSpace.toDistr_inclusionOfExponentLE hpr v⟩

/-- Applying a continuous linear map `L : F →L[ℂ] G` to the values of a distribution in
`b^s_{p,∞}(E, F)` produces a distribution in `b^s_{p,∞}(E, G)`. -/
theorem MemLittleBesov.postcomp {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) (L : F →L[ℂ] G) :
    MemLittleBesov φ s p (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L u : 𝓢'(E, G)) := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, TauCeti.BesovSpace.postcomp_mem_littleBesov L hv,
    TauCeti.BesovSpace.toDistr_postcomp L v⟩

open scoped ContDiff in
/-- **Unbundled Fourier multiplier theorem on `MemLittleBesov`.** -/
theorem MemLittleBesov.fourierMultiplierCLM {g : E → ℂ} {m : ℝ} (hg : ContDiff ℝ ∞ g)
    (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) :
    (TemperedDistribution.fourierMultiplierCLM F g u).MemLittleBesov φ (s - m) p := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, TauCeti.BesovSpace.fourierMultiplierCLM_mem_littleBesov hg hgm rfl hv,
    TauCeti.BesovSpace.toDistr_fourierMultiplierCLM hg hgm rfl v⟩

/-- The Bessel potential `J^t` maps `b^s_{p,∞}` to `b^{s - t}_{p,∞}`. -/
theorem MemLittleBesov.besselPotential {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) (t : ℝ) :
    (besselPotential E F t u).MemLittleBesov φ (s - t) p := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, TauCeti.BesovSpace.besselPotentialEquiv_mem_littleBesov t rfl hv,
    TauCeti.BesovSpace.toDistr_besselPotentialEquiv t rfl v⟩

/-- **The lifting property of little Besov spaces.** `J^t u ∈ b^s_{p,∞}` if and only if
`u ∈ b^{t + s}_{p,∞}`. -/
@[simp]
theorem memLittleBesov_besselPotential_iff {u : 𝓢'(E, F)} {t : ℝ} :
    (besselPotential E F t u).MemLittleBesov φ s p ↔ u.MemLittleBesov φ (t + s) p :=
  ⟨fun h ↦ by simpa [add_comm s t] using h.besselPotential (-t),
    fun hu ↦ by simpa using hu.besselPotential t⟩

/-- **Unbundled smooth multiplier theorem on `MemLittleBesov`.** -/
theorem MemLittleBesov.smulLeftCLM {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) {g : E → ℂ}
    (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    (TemperedDistribution.smulLeftCLM F g u).MemLittleBesov φ s p := by
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨_, TauCeti.BesovSpace.smulLeftCLM_mem_littleBesov hg hbd hv,
    TauCeti.BesovSpace.toDistr_smulLeftCLM hg hbd v⟩

/-- **For `1 ≤ p < ∞`, `H^{s,p}(E, F) ⊆ b^s_{p,∞}(E, F)` on tempered distributions.** -/
theorem MemSobolev.memLittleBesov (hp : p ≠ ∞) {u : 𝓢'(E, F)} (hu : u.MemSobolev s p)
    (φ : ContDiffBump (0 : E)) : u.MemLittleBesov φ s p :=
  ⟨BesselPotentialSpace.toBesovSpace φ hu.toBesselPotentialSpace,
    BesselPotentialSpace.toBesovSpace_mem_littleBesov φ hp hu.toBesselPotentialSpace, by simp⟩

/-- **For `1 ≤ p < ∞`, every `B^s_{p,q}` with `q < ∞` lies in `b^s_{p,∞}`.** -/
theorem MemBesov.memLittleBesov_of_ne_top (hp : p ≠ ∞) {u : 𝓢'(E, F)} {q : ℝ≥0∞}
    (hu : u.MemBesov φ s p q) (hq : q ≠ ∞) : u.MemLittleBesov φ s p := by
  have : Fact (1 ≤ max q 1) := ⟨le_max_right q 1⟩
  have hmax : max q 1 ≠ ∞ := (max_lt_iff.2 ⟨hq.lt_top, ENNReal.one_lt_top⟩).ne
  have hu' : u.MemBesov φ s p (max q 1) := hu.mono le_rfl (le_max_left q 1)
  exact ⟨_, TauCeti.BesovSpace.inclusion_le_top_mem_littleBesov hp le_rfl hmax hu'.toBesovSpace,
    by simp⟩

/-- **Strict order inclusion into little Besov spaces for `1 ≤ p < ∞`.** For `s' < s` and *every*
fine index `q` (including `q = ∞`), `B^s_{p,q} ⊆ b^{s'}_{p,∞}`. -/
theorem MemBesov.memLittleBesov_of_lt (hp : p ≠ ∞) {u : 𝓢'(E, F)} {s' : ℝ} {q : ℝ≥0∞}
    (hu : u.MemBesov φ s p q) (hs : s' < s) : u.MemLittleBesov φ s' p :=
  (hu.of_lt hs one_ne_zero).memLittleBesov_of_ne_top hp ENNReal.one_ne_top

end Predicate

end TemperedDistribution

namespace SchwartzMap

/-- Every Schwartz function lies in every little Besov space `b^s_{p,∞}` (`1 ≤ p ≤ ∞`). -/
theorem memLittleBesov (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : 𝓢(E, F)) :
    (f : 𝓢'(E, F)).MemLittleBesov φ s p :=
  ⟨toBesovSpaceCLM F φ s p ∞ f, TauCeti.BesovSpace.toBesovSpaceCLM_mem_littleBesov f,
    toDistr_toBesovSpaceCLM φ s p ∞ f⟩

end SchwartzMap

section DiracAndNonDensity

open Module

/-- **At the critical regularity `s = -n (1 - 1/p)`, the Dirac mass does not lie in `b^s_{p,∞}`**
in positive dimension `n ≥ 1` (`1 ≤ p ≤ ∞`): its weighted Littlewood–Paley block norms for `j ≥ 1`
are a nonzero constant independent of `j`, whereas `δ₀ ∈ B^s_{p,∞}` by
`TemperedDistribution.memBesov_delta_zero`. -/
theorem TemperedDistribution.not_memLittleBesov_delta_zero [Nontrivial E]
    (φ : ContDiffBump (0 : E)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ¬ (delta (0 : E)).MemLittleBesov φ (-(finrank ℝ E * (1 - p.toReal⁻¹))) p := by
  set m : ℝ := finrank ℝ E * (1 - p.toReal⁻¹)
  set f : ℕ → Lp ℂ p (volume : Measure E) :=
    fun j ↦ (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).toLp p
  have hc : 0 < ‖f 1‖ :=
    φ.norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_pos 1
      (zero_lt_one.trans_le Fact.out).ne'
  have hconst (j : ℕ) : (2 : ℝ) ^ (-m * (j + 1 : ℕ)) * ‖f (j + 1)‖ = 2 ^ (-m) * ‖f 1‖ := by
    simpa [f, m, neg_add_cancel] using
      φ.rpow_mul_norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_succ (-m) j p
  intro hu
  obtain ⟨g, hg, ht, -⟩ := memLittleBesov_iff.1 hu
  have hgf : g = f := funext fun j ↦ Lp.toTemperedDistribution_injective
    (by dsimp only; rw [← hg j, littlewoodPaleyBlock_delta_zero_eq_toLp φ j p])
  rw [hgf] at ht
  have ht' : Tendsto (fun _ : ℕ ↦ (2 : ℝ) ^ (-m) * ‖f 1‖) atTop (𝓝 0) :=
    (ht.comp (tendsto_add_atTop_nat 1)).congr hconst
  have hzero : (2 : ℝ) ^ (-m) * ‖f 1‖ = 0 := tendsto_nhds_unique tendsto_const_nhds ht'
  linarith [mul_pos (Real.rpow_pos_of_pos two_pos (-m)) hc]

/-- **Exact little-Besov regularity of the Dirac mass.** On a finite-dimensional real inner product
space of positive dimension `n ≥ 1`, for every `1 ≤ p ≤ ∞` (including `p = ∞`), `δ₀ ∈ b^s_{p,∞}` if
and only if `s < -n (1 - 1/p)` (with `1/∞ = 0`). -/
theorem TemperedDistribution.memLittleBesov_delta_zero_iff [Nontrivial E]
    (φ : ContDiffBump (0 : E)) {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (delta (0 : E)).MemLittleBesov φ s p ↔ s < -(finrank ℝ E * (1 - p.toReal⁻¹)) := by
  refine ⟨fun hu ↦ ?_, fun hs ↦ ?_⟩
  · by_contra! hle
    exact not_memLittleBesov_delta_zero φ p (hu.mono hle)
  · -- Below the critical exponent, `δ₀ ∈ B^s_{p,1}` so its weighted blocks tend to zero, and every
    -- block `𝓕⁻ ψⱼ` is already a Schwartz function (even at `p = ∞`).
    have h1 : (delta (0 : E)).MemBesov φ s p 1 :=
      (memBesov_delta_zero_iff φ one_ne_zero).2 (Or.inl hs)
    set v : TauCeti.BesovSpace ℂ φ s p 1 := h1.toBesovSpace
    refine memLittleBesov_iff.2 ⟨v.block, fun j ↦ ?_,
      TauCeti.BesovSpace.tendsto_rpow_mul_norm_block ENNReal.one_ne_top v, fun j ↦ ?_⟩
    · rw [← h1.toDistr_toBesovSpace, ← TauCeti.BesovSpace.coe_block]
    · refine subset_closure ⟨𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j),
        Lp.toTemperedDistribution_injective ?_⟩
      dsimp only
      rw [TauCeti.BesovSpace.coe_block, h1.toDistr_toBesovSpace,
        littlewoodPaleyBlock_delta_zero_eq_toLp φ j p]

namespace TauCeti.BesovSpace

/-- **The little Besov space is a proper subspace of `B^s_{p,∞}(E, F)`** for every smoothness order
`s : ℝ` and every `1 ≤ p ≤ ∞` whenever `E` and `F` are nontrivial. -/
theorem littleBesov_ne_top [Nontrivial E] [Nontrivial F] (φ : ContDiffBump (0 : E)) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    littleBesov F φ s p ≠ ⊤ := by
  -- Shift `δ₀` from `-n (1 - 1/p)` to order `s` via `besselPotentialEquiv`, then embed `ℂ` as a
  -- complemented summand of `F` via Hahn–Banach.
  set s₀ : ℝ := -(finrank ℝ E * (1 - p.toReal⁻¹))
  let u₀ : BesovSpace ℂ φ s₀ p ∞ := (memBesov_delta_zero φ p).toBesovSpace
  have hu₀ : u₀ ∉ littleBesov ℂ φ s₀ p :=
    (memBesov_delta_zero φ p).toBesovSpace_mem_littleBesov_iff.not.2
      (not_memLittleBesov_delta_zero φ p)
  let u₁ : BesovSpace ℂ φ s p ∞ := besselPotentialEquiv ℂ φ p ∞ (s₀ - s) (by ring) u₀
  have hu₁ : u₁ ∉ littleBesov ℂ φ s p := by
    rwa [besselPotentialEquiv_mem_littleBesov_iff]
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  obtain ⟨ℓ, -, hℓv⟩ := exists_dual_vector (𝕜 := ℂ) v hvn
  let ι : ℂ →L[ℂ] F := ContinuousLinearMap.toSpanSingleton ℂ (((‖v‖ : ℂ)⁻¹) • v)
  have hcomp : ℓ.comp ι = ContinuousLinearMap.id ℂ ℂ := by
    ext1
    simp [ι, hℓv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hvn)]
  intro htop
  have hmem : postcomp φ s p ∞ ι u₁ ∈ littleBesov F φ s p := htop ▸ Submodule.mem_top
  have hback := postcomp_mem_littleBesov ℓ hmem
  rw [postcomp_postcomp, hcomp, postcomp_id, ContinuousLinearMap.id_apply] at hback
  exact hu₁ hback

/-- **Schwartz functions are NOT dense in `B^s_{p,∞}(E, F)`** in positive dimension with nontrivial
fiber, for any `s ∈ ℝ` and any `1 ≤ p ≤ ∞`: their closure in `B^s_{p,∞}(E, F)` is the proper
subspace `b^s_{p,∞}(E, F)`. -/
theorem _root_.SchwartzMap.not_denseRange_toBesovSpaceCLM_top [Nontrivial E] [Nontrivial F]
    (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ¬ DenseRange (SchwartzMap.toBesovSpaceCLM (E := E) F φ s p ∞) := by
  rw [denseRange_iff_closure_range, ← coe_littleBesov]
  exact fun h ↦ littleBesov_ne_top (F := F) φ s p (SetLike.ext' h)

end TauCeti.BesovSpace

end DiracAndNonDensity
