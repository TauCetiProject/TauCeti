/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.BesselPotential.Besov

/-!
# The inclusion `H^{s,p} ⊆ H^{r,p}` of Bessel-potential spaces

For real orders `r ≤ s`, `1 ≤ p ≤ ∞` and a complex Banach space `G`, every tempered distribution
in Mathlib's Bessel-potential space `H^{s,p}(E, G)` lies in `H^{r,p}(E, G)`
(`TemperedDistribution.MemSobolev.of_le`, through the Besov spaces). This file bundles that
inclusion as a continuous linear map `BesselPotentialSpace.inclusion : H^{s,p}(E, G) →L[ℂ]
H^{r,p}(E, G)`, which keeps the underlying tempered distribution.

Its continuity comes from the closed graph theorem rather than from a norm computation: every
`H^{s,p}` embeds continuously in the tempered distributions
(`BesselPotentialSpace.continuous_toDistr`), so a linear map into `H^{s,p}` from a Banach space is
continuous as soon as its composite with this embedding is
(`BesselPotentialSpace.continuous_of_continuous_toDistr`). Taking `r = 0` gives the continuous
inclusion `H^{s,p}(E, G) ⊆ H^{0,p}(E, G) = Lᵖ(E, G)` for `0 ≤ s`.

For `p = 2` and a complex Hilbert space `F` the inclusion `H^s(E, F) ⊆ H^r(E, F)` has norm at most
`1`. This is Plancherel's theorem: the `H^s` norm of `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`
(`BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq`), where `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`,
and `⟨ξ⟩ ^ r 𝓕 u = ⟨ξ⟩ ^ (r - s) ⟨ξ⟩ ^ s 𝓕 u` with `0 < ⟨ξ⟩ ^ (r - s) ≤ 1`.

Compactness properties of the inclusion, such as the Rellich theorem for distributions with a
common compact support, are statements about this map.

## Main declarations

* `BesselPotentialSpace.continuous_toDistr`: `H^{s,p}(E, G)` embeds continuously in `𝓢'(E, G)`.
* `BesselPotentialSpace.continuous_of_continuous_toDistr`: the closed graph criterion for linear
  maps into `H^{s,p}`.
* `BesselPotentialSpace.inclusion`: the inclusion `H^{s,p}(E, G) →L[ℂ] H^{r,p}(E, G)` for
  `r ≤ s`.
* `BesselPotentialSpace.toDistr_inclusion`: it does not change the tempered distribution.
* `BesselPotentialSpace.inclusion_self`, `BesselPotentialSpace.inclusion_inclusion`: the inclusion
  of a space into itself is the identity, and inclusions compose.
* `BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM`: it is the identity on Schwartz
  functions.
* `BesselPotentialSpace.inclusionLp`: the inclusion `H^{s,p}(E, G) →L[ℂ] Lᵖ(E, G)` for `0 ≤ s`,
  with `BesselPotentialSpace.toTemperedDistribution_inclusionLp`.
* `BesselPotentialSpace.norm_inclusion_le`: for `p = 2` its operator norm is at most `1`, and
  `BesselPotentialSpace.norm_le_of_toDistr_eq`: an element of `H^r` with the tempered distribution
  of `u ∈ H^s` has norm at most `‖u‖`.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

namespace BesselPotentialSpace

variable {r s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The underlying tempered distribution of an element of `H^{s,p}(E, G)` depends continuously on
it: it is the Bessel potential of order `-s` of the `Lᵖ` function `toLp u`. -/
theorem continuous_toDistr : Continuous fun u : H^{s, p}(E, G) ↦ u.toDistr := by
  have h := ((besselPotential E G (-s)).comp ((Lp.toTemperedDistributionCLM G volume p).comp
    (toLpₗᵢ E G s p).toContinuousLinearEquiv.toContinuousLinearMap)).continuous
  exact h.congr fun u ↦ by simp

/-- **Closed graph criterion.** A real-linear map `L` from a Banach space into `H^{s,p}(E, G)` is
continuous as soon as `x ↦ (L x).toDistr` is continuous into the tempered distributions. -/
theorem continuous_of_continuous_toDistr {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (L : X →ₗ[ℝ] H^{s, p}(E, G))
    (hL : Continuous fun x ↦ (L x).toDistr) : Continuous L := by
  refine L.continuous_of_seq_closed_graph fun u x y hu hy ↦ ext ?_
  exact tendsto_nhds_unique ((continuous_toDistr.tendsto y).comp hy) ((hL.tendsto x).comp hu)

/-- The inclusion `H^{s,p}(E, G) ⊆ H^{r,p}(E, G)` of Bessel-potential spaces for `r ≤ s`, as a
continuous linear map. It keeps the underlying tempered distribution
(`BesselPotentialSpace.toDistr_inclusion`), and for `p = 2` and a Hilbert space it has norm at most
`1` (`BesselPotentialSpace.norm_inclusion_le`). -/
def inclusion (h : r ≤ s) : H^{s, p}(E, G) →L[ℂ] H^{r, p}(E, G) :=
  let L : H^{s, p}(E, G) →ₗ[ℂ] H^{r, p}(E, G) :=
    { toFun u := (u.memSobolev_toDistr.of_le h).toBesselPotentialSpace
      map_add' u v := ext (by simp)
      map_smul' c u := ext (by simp) }
  { L with
    cont := continuous_of_continuous_toDistr (L.restrictScalars ℝ) <|
      continuous_toDistr.congr fun u ↦ by simp [L] }

@[simp]
theorem toDistr_inclusion (h : r ≤ s) (u : H^{s, p}(E, G)) : (inclusion h u).toDistr = u.toDistr :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- The inclusion of `H^{s,p}` into itself is the identity. -/
@[simp]
theorem inclusion_self (u : H^{s, p}(E, G)) : inclusion le_rfl u = u :=
  ext (by simp)

/-- Inclusions compose: `H^{s,p} ⊆ H^{r,p} ⊆ H^{t,p}` is `H^{s,p} ⊆ H^{t,p}`. -/
@[simp]
theorem inclusion_inclusion {t : ℝ} (h₁ : r ≤ s) (h₂ : t ≤ r) (u : H^{s, p}(E, G)) :
    inclusion h₂ (inclusion h₁ u) = inclusion (h₂.trans h₁) u :=
  ext (by simp)

/-- On Schwartz functions the inclusion `H^{s,p} ⊆ H^{r,p}` is the identity. -/
@[simp]
theorem inclusion_toBesselPotentialSpaceCLM (h : r ≤ s) (u : 𝓢(E, G)) :
    inclusion h (SchwartzMap.toBesselPotentialSpaceCLM s p u) =
      SchwartzMap.toBesselPotentialSpaceCLM r p u :=
  ext (by simp)

/-- The continuous inclusion `H^{s,p}(E, G) ⊆ H^{0,p}(E, G) = Lᵖ(E, G)` for `0 ≤ s`. It sends `u`
to the `Lᵖ` function whose tempered distribution is `u.toDistr`
(`BesselPotentialSpace.toTemperedDistribution_inclusionLp`), unlike `BesselPotentialSpace.toLp`,
which sends `u` to its Bessel potential of order `s`. -/
def inclusionLp (hs : 0 ≤ s) : H^{s, p}(E, G) →L[ℂ] Lp G p (volume : Measure E) :=
  (toLpₗᵢ E G 0 p).toContinuousLinearEquiv.toContinuousLinearMap.comp (inclusion hs)

@[simp]
theorem toTemperedDistribution_inclusionLp (hs : 0 ≤ s) (u : H^{s, p}(E, G)) :
    (inclusionLp hs u : 𝓢'(E, G)) = u.toDistr := by
  simpa [inclusionLp] using besselPotential_neg_toLp_eq (f := inclusion hs u)

section Hilbert

/-- The weighted Fourier transform of `u ∈ H^s` has, at every lower order `r ≤ s`, an `L²`
representative of norm at most `‖u‖`. -/
private theorem exists_smulLeftCLM_fourier_eq_and_norm_le (h : r ≤ s) (u : H^{s}(E, F)) :
    ∃ G : Lp F 2 (volume : Measure E),
      smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) (𝓕 u.toDistr) = G ∧
        ‖G‖ ≤ ‖u‖ := by
  set w : E → ℂ := fun x ↦ (((1 + ‖x‖ ^ 2) ^ ((r - s) / 2) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := by fun_prop
  have hw_le (x : E) : ‖w x‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by simp)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) zero_le_two)
  -- The weighted Fourier transform at order `s` is `𝓕 u.toLp`.
  set G₀ : Lp F 2 (volume : Measure E) := 𝓕 u.toLp
  have hG₀ : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 u.toDistr) =
      G₀ := by
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply, u.bessel_toDistr_eq_toLp,
      Lp.fourier_toTemperedDistribution_eq]
  have hmem : MemLp (fun x ↦ w x • G₀ x) 2 (volume : Measure E) :=
    (Lp.memLp G₀).of_le ((hw.1.continuous.aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable G₀)) (.of_forall fun x ↦ by
        rw [norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hw_le x))
  refine ⟨hmem.toLp, ?_, ?_⟩
  · -- `⟨ξ⟩ ^ r 𝓕 u = ⟨ξ⟩ ^ (r - s) ⟨ξ⟩ ^ s 𝓕 u = w • G₀`.
    have hweight : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) =
        (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) * w := by
      ext x
      simp only [w, Pi.mul_apply, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity :
        (0 : ℝ) < 1 + ‖x‖ ^ 2)]
      congr 2
      ring
    rw [hweight, ← smulLeftCLM_smulLeftCLM_apply
      (g₁ := fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (by fun_prop) hw, hG₀]
    ext φ
    rw [Lp.smulLeftCLM_toTemperedDistribution_apply hw, Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (hmem.coeFn_toLp.mono fun x hx ↦ by simp only [hx])
  · rw [← norm_toLp_eq, ← Lp.norm_fourier_eq u.toLp]
    refine Lp.norm_le_norm_of_ae_le (hmem.coeFn_toLp.mono fun x hx ↦ ?_)
    rw [hx, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw_le x)

/-- For `p = 2` and a Hilbert space, the inclusion `H^s ⊆ H^r` does not increase norms. -/
theorem norm_inclusion_apply_le (h : r ≤ s) (u : H^{s}(E, F)) : ‖inclusion h u‖ ≤ ‖u‖ := by
  obtain ⟨g, hg, hle⟩ := exists_smulLeftCLM_fourier_eq_and_norm_le h u
  refine (norm_eq_of_smulLeftCLM_fourier_eq ?_).trans_le hle
  rwa [toDistr_inclusion]

/-- For `p = 2` and a Hilbert space, the inclusion `H^s ⊆ H^r` has operator norm at most `1`. -/
theorem norm_inclusion_le (h : r ≤ s) : ‖(inclusion h : H^{s}(E, F) →L[ℂ] H^{r}(E, F))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa only [one_mul] using norm_inclusion_apply_le h u

/-- An element of `H^r` with the tempered distribution of `u ∈ H^s`, `r ≤ s`, is the image of `u`
under the inclusion, so its norm is at most `‖u‖`. -/
theorem norm_le_of_toDistr_eq (h : r ≤ s) {u : H^{s}(E, F)} {v : H^{r}(E, F)}
    (huv : u.toDistr = v.toDistr) : ‖v‖ ≤ ‖u‖ := by
  obtain rfl : v = inclusion h u := ext (by rw [toDistr_inclusion, huv])
  exact norm_inclusion_apply_le h u

end Hilbert

end BesselPotentialSpace
