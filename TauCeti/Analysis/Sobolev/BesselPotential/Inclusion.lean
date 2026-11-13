/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The inclusion `H^s ⊆ H^r` of Bessel-potential spaces

For real orders `r ≤ s` and a complex Hilbert space `F`, every tempered distribution in
Mathlib's Bessel-potential space `H^s(E, F) = H^{s,2}(E, F)` lies in `H^r(E, F)`
(`TemperedDistribution.MemSobolev.mono`). This file bundles that inclusion as a continuous linear
map `BesselPotentialSpace.inclusion : H^s(E, F) →L[ℂ] H^r(E, F)` of norm at most `1`, which keeps
the underlying tempered distribution.

The norm bound is Plancherel's theorem: the `H^s` norm of `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`
(`BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq`), where `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`,
and `⟨ξ⟩ ^ r 𝓕 u = ⟨ξ⟩ ^ (r - s) ⟨ξ⟩ ^ s 𝓕 u` with `0 < ⟨ξ⟩ ^ (r - s) ≤ 1`.

Compactness properties of the inclusion, such as the Rellich theorem for distributions with a
common compact support, are statements about this map.

## Main declarations

* `BesselPotentialSpace.inclusion`: the inclusion `H^s(E, F) →L[ℂ] H^r(E, F)` for `r ≤ s`.
* `BesselPotentialSpace.toDistr_inclusion`: it does not change the tempered distribution.
* `BesselPotentialSpace.norm_inclusion_le`: its operator norm is at most `1`, and
  `BesselPotentialSpace.norm_le_of_toDistr_eq`: an element of `H^r` with the tempered distribution
  of `u ∈ H^s` has norm at most `‖u‖`.
* `BesselPotentialSpace.inclusion_self`, `BesselPotentialSpace.inclusion_inclusion`: the inclusion
  of a space into itself is the identity, and inclusions compose.
* `BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM`: it is the identity on Schwartz
  functions.
* `BesselPotentialSpace.inclusion_injective`, `BesselPotentialSpace.toLp_inclusion_injective`: it
  is injective, and an element is determined by the `L²` function of its inclusion.
* `BesselPotentialSpace.coeFn_toLp_inclusion_add`, `BesselPotentialSpace.coeFn_toLp_inclusion_smul`:
  the `L²` function of the inclusion is additive and homogeneous almost everywhere.
* `BesselPotentialSpace.toTemperedDistribution_toLp_inclusion`: for `s ≥ 0`, the inclusion into
  `H^0(E, F) = L²` exhibits every element of `H^s(E, F)` as an `L²` function, which lies in `H^s`
  (`BesselPotentialSpace.memSobolev_toLp_inclusion`) and defines `u` again
  (`BesselPotentialSpace.toBesselPotentialSpace_memSobolev_toLp_inclusion`).
* `BesselPotentialSpace.toLp_inclusion_toBesselPotentialSpace`: for `s ≥ 0`, the `L²` function of
  the element of `H^s(E, F)` defined by an `L²` function `g` is `g`.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace BesselPotentialSpace

variable {r s : ℝ}

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

/-- The inclusion `H^s(E, F) ⊆ H^r(E, F)` of Bessel-potential spaces for `r ≤ s`, as a continuous
linear map. It keeps the underlying tempered distribution (`BesselPotentialSpace.toDistr_inclusion`)
and has norm at most `1` (`BesselPotentialSpace.norm_inclusion_le`). -/
def inclusion (h : r ≤ s) : H^{s}(E, F) →L[ℂ] H^{r}(E, F) :=
  LinearMap.mkContinuous
    { toFun u := (u.memSobolev_toDistr.mono h).toBesselPotentialSpace
      map_add' u v := ext (by simp)
      map_smul' c u := ext (by simp) }
    1 fun u ↦ by
      obtain ⟨G, hG, hle⟩ := exists_smulLeftCLM_fourier_eq_and_norm_le h u
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      refine (norm_eq_of_smulLeftCLM_fourier_eq ?_).trans_le hle
      rwa [MemSobolev.toBesselPotentialSpace_toDistr]

@[simp]
theorem toDistr_inclusion (h : r ≤ s) (u : H^{s}(E, F)) : (inclusion h u).toDistr = u.toDistr :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- The inclusion `H^s ⊆ H^r` has operator norm at most `1`. -/
theorem norm_inclusion_le (h : r ≤ s) : ‖(inclusion h : H^{s}(E, F) →L[ℂ] H^{r}(E, F))‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The inclusion `H^s ⊆ H^r` does not increase norms. -/
theorem norm_inclusion_apply_le (h : r ≤ s) (u : H^{s}(E, F)) : ‖inclusion h u‖ ≤ ‖u‖ := by
  simpa only [one_mul] using (inclusion h).le_of_opNorm_le (norm_inclusion_le h) u

/-- An element of `H^r` with the tempered distribution of `u ∈ H^s`, `r ≤ s`, is the image of `u`
under the inclusion, so its norm is at most `‖u‖`. -/
theorem norm_le_of_toDistr_eq (h : r ≤ s) {u : H^{s}(E, F)} {v : H^{r}(E, F)}
    (huv : u.toDistr = v.toDistr) : ‖v‖ ≤ ‖u‖ := by
  obtain rfl : v = inclusion h u := ext (by rw [toDistr_inclusion, huv])
  exact norm_inclusion_apply_le h u

/-- The inclusion of `H^s` into itself is the identity. -/
@[simp]
theorem inclusion_self (u : H^{s}(E, F)) : inclusion le_rfl u = u :=
  ext (by simp)

/-- Inclusions compose: `H^s ⊆ H^r ⊆ H^t` is `H^s ⊆ H^t`. -/
@[simp]
theorem inclusion_inclusion {t : ℝ} (h₁ : r ≤ s) (h₂ : t ≤ r) (u : H^{s}(E, F)) :
    inclusion h₂ (inclusion h₁ u) = inclusion (h₂.trans h₁) u :=
  ext (by simp)

/-- On Schwartz functions the inclusion `H^s ⊆ H^r` is the identity. -/
@[simp]
theorem inclusion_toBesselPotentialSpaceCLM (h : r ≤ s) (u : 𝓢(E, F)) :
    inclusion h (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM r 2 u :=
  ext (by simp)

/-- The inclusion `H^s ⊆ H^r` is injective. -/
theorem inclusion_injective (h : r ≤ s) :
    Function.Injective (inclusion h : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) := fun u v huv ↦
  ext (by rw [← toDistr_inclusion h u, huv, toDistr_inclusion])

/-- An element of `H^s(E, F)` is determined by the `L²` function of its inclusion into `H^r(E, F)`.
For `r = 0` this is the `L²` function of the element itself
(`toTemperedDistribution_toLp_inclusion`). -/
theorem toLp_inclusion_injective (h : r ≤ s) :
    Function.Injective fun u : H^{s}(E, F) ↦ (inclusion h u).toLp :=
  (injective_toLp E F r 2).comp (inclusion_injective h)

/-- The `L²` function of the inclusion of `u + v` is almost everywhere the sum of those of `u`
and `v`. -/
theorem coeFn_toLp_inclusion_add (h : r ≤ s) (u v : H^{s}(E, F)) :
    ⇑(inclusion h (u + v)).toLp =ᵐ[volume] ⇑(inclusion h u).toLp + ⇑(inclusion h v).toLp := by
  rw [map_add, toLp_add]
  exact Lp.coeFn_add _ _

/-- The `L²` function of the inclusion of `c • u` is almost everywhere `c` times that of `u`. -/
theorem coeFn_toLp_inclusion_smul (h : r ≤ s) (c : ℂ) (u : H^{s}(E, F)) :
    ⇑(inclusion h (c • u)).toLp =ᵐ[volume] c • ⇑(inclusion h u).toLp := by
  rw [map_smul, toLp_smul]
  exact Lp.coeFn_smul _ _

/-- **Elements of `H^s`, `s ≥ 0`, are `L²` functions.** The `L²` function underlying the
inclusion of `u ∈ H^s(E, F)` into `H^0(E, F)` has the tempered distribution `u`. -/
@[simp]
theorem toTemperedDistribution_toLp_inclusion (h : 0 ≤ s) (u : H^{s}(E, F)) :
    ((inclusion h u).toLp : 𝓢'(E, F)) = u := by
  rw [← (inclusion h u).bessel_toDistr_eq_toLp]
  simp [besselPotential_zero]

/-- For `s ≥ 0`, the `L²` function of `u ∈ H^s(E, F)` lies in `H^s`. -/
theorem memSobolev_toLp_inclusion (h : 0 ≤ s) (u : H^{s}(E, F)) :
    MemSobolev s 2 ((inclusion h u).toLp : 𝓢'(E, F)) := by
  rw [toTemperedDistribution_toLp_inclusion]
  exact u.memSobolev_toDistr

/-- For `s ≥ 0`, the element of `H^s(E, F)` defined by the `L²` function of `u ∈ H^s(E, F)` is
`u`. -/
theorem toBesselPotentialSpace_memSobolev_toLp_inclusion (h : 0 ≤ s) (u : H^{s}(E, F)) :
    (memSobolev_toLp_inclusion h u).toBesselPotentialSpace = u :=
  ext (by simp)

/-- For `s ≥ 0`, the `L²` function of the element of `H^s(E, F)` defined by an `L²` function `g`
is `g`. -/
theorem toLp_inclusion_toBesselPotentialSpace (h : 0 ≤ s) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    {g : Lp F 2 (volume : Measure E)} (hg : (g : 𝓢'(E, F)) = f) :
    (inclusion h hf.toBesselPotentialSpace).toLp = g := by
  refine LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot ?_
  simp [hg]

end BesselPotentialSpace
