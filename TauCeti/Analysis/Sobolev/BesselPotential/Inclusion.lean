/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# The inclusion `H^s ⊆ H^r` of Bessel-potential spaces

For real orders `r ≤ s` and a complex Hilbert space `F`, every tempered distribution in
Mathlib's Bessel-potential space `H^s(E, F) = H^{s,2}(E, F)` lies in `H^r(E, F)`
(`TemperedDistribution.MemSobolev.mono`). This file bundles that inclusion as a continuous linear
map `BesselPotentialSpace.inclusion : H^s(E, F) →L[ℂ] H^r(E, F)` of norm at most `1`, which keeps
the underlying tempered distribution.

The norm bound is Plancherel's theorem: the `H^s` norm of `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`
(`BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq`), where `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`,
and `⟨ξ⟩ ^ r 𝓕 u = ⟨ξ⟩ ^ (r - s) ⟨ξ⟩ ^ s 𝓕 u` with `0 < ⟨ξ⟩ ^ (r - s) ≤ 1`
(`BesselPotentialSpace.norm_le_mul_norm_of_smulLeftCLM_fourier_eq`).

Compactness properties of the inclusion, such as the Rellich theorem for distributions with a
common compact support, are statements about this map.

## Main declarations

* `BesselPotentialSpace.inclusion`: the inclusion `H^s(E, F) →L[ℂ] H^r(E, F)` for `r ≤ s`.
* `BesselPotentialSpace.toDistr_inclusion`: it does not change the tempered distribution.
* `BesselPotentialSpace.norm_inclusion_le`: its operator norm is at most `1`, and
  `BesselPotentialSpace.norm_le_of_toDistr_eq`: an element of `H^r` with the tempered distribution
  of `u ∈ H^s` has norm at most `‖u‖`.
* `BesselPotentialSpace.norm_inclusion_sq_eq_integral`: the norm of `inclusion h u` on the Fourier
  side.
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

/-- The inclusion `H^s(E, F) ⊆ H^r(E, F)` of Bessel-potential spaces for `r ≤ s`, as a continuous
linear map. It keeps the underlying tempered distribution (`BesselPotentialSpace.toDistr_inclusion`)
and has norm at most `1` (`BesselPotentialSpace.norm_inclusion_le`). -/
def inclusion (h : r ≤ s) : H^{s}(E, F) →L[ℂ] H^{r}(E, F) :=
  LinearMap.mkContinuous
    { toFun u := (u.memSobolev_toDistr.mono h).toBesselPotentialSpace
      map_add' u v := ext (by simp)
      map_smul' c u := ext (by simp) }
    1 fun u ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine norm_le_mul_norm_of_smulLeftCLM_fourier_eq (by fun_prop)
        (norm_one_add_norm_sq_rpow_sub_le h) ?_
      rw [MemSobolev.toBesselPotentialSpace_toDistr, smulLeftCLM_rpow_sub_smulLeftCLM]

@[simp]
theorem toDistr_inclusion (h : r ≤ s) (u : H^{s}(E, F)) : (inclusion h u).toDistr = u.toDistr :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- The `H^r` norm of `u ∈ H^s`, `r ≤ s`, on the Fourier side:
`‖u‖²_{H^r} = ∫ ⟨ξ⟩ ^ (2 (r - s)) ‖𝓕 u.toLp ξ‖² dξ`, where `u.toLp = J^s u` has
`L²` norm `‖u‖_{H^s}`. -/
theorem norm_inclusion_sq_eq_integral (h : r ≤ s) (u : H^{s}(E, F)) :
    ‖inclusion h u‖ ^ 2 =
      ∫ x, (1 + ‖x‖ ^ 2) ^ (r - s) * ‖(𝓕 u.toLp : Lp F 2 (volume : Measure E)) x‖ ^ 2 := by
  rw [norm_sq_eq_integral_of_smulLeftCLM_fourier_eq (u := u) (by fun_prop)
    (norm_one_add_norm_sq_rpow_sub_le h)]
  · refine integral_congr_ae (.of_forall fun x ↦ ?_)
    dsimp only
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    norm_num
  · rw [toDistr_inclusion, smulLeftCLM_rpow_sub_smulLeftCLM]

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
