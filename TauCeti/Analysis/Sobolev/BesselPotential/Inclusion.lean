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
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

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
(`BesselPotentialSpace.continuous_of_continuous_toDistr`). The same argument restricts every
continuous linear operator `A` on tempered distributions that maps `H^{s,p}(E, G)` into
`H^{r,p}(E, G')` to a bounded operator between these spaces (`BesselPotentialSpace.mapCLM`); the
inclusion is the restriction of the identity. Taking `r = 0` gives the continuous
inclusion `H^{s,p}(E, G) ⊆ H^{0,p}(E, G) = Lᵖ(E, G)` for `0 ≤ s`.

For `p = 2` and a complex Hilbert space `F` the inclusion `H^s(E, F) ⊆ H^r(E, F)` has norm at most
`1`. This is Plancherel's theorem: the `H^s` norm of `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`
(`BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq`), where `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`,
and `⟨ξ⟩ ^ r 𝓕 u = ⟨ξ⟩ ^ (r - s) ⟨ξ⟩ ^ s 𝓕 u` with `0 < ⟨ξ⟩ ^ (r - s) ≤ 1`. The same computation
bounds every Fourier multiplier `H^s → H^r` whose symbol `g` satisfies
`‖g ξ‖ ⟨ξ⟩ ^ r ≤ C ⟨ξ⟩ ^ s` (`BesselPotentialSpace.norm_le_of_toDistr_eq_fourierMultiplierCLM`).

Compactness properties of the inclusion, such as the Rellich theorem for distributions with a
common compact support, are statements about this map.

## Main declarations

* `BesselPotentialSpace.continuous_toLp`: the `Lᵖ` function `J^s u` depends continuously on `u`.
* `BesselPotentialSpace.continuous_toDistr`: `H^{s,p}(E, G)` embeds continuously in `𝓢'(E, G)`.
* `BesselPotentialSpace.continuous_of_continuous_toDistr`: the closed graph criterion for linear
  maps into `H^{s,p}`.
* `BesselPotentialSpace.mapCLM`: the restriction `H^{s,p}(E, G) →L[ℂ] H^{r,p}(E, G')` of an
  operator on tempered distributions that maps `H^{s,p}` into `H^{r,p}`.
* `BesselPotentialSpace.inclusion`: the inclusion `H^{s,p}(E, G) →L[ℂ] H^{r,p}(E, G)` for
  `r ≤ s`.
* `BesselPotentialSpace.toDistr_inclusion`: it does not change the tempered distribution, and
  `BesselPotentialSpace.inclusion_injective`: it is injective.
* `BesselPotentialSpace.inclusion_self`, `BesselPotentialSpace.inclusion_inclusion`: the inclusion
  of a space into itself is the identity, and inclusions compose.
* `BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM`: it is the identity on Schwartz
  functions.
* `BesselPotentialSpace.inclusionLp`: the inclusion `H^{s,p}(E, G) →L[ℂ] Lᵖ(E, G)` for `0 ≤ s`,
  characterised by `BesselPotentialSpace.toTemperedDistribution_inclusionLp` and
  `BesselPotentialSpace.inclusionLp_eq_iff`, and injective
  (`BesselPotentialSpace.inclusionLp_injective`; a.e. form
  `BesselPotentialSpace.ext_of_ae_eq_inclusionLp`). Its normal forms are
  `BesselPotentialSpace.toLp_inclusion`, `BesselPotentialSpace.inclusionLp_zero`,
  `BesselPotentialSpace.inclusionLp_inclusion` and
  `BesselPotentialSpace.inclusionLp_toBesselPotentialSpaceCLM`.
* `BesselPotentialSpace.toLp_inclusion_injective`: an element is determined by the `Lᵖ` function
  of its inclusion, and `BesselPotentialSpace.coeFn_toLp_inclusion_add`,
  `BesselPotentialSpace.coeFn_toLp_inclusion_smul`: that function is additive and homogeneous
  almost everywhere; `BesselPotentialSpace.coeFn_inclusionLp_add_ae_eq`,
  `BesselPotentialSpace.coeFn_inclusionLp_sub_ae_eq` and
  `BesselPotentialSpace.coeFn_inclusionLp_smul_ae_eq` compute the `Lᵖ` function of a sum,
  difference or multiple from those of its terms.
* `BesselPotentialSpace.toTemperedDistribution_toLp_inclusion`: for `s ≥ 0`, the inclusion into
  `H^{0,p}(E, G) = Lᵖ` exhibits every element of `H^{s,p}(E, G)` as an `Lᵖ` function, which lies
  in `H^{s,p}` (`BesselPotentialSpace.memSobolev_inclusionLp`) and defines `u` again
  (`BesselPotentialSpace.toBesselPotentialSpace_memSobolev_inclusionLp`).
* `BesselPotentialSpace.toLp_inclusion_toBesselPotentialSpace`: for `s ≥ 0`, the `Lᵖ` function of
  the element of `H^{s,p}(E, G)` defined by an `Lᵖ` function `g` is `g`.
* `BesselPotentialSpace.coeFn_fourier_toLp_inclusion`: for `p = 2`, on the Fourier side the
  inclusion `H^s ⊆ H^r` is multiplication by `⟨ξ⟩ ^ (r - s)`.
* `BesselPotentialSpace.norm_inclusion_le`, `BesselPotentialSpace.norm_inclusionLp_le`: for `p = 2`
  the operator norms of `inclusion` and `inclusionLp` are at most `1`, and
  `BesselPotentialSpace.norm_le_of_toDistr_eq`: an element of `H^r` with the tempered distribution
  of `u ∈ H^s` has norm at most `‖u‖`.
* `BesselPotentialSpace.norm_le_of_toDistr_eq_fourierMultiplierCLM`: for `p = 2`, the norm bound
  `‖v‖ ≤ C ‖u‖` when `v ∈ H^r` is the image of `u ∈ H^s` under a Fourier multiplier with symbol
  bounded by `C ⟨ξ⟩ ^ (s - r)`.
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

/-- The `Lᵖ` function `J^s u` of an element `u` of `H^{s,p}(E, G)` depends continuously on it. -/
@[fun_prop]
theorem continuous_toLp : Continuous fun u : H^{s, p}(E, G) ↦ u.toLp :=
  (toLpₗᵢ E G s p).continuous.congr toLpₗᵢ_apply

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

section mapCLM

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℂ G'] [CompleteSpace G']

/-- **Restriction of an operator on tempered distributions to Bessel-potential spaces.** A
continuous linear map `A : 𝓢'(E, G) →L[ℂ] 𝓢'(E, G')` that maps `H^{s,p}(E, G)` into
`H^{r,p}(E, G')` restricts to a bounded operator between these spaces; its continuity is the
closed graph theorem. The restriction keeps the action of `A` on the underlying tempered
distributions (`BesselPotentialSpace.toDistr_mapCLM`). -/
def mapCLM (A : 𝓢'(E, G) →L[ℂ] 𝓢'(E, G'))
    (hA : ∀ u : H^{s, p}(E, G), MemSobolev r p (A u.toDistr)) :
    H^{s, p}(E, G) →L[ℂ] H^{r, p}(E, G') :=
  let L : H^{s, p}(E, G) →ₗ[ℂ] H^{r, p}(E, G') :=
    { toFun u := (hA u).toBesselPotentialSpace
      map_add' u v := ext (by simp)
      map_smul' c u := ext (by simp) }
  { L with
    cont := continuous_of_continuous_toDistr (L.restrictScalars ℝ) <|
      (A.continuous.comp continuous_toDistr).congr fun u ↦ by simp [L] }

/-- `mapCLM A hA` acts on the underlying tempered distributions by `A`. -/
@[simp]
theorem toDistr_mapCLM (A : 𝓢'(E, G) →L[ℂ] 𝓢'(E, G'))
    (hA : ∀ u : H^{s, p}(E, G), MemSobolev r p (A u.toDistr)) (u : H^{s, p}(E, G)) :
    (mapCLM A hA u).toDistr = A u.toDistr :=
  MemSobolev.toBesselPotentialSpace_toDistr _

end mapCLM

/-- The inclusion `H^{s,p}(E, G) ⊆ H^{r,p}(E, G)` of Bessel-potential spaces for `r ≤ s`, as a
continuous linear map: the restriction `BesselPotentialSpace.mapCLM` of the identity of `𝓢'(E, G)`.
It keeps the underlying tempered distribution (`BesselPotentialSpace.toDistr_inclusion`), and for
`p = 2` and a Hilbert space it has norm at most `1` (`BesselPotentialSpace.norm_inclusion_le`). -/
def inclusion (h : r ≤ s) : H^{s, p}(E, G) →L[ℂ] H^{r, p}(E, G) :=
  mapCLM (.id ℂ _) fun u ↦ u.memSobolev_toDistr.of_le h

@[simp]
theorem toDistr_inclusion (h : r ≤ s) (u : H^{s, p}(E, G)) : (inclusion h u).toDistr = u.toDistr :=
  toDistr_mapCLM _ _ u

/-- The inclusion `H^{s,p} ⊆ H^{r,p}` is injective. -/
theorem inclusion_injective (h : r ≤ s) :
    Function.Injective (inclusion h : H^{s, p}(E, G) → H^{r, p}(E, G)) := fun u v huv ↦
  ext (by simpa using congrArg toDistr huv)

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

/-- On `H^{0,p}` the `Lᵖ` part `toLp` has tempered distribution `u.toDistr`. -/
@[simp]
theorem toTemperedDistribution_toLp_zero (u : H^{0, p}(E, G)) :
    (u.toLp : 𝓢'(E, G)) = u.toDistr := by
  simpa using besselPotential_neg_toLp_eq (f := u)

/-- `inclusionLp hs u` is the `Lᵖ` function whose tempered distribution is `u.toDistr`. -/
theorem inclusionLp_eq_iff (hs : 0 ≤ s) {u : H^{s, p}(E, G)} {f : Lp G p (volume : Measure E)} :
    inclusionLp hs u = f ↔ (f : 𝓢'(E, G)) = u.toDistr := by
  refine ⟨fun h ↦ h ▸ toTemperedDistribution_inclusionLp hs u, fun h ↦ ?_⟩
  refine LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot ?_
  simp [h]

/-- The inclusion `H^{s,p} ⊆ Lᵖ` is injective. -/
theorem inclusionLp_injective (hs : 0 ≤ s) :
    Function.Injective (inclusionLp hs : H^{s, p}(E, G) → Lp G p (volume : Measure E)) :=
  fun u v huv ↦ ext (by rw [← toTemperedDistribution_inclusionLp hs, huv,
    toTemperedDistribution_inclusionLp])

/-- Two elements of `H^{s,p}` whose `Lᵖ` functions agree almost everywhere are equal. -/
theorem ext_of_ae_eq_inclusionLp (hs : 0 ≤ s) {u v : H^{s, p}(E, G)}
    (huv : inclusionLp hs u =ᵐ[volume] inclusionLp hs v) : u = v :=
  inclusionLp_injective hs (Lp.ext huv)

/-- The `Lᵖ` part of the inclusion of `u` in `H^{0,p}` is the inclusion of `u` into `Lᵖ`. -/
@[simp]
theorem toLp_inclusion (hs : 0 ≤ s) (u : H^{s, p}(E, G)) :
    (inclusion hs u).toLp = inclusionLp hs u := by
  simp [inclusionLp]

/-- On `H^{0,p}` the inclusion into `Lᵖ` is the `Lᵖ` part `toLp`. -/
@[simp]
theorem inclusionLp_zero (u : H^{0, p}(E, G)) : inclusionLp le_rfl u = u.toLp := by
  rw [← toLp_inclusion, inclusion_self]

/-- The inclusion into `Lᵖ` of an included element is the inclusion of the original element. -/
@[simp]
theorem inclusionLp_inclusion (h : r ≤ s) (hr : 0 ≤ r) (u : H^{s, p}(E, G)) :
    inclusionLp hr (inclusion h u) = inclusionLp (hr.trans h) u := by
  rw [← toLp_inclusion, inclusion_inclusion, toLp_inclusion]

/-- On Schwartz functions the inclusion `H^{s,p} ⊆ Lᵖ` is the inclusion of `𝓢` into `Lᵖ`. -/
@[simp]
theorem inclusionLp_toBesselPotentialSpaceCLM (hs : 0 ≤ s) (u : 𝓢(E, G)) :
    inclusionLp hs (SchwartzMap.toBesselPotentialSpaceCLM s p u) = u.toLp p := by
  simp only [inclusionLp, ContinuousLinearMap.comp_apply, inclusion_toBesselPotentialSpaceCLM,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, toLpₗᵢ_apply]
  exact SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero u

/-- An element of `H^{s,p}(E, G)` is determined by the `Lᵖ` function of its inclusion into
`H^{r,p}(E, G)`. For `r = 0` this is the inclusion into `Lᵖ` (`toLp_inclusion`). -/
theorem toLp_inclusion_injective (h : r ≤ s) :
    Function.Injective fun u : H^{s, p}(E, G) ↦ (inclusion h u).toLp :=
  (injective_toLp E G r p).comp (inclusion_injective h)

/-- The `Lᵖ` function of the inclusion of `u + v` is almost everywhere the sum of those of `u`
and `v`. -/
theorem coeFn_toLp_inclusion_add (h : r ≤ s) (u v : H^{s, p}(E, G)) :
    ⇑(inclusion h (u + v)).toLp =ᵐ[volume] ⇑(inclusion h u).toLp + ⇑(inclusion h v).toLp := by
  rw [map_add, toLp_add]
  exact Lp.coeFn_add _ _

/-- The `Lᵖ` function of the inclusion of `u - v` is almost everywhere the difference of those of
`u` and `v`. -/
theorem coeFn_toLp_inclusion_sub (h : r ≤ s) (u v : H^{s, p}(E, G)) :
    ⇑(inclusion h (u - v)).toLp =ᵐ[volume] ⇑(inclusion h u).toLp - ⇑(inclusion h v).toLp := by
  rw [map_sub, toLp_sub]
  exact Lp.coeFn_sub _ _

/-- The `Lᵖ` function of the inclusion of `-u` is almost everywhere the negative of that of
`u`. -/
theorem coeFn_toLp_inclusion_neg (h : r ≤ s) (u : H^{s, p}(E, G)) :
    ⇑(inclusion h (-u)).toLp =ᵐ[volume] -⇑(inclusion h u).toLp := by
  rw [map_neg, toLp_neg]
  exact Lp.coeFn_neg _

/-- The `Lᵖ` function of the inclusion of `c • u` is almost everywhere `c` times that of `u`. -/
theorem coeFn_toLp_inclusion_smul (h : r ≤ s) (c : ℂ) (u : H^{s, p}(E, G)) :
    ⇑(inclusion h (c • u)).toLp =ᵐ[volume] c • ⇑(inclusion h u).toLp := by
  rw [map_smul, toLp_smul]
  exact Lp.coeFn_smul _ _

/-- If the `Lᵖ` functions of `u` and `v` are almost everywhere `F` and `F'`, then that of `u + v`
is almost everywhere `F + F'`. -/
theorem coeFn_inclusionLp_add_ae_eq (hs : 0 ≤ s) {u v : H^{s, p}(E, G)} {F F' : E → G}
    (hu : ⇑(inclusionLp hs u) =ᵐ[volume] F) (hv : ⇑(inclusionLp hs v) =ᵐ[volume] F') :
    ⇑(inclusionLp hs (u + v)) =ᵐ[volume] fun z ↦ F z + F' z := by
  rw [map_add]
  exact (Lp.coeFn_add _ _).trans (hu.add hv)

/-- If the `Lᵖ` functions of `u` and `v` are almost everywhere `F` and `F'`, then that of `u - v`
is almost everywhere `F - F'`. -/
theorem coeFn_inclusionLp_sub_ae_eq (hs : 0 ≤ s) {u v : H^{s, p}(E, G)} {F F' : E → G}
    (hu : ⇑(inclusionLp hs u) =ᵐ[volume] F) (hv : ⇑(inclusionLp hs v) =ᵐ[volume] F') :
    ⇑(inclusionLp hs (u - v)) =ᵐ[volume] fun z ↦ F z - F' z := by
  rw [map_sub]
  exact (Lp.coeFn_sub _ _).trans (hu.sub hv)

/-- If the `Lᵖ` function of `u` is almost everywhere `F`, then that of `-u` is almost everywhere
`-F`. -/
theorem coeFn_inclusionLp_neg_ae_eq (hs : 0 ≤ s) {u : H^{s, p}(E, G)} {F : E → G}
    (hu : ⇑(inclusionLp hs u) =ᵐ[volume] F) :
    ⇑(inclusionLp hs (-u)) =ᵐ[volume] fun z ↦ -F z := by
  rw [map_neg]
  exact (Lp.coeFn_neg _).trans hu.neg

/-- If the `Lᵖ` function of `u` is almost everywhere `F`, then that of `c • u` is almost everywhere
`c • F`. -/
theorem coeFn_inclusionLp_smul_ae_eq (hs : 0 ≤ s) (c : ℂ) {u : H^{s, p}(E, G)} {F : E → G}
    (hu : ⇑(inclusionLp hs u) =ᵐ[volume] F) :
    ⇑(inclusionLp hs (c • u)) =ᵐ[volume] fun z ↦ c • F z := by
  rw [map_smul]
  exact (Lp.coeFn_smul _ _).trans (hu.const_smul c)

/-- **Elements of `H^{s,p}`, `s ≥ 0`, are `Lᵖ` functions.** The `Lᵖ` function underlying the
inclusion of `u ∈ H^{s,p}(E, G)` into `H^{0,p}(E, G)` has the tempered distribution `u`. -/
theorem toTemperedDistribution_toLp_inclusion (h : 0 ≤ s) (u : H^{s, p}(E, G)) :
    ((inclusion h u).toLp : 𝓢'(E, G)) = u := by
  simp

/-- For `s ≥ 0`, the `Lᵖ` function `inclusionLp h u` of `u ∈ H^{s,p}(E, G)` lies in `H^{s,p}`. -/
theorem memSobolev_inclusionLp (h : 0 ≤ s) (u : H^{s, p}(E, G)) :
    MemSobolev s p (inclusionLp h u : 𝓢'(E, G)) := by
  rw [toTemperedDistribution_inclusionLp]
  exact u.memSobolev_toDistr

/-- For `s ≥ 0`, the element of `H^{s,p}(E, G)` defined by the `Lᵖ` function `inclusionLp h u` of
`u ∈ H^{s,p}(E, G)` is `u`. -/
theorem toBesselPotentialSpace_memSobolev_inclusionLp (h : 0 ≤ s) (u : H^{s, p}(E, G)) :
    (memSobolev_inclusionLp h u).toBesselPotentialSpace = u :=
  ext (by simp)

/-- For `s ≥ 0`, the `Lᵖ` function of the element of `H^{s,p}(E, G)` defined by an `Lᵖ` function
`g` is `g`. -/
theorem toLp_inclusion_toBesselPotentialSpace (h : 0 ≤ s) {f : 𝓢'(E, G)} (hf : MemSobolev s p f)
    {g : Lp G p (volume : Measure E)} (hg : (g : 𝓢'(E, G)) = f) :
    (inclusion h hf.toBesselPotentialSpace).toLp = g := by
  rw [toLp_inclusion, inclusionLp_eq_iff, hg, MemSobolev.toBesselPotentialSpace_toDistr]

section Hilbert

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace G] in
/-- The Fourier multiplier `⟨ξ⟩ ^ (r - s)` of the inclusion `H^s ⊆ H^r`, `r ≤ s`, does not increase
norms. -/
private theorem norm_inclusion_weight_smul_le (h : r ≤ s) (x : E) (v : G) :
    ‖(((1 + ‖x‖ ^ 2) ^ ((r - s) / 2) : ℝ) : ℂ) • v‖ ≤ ‖v‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (TauCeti.one_add_norm_sq_rpow_le_one x (sub_nonpos.2 h))

/-- **The inclusion on the Fourier side.** For `r ≤ s` and `u ∈ H^s`, the `L²` Fourier transform
of the `L²` part of `u`, viewed in `H^r`, is `⟨ξ⟩ ^ (r - s)` times that of `u`. -/
theorem coeFn_fourier_toLp_inclusion (h : r ≤ s) (u : H^{s}(E, F)) :
    ⇑(𝓕 (inclusion h u).toLp : Lp F 2 (volume : Measure E)) =ᵐ[volume]
      fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((r - s) / 2) : ℝ) : ℂ) • 𝓕 u.toLp ξ :=
  fourier_toLp_ae_eq_of_toDistr_eq (toDistr_inclusion h u).symm

/-- **Fourier multipliers between the Hilbert Bessel-potential spaces.** Let `g` be a symbol of
temperate growth with `‖g ξ‖ ⟨ξ⟩ ^ r ≤ C ⟨ξ⟩ ^ s` for every frequency `ξ`, where
`⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. If `v ∈ H^r` is the image of `u ∈ H^s` under the Fourier
multiplier with symbol `g`, then `‖v‖ ≤ C ‖u‖`. -/
theorem norm_le_of_toDistr_eq_fourierMultiplierCLM {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {C : ℝ} (hC : ∀ ξ : E, ‖g ξ‖ * (1 + ‖ξ‖ ^ 2) ^ (r / 2) ≤ C * (1 + ‖ξ‖ ^ 2) ^ (s / 2))
    {u : H^{s}(E, F)} {v : H^{r}(E, F)}
    (huv : v.toDistr = fourierMultiplierCLM F g u.toDistr) : ‖v‖ ≤ C * ‖u‖ := by
  -- The weighted Fourier transform of `v` is `w • 𝓕 u.toLp`, with `w = g ⟨ξ⟩ ^ (r - s)`.
  set w : E → ℂ := fun ξ ↦ g ξ * (((1 + ‖ξ‖ ^ 2) ^ ((r - s) / 2) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := by fun_prop
  have hw_le (ξ : E) : ‖w ξ‖ ≤ C := by
    have hpos : 0 < (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by positivity
    have hsplit : (1 + ‖ξ‖ ^ 2) ^ ((r - s) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ (r / 2) / (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
      rw [eq_div_iff hpos.ne', ← TauCeti.one_add_norm_sq_rpow_add, sub_add_cancel]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hsplit, ← mul_div_assoc,
      div_le_iff₀ hpos]
    exact hC ξ
  set G₀ : Lp F 2 (volume : Measure E) := 𝓕 u.toLp
  have hG₀ : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 u.toDistr) =
      G₀ :=
    (toTemperedDistribution_fourier_toLp u).symm
  have hmem : MemLp (fun x ↦ w x • G₀ x) 2 (volume : Measure E) :=
    (Lp.memLp G₀).of_le_mul ((hw.1.continuous.aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable G₀)) (.of_forall fun x ↦ by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hw_le x) (norm_nonneg _))
  have hweight : g * (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) =
      (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) * w := by
    ext x
    simp only [w, Pi.mul_apply]
    rw [mul_left_comm, ← Complex.ofReal_mul, ← TauCeti.one_add_norm_sq_rpow_add]
    congr 3
    ring
  have hfourier : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ))
      (𝓕 v.toDistr) = hmem.toLp := by
    rw [huv, fourierMultiplierCLM_apply, fourier_fourierInv_eq,
      smulLeftCLM_smulLeftCLM_apply hg (by fun_prop), hweight,
      ← smulLeftCLM_smulLeftCLM_apply (by fun_prop) hw, hG₀]
    ext φ
    rw [Lp.smulLeftCLM_toTemperedDistribution_apply hw, Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (hmem.coeFn_toLp.mono fun x hx ↦ by simp only [hx])
  rw [norm_eq_of_smulLeftCLM_fourier_eq hfourier, ← norm_fourier_toLp_eq u]
  exact Lp.norm_le_mul_norm_of_ae_le_mul (hmem.coeFn_toLp.mono fun x hx ↦ by
    rw [hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (hw_le x) (norm_nonneg _))

/-- For `p = 2` and a Hilbert space, the inclusion `H^s ⊆ H^r` does not increase norms. -/
theorem norm_inclusion_apply_le (h : r ≤ s) (u : H^{s}(E, F)) : ‖inclusion h u‖ ≤ ‖u‖ := by
  rw [← norm_fourier_toLp_eq, ← norm_fourier_toLp_eq u]
  exact Lp.norm_le_norm_of_ae_le ((coeFn_fourier_toLp_inclusion h u).mono fun x hx ↦
    hx ▸ norm_inclusion_weight_smul_le h x _)

/-- For `p = 2` and a Hilbert space, the inclusion `H^s ⊆ H^r` has operator norm at most `1`. -/
theorem norm_inclusion_le (h : r ≤ s) : ‖(inclusion h : H^{s}(E, F) →L[ℂ] H^{r}(E, F))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa only [one_mul] using norm_inclusion_apply_le h u

/-- For `p = 2` and a Hilbert space, the inclusion `H^s ⊆ L²`, `0 ≤ s`, does not increase norms. -/
theorem norm_inclusionLp_apply_le (hs : 0 ≤ s) (u : H^{s}(E, F)) : ‖inclusionLp hs u‖ ≤ ‖u‖ := by
  rw [← toLp_inclusion, norm_toLp_eq]
  exact norm_inclusion_apply_le hs u

/-- For `p = 2` and a Hilbert space, the inclusion `H^s ⊆ L²`, `0 ≤ s`, has operator norm at
most `1`. -/
theorem norm_inclusionLp_le (hs : 0 ≤ s) :
    ‖(inclusionLp hs : H^{s}(E, F) →L[ℂ] Lp F 2 (volume : Measure E))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa only [one_mul] using norm_inclusionLp_apply_le hs u

/-- An element of `H^r` with the tempered distribution of `u ∈ H^s`, `r ≤ s`, is the image of `u`
under the inclusion, so its norm is at most `‖u‖`. -/
theorem norm_le_of_toDistr_eq (h : r ≤ s) {u : H^{s}(E, F)} {v : H^{r}(E, F)}
    (huv : u.toDistr = v.toDistr) : ‖v‖ ≤ ‖u‖ := by
  obtain rfl : v = inclusion h u := ext (by rw [toDistr_inclusion, huv])
  exact norm_inclusion_apply_le h u

end Hilbert

end BesselPotentialSpace
