/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
public import TauCeti.Analysis.Sobolev.BesselPotential.ComplexOrder
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Cpow
import TauCeti.Analysis.Fourier.MihlinHormander
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

/-!
# Bessel potentials of imaginary order on `Lᵖ` and `H^{s,p}`

Let `E` be a finite-dimensional real inner product space and `1 < p < ∞`. The Bessel potential
`J^z` of complex order `z` is the Fourier multiplier whose symbol is the complex power
`⟨ξ⟩ ^ z = (1 + ‖ξ‖ ^ 2) ^ (z / 2)` of the Japanese bracket (`TauCeti.japaneseBracketCpow`). For
`p = 2` the imaginary orders act isometrically, by Plancherel's theorem. For `p ≠ 2` this file
proves that they are still bounded on `Lᵖ`, with norm growing at most polynomially in the order:

`‖J^{it} f‖_p ≤ C (1 + |t|) ^ N ‖f‖_p`, `N = ⌊n / 2⌋ + 1`, `n = dim E`.

The symbol `⟨ξ⟩ ^ z` with `re z ≤ 0` satisfies Mihlin's condition of order `N` with constant
`C (1 + ‖z‖) ^ N` (`TauCeti.exists_norm_iteratedFDeriv_japaneseBracketCpow_le_div_pow`), so the
Mihlin–Hörmander multiplier theorem gives `‖J^z f‖_p ≤ C (1 + ‖z‖) ^ N ‖f‖_p`
(`TauCeti.exists_fourierMultiplierCLM_japaneseBracketCpow_eq_and_norm_le`).

On the Bessel-potential spaces `H^{s,p}`, whose norm is the `Lᵖ` norm of `J^s u`, the operator
`J^z` maps `H^{s,p}` to `H^{s - re z,p}` for every complex `z`: the symbols multiply,
`⟨ξ⟩ ^ (s - re z) ⟨ξ⟩ ^ z = ⟨ξ⟩ ^ (i im z) ⟨ξ⟩ ^ s`
(`TemperedDistribution.besselPotential_fourierMultiplierCLM_japaneseBracketCpow`), so only the
imaginary part of the order enters the norm. This gives the bounded operator
`BesselPotentialSpace.besselPotentialCLM hp hp_top z : H^{s,p}(E, F) →L[ℂ] H^{s - re z,p}(E, F)`
with

`‖J^z‖_{H^{s,p} → H^{s - re z,p}} ≤ C (1 + |im z|) ^ N`

for a constant `C` independent of `s` and `z`
(`BesselPotentialSpace.exists_norm_besselPotentialCLM_le`). This polynomial bound is the
admissible-growth estimate that Stein's interpolation theorem for analytic families of operators
needs on the scale of spaces `H^{s,p}` of different orders `s`; this file does not prove
holomorphy in `z`.

## Main declarations

* `TauCeti.exists_fourierMultiplierCLM_japaneseBracketCpow_eq_and_norm_le`: for `re z ≤ 0`, the
  Bessel potential `J^z` is bounded on `Lᵖ` with norm at most `C (1 + ‖z‖) ^ N`.
* `TemperedDistribution.besselPotential_fourierMultiplierCLM_japaneseBracketCpow`:
  `J^{s - re z} J^z u = J^{i im z} J^s u` on tempered distributions, the composition law
  `J^w J^v u = J^{v + w} u`
  (`fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow`), and
  `J^0 u = u` (`fourierMultiplierCLM_japaneseBracketCpow_zero`).
* `TemperedDistribution.MemSobolev.fourierMultiplierCLM_japaneseBracketCpow`: `J^z` maps
  `H^{s,p}` into `H^{s - re z,p}`.
* `BesselPotentialSpace.besselPotentialCLM`: `J^z` as a bounded operator
  `H^{s,p}(E, F) →L[ℂ] H^{s - re z,p}(E, F)`, agreeing with `SchwartzMap.besselPotentialCLM z`
  on Schwartz functions (`BesselPotentialSpace.besselPotentialCLM_toBesselPotentialSpaceCLM`)
  and with Mathlib's `TemperedDistribution.besselPotential` at real orders
  (`BesselPotentialSpace.toDistr_besselPotentialCLM_ofReal`), with orders adding under composition
  (`BesselPotentialSpace.besselPotentialCLM_besselPotentialCLM`) and order `0` acting as the
  identity (`BesselPotentialSpace.besselPotentialCLM_zero`), and
  `BesselPotentialSpace.exists_norm_besselPotentialCLM_le` its norm bound `C (1 + |im z|) ^ N`.
* `BesselPotentialSpace.toOrderZeroₗᵢ`: the real-order Bessel potential `J^s` as an isometry
  `H^{s,p}(E, F) ≃ₗᵢ[ℂ] H^{0,p}(E, F)`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  §3 (the Mihlin multiplier theorem) and Chapter V, §3 (Bessel potentials).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, §6.4, where the bounds on
  imaginary powers enter the complex interpolation of the spaces `H^{s,p}`.
-/

public section

noncomputable section

open MeasureTheory Module TemperedDistribution
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The Bessel potentials of complex order shift the Sobolev order by their real part.** For
a tempered distribution `u`, a real `s` and a complex `z`,
`J^{s - re z} (J^z u) = J^{i im z} (J^s u)`, where `J^r` is Mathlib's Bessel potential
`TemperedDistribution.besselPotential` and `J^z` the Fourier multiplier with symbol `⟨ξ⟩ ^ z`. -/
theorem besselPotential_fourierMultiplierCLM_japaneseBracketCpow (s : ℝ) (z : ℂ)
    (u : 𝓢'(E, F)) :
    besselPotential E F (s - z.re) (fourierMultiplierCLM F (TauCeti.japaneseBracketCpow z) u) =
      fourierMultiplierCLM F (TauCeti.japaneseBracketCpow (z.im * Complex.I))
        (besselPotential E F s u) := by
  have hr (r : ℝ) : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_one_add_norm_sq_rpow E _)
  -- `besselPotential E F r` is the Fourier multiplier with the real bracket power.
  have hb (r : ℝ) (v : 𝓢'(E, F)) : besselPotential E F r v =
      fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) v := by
    rw [besselPotential]
  rw [hb, hb, fourierMultiplierCLM_fourierMultiplierCLM_apply
      (TauCeti.hasTemperateGrowth_japaneseBracketCpow z) (hr _),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (hr _)
      (TauCeti.hasTemperateGrowth_japaneseBracketCpow _)]
  have hsym : (TauCeti.japaneseBracketCpow z *
      fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((s - z.re) / 2) : ℝ) : ℂ)) =
      (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) *
        TauCeti.japaneseBracketCpow (z.im * Complex.I) := by
    funext ξ
    simp only [Pi.mul_apply, ← TauCeti.japaneseBracketCpow_ofReal,
      ← TauCeti.japaneseBracketCpow_add]
    congr 1
    apply Complex.ext <;> simp
  rw [hsym]

/-- The Fourier multiplier with symbol `⟨ξ⟩ ^ 0 = 1` is the identity: `J^0 u = u` on tempered
distributions. -/
@[simp]
theorem fourierMultiplierCLM_japaneseBracketCpow_zero (u : 𝓢'(E, F)) :
    fourierMultiplierCLM F (TauCeti.japaneseBracketCpow (0 : ℂ)) u = u := by
  have h : TauCeti.japaneseBracketCpow (0 : ℂ) = fun _ : E ↦ (1 : ℂ) :=
    funext TauCeti.japaneseBracketCpow_zero
  rw [h, fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]

/-- Fourier multipliers with complex powers of the Japanese bracket compose by adding the orders:
`J^w (J^v u) = J^{v + w} u` on tempered distributions. -/
theorem fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow
    (v w : ℂ) (u : 𝓢'(E, F)) :
    fourierMultiplierCLM F (TauCeti.japaneseBracketCpow w)
        (fourierMultiplierCLM F (TauCeti.japaneseBracketCpow v) u) =
      fourierMultiplierCLM F (TauCeti.japaneseBracketCpow (v + w)) u := by
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply
    (TauCeti.hasTemperateGrowth_japaneseBracketCpow v)
    (TauCeti.hasTemperateGrowth_japaneseBracketCpow w)]
  congr 2
  funext ξ
  simp only [Pi.mul_apply, TauCeti.japaneseBracketCpow_add]

/-- Mathlib's Bessel potential of real order `s` is the Fourier multiplier with the complex power
`⟨ξ⟩ ^ s` of the Japanese bracket. -/
theorem besselPotential_eq_fourierMultiplierCLM_japaneseBracketCpow (s : ℝ) (u : 𝓢'(E, F)) :
    besselPotential E F s u = fourierMultiplierCLM F (TauCeti.japaneseBracketCpow (s : ℂ)) u := by
  rw [besselPotential]
  congr 2
  funext ξ
  exact (TauCeti.japaneseBracketCpow_ofReal s ξ).symm

end TemperedDistribution

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace TauCeti

/-- **Bessel potentials of order with nonpositive real part are bounded on `Lᵖ`.** For
`1 < p < ∞` there is a constant `C` such that for every complex `z` with `re z ≤ 0`, in
particular every imaginary `z`, and every `f ∈ Lᵖ(E, F)`, the Bessel potential
`J^z f = 𝓕⁻ (⟨ξ⟩ ^ z 𝓕 f)` is an `Lᵖ` function `g` with
`‖g‖_p ≤ C (1 + ‖z‖) ^ N ‖f‖_p`, `N = ⌊dim E / 2⌋ + 1`. -/
theorem exists_fourierMultiplierCLM_japaneseBracketCpow_eq_and_norm_le (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ z : ℂ, z.re ≤ 0 → ∀ f : Lp F p (volume : Measure E),
      ∃ g : Lp F p (volume : Measure E),
        fourierMultiplierCLM F (japaneseBracketCpow z) (f : 𝓢'(E, F)) = (g : 𝓢'(E, F)) ∧
          ‖g‖ ≤ C * (1 + ‖z‖) ^ (finrank ℝ E / 2 + 1) * ‖f‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- On the zero space the only frequency is `0`, where the symbol is `1`.
    refine ⟨1, fun z _ f ↦ ⟨f, ?_, ?_⟩⟩
    · have h : japaneseBracketCpow z = fun _ : E ↦ (1 : ℂ) :=
        funext fun ξ ↦ by rw [Subsingleton.elim ξ 0, japaneseBracketCpow_zero_right]
      rw [h, fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
    · have : (1 : ℝ) ≤ (1 + ‖z‖) ^ (finrank ℝ E / 2 + 1) :=
        one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg z))
      push_cast
      nlinarith [norm_nonneg f]
  set N := finrank ℝ E / 2 + 1
  obtain ⟨C₀, hC₀⟩ := exists_fourierMultiplierCLM_eq_and_norm_le_of_norm_iteratedFDeriv_le
    (F := F) (V := E) (N := N) (by omega) hp hp_top
  obtain ⟨C₁, hC₁⟩ := exists_norm_iteratedFDeriv_japaneseBracketCpow_le_div_pow (H := E) N
  refine ⟨C₀ * C₁, fun z hz f ↦ ?_⟩
  obtain ⟨g, hg, hgf⟩ := hC₀ (hasTemperateGrowth_japaneseBracketCpow z) (hC₁ z hz) f
  refine ⟨g, hg, hgf.trans_eq ?_⟩
  push_cast
  ring

end TauCeti

/-- **The Bessel potential `J^z` maps `H^{s,p}` into `H^{s - re z,p}`**, for `1 < p < ∞` and every
complex `z`. -/
theorem TemperedDistribution.MemSobolev.fourierMultiplierCLM_japaneseBracketCpow (hp : 1 < p)
    (hp_top : p ≠ ∞) {s : ℝ} {u : 𝓢'(E, F)} (hu : u.MemSobolev s p) (z : ℂ) :
    (fourierMultiplierCLM F (TauCeti.japaneseBracketCpow z) u).MemSobolev (s - z.re) p := by
  obtain ⟨C, hC⟩ :=
    TauCeti.exists_fourierMultiplierCLM_japaneseBracketCpow_eq_and_norm_le (E := E) (F := F) hp
      hp_top
  obtain ⟨f, hf⟩ := hu
  obtain ⟨g, hg, -⟩ := hC (z.im * Complex.I) (by simp) f
  exact ⟨g, by rw [besselPotential_fourierMultiplierCLM_japaneseBracketCpow, hf, hg]⟩

namespace BesselPotentialSpace

variable {s : ℝ}

/-- **The Bessel potential of complex order on the Sobolev scale.** For `1 < p < ∞` and a complex
`z`, the Fourier multiplier `J^z` with symbol `⟨ξ⟩ ^ z` as a bounded operator
`H^{s,p}(E, F) →L[ℂ] H^{s - re z,p}(E, F)`. Its norm is at most `C (1 + |im z|) ^ N`
(`BesselPotentialSpace.exists_norm_besselPotentialCLM_le`). -/
def besselPotentialCLM (hp : 1 < p) (hp_top : p ≠ ∞) (z : ℂ) :
    H^{s, p}(E, F) →L[ℂ] H^{s - z.re, p}(E, F) :=
  mapCLM (fourierMultiplierCLM F (TauCeti.japaneseBracketCpow z)) fun u ↦
    u.memSobolev_toDistr.fourierMultiplierCLM_japaneseBracketCpow hp hp_top z

/-- `besselPotentialCLM hp hp_top z` acts on the underlying tempered distributions as the Fourier
multiplier with symbol `⟨ξ⟩ ^ z`. -/
@[simp]
theorem toDistr_besselPotentialCLM (hp : 1 < p) (hp_top : p ≠ ∞) (z : ℂ) (u : H^{s, p}(E, F)) :
    (besselPotentialCLM hp hp_top z u).toDistr =
      fourierMultiplierCLM F (TauCeti.japaneseBracketCpow z) u.toDistr :=
  toDistr_mapCLM _ _ u

/-- At a real order `t`, `besselPotentialCLM hp hp_top t` acts on the underlying tempered
distributions as Mathlib's Bessel potential `TemperedDistribution.besselPotential E F t`. -/
theorem toDistr_besselPotentialCLM_ofReal (hp : 1 < p) (hp_top : p ≠ ∞) (t : ℝ)
    (u : H^{s, p}(E, F)) :
    (besselPotentialCLM hp hp_top (t : ℂ) u).toDistr = besselPotential E F t u.toDistr := by
  rw [toDistr_besselPotentialCLM, besselPotential]
  congr 2
  funext ξ
  exact TauCeti.japaneseBracketCpow_ofReal t ξ

/-- The Bessel potential of order `0` on the Sobolev scale is the identity, after identifying
`H^{s - re 0,p}` with `H^{s,p}`. -/
theorem besselPotentialCLM_zero (hp : 1 < p) (hp_top : p ≠ ∞) (u : H^{s, p}(E, F)) :
    besselPotentialCLM hp hp_top 0 u = u.copy (s - (0 : ℂ).re) (by simp) := by
  ext1
  rw [toDistr_copy _ (by simp), toDistr_besselPotentialCLM,
    fourierMultiplierCLM_japaneseBracketCpow_zero]

/-- The orders of Bessel potentials on the Sobolev scale add: `J^w (J^z u) = J^(z + w) u`, after
identifying `H^{s - re (z + w),p}` with `H^{s - re z - re w,p}`. -/
@[simp]
theorem besselPotentialCLM_besselPotentialCLM (hp : 1 < p) (hp_top : p ≠ ∞) (z w : ℂ)
    (u : H^{s, p}(E, F)) :
    besselPotentialCLM hp hp_top w (besselPotentialCLM hp hp_top z u) =
      (besselPotentialCLM hp hp_top (z + w) u).copy (s - z.re - w.re)
        (by rw [Complex.add_re]; ring) := by
  ext1
  rw [toDistr_copy _ (by rw [Complex.add_re]; ring), toDistr_besselPotentialCLM,
    toDistr_besselPotentialCLM, toDistr_besselPotentialCLM,
    fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow]

variable (E F) in
/-- The Bessel potential `J^s` as a linear isometry equivalence
`H^{s,p}(E, F) ≃ₗᵢ[ℂ] H^{0,p}(E, F)`: both spaces are identified with `Lᵖ` by
`BesselPotentialSpace.toLpₗᵢ`. -/
def toOrderZeroₗᵢ (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{0, p}(E, F) :=
  (toLpₗᵢ E F s p).trans (toLpₗᵢ E F 0 p).symm

/-- `toOrderZeroₗᵢ` acts on the underlying tempered distributions as the Bessel potential `J^s`. -/
@[simp]
theorem toDistr_toOrderZeroₗᵢ (u : H^{s, p}(E, F)) :
    (toOrderZeroₗᵢ E F s p u).toDistr = besselPotential E F s u.toDistr := by
  have h : (toOrderZeroₗᵢ E F s p u).toDistr = besselPotential E F (-0) u.toLp := by
    simp [toOrderZeroₗᵢ]
  rw [h, neg_zero, besselPotential_zero, ContinuousLinearMap.id_apply,
    ← u.bessel_toDistr_eq_toLp]

/-- The inverse of `toOrderZeroₗᵢ` acts on the underlying tempered distributions as the Bessel
potential `J^{-s}`. -/
@[simp]
theorem toDistr_toOrderZeroₗᵢ_symm (u : H^{0, p}(E, F)) :
    ((toOrderZeroₗᵢ E F s p).symm u).toDistr = besselPotential E F (-s) u.toDistr := by
  have h : ((toOrderZeroₗᵢ E F s p).symm u).toDistr = besselPotential E F (-s) u.toLp := by
    simp [toOrderZeroₗᵢ]
  rw [h, ← u.bessel_toDistr_eq_toLp, besselPotential_zero, ContinuousLinearMap.id_apply]

/-- On Schwartz functions, `besselPotentialCLM hp hp_top z` is the Bessel potential
`SchwartzMap.besselPotentialCLM z` of complex order. -/
@[simp]
theorem besselPotentialCLM_toBesselPotentialSpaceCLM (hp : 1 < p) (hp_top : p ≠ ∞) (z : ℂ)
    (u : 𝓢(E, F)) :
    besselPotentialCLM hp hp_top z (SchwartzMap.toBesselPotentialSpaceCLM s p u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - z.re) p (SchwartzMap.besselPotentialCLM z u) := by
  ext1
  rw [toDistr_besselPotentialCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.besselPotentialCLM_def,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq
      (TauCeti.hasTemperateGrowth_japaneseBracketCpow z)]

/-- **The norm of `J^z` on the Sobolev scale grows polynomially in the imaginary part of the
order.** For `1 < p < ∞` there is a constant `C`, independent of `s` and `z`, such that
`‖J^z‖_{H^{s,p} → H^{s - re z,p}} ≤ C (1 + |im z|) ^ N`, `N = ⌊dim E / 2⌋ + 1`. -/
theorem exists_norm_besselPotentialCLM_le (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (s : ℝ) (z : ℂ),
      ‖(besselPotentialCLM hp hp_top z : H^{s, p}(E, F) →L[ℂ] H^{s - z.re, p}(E, F))‖ ≤
        C * (1 + |z.im|) ^ (finrank ℝ E / 2 + 1) := by
  obtain ⟨C, hC⟩ :=
    TauCeti.exists_fourierMultiplierCLM_japaneseBracketCpow_eq_and_norm_le (E := E) (F := F) hp
      hp_top
  refine ⟨C, fun s z ↦ ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_⟩
  obtain ⟨g, hg, hgu⟩ := hC (z.im * Complex.I) (by simp) u.toLp
  have hz : ‖(z.im : ℂ) * Complex.I‖ = |z.im| := by simp
  rw [hz] at hgu
  -- The `Lᵖ` function of `J^z u` is `J^{i im z}` applied to the `Lᵖ` function of `u`.
  have hv : (besselPotentialCLM hp hp_top z u).toLp = g := by
    refine Lp.toTemperedDistribution_injective ?_
    beta_reduce
    rw [← (besselPotentialCLM hp hp_top z u).bessel_toDistr_eq_toLp, toDistr_besselPotentialCLM,
      besselPotential_fourierMultiplierCLM_japaneseBracketCpow, u.bessel_toDistr_eq_toLp, hg]
  rw [← norm_toLp_eq, hv, ← norm_toLp_eq u]
  exact hgu

end BesselPotentialSpace
