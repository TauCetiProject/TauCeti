/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Frequency multipliers in the Kohn–Nirenberg calculus

A coefficient `b(ξ)` that depends only on the frequency quantizes to a Fourier multiplier
`b(D)`: with the left quantization `Op(a) u (x) = ∫ exp(2πi ⟪x, ζ⟫) a(x, 2πζ) (𝓕 u ζ) dζ` of
`TauCeti.quantizeSchwartzValue`, the Fourier transform of `Op(b) u` is `ζ ↦ b(2πζ) (𝓕 u ζ)`.
For operator-valued `b` of temperate growth this is a continuous linear map of Schwartz spaces,
`TauCeti.quantizeFrequencyCLM b : 𝓢(E, V) →L[ℂ] 𝓢(E, W)`, extending Mathlib's scalar
`SchwartzMap.fourierMultiplierCLM` to matrix-valued (bundle) symbols.

Composition on the right with a frequency multiplier is exact in the left quantization:
`Op(a) ∘ Op(b) = Op(a b)`, with the pointwise product `a(x, ξ) ∘ b(ξ)`, and no lower-order
correction (`TauCeti.quantizeSchwartzValue_quantizeFrequencyCLM`). In particular composing a
quantization with Mathlib's Bessel potential `J^s`, the Fourier multiplier
`(1 + ‖ζ‖²) ^ (s / 2)` in Mathlib's frequency `ζ`, multiplies its symbol by the Bessel weight
`(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency `ξ = 2πζ`. Composition on the left is not
exact and needs the full composition calculus.

On `ℝⁿ`, a smooth coefficient `b(ξ)` with `‖D^k b(ξ)‖ ≤ C_k ⟨ξ⟩ ^ (m - k)` is a symbol of order
`m` with estimates uniform in the position (`TauCeti.Symbol.ofFrequency`). Examples are the
Bessel weight (`TauCeti.Symbol.besselPotential`, of order `s`), whose quantization is Mathlib's
`TemperedDistribution.besselPotential`, and the linear coefficient `⟪ξ, v⟫` of `-i ∂_v`
(`TauCeti.Symbol.ofInner`), which has order `1` but not order `0`.

## Main declarations

* `TauCeti.quantizeFrequencyCLM`: the Fourier multiplier `b(D)` of an operator-valued
  frequency coefficient, with `TauCeti.fourier_quantizeFrequencyCLM_apply` and
  `TauCeti.quantizeSchwartzValue_comp_snd`.
* `TauCeti.quantizeSchwartzValue_quantizeFrequencyCLM`: `Op(a) (b(D) u) = Op(a b) u`, and
  `TauCeti.quantizeSchwartzValue_fourierMultiplierCLM` for Mathlib's scalar multipliers.
* `TauCeti.quantizeFrequencyCLM_comp`: frequency multipliers compose by the pointwise product.
* `TauCeti.toTemperedDistribution_quantizeFrequencyCLM_besselPotential`: the Bessel weight
  quantizes to Mathlib's Bessel potential.
* `TauCeti.Symbol.ofFrequency`, `TauCeti.Symbol.isUniform_ofFrequency`: frequency-only symbols.
* `TauCeti.Symbol.besselPotential` and `TauCeti.Symbol.ofInner`, with
  `TauCeti.Symbol.not_exists_coefficient_eq_ofInner_coefficient`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4) and (2.5)–(2.7).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff LineDeriv
open MeasureTheory Real FourierTransform

noncomputable section

/-- **Symbol estimates give temperate growth.** A smooth function whose `k`-th derivative is
bounded by `C_k (1 + ‖x‖²) ^ ((m - k) / 2)` for every `k` has temperate growth. -/
theorem Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {m : ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ k : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2)) :
    f.HasTemperateGrowth := by
  refine ⟨hf, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hbound k
  refine ⟨⌈m⌉₊, max C 0, fun x ↦ (hC x).trans ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  have hw : (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ (1 + ‖x‖) ^ ⌈m⌉₊ :=
    calc (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ (1 + ‖x‖ ^ 2) ^ ((⌈m⌉₊ : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by
            have := Nat.le_ceil m
            have : (0 : ℝ) ≤ k := k.cast_nonneg
            linarith)
      _ ≤ ((1 + ‖x‖) ^ 2) ^ ((⌈m⌉₊ : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg x]) (by positivity)
      _ = (1 + ‖x‖) ^ ⌈m⌉₊ := by
          rw [← Real.rpow_natCast (1 + ‖x‖) 2, ← Real.rpow_mul (by positivity),
            ← Real.rpow_natCast]
          congr 1
          push_cast
          ring
  calc C * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ max C 0 * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + ‖x‖) ^ ⌈m⌉₊ := mul_le_mul_of_nonneg_left hw (le_max_right _ _)

namespace TauCeti

section Multiplier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

open scoped Classical in
/-- The quantization `b(D)` of a coefficient `b(ξ)` depending only on the angular frequency, as a
continuous linear map of Schwartz spaces: `u ↦ 𝓕⁻ (ζ ↦ b(2πζ) (𝓕 u ζ))`. For a scalar
coefficient this is Mathlib's `SchwartzMap.fourierMultiplierCLM` with the frequency rescaled by
`2π` (`TauCeti.quantizeFrequencyCLM_smul_id`). If `b` does not have temperate growth, the map is
defined to be `0`. -/
def quantizeFrequencyCLM (b : E → V →L[ℂ] W) : 𝓢(E, V) →L[ℂ] 𝓢(E, W) :=
  if hb : b.HasTemperateGrowth then
    fourierInvCLM ℂ 𝓢(E, W) ∘L
      SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ W)
        (g := fun ζ : E ↦ b ((2 * π) • ζ)) (by fun_prop) ∘L
      fourierCLM ℂ 𝓢(E, V)
  else 0

variable [CompleteSpace W] {b : E → V →L[ℂ] W}

/-- The Fourier transform of `b(D) u` is `ζ ↦ b(2πζ) (𝓕 u ζ)`. -/
@[simp]
theorem fourier_quantizeFrequencyCLM_apply (hb : b.HasTemperateGrowth) (u : 𝓢(E, V)) (ζ : E) :
    𝓕 (quantizeFrequencyCLM b u) ζ = b ((2 * π) • ζ) (𝓕 u ζ) := by
  simp [quantizeFrequencyCLM, hb]

/-- **Quantization of a frequency-only coefficient.** The left quantization of `(x, ξ) ↦ b(ξ)` is
the Fourier multiplier `b(D)`. -/
theorem quantizeSchwartzValue_comp_snd (hb : b.HasTemperateGrowth) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (fun p ↦ b p.2) u x = quantizeFrequencyCLM b u x := by
  conv_rhs => rw [← FourierPair.fourierInv_fourier_eq (F := 𝓢(E, W)) (quantizeFrequencyCLM b u)]
  rw [quantizeSchwartzValue_eq_fourierInv, SchwartzMap.fourierInv_coe]
  exact congrArg (fun f : E → W ↦ 𝓕⁻ f x)
    (funext fun ζ ↦ (fourier_quantizeFrequencyCLM_apply hb u ζ).symm)

/-- **Composition with a frequency multiplier on the right is exact.** In the left quantization,
`Op(a) ∘ b(D) = Op(a b)` for the pointwise product `(a b)(x, ξ) = a(x, ξ) ∘ b(ξ)`. -/
theorem quantizeSchwartzValue_quantizeFrequencyCLM (hb : b.HasTemperateGrowth)
    (a : E × E → W →L[ℂ] U) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a (quantizeFrequencyCLM b u) x =
      quantizeSchwartzValue (fun p ↦ (a p).comp (b p.2)) u x := by
  simp [quantizeSchwartzValue_def, hb]

/-- Frequency multipliers compose by the pointwise product of their coefficients. -/
theorem quantizeFrequencyCLM_comp [CompleteSpace U] {c : E → W →L[ℂ] U}
    (hb : b.HasTemperateGrowth) (hc : c.HasTemperateGrowth) :
    (quantizeFrequencyCLM c).comp (quantizeFrequencyCLM b) =
      quantizeFrequencyCLM (fun ξ ↦ (c ξ).comp (b ξ)) := by
  have hcb : (fun ξ ↦ (c ξ).comp (b ξ)).HasTemperateGrowth :=
    (ContinuousLinearMap.compL ℂ V W U).bilinear_hasTemperateGrowth hc hb
  ext u x
  rw [ContinuousLinearMap.comp_apply, ← quantizeSchwartzValue_comp_snd hc,
    quantizeSchwartzValue_quantizeFrequencyCLM hb, ← quantizeSchwartzValue_comp_snd hcb]

/-- For a scalar coefficient `g(ξ)`, the multiplier `g(D)` is Mathlib's Fourier multiplier with
the frequency rescaled by `2π`. -/
theorem quantizeFrequencyCLM_smul_id [CompleteSpace V] {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    quantizeFrequencyCLM (fun ξ ↦ g ξ • ContinuousLinearMap.id ℂ V) =
      SchwartzMap.fourierMultiplierCLM V (fun ζ ↦ g ((2 * π) • ζ)) := by
  ext u x
  rw [← quantizeSchwartzValue_comp_snd (by fun_prop),
    quantizeSchwartzValue_eq_fourierMultiplierCLM hg]

omit [CompleteSpace W] in
/-- **Composition with a scalar Fourier multiplier on the right.** For Mathlib's multiplier
`g(D)` in the frequency `ζ`, `Op(a) ∘ g(D) = Op(g(ξ / 2π) a)` in the angular frequency `ξ`. -/
theorem quantizeSchwartzValue_fourierMultiplierCLM [CompleteSpace V] {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a (SchwartzMap.fourierMultiplierCLM V g u) x =
      quantizeSchwartzValue (fun p ↦ g ((2 * π)⁻¹ • p.2) • a p) u x := by
  have hg' : (fun ξ : E ↦ g ((2 * π)⁻¹ • ξ)).HasTemperateGrowth := by fun_prop
  have hmul : SchwartzMap.fourierMultiplierCLM V g =
      quantizeFrequencyCLM (fun ξ ↦ g ((2 * π)⁻¹ • ξ) • ContinuousLinearMap.id ℂ V) := by
    rw [quantizeFrequencyCLM_smul_id hg']
    simp only [inv_smul_smul₀ (by positivity : (2 * π) ≠ 0)]
  rw [hmul, quantizeSchwartzValue_quantizeFrequencyCLM (by fun_prop)]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Bessel weight `(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency has temperate growth. -/
private theorem hasTemperateGrowth_besselWeight (s : ℝ) :
    (fun ξ : E ↦ (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2)).comp
    ((2 * π)⁻¹ • ContinuousLinearMap.id ℝ E).hasTemperateGrowth)

/-- **The Bessel weight quantizes to the Bessel potential.** The multiplier with coefficient
`(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency `ξ` is Mathlib's Bessel potential
`TemperedDistribution.besselPotential E V s`, the multiplier `(1 + ‖ζ‖²) ^ (s / 2)` in the
frequency `ζ = ξ / 2π`. -/
theorem toTemperedDistribution_quantizeFrequencyCLM_besselPotential [CompleteSpace V] (s : ℝ)
    (u : 𝓢(E, V)) :
    (quantizeFrequencyCLM (fun ξ : E ↦
        (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V) u :
          𝓢'(E, V)) =
      TemperedDistribution.besselPotential E V s u := by
  rw [quantizeFrequencyCLM_smul_id (hasTemperateGrowth_besselWeight s),
    TemperedDistribution.besselPotential,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  simp only [inv_smul_smul₀ (by positivity : (2 * π) ≠ 0)]

end Multiplier

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Frequency

variable {b : CoordinateSpace n → V →L[ℂ] W}

/-- The frequency-only estimates hold with constants uniform in the position. -/
private theorem exists_bound_comp_snd (hb : ContDiff ℝ ∞ b)
    (hbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k b ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2))
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖mixedDeriv α β (fun p ↦ b p.2) x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  rcases eq_or_ne α [] with rfl | hα
  · obtain ⟨C, hC⟩ := hbound β.length
    refine ⟨max C 0, le_max_right _ _, fun x ξ ↦ ?_⟩
    rw [mixedDeriv_nil_comp_snd]
    calc ‖coordinateDeriv β b ξ‖ ≤ ‖iteratedFDeriv ℝ β.length b ξ‖ :=
          norm_coordinateDeriv_le β (hb.of_le (mod_cast le_top)) ξ
      _ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := hC ξ
      _ ≤ max C 0 * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · exact ⟨0, le_rfl, fun x ξ ↦ by simp [mixedDeriv_comp_snd b hα]⟩

/-- A smooth frequency-only coefficient `a(x, ξ) = b(ξ)` whose derivatives satisfy
`‖D^k b(ξ)‖ ≤ C_k ⟨ξ⟩ ^ (m - k)` is a symbol of order `m`. Its quantization is the Fourier
multiplier `b(D)` (`TauCeti.Symbol.quantizeSchwartzValue_ofFrequency`). -/
def ofFrequency (b : CoordinateSpace n → V →L[ℂ] W) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k b ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2)) :
    Symbol n V W m where
  coefficient p := b p.2
  contDiff_coefficient := hb.comp contDiff_snd
  exists_bound _ _ α β :=
    (exists_bound_comp_snd hb hbound α β).imp fun _ hC ↦ ⟨hC.1, fun x _ ξ ↦ hC.2 x ξ⟩

variable (hb : ContDiff ℝ ∞ b)
  (hbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k b ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2))

@[simp]
theorem coefficient_ofFrequency (p : CoordinateSpace n × CoordinateSpace n) :
    (ofFrequency b hb hbound).coefficient p = b p.2 := (rfl)

/-- A frequency-only symbol satisfies its estimates uniformly in the position. -/
theorem isUniform_ofFrequency : (ofFrequency b hb hbound).IsUniform :=
  isUniform_iff.2 (exists_bound_comp_snd hb hbound)

/-- The quantization of a frequency-only symbol is the Fourier multiplier `b(D)`. -/
theorem quantizeSchwartzValue_ofFrequency [CompleteSpace W] (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofFrequency b hb hbound).coefficient u x =
      quantizeFrequencyCLM b u x :=
  quantizeSchwartzValue_comp_snd
    (Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hb hbound) u x

end Frequency

section Examples

/-- Real scalar coefficients with symbol estimates give operator-valued ones. -/
private theorem contDiff_ofReal_smul_and_exists_norm_iteratedFDeriv_le
    {g : CoordinateSpace n → ℝ} (hg : ContDiff ℝ ∞ g) (T : V →L[ℂ] W)
    (hbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2)) :
    ContDiff ℝ ∞ (fun ξ ↦ (g ξ : ℂ) • T) ∧ ∀ k : ℕ, ∃ C, ∀ ξ,
      ‖iteratedFDeriv ℝ k (fun ξ ↦ (g ξ : ℂ) • T) ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) := by
  set L : ℝ →L[ℝ] V →L[ℂ] W := (1 : ℝ →L[ℝ] ℝ).smulRight T
  have hL : (fun ξ ↦ (g ξ : ℂ) • T) = L ∘ g := by
    funext ξ
    simp [L, Complex.coe_smul]
  rw [hL]
  refine ⟨L.contDiff.comp hg, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hbound k
  refine ⟨‖L‖ * max C 0, fun ξ ↦ ?_⟩
  calc ‖iteratedFDeriv ℝ k (L ∘ g) ξ‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k g ξ‖ :=
        L.norm_iteratedFDeriv_comp_left hg.contDiffAt (mod_cast le_top)
    _ ≤ ‖L‖ * (max C 0 * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2)) :=
        mul_le_mul_of_nonneg_left ((hC ξ).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (norm_nonneg L)
    _ = ‖L‖ * max C 0 * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) := (mul_assoc _ _ _).symm

/-- Shrinking the frequency by `0 < c ≤ 1` changes the weight `(1 + ‖ξ‖²) ^ t` by a bounded
factor. -/
private theorem one_add_norm_smul_sq_rpow_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (t : ℝ)
    (ξ : CoordinateSpace n) :
    (1 + ‖c • ξ‖ ^ 2) ^ t ≤ max 1 ((c ^ 2) ^ t) * (1 + ‖ξ‖ ^ 2) ^ t := by
  have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc1
  rw [norm_smul, Real.norm_of_nonneg hc0.le, mul_pow]
  rcases le_total 0 t with ht | ht
  · calc (1 + c ^ 2 * ‖ξ‖ ^ 2) ^ t ≤ (1 + ‖ξ‖ ^ 2) ^ t :=
          Real.rpow_le_rpow (by positivity)
            (by nlinarith [sq_nonneg ‖ξ‖]) ht
      _ ≤ max 1 ((c ^ 2) ^ t) * (1 + ‖ξ‖ ^ 2) ^ t :=
          le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · calc (1 + c ^ 2 * ‖ξ‖ ^ 2) ^ t ≤ (c ^ 2 * (1 + ‖ξ‖ ^ 2)) ^ t :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) ht
      _ = (c ^ 2) ^ t * (1 + ‖ξ‖ ^ 2) ^ t := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ max 1 ((c ^ 2) ^ t) * (1 + ‖ξ‖ ^ 2) ^ t :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The Bessel weight `(1 + ‖ξ / 2π‖²) ^ (s / 2)` is smooth. -/
private theorem contDiff_besselWeight (s : ℝ) :
    ContDiff ℝ ∞ (fun ξ : CoordinateSpace n ↦ (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2)) :=
  (contDiff_const.add ((contDiff_norm_sq ℝ).comp (contDiff_const_smul _))).rpow_const_of_ne
    fun ξ ↦ (show (0 : ℝ) < 1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2 by positivity).ne'

/-- The Bessel weight `(1 + ‖ξ / 2π‖²) ^ (s / 2)` satisfies the symbol estimates of order `s`. -/
private theorem exists_norm_iteratedFDeriv_besselWeight_le (s : ℝ) (k : ℕ) :
    ∃ C, ∀ ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (fun ξ : CoordinateSpace n ↦ (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2)) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((s - k) / 2) := by
  set c : ℝ := (2 * π)⁻¹
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
  set g : CoordinateSpace n →L[ℝ] CoordinateSpace n := c • ContinuousLinearMap.id ℝ _
  set f : CoordinateSpace n → ℝ := fun x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun x ↦ by positivity
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le
    (E := CoordinateSpace n) (s / 2) k
  refine ⟨max C 0 * max 1 ((c ^ 2) ^ ((s - k) / 2)) * ‖g‖ ^ k, fun ξ ↦ ?_⟩
  have hcomp : (fun ξ : CoordinateSpace n ↦ (1 + ‖c • ξ‖ ^ 2) ^ (s / 2)) = f ∘ g := (rfl)
  rw [hcomp, g.iteratedFDeriv_comp_right hf ξ (mod_cast le_top)]
  have hexp : s / 2 - k / 2 = (s - k) / 2 := by ring
  calc ‖(iteratedFDeriv ℝ k f (g ξ)).compContinuousLinearMap fun _ ↦ g‖
        ≤ ‖iteratedFDeriv ℝ k f (g ξ)‖ * ∏ _ : Fin k, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k f (g ξ)‖ * ‖g‖ ^ k := by simp
    _ ≤ (max C 0 * (1 + ‖c • ξ‖ ^ 2) ^ ((s - k) / 2)) * ‖g‖ ^ k := by
        gcongr
        rw [← hexp]
        exact (hC (g ξ)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    _ ≤ (max C 0 * (max 1 ((c ^ 2) ^ ((s - k) / 2)) * (1 + ‖ξ‖ ^ 2) ^ ((s - k) / 2))) *
          ‖g‖ ^ k := by
        gcongr
        exact one_add_norm_smul_sq_rpow_le hc0 hc1 _ ξ
    _ = max C 0 * max 1 ((c ^ 2) ^ ((s - k) / 2)) * ‖g‖ ^ k *
          (1 + ‖ξ‖ ^ 2) ^ ((s - k) / 2) := by ring

/-- The Bessel weight `⟨ξ / 2π⟩ ^ s = (1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency, a
uniform symbol of order `s` (`TauCeti.Symbol.isUniform_besselPotential`). Its quantization is
Mathlib's Bessel potential `TemperedDistribution.besselPotential`
(`TauCeti.Symbol.quantizeSchwartzValue_besselPotential`). -/
def besselPotential (s : ℝ) : Symbol n V V s :=
  ofFrequency (fun ξ ↦ (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V)
    (contDiff_ofReal_smul_and_exists_norm_iteratedFDeriv_le (contDiff_besselWeight s) _
      (exists_norm_iteratedFDeriv_besselWeight_le s)).1
    (contDiff_ofReal_smul_and_exists_norm_iteratedFDeriv_le (contDiff_besselWeight s) _
      (exists_norm_iteratedFDeriv_besselWeight_le s)).2

@[simp]
theorem coefficient_besselPotential (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n) :
    (besselPotential s : Symbol n V V s).coefficient p =
      (((1 + ‖(2 * π)⁻¹ • p.2‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := (rfl)

theorem isUniform_besselPotential (s : ℝ) : (besselPotential s : Symbol n V V s).IsUniform :=
  isUniform_ofFrequency _ _

/-- The quantization of the Bessel weight is the Schwartz-space form of Mathlib's Bessel potential:
the Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`. -/
theorem quantizeSchwartzValue_besselPotential (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (besselPotential s : Symbol n V V s).coefficient u x =
      SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u x := by
  rw [show (besselPotential s : Symbol n V V s).coefficient = fun p ↦
      (((1 + ‖(2 * π)⁻¹ • p.2‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V from (rfl),
    quantizeSchwartzValue_eq_fourierMultiplierCLM
      (g := fun ξ ↦ (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
      (hasTemperateGrowth_besselWeight s)]
  simp only [inv_smul_smul₀ (by positivity : (2 * π) ≠ 0)]

/-- The linear function `⟪ξ, v⟫` satisfies the symbol estimates of order `1`. -/
private theorem exists_norm_iteratedFDeriv_inner_le (v : CoordinateSpace n) (k : ℕ) :
    ∃ C, ∀ ξ : CoordinateSpace n, ‖iteratedFDeriv ℝ k (fun ξ : CoordinateSpace n ↦ ⟪ξ, v⟫) ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (((1 : ℝ) - k) / 2) := by
  have h : (fun ξ : CoordinateSpace n ↦ ⟪ξ, v⟫) = innerSL ℝ v := by
    funext ξ
    rw [innerSL_apply_apply, real_inner_comm]
  rw [h]
  exact ⟨_, (innerSL ℝ v).norm_iteratedFDeriv_le_one_add_norm_sq_rpow k⟩

/-- The coefficient `⟪ξ, v⟫` of `D_v = -i ∂_v`, a uniform symbol of order `1`
(`TauCeti.Symbol.quantizeSchwartzValue_ofInner`). It is not a symbol of order `0`
(`TauCeti.Symbol.not_exists_coefficient_eq_ofInner_coefficient`). -/
def ofInner (v : CoordinateSpace n) : Symbol n V V 1 :=
  ofFrequency (fun ξ ↦ ((⟪ξ, v⟫ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V)
    (contDiff_ofReal_smul_and_exists_norm_iteratedFDeriv_le (g := fun ξ ↦ ⟪ξ, v⟫)
      (contDiff_id.inner ℝ contDiff_const) _ (exists_norm_iteratedFDeriv_inner_le v)).1
    (contDiff_ofReal_smul_and_exists_norm_iteratedFDeriv_le (g := fun ξ ↦ ⟪ξ, v⟫)
      (contDiff_id.inner ℝ contDiff_const) _ (exists_norm_iteratedFDeriv_inner_le v)).2

@[simp]
theorem coefficient_ofInner (v : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    (ofInner v : Symbol n V V 1).coefficient p =
      ((⟪p.2, v⟫ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := (rfl)

theorem isUniform_ofInner (v : CoordinateSpace n) : (ofInner v : Symbol n V V 1).IsUniform :=
  isUniform_ofFrequency _ _

/-- The symbol `⟪ξ, v⟫` quantizes to `D_v = -i ∂_v`. -/
theorem quantizeSchwartzValue_ofInner [CompleteSpace V] (v : CoordinateSpace n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofInner v : Symbol n V V 1).coefficient u x = -Complex.I • ∂_{v} u x :=
  quantizeSchwartzValue_inner_eq_lineDerivOp v u x

/-- The order of `⟪ξ, v⟫` is exactly `1`: for `v ≠ 0` and a nonzero fibre, no symbol of order `0`
has this coefficient, since it is unbounded along the ray `ξ = t v`. -/
theorem not_exists_coefficient_eq_ofInner_coefficient [Nontrivial V] {v : CoordinateSpace n}
    (hv : v ≠ 0) :
    ¬∃ a : Symbol n V V 0, a.coefficient = (ofInner v : Symbol n V V 1).coefficient := by
  rintro ⟨a, ha⟩
  obtain ⟨C, -, hC⟩ := a.exists_bound {0} isCompact_singleton [] []
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  have h := hC 0 rfl (((|C| + 1) / ‖v‖ ^ 2) • v)
  rw [mixedDeriv_nil_nil, ha, coefficient_ofInner] at h
  simp only [List.length_nil, CharP.cast_eq_zero, sub_zero, zero_div, Real.rpow_zero, mul_one,
    norm_smul, ContinuousLinearMap.norm_id, Complex.norm_real, Real.norm_eq_abs,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  rw [div_mul_cancel₀ _ hv2.ne', abs_of_pos (by positivity)] at h
  linarith [le_abs_self C]

end Examples

end Symbol

end TauCeti
