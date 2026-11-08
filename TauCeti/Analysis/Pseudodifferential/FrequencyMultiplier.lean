/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
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
Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)`, the Schwartz-space form of
`TemperedDistribution.besselPotential`, and the linear coefficient `⟪ξ, v⟫` of `-i ∂_v`
(`TauCeti.Symbol.ofInner`), which has order `1` but no smaller order.

## Main declarations

* `TauCeti.quantizeFrequencyCLM`: the Fourier multiplier `b(D)` of an operator-valued
  frequency coefficient, with `TauCeti.fourier_quantizeFrequencyCLM_apply` and
  `TauCeti.quantizeSchwartzValue_comp_snd`.
* `TauCeti.quantizeSchwartzValue_quantizeFrequencyCLM`: `Op(a) (b(D) u) = Op(a b) u`, and
  `TauCeti.quantizeSchwartzValue_fourierMultiplierCLM` for Mathlib's scalar multipliers, which
  are frequency multipliers by `TauCeti.fourierMultiplierCLM_eq_quantizeFrequencyCLM`.
* `TauCeti.quantizeFrequencyCLM_comp`: frequency multipliers compose by the pointwise product.
* `TauCeti.quantizeFrequencyCLM_besselWeight`,
  `TauCeti.toTemperedDistribution_quantizeFrequencyCLM_besselPotential`: the Bessel weight
  quantizes to Mathlib's Bessel multiplier and Bessel potential.
* `TauCeti.Symbol.quantizeSchwartzValue_ofFrequency`: the frequency-only symbol
  `TauCeti.Symbol.ofFrequency` quantizes to `b(D)`.
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

/-- The multiplier of a coefficient without temperate growth is defined to be `0`. -/
theorem quantizeFrequencyCLM_of_not_hasTemperateGrowth {b : E → V →L[ℂ] W}
    (hb : ¬b.HasTemperateGrowth) : quantizeFrequencyCLM b = 0 := by
  simp [quantizeFrequencyCLM, hb]

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
/-- Mathlib's scalar Fourier multiplier `g(D)` in the frequency `ζ` is the multiplier with
coefficient `g(ξ / 2π)` in the angular frequency `ξ = 2πζ`. -/
theorem fourierMultiplierCLM_eq_quantizeFrequencyCLM [CompleteSpace V] {g : E → ℂ}
    (hg : g.HasTemperateGrowth) :
    SchwartzMap.fourierMultiplierCLM V g =
      quantizeFrequencyCLM (fun ξ ↦ g ((2 * π)⁻¹ • ξ) • ContinuousLinearMap.id ℂ V) := by
  rw [quantizeFrequencyCLM_smul_id (by fun_prop)]
  simp only [inv_smul_smul₀ (by positivity : (2 * π) ≠ 0)]

omit [CompleteSpace W] in
/-- **Composition with a scalar Fourier multiplier on the right.** For Mathlib's multiplier
`g(D)` in the frequency `ζ`, `Op(a) ∘ g(D) = Op(g(ξ / 2π) a)` in the angular frequency `ξ`. -/
theorem quantizeSchwartzValue_fourierMultiplierCLM [CompleteSpace V] {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a (SchwartzMap.fourierMultiplierCLM V g u) x =
      quantizeSchwartzValue (fun p ↦ g ((2 * π)⁻¹ • p.2) • a p) u x := by
  rw [fourierMultiplierCLM_eq_quantizeFrequencyCLM hg,
    quantizeSchwartzValue_quantizeFrequencyCLM (by fun_prop)]
  simp

/-- **The Bessel weight quantizes to the Bessel multiplier.** The multiplier with coefficient
`(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency `ξ` is Mathlib's Fourier multiplier
`(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`. -/
theorem quantizeFrequencyCLM_besselWeight [CompleteSpace V] (s : ℝ) :
    quantizeFrequencyCLM (fun ξ : E ↦
        (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V) =
      SchwartzMap.fourierMultiplierCLM V (fun ζ : E ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) :=
  (fourierMultiplierCLM_eq_quantizeFrequencyCLM
    (g := fun ζ : E ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (by fun_prop)).symm

/-- **The Bessel weight quantizes to the Bessel potential.** As a tempered distribution, the
multiplier with coefficient `(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency `ξ` is Mathlib's
Bessel potential `TemperedDistribution.besselPotential E V s`, the multiplier
`(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`. -/
theorem toTemperedDistribution_quantizeFrequencyCLM_besselPotential [CompleteSpace V] (s : ℝ)
    (u : 𝓢(E, V)) :
    (quantizeFrequencyCLM (fun ξ : E ↦
        (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V) u :
          𝓢'(E, V)) =
      TemperedDistribution.besselPotential E V s u := by
  rw [quantizeFrequencyCLM_besselWeight, TemperedDistribution.besselPotential,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]

end Multiplier

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Frequency

variable {b : CoordinateSpace n → V →L[ℂ] W} (hb : ContDiff ℝ ∞ b)
  (hbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k b ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2))

/-- The quantization of a frequency-only symbol is the Fourier multiplier `b(D)`. -/
theorem quantizeSchwartzValue_ofFrequency [CompleteSpace W] (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofFrequency b hb hbound).coefficient u x =
      quantizeFrequencyCLM b u x := by
  rw [funext (coefficient_ofFrequency hb hbound)]
  exact quantizeSchwartzValue_comp_snd
    (Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hb hbound) u x

end Frequency

section Examples

/-- The Bessel weight `(1 + ‖ξ / 2π‖²) ^ (s / 2)` satisfies the symbol estimates of order `s`. -/
private theorem exists_norm_iteratedFDeriv_besselWeight_le (s : ℝ) (k : ℕ) :
    ∃ C, ∀ ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (fun ξ : CoordinateSpace n ↦ (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2)) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((s - k) / 2) := by
  rw [sub_div]
  exact exists_norm_iteratedFDeriv_one_add_norm_smul_sq_rpow_le (by positivity) (s / 2) k

/-- The Bessel weight `⟨ξ / 2π⟩ ^ s = (1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency, a
uniform symbol of order `s` (`TauCeti.Symbol.isUniform_besselPotential`). Its quantization is
Mathlib's Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`
(`TauCeti.Symbol.quantizeSchwartzValue_besselPotential`), which as a tempered distribution is
Mathlib's Bessel potential `TemperedDistribution.besselPotential`
(`TauCeti.toTemperedDistribution_quantizeFrequencyCLM_besselPotential`). -/
def besselPotential (s : ℝ) : Symbol n V V s :=
  ofFrequency (fun ξ ↦ (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V)
    ((Complex.ofRealCLM.contDiff.comp
      (Function.hasTemperateGrowth_one_add_norm_smul_sq_rpow _ _).1).smul contDiff_const)
    fun k ↦ by
      simpa only [ContinuousLinearMap.smulRight_apply, Complex.ofRealCLM_apply] using
        ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_le_one_add_norm_sq_rpow
          (Complex.ofRealCLM.smulRight (ContinuousLinearMap.id ℂ V))
          ((Function.hasTemperateGrowth_one_add_norm_smul_sq_rpow _ _).1.of_le (mod_cast le_top))
          (exists_norm_iteratedFDeriv_besselWeight_le s k)

@[simp]
theorem coefficient_besselPotential (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n) :
    (besselPotential s : Symbol n V V s).coefficient p =
      (((1 + ‖(2 * π)⁻¹ • p.2‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V :=
  coefficient_ofFrequency _ _ p

theorem isUniform_besselPotential (s : ℝ) : (besselPotential s : Symbol n V V s).IsUniform :=
  isUniform_ofFrequency _ _

/-- The quantization of the Bessel weight is the Schwartz-space form of Mathlib's Bessel potential:
the Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`. -/
theorem quantizeSchwartzValue_besselPotential (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (besselPotential s : Symbol n V V s).coefficient u x =
      SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u x := by
  rw [funext (coefficient_besselPotential (n := n) (V := V) s),
    quantizeSchwartzValue_eq_fourierMultiplierCLM
      (g := fun ξ ↦ (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (by fun_prop)]
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

/-- The coefficient `⟪ξ, v⟫` of `D_v = -i ∂_v` (`TauCeti.Symbol.quantizeSchwartzValue_ofInner`),
a uniform symbol of order `1` (`TauCeti.Symbol.isUniform_ofInner`). It is not a symbol of any
order `m < 1` (`TauCeti.Symbol.not_exists_coefficient_eq_ofInner_coefficient`). -/
def ofInner (v : CoordinateSpace n) : Symbol n V V 1 :=
  ofFrequency (fun ξ ↦ ((⟪ξ, v⟫ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V)
    ((Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)).smul contDiff_const)
    fun k ↦ by
      simpa only [ContinuousLinearMap.smulRight_apply, Complex.ofRealCLM_apply] using
        ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_le_one_add_norm_sq_rpow
          (Complex.ofRealCLM.smulRight (ContinuousLinearMap.id ℂ V)) (g := fun ξ ↦ ⟪ξ, v⟫)
          ((contDiff_id.inner ℝ contDiff_const).of_le (mod_cast le_top))
          (exists_norm_iteratedFDeriv_inner_le v k)

@[simp]
theorem coefficient_ofInner (v : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    (ofInner v : Symbol n V V 1).coefficient p =
      ((⟪p.2, v⟫ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V :=
  coefficient_ofFrequency _ _ p

theorem isUniform_ofInner (v : CoordinateSpace n) : (ofInner v : Symbol n V V 1).IsUniform :=
  isUniform_ofFrequency _ _

/-- The symbol `⟪ξ, v⟫` quantizes to `D_v = -i ∂_v`. -/
theorem quantizeSchwartzValue_ofInner [CompleteSpace V] (v : CoordinateSpace n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofInner v : Symbol n V V 1).coefficient u x =
      -Complex.I • ∂_{v} u x := by
  rw [funext (coefficient_ofInner (V := V) v)]
  exact quantizeSchwartzValue_inner_eq_lineDerivOp v u x

/-- `⟪ξ, v⟫` has no order below `1`: for `v ≠ 0`, a nonzero fibre and `m < 1`, no symbol of
order `m` has this coefficient, since along the ray `ξ = t v` it grows like `t`, faster than
`⟨ξ⟩ ^ m`. -/
theorem not_exists_coefficient_eq_ofInner_coefficient [Nontrivial V] {v : CoordinateSpace n}
    (hv : v ≠ 0) (hm : m < 1) :
    ¬∃ a : Symbol n V V m, a.coefficient = (ofInner v : Symbol n V V 1).coefficient := by
  rintro ⟨a, ha⟩
  obtain ⟨C, -, hC⟩ := a.exists_bound {0} isCompact_singleton [] []
  set m₀ := max m 0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hp : 0 < 1 - m₀ := sub_pos.2 (max_lt hm one_pos)
  -- Choose `S ≥ 2` with `S ^ (1 - m₀) > 2 |C| / ‖v‖`; test the bound at `ξ = (S / 2) v / ‖v‖`.
  obtain ⟨S, hS, hS2⟩ := (((tendsto_rpow_atTop hp).eventually_gt_atTop (2 * |C| / ‖v‖)).and
    (Filter.eventually_ge_atTop 2)).exists
  have hS0 : 0 < S := by linarith
  set ξ : CoordinateSpace n := (S / (2 * ‖v‖)) • v
  have hξ : ‖ξ‖ = S / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hinner : ⟪ξ, v⟫ = S / 2 * ‖v‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h : S / 2 * ‖v‖ ≤ C * (1 + (S / 2) ^ 2) ^ (m / 2) := by
    simpa [ha, norm_smul, hinner, hξ, abs_of_pos hS0] using hC 0 rfl ξ
  -- The weight is at most `(1 + S / 2) ^ m₀ ≤ S ^ m₀`.
  have hweight : (1 + (S / 2) ^ 2) ^ (m / 2) ≤ S ^ m₀ :=
    calc (1 + (S / 2) ^ 2) ^ (m / 2) ≤ (1 + (S / 2) ^ 2) ^ (m₀ / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith [le_max_left m 0])
      _ ≤ (1 + S / 2) ^ m₀ := by
          simpa [abs_of_nonneg hS0.le] using
            one_add_norm_sq_rpow_half_le_one_add_norm_rpow (S / 2) (le_max_right m 0)
      _ ≤ S ^ m₀ := Real.rpow_le_rpow (by positivity) (by linarith) (le_max_right m 0)
  have hbound : C * (1 + (S / 2) ^ 2) ^ (m / 2) ≤ |C| * S ^ m₀ :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hweight (abs_nonneg C))
  have key : 2 * |C| * S ^ m₀ < S * ‖v‖ :=
    calc 2 * |C| * S ^ m₀ < S ^ (1 - m₀) * ‖v‖ * S ^ m₀ :=
          mul_lt_mul_of_pos_right ((div_lt_iff₀ hvpos).1 hS) (Real.rpow_pos_of_pos hS0 _)
      _ = S * ‖v‖ := by
          rw [mul_right_comm, ← Real.rpow_add hS0, sub_add_cancel, Real.rpow_one]
  linarith

end Examples

end Symbol

end TauCeti
