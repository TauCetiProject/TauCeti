/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Uniform
public import TauCeti.Analysis.Pseudodifferential.L2
public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Sobolev mapping of uniform pseudodifferential operators

Let `a ∈ S^m_{1,0}` be a symbol of real order `m` on `ℝⁿ` whose derivative bounds
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in the position `x`
(`TauCeti.Symbol.IsUniform`). Unlike `TauCeti.Symbol.quantizeSobolev`, no compact spatial support is
assumed. Conjugating `Op(a)` on Schwartz space by Mathlib's Bessel multipliers `J^{s - m}` and
`J^{-s}` replaces `a` by the uniform composition symbol

`c = ⟨ξ / 2π⟩ ^ (s - m) #_u (a ∘ ⟨ξ / 2π⟩ ^ (-s))`

of order `0` (`TauCeti.Symbol.uniformSharp`, `TauCeti.Symbol.besselPotential`). Applying the
order-zero `L²` Calderón–Vaillancourt theorem (`TauCeti.Symbol.quantizeUniformOrderZero`) to `c`
yields boundedness `Op(a) : H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)` between Bessel-potential spaces for
every real `s`, both when `V` and `W` are complex Hilbert spaces and when they are
finite-dimensional complex normed spaces.

Because `Op(a)` maps Schwartz space continuously into itself (`TauCeti.Symbol.quantizeUniformCLM`),
the composition identity `Op(a #_u b) = Op(a) ∘ Op(b)` transfers by density from Schwartz space to
all Bessel-potential spaces (`TauCeti.Symbol.toDistr_quantizeUniform_uniformSharp`). When `a` also
has compact spatial support, `TauCeti.Symbol.quantizeUniform` agrees with
`TauCeti.Symbol.quantizeSobolev` (`TauCeti.Symbol.quantizeUniform_eq_quantizeSobolev`), and at
`m = s = 0` it agrees with `TauCeti.Symbol.quantizeUniformOrderZero`.

Finally, this file checks the boundary cases of the `L²` theory: the constant identity symbol `1`
quantizes on `H^0` to the identity operator (of norm `1` on a nontrivial fibre), multiplication by a
uniformly bounded smooth spatial coefficient `f(x)` has `L²` operator norm at most `sup_x ‖f(x)‖`,
and multiplication by a coordinate function `x_j` has local order `0` without being `L²`-bounded on
Schwartz functions.

## Main declarations

* `TauCeti.Symbol.quantizeUniform`: the bounded extension `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)` of
  `Op(a)` for a uniform symbol `a` of order `m`, with
  `TauCeti.Symbol.quantizeUniform_toBesselPotentialSpaceCLM`,
  `TauCeti.Symbol.toDistr_quantizeUniform_toBesselPotentialSpaceCLM_apply`, and
  `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM` (specializing to
  `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_zero` and
  `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_of_sub_eq_two_mul`).
* `TauCeti.Symbol.exists_quantizeUniform`: all-real-order `H^s → H^{s - m}` boundedness for
  finite-dimensional complex normed coefficient spaces (specializing to
  `TauCeti.Symbol.exists_quantizeUniformSobolev_of_sub_eq_two_mul`).
* `TauCeti.Symbol.quantizeUniform_eq_quantizeSobolev`,
  `TauCeti.Symbol.quantizeUniform_zero_eq_quantizeUniformOrderZero`: compatibility with the compact
  spatial support Sobolev extension and the order-zero `L²` extension.
* `TauCeti.Symbol.quantizeUniform_comp_quantizeUniform`,
  `TauCeti.Symbol.toDistr_quantizeUniform_uniformSharp`: `Op(a #_u b) = Op(a) ∘ Op(b)` on
  Bessel-potential spaces.
* `TauCeti.Symbol.quantizeUniformOrderZero_const_id`,
  `TauCeti.Symbol.norm_quantizeUniformOrderZero_const_id`,
  `TauCeti.Symbol.norm_quantizeUniformOrderZero_ofSpatial_le`,
  `TauCeti.Symbol.not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le`: operator-level
  identifications and sharpness of the uniform hypothesis.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3, (3.1)
  and Proposition 3.5.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal SchwartzMap BesselPotentialSpace ContDiff

namespace TauCeti

namespace Symbol

/-! ### Conjugation by Bessel multipliers and extension to `H^s` -/

section NormedSpace

variable {n : ℕ} {m m' : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- The order-zero symbol `⟨ξ / 2π⟩ ^ (s - m) #_u (a ∘ ⟨ξ / 2π⟩ ^ (-s))` obtained by conjugating a
uniform symbol `a` of order `m` by Mathlib's Bessel multipliers of orders `s - m` and `-s`. -/
private def besselConjSymbol (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) : Symbol n V W 0 :=
  Symbol.inclusion (by linarith : (s - m) + (m + -s) ≤ 0)
    ((besselPotential (s - m) : Symbol n W W (s - m)).uniformSharp
      (a.comp (besselPotential (-s))) (ha.comp (isUniform_besselPotential (-s))))

omit [CompleteSpace V] [CompleteSpace W] in
private theorem isUniform_besselConjSymbol {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    (besselConjSymbol a ha s).IsUniform :=
  ((isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))).inclusion (by linarith)

/-- Applying `Op(besselConjSymbol a ha s)` to `J^s u` gives `J^{s - m} (Op(a) u)`. -/
private theorem quantizeSchwartzValue_besselConjSymbol {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    quantizeSchwartzValue (besselConjSymbol a ha s).coefficient
        (SchwartzMap.fourierMultiplierCLM V
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u) =
      ⇑(SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha u)) := by
  set v := SchwartzMap.fourierMultiplierCLM V
    (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u
  have hav : quantizeUniformCLM (a.comp (besselPotential (-s)))
      (ha.comp (isUniform_besselPotential (-s))) v = quantizeUniformCLM a ha u := by
    have hcomp : quantizeUniformCLM (a.comp (besselPotential (-s)))
          (ha.comp (isUniform_besselPotential (-s))) ∘L
        SchwartzMap.fourierMultiplierCLM V
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) =
        quantizeUniformCLM a ha := by
      rw [quantizeUniformCLM_comp_besselMultiplier]
      exact quantizeUniformCLM_congr _ ha (by
        rw [coefficient_comp_besselPotential_comp_besselPotential, neg_add_cancel,
          coefficient_comp_besselPotential_zero])
    exact congrArg (· u) hcomp
  funext x
  rw [besselConjSymbol, coefficient_inclusion,
    quantizeSchwartzValue_besselPotential_uniformSharp
      (ha.comp (isUniform_besselPotential (-s))) (s - m) v x, hav]

/-- Any `L²` bound on the conjugated order-zero symbol `besselConjSymbol a ha s` transfers to an
`H^s → H^{s - m}` bound on `Op(a)` for Schwartz inputs. -/
private theorem norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConj
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (besselConjSymbol a ha s).coefficient v) 2 volume ≤
        ENNReal.ofReal C * eLpNorm v 2 volume)
    (u : 𝓢(CoordinateSpace n, V)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
      C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  set v := SchwartzMap.fourierMultiplierCLM V
    (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u
  have hLHS : ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ =
      (eLpNorm (quantizeSchwartzValue (besselConjSymbol a ha s).coefficient v)
        2 volume).toReal := by
    rw [← BesselPotentialSpace.norm_toLp_eq, SchwartzMap.toLp_toBesselPotentialSpaceCLM,
      SchwartzMap.norm_toLp, ← quantizeSchwartzValue_besselConjSymbol ha s u]
  have hRHS : ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ = (eLpNorm v 2 volume).toReal := by
    rw [← BesselPotentialSpace.norm_toLp_eq, SchwartzMap.toLp_toBesselPotentialSpaceCLM,
      SchwartzMap.norm_toLp]
  rw [hLHS, hRHS, ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (v.memLp 2).eLpNorm_ne_top)
    (hC v)

/-- **Sobolev mapping of uniform pseudodifferential operators.** For a uniform symbol `a` of real
order `m` and every real `s`, `quantizeUniform a ha s` is the continuous linear extension of
`Op(a)` from Schwartz functions to `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)`. When `V` and `W` are
complex Hilbert spaces (`TauCeti.Symbol.quantizeUniform_toBesselPotentialSpaceCLM`) or
finite-dimensional complex normed spaces
(`TauCeti.Symbol.quantizeUniform_toBesselPotentialSpaceCLM_of_finiteDimensional`), it agrees with
`TauCeti.Symbol.quantizeUniformCLM` on Schwartz functions. -/
def quantizeUniform (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W) :=
  ((SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) 2).comp
      (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap

private theorem quantizeUniform_toBesselPotentialSpaceCLM_of_norm_le {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ)
    (hC : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniform ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) :=
  LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top) hC u

private theorem quantizeUniform_eq_of_forall_toBesselPotentialSpaceCLM {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ)
    (L : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W))
    (hL : ∀ u : 𝓢(CoordinateSpace n, V),
      L (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
        SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)) :
    a.quantizeUniform ha s = L := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [quantizeUniform_toBesselPotentialSpaceCLM_of_norm_le ha s
    ⟨‖L‖, fun v ↦ (hL v).symm ▸ L.le_opNorm _⟩ u, hL u]

/-- The zero symbol quantizes to `0 : H^s →L[ℂ] H^{s - m}`. -/
@[simp]
theorem quantizeUniform_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ) :
    (0 : Symbol n V W m).quantizeUniform h s = 0 :=
  quantizeUniform_eq_of_forall_toBesselPotentialSpaceCLM h s 0 fun _ ↦ by simp

/-! ### Finite-dimensional complex normed coefficient spaces -/

/-- For finite-dimensional complex normed spaces `V` and `W`, a uniform symbol `a` of order `m`
satisfies the `H^s → H^{s - m}` norm estimate on Schwartz functions. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    (isUniform_besselConjSymbol ha s).exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional
  exact ⟨C, hC0, norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConj ha s hC0 hC⟩

/-- On Schwartz functions between finite-dimensional complex normed spaces, `quantizeUniform`
agrees with `quantizeUniformCLM`. -/
theorem quantizeUniform_toBesselPotentialSpaceCLM_of_finiteDimensional
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniform ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) := by
  obtain ⟨C, -, hC⟩ :=
    ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s
  exact quantizeUniform_toBesselPotentialSpaceCLM_of_norm_le ha s ⟨C, hC⟩ u

/-- **All-real-order Sobolev mapping for uniform symbols** between finite-dimensional complex
normed spaces: for every real `s`, `Op(a)` extends from Schwartz functions to a bounded operator
`H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)`. -/
theorem exists_quantizeUniform [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  refine ⟨a.quantizeUniform ha s, fun u φ ↦ ?_⟩
  rw [quantizeUniform_toBesselPotentialSpaceCLM_of_finiteDimensional ha s u,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply, coe_quantizeUniformCLM]

/-- **Sobolev mapping of uniform symbols at even steps** between finite-dimensional complex normed
spaces (`s - m = 2 * k`), a special case of `TauCeti.Symbol.exists_quantizeUniform`. -/
theorem exists_quantizeUniformSobolev_of_sub_eq_two_mul
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (a : Symbol n V W m) (ha : a.IsUniform)
    {s : ℝ} {k : ℤ} (_hk : s - m = 2 * k) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  exists_quantizeUniform a ha s

end NormedSpace

/-! ### Complex Hilbert coefficient spaces and operator calculus on `H^s` -/

section InnerProductSpace

variable {n : ℕ} {m m' : ℝ} {V W U : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]

/-- For complex Hilbert spaces `V` and `W`, a uniform symbol `a` of order `m` satisfies the
`H^s → H^{s - m}` norm estimate on Schwartz functions. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    (isUniform_besselConjSymbol ha s).exists_eLpNorm_quantizeSchwartzValue_le
  exact ⟨C, hC0, norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConj ha s hC0 hC⟩

/-- On Schwartz functions between complex Hilbert spaces, `quantizeUniform` agrees with
`quantizeUniformCLM`. -/
@[simp]
theorem quantizeUniform_toBesselPotentialSpaceCLM {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniform ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s
  exact quantizeUniform_toBesselPotentialSpaceCLM_of_norm_le ha s ⟨C, hC⟩ u

/-- On a Schwartz function `u`, `Op(a) : H^s → H^{s - m}` evaluates as a tempered distribution to
the quantization integral `quantizeSchwartzValue a.coefficient u`. -/
theorem toDistr_quantizeUniform_toBesselPotentialSpaceCLM_apply {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniform ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeUniform_toBesselPotentialSpaceCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.coe_apply, coe_quantizeUniformCLM]

/-- Uniform symbols of order `m` between complex Hilbert spaces quantize to bounded operators
`H^s → H^{s - m}` for every real `s`. -/
theorem hasSobolevExtension_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) :=
  SchwartzMap.hasSobolevExtension_iff.mpr
    ⟨a.quantizeUniform ha s,
      ContinuousLinearMap.ext (quantizeUniform_toBesselPotentialSpaceCLM ha s)⟩

/-- **Calderón–Vaillancourt.** The quantization of a uniform symbol of order at most `0` extends
to a bounded operator on `H⁰ = L²`. -/
theorem hasSobolevExtension_quantizeUniformCLM_zero {b : Symbol n V W m}
    (hb : b.IsUniform) (hm : m ≤ 0) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) 0 0 :=
  (hasSobolevExtension_quantizeUniformCLM b hb 0).mono (by linarith)

/-- Uniform symbols of order `m` quantize to bounded operators `H^s → H^{s - m}` when
`s - m ∈ 2ℤ`, a special case of `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`. -/
theorem hasSobolevExtension_quantizeUniformCLM_of_sub_eq_two_mul (a : Symbol n V W m)
    (ha : a.IsUniform) {s : ℝ} {k : ℤ} (_hk : s - m = 2 * k) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) :=
  hasSobolevExtension_quantizeUniformCLM a ha s

/-- **Sobolev mapping of uniform symbols at even steps**, for complex Hilbert fibres, a special
case of `TauCeti.Symbol.toDistr_quantizeUniform_toBesselPotentialSpaceCLM_apply`. -/
theorem exists_quantizeUniformSobolevHilbert_of_sub_eq_two_mul (a : Symbol n V W m)
    (ha : a.IsUniform) {s : ℝ} {k : ℤ} (_hk : s - m = 2 * k) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  ⟨a.quantizeUniform ha s, toDistr_quantizeUniform_toBesselPotentialSpaceCLM_apply ha s⟩

private theorem quantizeUniform_congr {a b : Symbol n V W m} (hab : a = b) (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) : a.quantizeUniform ha s = b.quantizeUniform hb s := by
  subst hab; rfl

/-- The operator `Op(a) : H^s → H^{s - m}` is additive in the uniform symbol `a`. -/
theorem quantizeUniform_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform)
    (s : ℝ) :
    (a + b).quantizeUniform (ha.add hb) s = a.quantizeUniform ha s + b.quantizeUniform hb s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  simp [quantizeUniformCLM_add ha hb]

/-- The operator `Op(a) : H^s → H^{s - m}` is homogeneous in the uniform symbol `a`. -/
theorem quantizeUniform_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) (s : ℝ) :
    (c • a).quantizeUniform (ha.smul c) s = c • a.quantizeUniform ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  simp [quantizeUniformCLM_smul ha c]

/-- Negating a uniform symbol negates its Sobolev extension. -/
theorem quantizeUniform_neg {a : Symbol n V W m} (ha : a.IsUniform) (hna : (-a).IsUniform)
    (s : ℝ) : (-a).quantizeUniform hna s = -a.quantizeUniform ha s := by
  rw [quantizeUniform_congr (neg_one_smul ℂ a).symm hna (ha.smul (-1)) s,
    quantizeUniform_smul ha, neg_one_smul]

/-- Subtracting uniform symbols subtracts their Sobolev extensions. -/
theorem quantizeUniform_sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform)
    (hab : (a - b).IsUniform) (s : ℝ) :
    (a - b).quantizeUniform hab s = a.quantizeUniform ha s - b.quantizeUniform hb s := by
  rw [eq_sub_iff_add_eq, ← quantizeUniform_add hab hb s]
  exact quantizeUniform_congr (sub_add_cancel a b) _ _ s

/-- Viewing a uniform symbol of order `m` as one of order `m' ≥ m` composes `quantizeUniform` with
the inclusion `H^{s - m} ⊆ H^{s - m'}`. -/
theorem quantizeUniform_inclusion {a : Symbol n V W m} (h : m ≤ m') (ha : a.IsUniform) (s : ℝ) :
    (inclusion h a).quantizeUniform (ha.inclusion h) s =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeUniform ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  simp [quantizeUniformCLM_inclusion ha h]

/-- The Sobolev extensions `Op(a) : H^s → H^{s - m}` commute with the inclusions `H^s ⊆ H^r`. -/
theorem quantizeUniform_comp_inclusion {a : Symbol n V W m} (ha : a.IsUniform) {r s : ℝ}
    (h : r ≤ s) :
    a.quantizeUniform ha r ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeUniform ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  simp

private theorem toDistr_quantizeUniform_inclusion {a : Symbol n V W m} {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.IsUniform) (hb : b.IsUniform) {s t : ℝ}
    (hts : t ≤ s) (u : H^{s}(CoordinateSpace n, V)) :
    (a.quantizeUniform ha s u).toDistr =
      (b.quantizeUniform hb t (BesselPotentialSpace.inclusion hts u)).toDistr := by
  have key : BesselPotentialSpace.inclusion (min_le_left (s - m) (t - m')) ∘L
        a.quantizeUniform ha s =
      BesselPotentialSpace.inclusion (min_le_right (s - m) (t - m')) ∘L
        b.quantizeUniform hb t ∘L BesselPotentialSpace.inclusion hts := by
    refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun v ↦
      BesselPotentialSpace.ext ?_
    ext φ; simp [hab]
  simpa using congrArg (fun T ↦ (T u).toDistr) key

/-- **Compatibility across orders.** Uniform symbols `a` and `b` with the same coefficient induce
the same action on elements of `H^s` and `H^t` representing the same tempered distribution. -/
theorem toDistr_quantizeUniform_congr {a : Symbol n V W m} {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.IsUniform) (hb : b.IsUniform) {s t : ℝ}
    {u : H^{s}(CoordinateSpace n, V)} {v : H^{t}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniform ha s u).toDistr = (b.quantizeUniform hb t v).toDistr := by
  rcases le_total t s with h | h
  · rw [toDistr_quantizeUniform_inclusion hab ha hb h u]
    congr 2
    exact BesselPotentialSpace.ext (by rw [BesselPotentialSpace.toDistr_inclusion, huv])
  · rw [toDistr_quantizeUniform_inclusion hab.symm hb ha h v]
    congr 2
    exact BesselPotentialSpace.ext (by rw [BesselPotentialSpace.toDistr_inclusion, huv])

/-- **Compatibility with compact spatial support.** When `a` has compact spatial support, its
uniform Sobolev extension `quantizeUniform` equals `quantizeSobolev`. -/
theorem quantizeUniform_eq_quantizeSobolev {a : Symbol n V W m} (hc : a.HasCompactSpatialSupport)
    (ha : a.IsUniform := hc.isUniform) (s : ℝ) :
    a.quantizeUniform ha s = a.quantizeSobolev hc s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext φ; simp

/-- **Compatibility at order zero.** For `m = 0` and `s = 0`, `quantizeUniform` agrees with
`quantizeUniformOrderZero` up to the identification `H^{0 - 0} = H^0`. -/
theorem quantizeUniform_zero_eq_quantizeUniformOrderZero {a : Symbol n V W 0} (ha : a.IsUniform) :
    BesselPotentialSpace.inclusion (sub_zero (0 : ℝ)).ge ∘L a.quantizeUniform ha 0 =
      a.quantizeUniformOrderZero ha := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  simp [quantizeUniformOrderZero_toBesselPotentialSpaceCLM ha
    ha.exists_eLpNorm_quantizeSchwartzValue_le]

/-- **Operator composition of uniform symbols on Bessel-potential spaces.** For uniform symbols
`a` and `b` of orders `m'` and `m`, `Op(a) ∘ Op(b) = Op(a #_u b)` as bounded operators
`H^s →L[ℂ] H^{s - m - m'}` (up to the equality `s - m - m' = s - (m' + m)`). -/
theorem quantizeUniform_comp_quantizeUniform {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    (a.quantizeUniform ha (s - m)).comp (b.quantizeUniform hb s) =
      BesselPotentialSpace.inclusion (le_of_eq (by ring) : s - m - m' ≤ s - (m' + m)) ∘L
        (a.uniformSharp b hb).quantizeUniform (ha.uniformSharp hb) s := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  simp [quantizeUniformCLM_uniformSharp ha hb]

/-- **Composition of uniform quantizations as tempered distributions.** For uniform symbols `a`
and `b`, `Op(a #_u b) u` and `Op(a) (Op(b) u)` have the same underlying tempered distribution for
every `u ∈ H^s`. -/
theorem toDistr_quantizeUniform_uniformSharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ((a.uniformSharp b hb).quantizeUniform (ha.uniformSharp hb) s u).toDistr =
      (a.quantizeUniform ha (s - m) (b.quantizeUniform hb s u)).toDistr := by
  have h := congrArg (fun T ↦ (T u).toDistr) (quantizeUniform_comp_quantizeUniform ha hb s)
  simpa using h.symm

/-- **Uniform smoothing operators.** A symbol whose coefficient is represented by a uniform symbol
at every real order maps any `H^r` continuously into any `H^s`. -/
theorem exists_continuousLinearMap_toDistr_quantizeUniform_eq {a : Symbol n V W m}
    (ha : a.IsUniform)
    (hsm : ∀ N : ℝ, ∃ b : Symbol n V W N, b.IsUniform ∧ b.coefficient = a.coefficient)
    (r s : ℝ) :
    ∃ T : H^{r}(CoordinateSpace n, V) →L[ℂ] H^{s}(CoordinateSpace n, W),
      ∀ {t : ℝ} {v : H^{t}(CoordinateSpace n, V)} {u : H^{r}(CoordinateSpace n, V)},
        v.toDistr = u.toDistr → (a.quantizeUniform ha t v).toDistr = (T u).toDistr := by
  obtain ⟨b, hb, hcoeff⟩ := hsm (r - s)
  refine ⟨BesselPotentialSpace.inclusion (by rw [sub_sub_cancel]) ∘L b.quantizeUniform hb r,
    fun huv ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion]
  exact toDistr_quantizeUniform_congr hcoeff.symm ha hb huv

/-- A constant symbol `const T` quantizes on `H^s` to postcomposition with `T`. -/
theorem quantizeUniform_const (T : V →L[ℂ] W) (s : ℝ) :
    (const T : Symbol n V W 0).quantizeUniform (isUniform_const T) s =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L BesselPotentialSpace.postcomp _ s 2 T :=
  quantizeUniform_eq_of_forall_toBesselPotentialSpaceCLM (isUniform_const T) s _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, quantizeUniformCLM_const,
      ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
      BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]

/-- The constant identity symbol `1` quantizes on `H^s` to the canonical identification
`H^s →L[ℂ] H^{s - 0}`. -/
@[simp]
theorem quantizeUniform_const_id (s : ℝ) :
    (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniform (isUniform_const _) s =
      BesselPotentialSpace.inclusion (sub_zero s).le := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [quantizeUniform_toBesselPotentialSpaceCLM, quantizeUniformCLM_const,
    BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]
  congr 1

/-- Multiplication by a Schwartz scalar function `χ` on `H^s` is the Sobolev quantization of the
uniform spatial symbol `χ(x) id`. -/
theorem quantizeUniform_ofSpatial_smul (χ : 𝓢(CoordinateSpace n, ℂ))
    (hχ : ContDiff ℝ ∞ fun x ↦ χ x • ContinuousLinearMap.id ℂ V)
    (hu : (ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) hχ).IsUniform) (s : ℝ) :
    (ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) hχ).quantizeUniform hu s =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L BesselPotentialSpace.smulLeftCLM s χ :=
  quantizeUniform_eq_of_forall_toBesselPotentialSpaceCLM hu s _ fun u ↦
    BesselPotentialSpace.ext <| by
      have hc : (ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) hχ).coefficient =
          fun p ↦ χ p.1 • ContinuousLinearMap.id ℂ V := funext (coefficient_ofSpatial _ hχ)
      have hq (x : CoordinateSpace n) :
          quantizeSchwartzValue (fun p ↦ χ p.1 • ContinuousLinearMap.id ℂ V) u x = χ x • u x := by
        simpa using quantizeSchwartzValue_comp_fst (fun y ↦ χ y • ContinuousLinearMap.id ℂ V) u x
      ext φ
      simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
        BesselPotentialSpace.toDistr_smulLeftCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
        TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq,
        SchwartzMap.toTemperedDistributionCLM_apply_apply,
        SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, coe_quantizeUniformCLM, hc, hq]

end InnerProductSpace

/-! ### Constant symbols, spatial multipliers, and sharpness of uniformity -/

section SpatialBounds

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- **The constant symbol `1` quantizes to the identity on `H^0`.** Unlike compactly supported
symbols (`TauCeti.exists_not_tsupport_quantizeSchwartzValue_id_subset`), it has no compact spatial
support when `V` is nontrivial. -/
@[simp]
theorem quantizeUniformOrderZero_const_id :
    (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
        (isUniform_const _) =
      ContinuousLinearMap.id ℂ H^{0}(CoordinateSpace n, V) := by
  have h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue
          (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume :=
    ⟨1, zero_le_one, fun u ↦ by
      rw [← coe_quantizeUniformCLM _ (isUniform_const _), quantizeUniformCLM_const,
        ENNReal.ofReal_one, one_mul]
      exact le_of_eq (congrArg (fun v : 𝓢(CoordinateSpace n, V) ↦ eLpNorm v 2 volume)
        (by ext x; simp))⟩
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [quantizeUniformOrderZero_toBesselPotentialSpaceCLM (isUniform_const _) h1 u,
    quantizeUniformCLM_const, ContinuousLinearMap.id_apply]
  congr 1

/-- On a nontrivial Banach fibre `V`, the order-zero `L²` quantization of `1` has operator norm
equal to `1`. -/
theorem norm_quantizeUniformOrderZero_const_id [Nontrivial V] :
    ‖(const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
        (isUniform_const _)‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let φ : ContDiffBump (0 : CoordinateSpace n) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hf_supp : HasCompactSupport (fun x : CoordinateSpace n ↦ φ x • v) :=
    φ.hasCompactSupport.smul_right
  have hf_diff : ContDiff ℝ ∞ (fun x : CoordinateSpace n ↦ φ x • v) :=
    φ.contDiff.smul (contDiff_const (c := v))
  let u : 𝓢(CoordinateSpace n, V) := hf_supp.toSchwartzMap hf_diff
  have hu0 : u 0 ≠ 0 := by
    rw [HasCompactSupport.toSchwartzMap_toFun,
      φ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), one_smul]
    exact hv
  have hu_ne : u ≠ 0 := fun h ↦ hu0 (by simp [h])
  have hnorm_ne : ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ ≠ 0 := by
    rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero]
    refine ENNReal.toReal_ne_zero.2 ⟨?_, (u.memLp 2).eLpNorm_ne_top⟩
    rw [ne_eq, eLpNorm_eq_zero_iff two_ne_zero]
    exact fun hae ↦ hu_ne (SchwartzMap.ext fun x ↦
      congrFun ((u.continuous.ae_eq_iff_eq volume continuous_zero).1 hae) x)
  have : Nontrivial H^{0}(CoordinateSpace n, V) :=
    ⟨⟨SchwartzMap.toBesselPotentialSpaceCLM 0 2 u, 0, fun h ↦ hnorm_ne (by simp [h])⟩⟩
  rw [quantizeUniformOrderZero_const_id, ContinuousLinearMap.norm_id]

/-- **Sharp `L²` norm bound for spatial multiplication symbols.** If `f(x)` defines a uniform
spatial symbol of order `0` with `‖f(x)‖ ≤ C` everywhere (`0 ≤ C`), then `‖Op(f)‖_{H^0 → H^0} ≤ C`;
in particular `C = 0` gives the zero operator. -/
theorem norm_quantizeUniformOrderZero_ofSpatial_le {f : CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) (hu : (ofSpatial f hf).IsUniform) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖(ofSpatial f hf).quantizeUniformOrderZero hu‖ ≤ C := by
  refine norm_quantizeUniformOrderZero_le hu hC0 fun u ↦ ?_
  have hc : (ofSpatial f hf).coefficient = fun p ↦ f p.1 := funext (coefficient_ofSpatial f hf)
  have hq : quantizeSchwartzValue (ofSpatial f hf).coefficient u = fun x ↦ f x (u x) := by
    funext x; rw [hc, quantizeSchwartzValue_comp_fst]
  have hle : eLpNorm (fun x ↦ f x (u x)) 2 volume ≤ eLpNorm (C • ⇑u) 2 volume := by
    refine eLpNorm_mono (hf.continuous.clm_apply u.continuous).aestronglyMeasurable fun x ↦ ?_
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hC0]
    exact (ContinuousLinearMap.le_opNorm (f x) (u x)).trans
      (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  have hc_norm : ‖C‖ₑ = ENNReal.ofReal C := by rw [← ofReal_norm, Real.norm_of_nonneg hC0]
  rw [hq, ← hc_norm, ← eLpNorm_const_smul C (⇑u) 2 volume]
  exact hle

private theorem eLpNorm_sub_two_le_quantizeSchwartzValue_ofSpatial_smul
    (j : Fin n) (T : V →L[ℂ] W) (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T)
    {φ : ContDiffBump (0 : CoordinateSpace n)} (hφ : φ.rOut = 2)
    {u₀ : 𝓢(CoordinateSpace n, V)} {v : V} (hu₀ : ∀ y, u₀ y = φ y • v)
    {R : ℝ} (hR2 : 0 ≤ R - 2) :
    ENNReal.ofReal (R - 2) * eLpNorm (u₀.postcompCLM T) 2 volume ≤
      eLpNorm (quantizeSchwartzValue (ofSpatial (fun x ↦ x j • T) hf).coefficient
        (u₀.compSubConstCLM ℂ (R • EuclideanSpace.single j (1 : ℝ)))) 2 volume := by
  set aR : CoordinateSpace n := R • EuclideanSpace.single j (1 : ℝ)
  set uR : 𝓢(CoordinateSpace n, V) := u₀.compSubConstCLM ℂ aR
  have hTuR : eLpNorm (fun x ↦ T (uR x)) 2 volume = eLpNorm (u₀.postcompCLM T) 2 volume := by
    have hcoe : (fun x ↦ T (uR x)) = ⇑(u₀.postcompCLM T) ∘ fun x ↦ x - aR := rfl
    rw [hcoe, eLpNorm_comp_measurePreserving (u₀.postcompCLM T).continuous.aestronglyMeasurable
      (measurePreserving_sub_right volume aR)]
  have hpt (x : CoordinateSpace n) :
      ‖(R - 2) • T (uR x)‖ ≤
        ‖quantizeSchwartzValue (ofSpatial (fun y ↦ y j • T) hf).coefficient uR x‖ := by
    have hc : (ofSpatial (fun y ↦ y j • T) hf).coefficient = fun p ↦ p.1 j • T :=
      funext (coefficient_ofSpatial _ hf)
    have hq : quantizeSchwartzValue (ofSpatial (fun y ↦ y j • T) hf).coefficient uR x =
        x j • T (uR x) := by
      rw [hc]
      simpa using quantizeSchwartzValue_comp_fst (fun y : CoordinateSpace n ↦ y j • T) uR x
    rw [hq, norm_smul, norm_smul, Real.norm_of_nonneg hR2, Real.norm_eq_abs]
    by_cases hsupp : x - aR ∈ Function.support φ
    · rw [φ.support_eq, hφ, Metric.mem_ball, dist_zero_right] at hsupp
      have hcoord : |(x - aR) j| ≤ 2 := (PiLp.norm_apply_le (x - aR) j).trans hsupp.le
      have haRj : aR j = R := by simp [aR]
      rw [PiLp.sub_apply, haRj, abs_le] at hcoord
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (x j)]) (norm_nonneg _)
    · have hφ0 : φ (x - aR) = 0 := Function.notMem_support.1 hsupp
      have huR0 : uR x = 0 := by simp [uR, SchwartzMap.compSubConstCLM_apply, hu₀, hφ0]
      simp [huR0]
  have hc_norm : ‖R - 2‖ₑ = ENNReal.ofReal (R - 2) := by
    rw [← ofReal_norm, Real.norm_of_nonneg hR2]
  calc ENNReal.ofReal (R - 2) * eLpNorm (u₀.postcompCLM T) 2 volume
      = eLpNorm ((R - 2) • fun x ↦ T (uR x)) 2 volume := by
          rw [eLpNorm_const_smul, hc_norm, hTuR]
    _ ≤ _ := eLpNorm_mono ((T.continuous.comp uR.continuous).const_smul _).aestronglyMeasurable hpt

/-- **Multiplication by a coordinate is not `L²`-bounded.** For any coordinate index `j` and
nonzero operator `T : V →L[ℂ] W`, the symbol `(x, ξ) ↦ x_j • T` has local order `0`
(`TauCeti.Symbol.ofSpatial`), fails to be uniform (`TauCeti.Symbol.not_isUniform_ofSpatial_smul`),
and satisfies no `L²` bound on Schwartz functions: translating a fixed nonzero bump along `e_j`
preserves its `L²` norm while making the output `L²` norm grow linearly. -/
theorem not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le (j : Fin n) {T : V →L[ℂ] W}
    (hT : T ≠ 0) (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T) :
    ¬∃ C : ℝ, ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (ofSpatial (fun x ↦ x j • T) hf).coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  rintro ⟨C, hC⟩
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by by_contra! h; exact hT (ContinuousLinearMap.ext h)
  let φ : ContDiffBump (0 : CoordinateSpace n) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hf_supp : HasCompactSupport (fun x : CoordinateSpace n ↦ φ x • v) :=
    φ.hasCompactSupport.smul_right
  have hf_diff : ContDiff ℝ ∞ (fun x : CoordinateSpace n ↦ φ x • v) :=
    φ.contDiff.smul (contDiff_const (c := v))
  let u₀ : 𝓢(CoordinateSpace n, V) := hf_supp.toSchwartzMap hf_diff
  have hu₀ (y : CoordinateSpace n) : u₀ y = φ y • v :=
    HasCompactSupport.toSchwartzMap_toFun hf_supp hf_diff y
  set N := eLpNorm u₀ 2 volume
  set M := eLpNorm (u₀.postcompCLM T) 2 volume
  have hN_top : N ≠ ⊤ := (u₀.memLp 2).eLpNorm_ne_top
  have hM_top : M ≠ ⊤ := ((u₀.postcompCLM T).memLp 2).eLpNorm_ne_top
  have hM_ne : M ≠ 0 := by
    rw [ne_eq, eLpNorm_eq_zero_iff two_ne_zero]; intro hae
    have h0 := congrFun (((u₀.postcompCLM T).continuous.ae_eq_iff_eq volume
      continuous_zero).1 hae) 0
    simp only [SchwartzMap.postcompCLM_apply, hu₀,
      φ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), one_smul, Pi.zero_apply]
      at h0
    exact hv h0
  have hM_pos : 0 < M.toReal := ENNReal.toReal_pos hM_ne hM_top
  set R : ℝ := max C 0 * N.toReal / M.toReal + 3
  have hR2 : 0 ≤ R - 2 := by
    have : 0 ≤ max C 0 * N.toReal / M.toReal := by positivity
    linarith
  set aR : CoordinateSpace n := R • EuclideanSpace.single j (1 : ℝ)
  set uR : 𝓢(CoordinateSpace n, V) := u₀.compSubConstCLM ℂ aR
  have huR_norm : eLpNorm uR 2 volume = N := by
    have hcoe : (⇑uR : CoordinateSpace n → V) = ⇑u₀ ∘ fun x ↦ x - aR := rfl
    rw [hcoe, eLpNorm_comp_measurePreserving u₀.continuous.aestronglyMeasurable
      (measurePreserving_sub_right volume aR)]
  have hlow : ENNReal.ofReal (R - 2) * M ≤ ENNReal.ofReal (max C 0) * N :=
    (eLpNorm_sub_two_le_quantizeSchwartzValue_ofSpatial_smul j T hf rfl hu₀ hR2).trans
      ((huR_norm ▸ hC uR).trans
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C 0)) zero_le))
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN_top) hlow
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR2,
    ENNReal.toReal_ofReal (le_max_right C 0)] at hreal
  have hRM : (R - 2) * M.toReal = max C 0 * N.toReal + M.toReal := by
    have : R - 2 = max C 0 * N.toReal / M.toReal + 1 := by simp only [R]; ring
    rw [this, add_mul, one_mul, div_mul_cancel₀ _ hM_pos.ne']
  linarith

end SpatialBounds

end Symbol

end TauCeti
