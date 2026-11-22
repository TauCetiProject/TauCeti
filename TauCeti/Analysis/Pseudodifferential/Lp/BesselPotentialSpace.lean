/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.BesselPotentialSpace
public import TauCeti.Analysis.Pseudodifferential.Lp.CalderonZygmund
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Pseudodifferential.Composition.Uniform
import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Extension

/-!
# Uniform pseudodifferential operators on `H^{s,p}`

Let `a` be a symbol of order `m` on `ℝⁿ`, with values in operators `V →L[ℂ] W` between complex
Hilbert spaces, whose estimates `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in
the position (`TauCeti.Symbol.IsUniform`), and let `1 < p < ∞`. This file proves that the left
quantization `Op(a)` extends from Schwartz functions to a bounded operator
`H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)` between Mathlib's Bessel-potential spaces, for every real
`s` (`TauCeti.Symbol.quantizeUniformBesselPotentialSpace`). For `p = 2` this is the Sobolev mapping
theorem `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`; for symbols with compact spatial
support it is `TauCeti.Symbol.quantizeBesselPotentialSpace`
(`TauCeti.Symbol.quantizeUniformBesselPotentialSpace_eq_quantizeBesselPotentialSpace`).
Uniform symbols of order `0` include the multiplications by smooth operator-valued functions `f`
all of whose derivatives are bounded (`TauCeti.Symbol.isUniform_ofSpatial_iff`,
`TauCeti.Symbol.quantizeUniformCLM_ofSpatial_apply`), so these act boundedly on every `H^{s,p}`.

## The argument

Write `J^t` for the Bessel multiplier, the Fourier multiplier with symbol `⟨ζ⟩ ^ t`, so that the
`H^{r,p}` norm of a Schwartz function `v` is the `Lᵖ` norm of `J^r v`. Since compositions of
uniform symbols are uniform (`TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`) and
composition with `J^s` on the right is exact
(`TauCeti.Symbol.quantizeUniformCLM_comp_besselMultiplier`),

`J^{s - m} ∘ Op(a) = Op(b) ∘ J^s`

on Schwartz space for a uniform symbol `b` of order `0`. The `Lᵖ` boundedness of `Op(b)`, the
Calderón–Zygmund theorem for pseudodifferential operators of order `0`
(`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt`), then gives
`‖Op(a) u‖_{H^{s - m,p}} ≤ C ‖u‖_{H^{s,p}}`, and the operator extends by density of the Schwartz
functions.

## Main declarations

* `TauCeti.Symbol.quantizeUniformBesselPotentialSpace`: the bounded operator
  `H^{s,p} → H^{s - m,p}`, which extends `Op(a)` from Schwartz functions
  (`TauCeti.Symbol.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM`).
* `TauCeti.Symbol.quantizeUniformBesselPotentialSpace_add`,
  `TauCeti.Symbol.quantizeUniformBesselPotentialSpace_smul` and their consequences: the operator is
  linear in the symbol.
* `TauCeti.Symbol.quantizeUniformBesselPotentialSpace_inclusion`,
  `TauCeti.Symbol.quantizeUniformBesselPotentialSpace_comp_inclusion`: compatibility with raising
  the order of the symbol and with the inclusions `H^{s,p} ⊆ H^{r,p}`.
* `TauCeti.Symbol.toDistr_quantizeUniformBesselPotentialSpace_congr`: the operators for different
  orders `s` agree as maps of tempered distributions.
* `TauCeti.Symbol.toDistr_quantizeUniformBesselPotentialSpace_comp`: composition of uniform
  quantizations on `H^{s,p}`.
* `TauCeti.Symbol.quantizeUniformBesselPotentialSpace_eq_quantizeBesselPotentialSpace`: for symbols
  with compact spatial support it is `TauCeti.Symbol.quantizeBesselPotentialSpace`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture II, §1
  (`Lᵖ` and `H^{s,p}` mapping of operators of order `m`).
* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VI, §5.
-/

public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ}

/-- **Pseudodifferential operators with uniform symbols on `H^{s,p}`.** For a symbol `a` of order
`m` whose estimates are uniform in the position, the left quantization `Op(a)` as a bounded
operator `H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)`. For complex Hilbert spaces `V` and `W` and
`1 < p < ∞` it extends `Op(a)` from Schwartz functions: on a Schwartz function `u` it is the
Schwartz function `Op(a) u`
(`TauCeti.Symbol.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM`), and by density of
the Schwartz functions it is the unique continuous linear map with this property
(`BesselPotentialSpace.continuousLinearMap_ext`). Otherwise its value is unspecified. -/
def quantizeUniformBesselPotentialSpace {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    H^{s, p}(CoordinateSpace n, V) →L[ℂ] H^{s - m, p}(CoordinateSpace n, W) :=
  ((toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) p).comp
    (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm
      (toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s p).toLinearMap

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Conjugation by Bessel multipliers.** For a uniform symbol `a` of order `m` and every real
`s` there is a uniform symbol `b` of order `0` with `J^{s - m} ∘ Op(a) = Op(b) ∘ J^s` on Schwartz
space. -/
private theorem IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) :
    ∃ (b : Symbol n V W 0) (hb : b.IsUniform),
      fourierMultiplierCLM W
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)) ∘L
        quantizeUniformCLM a ha =
      quantizeUniformCLM b hb ∘L fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) := by
  -- `J^{s - m} ∘ Op(a) = Op(c)` for a uniform symbol `c` of order `s`.
  obtain ⟨c, hc, hcomp⟩ :=
    (isUniform_besselPotential (V := W) (n := n) (s - m)).exists_quantizeUniformCLM_comp ha
  have hJ : quantizeUniformCLM (besselPotential (s - m)) (isUniform_besselPotential _) =
      fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)) := by
    ext u x
    rw [quantizeUniformCLM_apply, quantizeSchwartzValue_besselPotential]
  -- `Op(c) = Op(b) ∘ J^s` for `b = c ⟨ξ / 2π⟩ ^ (-s)`, of order `s + -s = 0`.
  have hc' := hc.comp (isUniform_besselPotential (V := V) (n := n) (-s))
  have h0 : s - m + m + -s ≤ 0 := by linarith
  refine ⟨Symbol.inclusion h0 (c.comp (besselPotential (-s))), hc'.inclusion h0, ?_⟩
  rw [← hJ, hcomp, quantizeUniformCLM_inclusion hc' h0, quantizeUniformCLM_comp_besselMultiplier]
  exact quantizeUniformCLM_congr _ _ (by
    rw [coefficient_comp_besselPotential_comp_besselPotential, neg_add_cancel,
      coefficient_comp_besselPotential_zero])

/-- **The `H^{s,p}` estimate on Schwartz functions.** For a uniform symbol `a` of order `m` and
`1 < p < ∞`, `‖Op(a) u‖_{H^{s - m,p}} ≤ C ‖u‖_{H^{s,p}}` for every Schwartz function `u`. -/
private theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s p u‖ := by
  obtain ⟨b, hb, hab⟩ := ha.exists_besselMultiplier_comp_quantizeUniformCLM_eq s
  obtain ⟨C, hC⟩ := hb.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt hp hp_top
  refine ⟨C, fun u ↦ ?_⟩
  -- The `H^{r,p}` norm of a Schwartz function `v` is the `Lᵖ` norm of `J^r v`.
  rw [← BesselPotentialSpace.norm_toLp_eq, ← BesselPotentialSpace.norm_toLp_eq,
    toLp_toBesselPotentialSpaceCLM, toLp_toBesselPotentialSpaceCLM, norm_toLp, norm_toLp,
    ← ContinuousLinearMap.comp_apply, hab, ContinuousLinearMap.comp_apply, coe_quantizeUniformCLM,
    ← ENNReal.coe_toReal C, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    ((fourierMultiplierCLM V
      (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u).memLp p).eLpNorm_ne_top)
    (hC _)

variable {a : Symbol n V W m} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Mapping of uniform pseudodifferential operators on `H^{s,p}`.** Let `1 < p < ∞`. On a
Schwartz function `u`, the operator `Op(a) : H^{s,p} → H^{s - m,p}` is the Schwartz function
`Op(a) u`. -/
@[simp]
theorem quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM (ha : a.IsUniform) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ ∞) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformBesselPotentialSpace ha s p (toBesselPotentialSpaceCLM s p u) =
      toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u) := by
  obtain ⟨C, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
  exact LinearMap.extendOfNorm_eq (denseRange_toBesselPotentialSpaceCLM s hp_top) ⟨C, hC⟩ u

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` is additive in the symbol. -/
theorem quantizeUniformBesselPotentialSpace_add {b : Symbol n V W m} (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ ∞) :
    (a + b).quantizeUniformBesselPotentialSpace (ha.add hb) s p =
      a.quantizeUniformBesselPotentialSpace ha s p +
        b.quantizeUniformBesselPotentialSpace hb s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, quantizeUniformCLM_add ha hb]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` is homogeneous in the symbol. -/
theorem quantizeUniformBesselPotentialSpace_smul (ha : a.IsUniform) (c : ℂ) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    (c • a).quantizeUniformBesselPotentialSpace (ha.smul c) s p =
      c • a.quantizeUniformBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, quantizeUniformCLM_smul ha]

/-- The zero symbol quantizes to the zero operator `H^{s,p} → H^{s - m,p}`. -/
@[simp]
theorem quantizeUniformBesselPotentialSpace_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    (0 : Symbol n V W m).quantizeUniformBesselPotentialSpace h s p = 0 := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes the negated symbol to the negated
operator. -/
theorem quantizeUniformBesselPotentialSpace_neg (ha : a.IsUniform) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    (-a).quantizeUniformBesselPotentialSpace ha.neg s p =
      -a.quantizeUniformBesselPotentialSpace ha s p := by
  have hq : quantizeUniformCLM (-a) ha.neg = -quantizeUniformCLM a ha := by
    rw [quantizeUniformCLM_congr ha.neg (ha.smul (-1)) (by simp), quantizeUniformCLM_smul,
      neg_one_smul]
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, hq]

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes differences of symbols to differences of
operators. -/
theorem quantizeUniformBesselPotentialSpace_sub {b : Symbol n V W m} (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ ∞) :
    (a - b).quantizeUniformBesselPotentialSpace (ha.sub hb) s p =
      a.quantizeUniformBesselPotentialSpace ha s p -
        b.quantizeUniformBesselPotentialSpace hb s p := by
  rw [eq_sub_iff_add_eq, ← quantizeUniformBesselPotentialSpace_add (ha.sub hb) hb s hp hp_top]
  simp_rw [sub_add_cancel]

/-- **Changing the order of the symbol.** Let `1 < p < ∞`. Viewing a symbol of order `m` as a
symbol of order `m' ≥ m` gives the operator `H^{s,p} → H^{s - m,p}` followed by the inclusion
`H^{s - m,p} ⊆ H^{s - m',p}`. -/
theorem quantizeUniformBesselPotentialSpace_inclusion (h : m ≤ m') (ha : a.IsUniform) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    (inclusion h a).quantizeUniformBesselPotentialSpace (ha.inclusion h) s p =
      BesselPotentialSpace.inclusion (by linarith) ∘L
        a.quantizeUniformBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM,
    quantizeUniformCLM_inclusion ha h]

/-- **Changing the Sobolev order.** Let `1 < p < ∞`. The operators
`Op(a) : H^{s,p} → H^{s - m,p}` for the different orders `s` are compatible with the inclusions
`H^{s,p} ⊆ H^{r,p}`. -/
theorem quantizeUniformBesselPotentialSpace_comp_inclusion (ha : a.IsUniform) {r s : ℝ}
    (h : r ≤ s) (hp : 1 < p) (hp_top : p ≠ ∞) :
    a.quantizeUniformBesselPotentialSpace ha r p ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L
        a.quantizeUniformBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]

/-- **Compatibility of the extensions.** The operator `Op(a) : H^{s,p} → H^{s - m,p}` only depends
on the coefficient of `a` and on the tempered distribution of its argument: uniform symbols `a`
and `b` of orders `m` and `m'` with the same coefficient give the same tempered distribution on
`u ∈ H^{s,p}` and `v ∈ H^{t,p}` whenever `u` and `v` have the same tempered distribution. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_congr {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.IsUniform) (hb : b.IsUniform) (hp : 1 < p)
    (hp_top : p ≠ ∞) {s t : ℝ} {u : H^{s, p}(CoordinateSpace n, V)}
    {v : H^{t, p}(CoordinateSpace n, V)} (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniformBesselPotentialSpace ha s p u).toDistr =
      (b.quantizeUniformBesselPotentialSpace hb t p v).toDistr :=
  toDistr_apply_congr_of_comp_eq hp_top (A := quantizeUniformCLM a ha)
    (ContinuousLinearMap.ext fun u ↦ by simp [hp, hp_top])
    (ContinuousLinearMap.ext fun u ↦ by simp [hp, hp_top, quantizeUniformCLM_congr ha hb hab]) huv

/-- **Composition of uniform quantizations on `H^{s,p}`.** Let `1 < p < ∞`. If the uniform symbol
`c` of order `m''` quantizes to the composition `Op(a) ∘ Op(b)` of uniform symbols of orders `m'`
and `m` on Schwartz space, as given by `TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`,
then `Op(c) : H^{s,p} → H^{s - m'',p}` is the composition of `Op(b) : H^{s,p} → H^{s - m,p}` and
`Op(a) : H^{s - m,p} → H^{s - m - m',p}`, as maps of tempered distributions. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_comp {U : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] [CompleteSpace U] {m'' : ℝ} {a : Symbol n W U m'} {b : Symbol n V W m}
    {c : Symbol n V U m''} (ha : a.IsUniform) (hb : b.IsUniform) (hc : c.IsUniform)
    (habc : quantizeUniformCLM a ha ∘L quantizeUniformCLM b hb = quantizeUniformCLM c hc) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ ∞) (u : H^{s, p}(CoordinateSpace n, V)) :
    (c.quantizeUniformBesselPotentialSpace hc s p u).toDistr =
      (a.quantizeUniformBesselPotentialSpace ha (s - m) p
        (b.quantizeUniformBesselPotentialSpace hb s p u)).toDistr := by
  have key : BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L
        c.quantizeUniformBesselPotentialSpace hc s p =
      BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L
        a.quantizeUniformBesselPotentialSpace ha (s - m) p ∘L
          b.quantizeUniformBesselPotentialSpace hb s p := by
    refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun v ↦ ?_
    simp [hp, hp_top, ← habc]
  simpa using congrArg (fun T ↦ T u) key

/-- **Comparison with compact spatial support.** For finite-dimensional complex Hilbert spaces and
a symbol with compact spatial support, the operator `Op(a) : H^{s,p} → H^{s - m,p}` of this file is
the operator `TauCeti.Symbol.quantizeBesselPotentialSpace` built from the Fourier transform of `a`
in the position. -/
theorem quantizeUniformBesselPotentialSpace_eq_quantizeBesselPotentialSpace
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ha : a.HasCompactSpatialSupport) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    a.quantizeUniformBesselPotentialSpace ha.isUniform s p =
      a.quantizeBesselPotentialSpace ha s p := by
  refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun u ↦ ?_
  simp [hp, hp_top]

end Symbol

end TauCeti
