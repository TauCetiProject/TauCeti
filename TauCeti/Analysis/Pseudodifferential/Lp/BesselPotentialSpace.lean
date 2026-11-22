/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.MulLeft
public import TauCeti.Analysis.Pseudodifferential.BesselPotentialSpace
public import TauCeti.Analysis.Pseudodifferential.Lp.CalderonZygmund
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Pseudodifferential.UniformSobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Extension

/-!
# Uniform pseudodifferential operators on `H^{s,p}`

Let `a` be a symbol of order `m` on `ℝⁿ`, with values in operators `V →L[ℂ] W` between complex
Hilbert spaces, whose estimates `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in
the position (`TauCeti.Symbol.IsUniform`), and let `1 < p < ∞`. This file proves that the operator
`TauCeti.Symbol.quantizeUniformBesselPotentialSpace : H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)` between
Mathlib's Bessel-potential spaces extends the left quantization `Op(a)` from Schwartz functions, for
every real `s` (`TauCeti.Symbol.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM`).
For `p = 2` this is the Sobolev mapping theorem
`TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`; for symbols with compact spatial support
and finite-dimensional normed fibres it is
`HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM` in the
namespace `TauCeti.Symbol`. Uniform symbols of order `0` include the multiplications by smooth
operator-valued functions `f` all of whose derivatives are bounded
(`TauCeti.Symbol.isUniform_ofSpatial_iff`), so these act boundedly on every `H^{s,p}`
(`TauCeti.Symbol.toDistr_quantizeUniformBesselPotentialSpace_ofSpatial`).

## The argument

Write `J^t` for the Bessel multiplier, the Fourier multiplier with symbol `⟨ζ⟩ ^ t`, so that the
`H^{r,p}` norm of a Schwartz function `v` is the `Lᵖ` norm of `J^r v`
(`SchwartzMap.norm_toBesselPotentialSpaceCLM_eq_eLpNorm`). Conjugation by Bessel multipliers
reduces the order to `0`
(`TauCeti.Symbol.IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq`):

`J^{s - m} ∘ Op(a) = Op(b) ∘ J^s`

on Schwartz space for a uniform symbol `b` of order `0`. The `Lᵖ` boundedness of `Op(b)`, the
Calderón–Zygmund theorem for pseudodifferential operators of order `0`
(`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt`), then gives
`‖Op(a) u‖_{H^{s - m,p}} ≤ C ‖u‖_{H^{s,p}}`, and the operator extends by density of the Schwartz
functions.

## Main declarations

* `TauCeti.Symbol.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM`: the operator
  `H^{s,p} → H^{s - m,p}` extends `Op(a)` from Schwartz functions.
* `TauCeti.Symbol.IsUniform.hasBesselPotentialSpaceExtension`: equivalently, `a` has the extension
  property `TauCeti.Symbol.HasBesselPotentialSpaceExtension`, from which the lemmas below follow.
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
* `TauCeti.Symbol.toDistr_quantizeUniformBesselPotentialSpace_ofSpatial`: for finite-dimensional
  fibres, the symbol `f(x)` quantizes to multiplication by `f`.

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

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

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
  -- `J^{s - m} (Op(a) u) = Op(b) (J^s u)`, and `Op(b)` is bounded on `Lᵖ`.
  rw [norm_toBesselPotentialSpaceCLM_eq_eLpNorm, norm_toBesselPotentialSpaceCLM_eq_eLpNorm,
    ← ContinuousLinearMap.comp_apply, hab, ContinuousLinearMap.comp_apply, coe_quantizeUniformCLM]
  refine (ENNReal.toReal_mono ?_ (hC _)).trans_eq (by simp [ENNReal.toReal_mul])
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top (SchwartzMap.memLp _ p volume).eLpNorm_ne_top

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
  exact quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM_of_norm_le ha hp_top hC u

/-- For `1 < p < ∞`, a uniform symbol between complex Hilbert spaces has the extension property
`TauCeti.Symbol.HasBesselPotentialSpaceExtension`. -/
theorem IsUniform.hasBesselPotentialSpaceExtension (ha : a.IsUniform) (hp : 1 < p)
    (hp_top : p ≠ ∞) : a.HasBesselPotentialSpaceExtension ha p :=
  hasBesselPotentialSpaceExtension_iff.2 fun s ↦
    quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM ha s hp hp_top

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` is additive in the symbol. -/
theorem quantizeUniformBesselPotentialSpace_add {b : Symbol n V W m} (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ ∞) :
    (a + b).quantizeUniformBesselPotentialSpace (ha.add hb) s p =
      a.quantizeUniformBesselPotentialSpace ha s p +
        b.quantizeUniformBesselPotentialSpace hb s p :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).quantizeUniformBesselPotentialSpace_add
    (hb.hasBesselPotentialSpaceExtension hp hp_top)
    ((ha.add hb).hasBesselPotentialSpaceExtension hp hp_top) s hp_top

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` is homogeneous in the symbol. -/
theorem quantizeUniformBesselPotentialSpace_smul (ha : a.IsUniform) (c : ℂ) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    (c • a).quantizeUniformBesselPotentialSpace (ha.smul c) s p =
      c • a.quantizeUniformBesselPotentialSpace ha s p :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).quantizeUniformBesselPotentialSpace_smul c
    ((ha.smul c).hasBesselPotentialSpaceExtension hp hp_top) s hp_top

/-- The zero symbol quantizes to the zero operator `H^{s,p} → H^{s - m,p}`. -/
@[simp]
theorem quantizeUniformBesselPotentialSpace_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    (0 : Symbol n V W m).quantizeUniformBesselPotentialSpace h s p = 0 :=
  (h.hasBesselPotentialSpaceExtension hp hp_top).quantizeUniformBesselPotentialSpace_zero s hp_top

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes the negated symbol to the negated
operator. -/
theorem quantizeUniformBesselPotentialSpace_neg (ha : a.IsUniform) (s : ℝ) (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    (-a).quantizeUniformBesselPotentialSpace ha.neg s p =
      -a.quantizeUniformBesselPotentialSpace ha s p :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).quantizeUniformBesselPotentialSpace_neg
    (ha.neg.hasBesselPotentialSpaceExtension hp hp_top) s hp_top

/-- The operator `Op(a) : H^{s,p} → H^{s - m,p}` takes differences of symbols to differences of
operators. -/
theorem quantizeUniformBesselPotentialSpace_sub {b : Symbol n V W m} (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ ∞) :
    (a - b).quantizeUniformBesselPotentialSpace (ha.sub hb) s p =
      a.quantizeUniformBesselPotentialSpace ha s p -
        b.quantizeUniformBesselPotentialSpace hb s p :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).quantizeUniformBesselPotentialSpace_sub
    (hb.hasBesselPotentialSpaceExtension hp hp_top)
    ((ha.sub hb).hasBesselPotentialSpaceExtension hp hp_top) s hp_top

/-- **Changing the order of the symbol.** Let `1 < p < ∞`. Viewing a symbol of order `m` as a
symbol of order `m' ≥ m` gives the operator `H^{s,p} → H^{s - m,p}` followed by the inclusion
`H^{s - m,p} ⊆ H^{s - m',p}`. -/
theorem quantizeUniformBesselPotentialSpace_inclusion (h : m ≤ m') (ha : a.IsUniform) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    (inclusion h a).quantizeUniformBesselPotentialSpace (ha.inclusion h) s p =
      BesselPotentialSpace.inclusion (by linarith) ∘L
        a.quantizeUniformBesselPotentialSpace ha s p :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).quantizeUniformBesselPotentialSpace_inclusion h
    ((ha.inclusion h).hasBesselPotentialSpaceExtension hp hp_top) s hp_top

/-- **Changing the Sobolev order.** Let `1 < p < ∞`. The operators
`Op(a) : H^{s,p} → H^{s - m,p}` for the different orders `s` are compatible with the inclusions
`H^{s,p} ⊆ H^{r,p}`. -/
theorem quantizeUniformBesselPotentialSpace_comp_inclusion (ha : a.IsUniform) {r s : ℝ}
    (h : r ≤ s) (hp : 1 < p) (hp_top : p ≠ ∞) :
    a.quantizeUniformBesselPotentialSpace ha r p ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L
        a.quantizeUniformBesselPotentialSpace ha s p :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).quantizeUniformBesselPotentialSpace_comp_inclusion
    h hp_top

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
  (ha.hasBesselPotentialSpaceExtension hp hp_top).toDistr_quantizeUniformBesselPotentialSpace_congr
    (hb.hasBesselPotentialSpaceExtension hp hp_top) hab hp_top huv

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
        (b.quantizeUniformBesselPotentialSpace hb s p u)).toDistr :=
  (ha.hasBesselPotentialSpaceExtension hp hp_top).toDistr_quantizeUniformBesselPotentialSpace_comp
    (hb.hasBesselPotentialSpaceExtension hp hp_top) (hc.hasBesselPotentialSpaceExtension hp hp_top)
    habc s hp_top u

open scoped ContDiff in
/-- **Multiplication operators.** Let `1 < p < ∞` and let `V` and `W` be finite-dimensional. For a
smooth `f : ℝⁿ → (V →L[ℂ] W)` all of whose derivatives are bounded, so that the symbol `f(x)` of
order `0` is uniform (`TauCeti.Symbol.isUniform_ofSpatial_iff`), this symbol quantizes to
multiplication by `f` on `H^{s,p}`. -/
theorem toDistr_quantizeUniformBesselPotentialSpace_ofSpatial [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ W] {f : CoordinateSpace n → V →L[ℂ] W} (hf : ContDiff ℝ ∞ f)
    (ha : (ofSpatial f hf).IsUniform) (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (u : H^{s, p}(CoordinateSpace n, V)) :
    ((ofSpatial f hf).quantizeUniformBesselPotentialSpace ha s p u).toDistr =
      TemperedDistribution.mulLeftCLM f u.toDistr := by
  have hA : f.HasTemperateGrowth := by
    simpa [coefficient_ofSpatial] using ha.hasTemperateGrowth_coefficient_slice 0
  have key : BesselPotentialSpace.toDistrCLM _ _ _ _ ∘L
        (ofSpatial f hf).quantizeUniformBesselPotentialSpace ha s p =
      TemperedDistribution.mulLeftCLM f ∘L BesselPotentialSpace.toDistrCLM _ _ _ _ := by
    refine BesselPotentialSpace.continuousLinearMap_ext hp_top fun v ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistrCLM_apply,
      quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM ha s hp hp_top,
      SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
    rw [TemperedDistribution.mulLeftCLM_toTemperedDistributionCLM_eq hA]
    congr 1
    ext x
    rw [quantizeUniformCLM_ofSpatial_apply, SchwartzMap.bilinLeftCLM_apply]
    rfl
  simpa using congrArg (fun T ↦ T u) key

end Symbol

end TauCeti
