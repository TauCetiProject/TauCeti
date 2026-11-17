/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Pseudodifferential.UniformSobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.ComplexOrder

/-!
# The commutator of a Bessel potential with a multiplication operator

Let `f : ℝⁿ → (V →L[ℂ] W)` be a smooth compactly supported function with values in the bounded
operators between two complex Hilbert spaces, for instance a matrix of test functions, and let
`M_f u = f u` be multiplication by `f`. Write `J^s` for Mathlib's Bessel potential, the Fourier
multiplier with symbol `⟨ζ⟩ ^ s = (1 + ‖ζ‖²) ^ (s / 2)`, so that `‖u‖_{H^s} = ‖J^s u‖_{L²}`.

The commutator `[J^s, M_f] = J^s M_f - M_f J^s` has order `s - 1`, one less than either product:
it is the quantization of the remainder of order `s - 1` in the composition expansion of the
Bessel weight `⟨ξ / 2π⟩ ^ s # f`
(`TauCeti.Symbol.besselPotentialCLM_comp_quantizeUniformCLM_ofSpatial_sub`).
Indeed, `J^s M_f` is the quantization of `⟨ξ / 2π⟩ ^ s # f`, whose leading term is the pointwise
product `⟨ξ / 2π⟩ ^ s f(x)`, and composing with the frequency multiplier `J^s` on the right is
exact, so `M_f J^s` is the quantization of exactly that product. The remainder is a symbol whose
estimates hold uniformly in the position, so the commutator extends to a bounded operator
`H^r → H^{r - s + 1}` for every real `r`, in particular `H^{s - 1} → L²`
(`TauCeti.Symbol.hasSobolevExtension_besselPotentialCLM_comp_quantizeUniformCLM_ofSpatial_sub`).

Writing `J^s (f u) = f J^s u + [J^s, M_f] u` and bounding `‖f J^s u‖_{L²}` pointwise gives the
**multiplier estimate with leading constant one**

`‖f u‖_{H^s} ≤ (sup_x ‖f(x)‖) ‖u‖_{H^s} + C ‖u‖_{H^{s - 1}}`,

where `sup_x ‖f(x)‖` is the supremum of the operator norms of the values of `f` and `C` depends on
`f` and `s` only (`TauCeti.Symbol.exists_norm_quantizeSobolev_ofSpatial_le`). Only the lower-order
term carries a constant depending on the derivatives of `f`. This is what makes a small principal
coefficient small in `H^s`: in the interior estimates for elliptic operators, a coefficient which is
small on a small chart contributes a small multiple of the top-order norm, which is absorbed, plus a
lower-order term. The estimate holds for every real `s`, including negative orders, where `u` is a
genuine tempered distribution and `f u` is given by the quantization `Op(f)` of the symbol
`f(x)` of order `0` (`TauCeti.Symbol.quantizeSobolev`); for scalar Schwartz multipliers that is the
multiplication `BesselPotentialSpace.smulLeftCLM`
(`TauCeti.Symbol.toDistr_quantizeSobolev_ofSpatial_smul_id`).

## Main results

* `TauCeti.Symbol.besselPotentialCLM_comp_quantizeUniformCLM_ofSpatial_sub`: the commutator
  `J^s M_f - M_f J^s` on Schwartz functions is the quantization of the remainder symbol
  `TauCeti.Symbol.sharpRemainder` of order `s - 1`.
* `TauCeti.Symbol.hasSobolevExtension_besselPotentialCLM_comp_quantizeUniformCLM_ofSpatial_sub`:
  the commutator extends to a bounded operator `H^r → H^{r - s + 1}` for every real `r`.
* `TauCeti.Symbol.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_ofSpatial_le`: the
  multiplier estimate on Schwartz functions.
* `TauCeti.Symbol.exists_norm_quantizeSobolev_ofSpatial_le`: the multiplier estimate on all of
  `H^s`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8 (the
  composition of pseudodifferential operators and its asymptotic expansion).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.5)–(2.7)
  (the composition expansion).
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap BesselPotentialSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {f : CoordinateSpace n → V →L[ℂ] W} (hf : ContDiff ℝ ∞ f)

/-! ### The commutator on Schwartz functions -/

/-- **The commutator of the Bessel potential with a multiplication operator.** For a smooth
compactly supported `f`, the commutator `J^s M_f - M_f J^s` of Mathlib's Bessel potential `J^s`
with multiplication by `f` is, on Schwartz functions, the quantization of the remainder symbol of
order `s - 1` of the composition `⟨ξ / 2π⟩ ^ s # f`. -/
theorem besselPotentialCLM_comp_quantizeUniformCLM_ofSpatial_sub
    (h : (ofSpatial f hf).HasCompactSpatialSupport) (s : ℝ) :
    SchwartzMap.besselPotentialCLM (E := CoordinateSpace n) (F := W) (s : ℂ) ∘L
        quantizeUniformCLM (ofSpatial f hf) h.isUniform -
      quantizeUniformCLM (ofSpatial f hf) h.isUniform ∘L
        SchwartzMap.besselPotentialCLM (E := CoordinateSpace n) (F := V) (s : ℂ) =
      quantizeUniformCLM ((besselPotential s).sharpRemainder (ofSpatial f hf) h 1)
        ((isUniform_besselPotential s).sharpRemainder h 1) := by
  have hsharp : quantizeUniformCLM ((besselPotential s).sharp (ofSpatial f hf) h)
      ((isUniform_besselPotential s).sharp h) =
      quantizeUniformCLM ((ofSpatial f hf).comp (besselPotential s))
          (h.isUniform.comp (isUniform_besselPotential s)) +
        quantizeUniformCLM ((besselPotential s).sharpRemainder (ofSpatial f hf) h 1)
          ((isUniform_besselPotential s).sharpRemainder h 1) := by
    ext u x
    rw [add_apply, add_apply, quantizeUniformCLM_apply, quantizeUniformCLM_apply,
      quantizeUniformCLM_apply, sharp_eq_comp_add_sharpRemainder_one, coefficient_add,
      quantizeSchwartzValue_coefficient_add, coefficient_inclusion]
    congr 2
    ext1 p
    simp [coefficient_comp, coefficient_ofSpatial, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.smul_comp]
  have hleft : SchwartzMap.besselPotentialCLM (E := CoordinateSpace n) (F := W) (s : ℂ) ∘L
      quantizeUniformCLM (ofSpatial f hf) h.isUniform =
      quantizeUniformCLM ((besselPotential s).sharp (ofSpatial f hf) h)
        ((isUniform_besselPotential s).sharp h) := by
    ext u x
    rw [ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply,
      quantizeSchwartzValue_besselPotential_sharp, SchwartzMap.besselPotentialCLM_ofReal]
    congr 2
    ext y
    rw [HasCompactSupport.toSchwartzMap_toFun, quantizeUniformCLM_apply]
  rw [hleft, hsharp, SchwartzMap.besselPotentialCLM_ofReal,
    quantizeUniformCLM_comp_besselMultiplier, add_sub_cancel_left]

/-- **The commutator of the Bessel potential with a multiplication operator has order `s - 1`.**
For a smooth compactly supported `f`, the commutator `J^s M_f - M_f J^s` extends to a bounded
operator `H^r → H^{r - s + 1}` for every real `r`; for `r = s - 1` this is a bounded operator
`H^{s - 1} → L²`. -/
theorem hasSobolevExtension_besselPotentialCLM_comp_quantizeUniformCLM_ofSpatial_sub
    (h : (ofSpatial f hf).HasCompactSpatialSupport) (s r : ℝ) :
    SchwartzMap.HasSobolevExtension
      (SchwartzMap.besselPotentialCLM (E := CoordinateSpace n) (F := W) (s : ℂ) ∘L
          quantizeUniformCLM (ofSpatial f hf) h.isUniform -
        quantizeUniformCLM (ofSpatial f hf) h.isUniform ∘L
          SchwartzMap.besselPotentialCLM (E := CoordinateSpace n) (F := V) (s : ℂ))
      r (r - s + 1) := by
  rw [besselPotentialCLM_comp_quantizeUniformCLM_ofSpatial_sub hf h s]
  convert hasSobolevExtension_quantizeUniformCLM _
    ((isUniform_besselPotential s).sharpRemainder h 1) r using 1
  push_cast
  ring

/-! ### The multiplier estimate -/

/-- **The multiplier estimate on Schwartz functions.** For a smooth compactly supported `f` and
every real `s` there is a constant `C` such that every Schwartz function `u` satisfies
`‖f u‖_{H^s} ≤ (sup_x ‖f(x)‖) ‖u‖_{H^s} + C ‖u‖_{H^{s - 1}}`: the leading coefficient is the
supremum of `‖f‖`, and the derivatives of `f` only enter the lower-order term. -/
theorem exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_ofSpatial_le
    (h : (ofSpatial f hf).HasCompactSpatialSupport) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          (quantizeUniformCLM (ofSpatial f hf) h.isUniform u)‖ ≤
        (⨆ x, ‖f x‖) * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ +
          C * ‖SchwartzMap.toBesselPotentialSpaceCLM (s - 1) 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ := SchwartzMap.hasSobolevExtension_iff_exists_norm_le.1
    (hasSobolevExtension_besselPotentialCLM_comp_quantizeUniformCLM_ofSpatial_sub hf h s
      (s - 1))
  rw [show s - 1 - s + 1 = 0 by ring] at hC
  have hfc : HasCompactSupport f := (hasCompactSpatialSupport_ofSpatial_iff hf).1 h
  have hbdd : BddAbove (Set.range fun x ↦ ‖f x‖) :=
    hf.continuous.norm.bddAbove_range_of_hasCompactSupport hfc.norm
  set M := quantizeUniformCLM (ofSpatial f hf) h.isUniform
  -- Multiplication by `f` is bounded on `L²` by the supremum of `‖f‖`.
  have hM (v : 𝓢(CoordinateSpace n, V)) :
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (M v)‖ ≤
        (⨆ x, ‖f x‖) * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 v‖ := by
    have hS : 0 ≤ ⨆ x, ‖f x‖ := Real.iSup_nonneg fun x ↦ norm_nonneg (f x)
    rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
      SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, ← ENNReal.toReal_ofReal hS,
      ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (v.memLp 2).eLpNorm_ne_top) (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (M v).continuous.aestronglyMeasurable (.of_forall fun x ↦ ?_) 2)
    have hMx : M v x = f x (v x) := by
      rw [quantizeUniformCLM_apply, funext (coefficient_ofSpatial f hf)]
      exact quantizeSchwartzValue_comp_fst f v x
    rw [hMx]
    exact ((f x).le_opNorm (v x)).trans
      (mul_le_mul_of_nonneg_right (le_ciSup hbdd x) (norm_nonneg _))
  refine ⟨C, hC0, fun u ↦ ?_⟩
  set J := SchwartzMap.besselPotentialCLM (E := CoordinateSpace n) (F := W) (s : ℂ)
  set J' := SchwartzMap.besselPotentialCLM (E := CoordinateSpace n) (F := V) (s : ℂ)
  have hJM : J (M u) = M (J' u) + (J ∘L M - M ∘L J') u := by
    simp
  calc ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (M u)‖
      = ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (J (M u))‖ := by
        rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_besselPotentialCLM, Complex.ofReal_re,
          zero_add]
    _ ≤ ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (M (J' u))‖ +
          ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 ((J ∘L M - M ∘L J') u)‖ := by
        rw [hJM, map_add]
        exact norm_add_le _ _
    _ ≤ (⨆ x, ‖f x‖) * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ +
          C * ‖SchwartzMap.toBesselPotentialSpaceCLM (s - 1) 2 u‖ := by
        gcongr
        · refine (hM _).trans_eq ?_
          rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_besselPotentialCLM, Complex.ofReal_re,
            zero_add]
        · exact hC u

/-- **The multiplier estimate.** For a smooth compactly supported `f : ℝⁿ → (V →L[ℂ] W)` and every
real `s` there is a constant `C` such that multiplication by `f`, the operator
`Op(f) : H^s → H^s` (`TauCeti.Symbol.quantizeSobolev`), satisfies

`‖f u‖_{H^s} ≤ (sup_x ‖f(x)‖) ‖u‖_{H^s} + C ‖u‖_{H^{s - 1}}`

for every `u ∈ H^s`. The leading coefficient is the supremum of the operator norms of the values of
`f`; the constant `C` of the lower-order term depends on `f` and `s`. -/
theorem exists_norm_quantizeSobolev_ofSpatial_le (h : (ofSpatial f hf).HasCompactSpatialSupport)
    (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : H^{s}(CoordinateSpace n, V),
      ‖(ofSpatial f hf).quantizeSobolev h s u‖ ≤
        (⨆ x, ‖f x‖) * ‖u‖ +
          C * ‖BesselPotentialSpace.inclusion (sub_le_self s zero_le_one) u‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_ofSpatial_le hf h s
  refine ⟨C, hC0, fun u ↦ ?_⟩
  induction u using (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s
      ENNReal.ofNat_ne_top).induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp ((ofSpatial f hf).quantizeSobolev h s).continuous)
      ((continuous_const.mul continuous_norm).add (continuous_const.mul
        (continuous_norm.comp (BesselPotentialSpace.inclusion _).continuous)))
  | ih u =>
    have hq : (ofSpatial f hf).quantizeSobolev h s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
        SchwartzMap.toBesselPotentialSpaceCLM (s - 0) 2
          (quantizeUniformCLM (ofSpatial f hf) h.isUniform u) := by
      refine BesselPotentialSpace.ext ?_
      ext φ
      rw [toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
        SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
      simp
    rw [hq, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM,
      SchwartzMap.norm_toBesselPotentialSpaceCLM, sub_zero,
      ← SchwartzMap.norm_toBesselPotentialSpaceCLM]
    exact hC u

end Symbol

end TauCeti
