/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.BesselPotentialSpace
public import TauCeti.Analysis.Pseudodifferential.CalderonVaillancourt
public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Pseudodifferential.Frequency.BesselConjugation
import TauCeti.Analysis.Pseudodifferential.L2

/-!
# Sobolev mapping of uniform symbols

Let `a` be a symbol of order `m` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). This file proves that its left quantization `Op(a)` extends from
Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between
Bessel-potential spaces for every real `s`, for complex Hilbert fibres of any dimension
(`TauCeti.Symbol.exists_quantizeUniformSobolevHilbert`) and for finite-dimensional normed fibres
(`TauCeti.Symbol.exists_quantizeUniformSobolev`). In contrast to
`TauCeti.Symbol.exists_quantizeSobolev`, no compact spatial support is assumed; the case
`s = m = 0` is the Calderón–Vaillancourt theorem `TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`.

## Composing with Bessel multipliers

Write `J^t` for Mathlib's Bessel multiplier, the Fourier multiplier `(1 + ‖ζ‖²) ^ (t / 2)`, which
is an isometry `H^s → H^{s - t}`; it is the quantization of the uniform symbol
`⟨ξ / 2π⟩ ^ t` of order `t` (`TauCeti.Symbol.besselPotential`,
`TauCeti.Symbol.quantizeUniformCLM_besselPotential`). Conjugating `Op(a)` by Bessel multipliers via
`TauCeti.Symbol.besselConjugate` reduces the order to `0`
(`TauCeti.Symbol.quantizeUniformCLM_besselConjugate_fourierMultiplierCLM`,
`TauCeti.Symbol.IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq`), so

`Op(a) = J^{-(s - m)} ∘ Op(a.besselConjugate ha s) ∘ J^s`,

where the middle factor is a uniform symbol of order `0`, bounded on `L²` by Calderón–Vaillancourt,
and the outer factors are the isometries `H^s → L²` and `L² → H^{s - m}`.

## Main results

* `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_zero`: the Calderón–Vaillancourt
  theorem in the form `SchwartzMap.HasSobolevExtension` of an operator `L² → L²`.
* `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM` and
  `TauCeti.Symbol.IsUniform.hasBesselPotentialSpaceExtension_two`: Sobolev mapping
  `H^s → H^{s - m}` (`p = 2`) for uniform symbols and every real `s`, for complex Hilbert fibres.
* `TauCeti.Symbol.IsUniformlySmoothing.hasSobolevExtension_quantizeUniformCLM`: uniformly smoothing
  symbols gain every number of derivatives.
* `TauCeti.Symbol.exists_quantizeUniformSobolevHilbert`: Sobolev mapping for complex Hilbert fibres
  acting on tempered distributions.
* `IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional`,
  `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_of_finiteDimensional`,
  `TauCeti.Symbol.IsUniform.hasBesselPotentialSpaceExtension_two_of_finiteDimensional`,
  `TauCeti.Symbol.exists_quantizeUniformSobolev`: Sobolev estimates and extensions for
  finite-dimensional complex normed fibres.
* `TauCeti.Symbol.norm_toBesselPotentialSpaceCLM_zero_quantizeUniformCLM_ofSpatial_le` and
  `TauCeti.Symbol.norm_quantizeSobolev_ofSpatial_le`: explicit `Lᵖ` / `L²` norm bounds for
  multiplication symbols `f(x)`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
-/

public section

open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv Laplacian ContDiff
  BesselPotentialSpace
open MeasureTheory Real FourierTransform

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Bessel-conjugate norm transport -/

section BesselNorm

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

private theorem norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (a.besselConjugate ha s).coefficient v) 2 volume ≤
        ENNReal.ofReal C * eLpNorm v 2 volume) (u : 𝓢(CoordinateSpace n, V)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
      C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  set v := SchwartzMap.fourierMultiplierCLM V
    (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_eq_eLpNorm,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_eq_eLpNorm,
    ← quantizeUniformCLM_besselConjugate_fourierMultiplierCLM ha s u, coe_quantizeUniformCLM,
    ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (v.memLp 2).eLpNorm_ne_top) (hC v)

end BesselNorm

/-! ### Extension to Bessel-potential spaces -/

section Extension

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {s r : ℝ}

/-- **Calderón–Vaillancourt.** The quantization of a uniform symbol of order at most `0` extends
to a bounded operator on `H⁰ = L²`. -/
theorem hasSobolevExtension_quantizeUniformCLM_zero {b : Symbol n V W m}
    (hb : b.IsUniform) (hm : m ≤ 0) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) 0 0 := by
  obtain ⟨T, hT⟩ := exists_quantizeUniformOrderZeroLp (inclusion hm b) (hb.inclusion hm)
  refine SchwartzMap.hasSobolevExtension_iff.mpr
    ⟨((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) W 0 2).symm.toContinuousLinearEquiv :
      Lp W 2 (volume : Measure (CoordinateSpace n)) →L[ℂ] H^{0}(CoordinateSpace n, W)) ∘L T ∘L
    ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V 0 2).toContinuousLinearEquiv :
      H^{0}(CoordinateSpace n, V) →L[ℂ] Lp V 2 (volume : Measure (CoordinateSpace n))), ?_⟩
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply,
    SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero, LinearIsometryEquiv.symm_apply_eq]
  refine Lp.ext ((hT u).trans ?_)
  filter_upwards [(quantizeUniformCLM b hb u).coeFn_toLp 2] with x hx
  rw [hx, coefficient_inclusion, quantizeUniformCLM_apply]

/-- **Sobolev mapping of uniform symbols**, in composable form, for complex Hilbert fibres. Uniform
symbols of order `m` quantize to bounded operators `H^s → H^{s - m}` for every real `s`. -/
theorem hasSobolevExtension_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) :=
  let ⟨C, hC0, hC⟩ := (ha.besselConjugate s).exists_eLpNorm_quantizeSchwartzValue_le
  SchwartzMap.hasSobolevExtension_iff_exists_norm_le.mpr
    ⟨C, hC0, norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate ha s hC0 hC⟩

/-- Every uniform symbol between complex Hilbert spaces has the `H^s` (`p = 2`) extension property
`HasBesselPotentialSpaceExtension`, without needing compact spatial support. -/
theorem IsUniform.hasBesselPotentialSpaceExtension_two {a : Symbol n V W m} (ha : a.IsUniform) :
    a.HasBesselPotentialSpaceExtension ha 2 :=
  hasBesselPotentialSpaceExtension_iff.2 fun s u ↦ by
    obtain ⟨C, -, hC⟩ := SchwartzMap.hasSobolevExtension_iff_exists_norm_le.mp
      (hasSobolevExtension_quantizeUniformCLM a ha s)
    exact quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM_of_norm_le ha
      ENNReal.ofNat_ne_top hC u

/-- **Uniformly smoothing symbols gain every number of derivatives.** For complex Hilbert fibres,
the quantization of a uniformly smoothing symbol extends to a bounded operator `H^t → H^s` for all
real `t` and `s`. -/
theorem IsUniformlySmoothing.hasSobolevExtension_quantizeUniformCLM {r : Symbol n V W m}
    (hr : r.IsUniformlySmoothing) (t s : ℝ) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM r hr.isUniform) t s := by
  obtain ⟨r', hr', hrr'⟩ := isUniformlySmoothing_iff.1 hr (t - s)
  rw [quantizeUniformCLM_congr hr.isUniform hr' hrr'.symm]
  simpa using Symbol.hasSobolevExtension_quantizeUniformCLM r' hr' t

/-- **Sobolev mapping of uniform symbols**, for complex Hilbert fibres. Let `a` be a symbol of
order `m` whose estimates are uniform in the position. For every real `s`, the quantization
`Op(a)` extends from Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`.
No compact spatial support and no finite dimension is needed. -/
theorem exists_quantizeUniformSobolevHilbert (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  obtain ⟨T, hT⟩ := SchwartzMap.hasSobolevExtension_iff.mp
    (hasSobolevExtension_quantizeUniformCLM a ha s)
  refine ⟨T, fun u φ ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_apply T, hT, ContinuousLinearMap.comp_apply,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply]
  simp only [quantizeUniformCLM_apply]

end Extension

/-! ### Multiplication operators -/

section Multiplication

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- **Multiplication is bounded on `Lᵖ` by the supremum.** For a smooth `f` of the position with
bounded derivatives, multiplication by `f`, the quantization `Op(f)`
(`TauCeti.Symbol.quantizeUniformCLM_ofSpatial_apply`), satisfies
`‖f u‖_{Lᵖ} ≤ (sup_x ‖f(x)‖) ‖u‖_{Lᵖ}` on Schwartz functions. -/
theorem norm_toBesselPotentialSpaceCLM_zero_quantizeUniformCLM_ofSpatial_le
    {f : CoordinateSpace n → V →L[ℂ] W} (hf : ContDiff ℝ ∞ f) (ha : (ofSpatial f hf).IsUniform)
    (p : ENNReal) [Fact (1 ≤ p)] (u : 𝓢(CoordinateSpace n, V)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM 0 p (quantizeUniformCLM (ofSpatial f hf) ha u)‖ ≤
      (⨆ x, ‖f x‖) * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 p u‖ := by
  obtain ⟨C, hC⟩ := (isUniform_ofSpatial_iff hf).1 ha []
  have hbdd : BddAbove (Set.range fun x ↦ ‖f x‖) := ⟨C, Set.forall_mem_range.2 fun x ↦ by
    simpa only [coordinateDeriv_nil] using hC x⟩
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    ← ENNReal.toReal_ofReal (Real.iSup_nonneg fun x ↦ norm_nonneg (f x)), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (u.memLp p).eLpNorm_ne_top) (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (quantizeUniformCLM _ ha u).continuous.aestronglyMeasurable (.of_forall fun x ↦ ?_) p)
  rw [quantizeUniformCLM_ofSpatial_apply]
  exact ((f x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (le_ciSup hbdd x) (norm_nonneg _))

end Multiplication

section MultiplicationL2

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Multiplication operators on `L²`.** For a compactly supported smooth
`f : ℝⁿ → (V →L[ℂ] W)` with `‖f x‖ ≤ C` everywhere, the quantization of the symbol `f(x)` of
order `0`, as an operator `H^0 → H^0`, has norm at most `C`. -/
theorem norm_quantizeSobolev_ofSpatial_le {f : CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) (h : (ofSpatial f hf).HasCompactSpatialSupport) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖(ofSpatial f hf).quantizeSobolev h 0‖ ≤ C := by
  -- The target order is `0 - 0`, which is only propositionally `0`.
  have hnorm {t : ℝ} (ht : t = 0) (w : 𝓢(CoordinateSpace n, W)) :
      ‖SchwartzMap.toBesselPotentialSpaceCLM t 2 w‖ =
        ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 w‖ := by
    subst ht
    rfl
  -- It suffices to bound the operator on the dense subspace of Schwartz functions.
  refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hC 0)) fun g ↦
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) 0 ENNReal.ofNat_ne_top).induction_on
      g (isClosed_le (by fun_prop) (by fun_prop)) fun u ↦ ?_
  have hu : (h.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
      ((ofSpatial f hf).contDiff_quantizeSchwartzValue u) =
        quantizeUniformCLM _ h.isUniform u := by
    ext x
    rw [HasCompactSupport.toSchwartzMap_toFun, quantizeUniformCLM_apply]
  rw [h.quantizeSobolev_toBesselPotentialSpaceCLM, hnorm (sub_self 0), hu]
  exact (norm_toBesselPotentialSpaceCLM_zero_quantizeUniformCLM_ofSpatial_le hf h.isUniform 2
    u).trans (mul_le_mul_of_nonneg_right (ciSup_le hC) (norm_nonneg _))

end MultiplicationL2

/-! ### Sobolev mapping for finite-dimensional normed fibres -/

section Mapping

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Sobolev estimate on Schwartz functions** for finite-dimensional complex normed fibres:
`‖Op(a) u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}`. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ :=
  let ⟨C, hC0, hC⟩ :=
    (ha.besselConjugate s).exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional
  ⟨C, hC0, norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate ha s hC0 hC⟩

/-- Uniform symbols of order `m` between finite-dimensional complex normed fibres quantize to
bounded operators `H^s → H^{s - m}` (`HasSobolevExtension`). -/
theorem hasSobolevExtension_quantizeUniformCLM_of_finiteDimensional (a : Symbol n V W m)
    (ha : a.IsUniform) (s : ℝ) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) :=
  SchwartzMap.hasSobolevExtension_iff_exists_norm_le.mpr
    (ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s)

/-- Every uniform symbol between finite-dimensional complex normed spaces has the `H^s`
(`p = 2`) extension property `HasBesselPotentialSpaceExtension`, without needing compact spatial
support. -/
theorem IsUniform.hasBesselPotentialSpaceExtension_two_of_finiteDimensional {a : Symbol n V W m}
    (ha : a.IsUniform) : a.HasBesselPotentialSpaceExtension ha 2 :=
  hasBesselPotentialSpaceExtension_iff.2 fun s u ↦ by
    obtain ⟨C, -, hC⟩ :=
      ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s
    exact quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM_of_norm_le ha
      ENNReal.ofNat_ne_top hC u

/-- **Sobolev mapping of uniform symbols.** Let `a` be a symbol of order `m` whose estimates are
uniform in the position, between finite-dimensional complex normed spaces. For every real `s`,
the quantization `Op(a)` extends from Schwartz functions to a bounded operator
`H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`. No compact spatial support is needed. -/
theorem exists_quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  have hext := ha.hasBesselPotentialSpaceExtension_two_of_finiteDimensional
  refine ⟨a.quantizeUniformBesselPotentialSpace ha s 2, fun u φ ↦ ?_⟩
  rw [hext.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM s u,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply]
  simp only [quantizeUniformCLM_apply]

end Mapping

end Symbol

end TauCeti
