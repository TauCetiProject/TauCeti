/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CalderonVaillancourt
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.UniformlySmoothing
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Pseudodifferential.Composition.Uniform
import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Pseudodifferential.Sobolev

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
`⟨ξ / 2π⟩ ^ t` of order `t` (`TauCeti.Symbol.besselPotential`). Composition with `J^t` on the
right is exact: `Op(a) ∘ J^t` is the quantization of `a ⟨ξ / 2π⟩ ^ t`
(`TauCeti.Symbol.quantizeUniformCLM_comp_besselMultiplier`). Composition on the left is not, but
since the composition of two uniform symbols is again one
(`TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`), `J^{s - m} ∘ Op(a) = Op(c)` for a
uniform symbol `c` of order `s`. Hence

`Op(a) = J^{-(s - m)} ∘ Op(c ⟨ξ / 2π⟩ ^ (-s)) ∘ J^s`,

where the middle factor is a uniform symbol of order `0`, bounded on `L²` by Calderón–Vaillancourt,
and the outer factors are the isometries `H^s → L²` and `L² → H^{s - m}`.

## Main results

* `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_zero`: the Calderón–Vaillancourt
  theorem in the form `SchwartzMap.HasSobolevExtension` of an operator `L² → L²`.
* `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`: the Sobolev mapping
  `H^s → H^{s - m}` for uniform symbols and every real `s`, for complex Hilbert fibres, in the
  composable form `SchwartzMap.HasSobolevExtension`.
* `TauCeti.Symbol.IsUniformlySmoothing.hasSobolevExtension_quantizeUniformCLM`: uniformly smoothing
  symbols quantize to bounded operators `H^t → H^s` for all real `t` and `s`.
* `TauCeti.Symbol.exists_quantizeUniformSobolevHilbert`: the same mapping as an extension acting
  on tempered distributions.
* `TauCeti.Symbol.exists_quantizeUniformSobolev`: the same mapping for finite-dimensional complex
  normed fibres.
* `TauCeti.Symbol.norm_toBesselPotentialSpaceCLM_zero_quantizeUniformCLM_ofSpatial_le`: for the
  symbol of multiplication by `f`, the `Lᵖ` bound has the explicit constant `sup_x ‖f(x)‖`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv Laplacian ContDiff
  BesselPotentialSpace
open MeasureTheory Real FourierTransform

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

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

/-- On a Schwartz function, an extension of `Op(b)` gives the tempered distribution of
`Op(b) u`. -/
private theorem exists_toDistr_of_hasSobolevExtension {b : Symbol n V W m} {hb : b.IsUniform}
    (h : SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) s r) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue b.coefficient u x := by
  obtain ⟨T, hT⟩ := SchwartzMap.hasSobolevExtension_iff.mp h
  refine ⟨T, fun u φ ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_apply T, hT, ContinuousLinearMap.comp_apply,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply]
  simp only [quantizeUniformCLM_apply]

/-- Uniform symbols of order at most `s` quantize to bounded operators `H^s → L²`:
`Op(b) = Op(b ⟨ξ / 2π⟩ ^ (-s)) ∘ J^s`, where `J^s : H^s → L²` is an isometry and the first
factor has order at most `0`. -/
private theorem hasSobolevExtension_quantizeUniformCLM_of_le {μ : ℝ} (b : Symbol n V W μ)
    (hb : b.IsUniform) {s : ℝ} (hs : μ ≤ s) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) s 0 := by
  have hb' := hb.comp (isUniform_besselPotential (V := V) (n := n) (-s))
  have hJ := SchwartzMap.hasSobolevExtension_besselMultiplier (F := V) (E := CoordinateSpace n) s
    (r := 0) (s := s) (by ring)
  have hb'' : quantizeUniformCLM b hb = quantizeUniformCLM _ hb' ∘L
      SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) := by
    rw [quantizeUniformCLM_comp_besselMultiplier]
    exact quantizeUniformCLM_congr _ _ (by
      rw [coefficient_comp_besselPotential_comp_besselPotential, neg_add_cancel,
        coefficient_comp_besselPotential_zero])
  rw [hb'']
  exact (hasSobolevExtension_quantizeUniformCLM_zero hb' (by linarith)).comp hJ

/-- **Sobolev mapping of uniform symbols**, in composable form. Uniform symbols of order `m`
quantize to bounded operators `H^s → H^{s - m}` for every real `s`. -/
theorem hasSobolevExtension_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) := by
  -- `J^{s - m} ∘ Op(a) = Op(c)` for a uniform symbol `c` of order `s`.
  obtain ⟨c, hc, hcomp⟩ :=
    (isUniform_besselPotential (V := W) (n := n) (s - m)).exists_quantizeUniformCLM_comp ha
  have hJ : quantizeUniformCLM (besselPotential (s - m)) (isUniform_besselPotential _) =
      SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)) := by
    ext u x
    rw [quantizeUniformCLM_apply, quantizeSchwartzValue_besselPotential]
  have ha' : quantizeUniformCLM a ha = SchwartzMap.fourierMultiplierCLM W
      (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (-(s - m) / 2) : ℝ) : ℂ)) ∘L
        quantizeUniformCLM c hc := by
    rw [← hcomp, ← ContinuousLinearMap.comp_assoc, hJ,
      SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_neg_comp_fourierMultiplierCLM,
      ContinuousLinearMap.id_comp]
  rw [ha']
  exact (SchwartzMap.hasSobolevExtension_besselMultiplier (-(s - m)) (by ring)).comp
    (hasSobolevExtension_quantizeUniformCLM_of_le c hc (by linarith))

/-- **Uniformly smoothing symbols gain every number of derivatives.** The quantization of a
uniformly smoothing symbol extends to a bounded operator `H^t → H^s` for all real `t` and `s`. -/
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
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  exists_toDistr_of_hasSobolevExtension (hasSobolevExtension_quantizeUniformCLM a ha s)

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

/-! ### Sobolev mapping -/

section Mapping

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Sobolev mapping of uniform symbols.** Let `a` be a symbol of order `m` whose estimates are
uniform in the position, between finite-dimensional complex normed spaces. For every real `s`,
the quantization `Op(a)` extends from Schwartz functions to a bounded operator
`H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`. No compact spatial support is needed.

The norms of `V` and `W` need not come from inner products: as for
`TauCeti.Symbol.exists_quantizeSobolev`, isomorphisms with `ℂ^k` and `ℂ^l` reduce the statement
to complex Hilbert fibres (`TauCeti.Symbol.exists_quantizeUniformSobolevHilbert`). -/
theorem exists_quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  obtain ⟨T, hT⟩ := exists_quantizeUniformSobolevHilbert _ (ha.map
    ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)) s
  exact ⟨_, toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂ hT⟩

end Mapping

end Symbol

end TauCeti
