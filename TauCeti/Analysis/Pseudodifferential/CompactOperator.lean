/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Rellich

/-!
# Compactness of quantizations with compact spatial support

Let `a` be a symbol of order `m` on `ℝⁿ` that vanishes for positions outside a compact set `K`.
Its quantization `Op(a)` is bounded from `H^s(ℝⁿ; V)` to `H^{s - m}(ℝⁿ; W)`
(`TauCeti.Symbol.quantizeSobolev`). This file shows that, for a finite-dimensional fibre `W`, it
is moreover **compact** as an operator `H^s → H^r` for every `r < s - m`. In particular:

* a symbol of negative order `m < 0` with compact spatial support quantizes to a compact operator
  `H^s → H^s` (`TauCeti.Symbol.exists_isCompactOperator_quantizeSobolev` with `r = s`);
* a smoothing symbol with compact spatial support quantizes to a compact operator `H^s → H^r` for
  all real `s` and `r` (`TauCeti.Symbol.IsSmoothing.exists_isCompactOperator_quantizeSobolev`).

These are the local compactness statements behind the Fredholm theory of elliptic operators: the
remainders of a parametrix are of negative order, hence compact. The hypothesis on the support
cannot be dropped: the constant symbol `1` of order `0` (or `⟨ξ⟩ ^ m`, of order `m`) quantizes to a
Fourier multiplier, which commutes with translations and is not compact.

The proof combines the Sobolev mapping theorem with the Rellich theorem for a common compact
support. Since `a(x, ξ) = 0` for `x ∉ K`, the function `Op(a) u` vanishes outside `K`, so
`φ · Op(a) u = Op(a) u` for every Schwartz function `φ` equal to `1` on `K`
(`TauCeti.Symbol.smulLeftCLM_comp_quantizeSobolev`). Hence the operator `H^s → H^r` factors as
`Op(a) : H^s → H^{s - m}` followed by `u ↦ φ u` from `H^{s - m}` to `H^r`, which is compact for
`r < s - m` (`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`).

## Main results

* `TauCeti.Symbol.smulLeftCLM_comp_quantizeSobolev`: multiplying `Op(a) u` by a Schwartz function
  equal to `1` on a set outside which `a` vanishes does not change it.
* `TauCeti.Symbol.isCompactOperator_inclusion_comp_quantizeSobolev`: `Op(a) : H^s → H^r` is
  compact for `r < s - m`, between complex Hilbert spaces `V` and `W` with `W` finite-dimensional.
* `TauCeti.Symbol.exists_isCompactOperator_quantizeSobolev`: the same for finite-dimensional
  complex normed `V` and `W`.
* `TauCeti.Symbol.IsSmoothing.exists_isCompactOperator_quantizeSobolev`: smoothing symbols with
  compact spatial support give compact operators between any two Bessel-potential spaces.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators I*, Ann. of Math. 87 (1968),
  (5.2) (operators of negative order on a compact manifold are compact on `H^s`).
* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (Rellich's theorem).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Hilbert

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

/-- **Locality of the quantization.** If the symbol `a` vanishes at every position outside `K`,
and the Schwartz function `φ` equals `1` on `K`, then multiplying `Op(a) u` by `φ` does not change
it: `φ · Op(a) = Op(a)` as operators `H^s → H^{s - m}`. -/
theorem smulLeftCLM_comp_quantizeSobolev (ha : a.HasCompactSpatialSupport) (s : ℝ)
    {K : Set (CoordinateSpace n)} (hK : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0)
    {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : EqOn φ 1 K) :
    BesselPotentialSpace.smulLeftCLM (s - m) φ ∘L a.quantizeSobolev ha s =
      a.quantizeSobolev ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext ψ
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_smulLeftCLM,
    TemperedDistribution.smulLeftCLM_apply_apply,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp only
  rw [SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth, smul_eq_mul]
  by_cases hx : x ∈ K
  · rw [hφ hx, Pi.one_apply, one_mul]
  · rw [quantizeSchwartzValue_congr_left (b := 0) (hK x hx), quantizeSchwartzValue_zero_left,
      smul_zero, smul_zero]

/-- **Compactness of quantizations with compact spatial support.** For a symbol `a` of order `m`
with compact spatial support and a finite-dimensional complex Hilbert space `W`, the quantization
`Op(a)`, followed by the inclusion `H^{s - m} ⊆ H^r`, is a compact operator `H^s → H^r` for every
`r < s - m`. For `m < 0` and `r = s` this says that operators of negative order are compact
on `H^s`. -/
theorem isCompactOperator_inclusion_comp_quantizeSobolev [FiniteDimensional ℂ W]
    (ha : a.HasCompactSpatialSupport) {r s : ℝ} (h : r < s - m) :
    IsCompactOperator (BesselPotentialSpace.inclusion h.le ∘L a.quantizeSobolev ha s) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  -- A Schwartz function `φ` equal to `1` on `K`, built from a bump function around a ball
  -- containing `K`.
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let χ : ContDiffBump (0 : CoordinateSpace n) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  obtain ⟨φ, hφχ⟩ : ∃ φ : 𝓢(CoordinateSpace n, ℂ), ∀ x, φ x = (χ x : ℂ) :=
    ⟨HasCompactSupport.toSchwartzMap (χ.hasCompactSupport.comp_left Complex.ofReal_zero)
      (Complex.ofRealCLM.contDiff.comp χ.contDiff), HasCompactSupport.toSchwartzMap_toFun _ _⟩
  have hφ : EqOn φ 1 K := fun x hx ↦ by
    have hχ : χ x = 1 := χ.one_of_mem_closedBall
      (Metric.closedBall_subset_closedBall (by simp only [χ]; linarith [le_max_left R 0]) (hR hx))
    rw [hφχ, hχ, Pi.one_apply, Complex.ofReal_one]
  rw [← smulLeftCLM_comp_quantizeSobolev ha s hKa hφ, ← ContinuousLinearMap.comp_assoc]
  exact (BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM φ h).comp_clm _

end Hilbert

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Compactness of quantizations with compact spatial support.** For a symbol `a` of order `m`
with compact spatial support between finite-dimensional complex normed spaces, and real orders
`r < s - m`, the quantization `Op(a)` extends from Schwartz functions to a compact operator
`H^s(ℝⁿ; V) → H^r(ℝⁿ; W)`.

As in `TauCeti.Symbol.exists_quantizeSobolev`, isomorphisms `e₁ : V ≃L[ℂ] ℂ^k`,
`e₂ : W ≃L[ℂ] ℂ^l` reduce this to the Hilbert-space statement
`TauCeti.Symbol.isCompactOperator_inclusion_comp_quantizeSobolev`, through
`TauCeti.Symbol.toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply`. -/
theorem exists_isCompactOperator_quantizeSobolev (a : Symbol n V W m)
    (ha : a.HasCompactSpatialSupport) {r s : ℝ} (h : r < s - m) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W), IsCompactOperator T ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Φ := (e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ
  refine ⟨BesselPotentialSpace.postcomp _ _ 2 (e₂.symm : _ →L[ℂ] W) ∘L
    (BesselPotentialSpace.inclusion h.le ∘L (a.map Φ).quantizeSobolev (ha.map Φ) s) ∘L
      BesselPotentialSpace.postcomp _ s 2 (e₁ : V →L[ℂ] _),
    ((isCompactOperator_inclusion_comp_quantizeSobolev (ha.map Φ) h).comp_clm _).clm_comp _,
    toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂ fun u φ ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]

/-- **Smoothing operators with compact spatial support are compact.** If `a` is a smoothing
symbol with compact spatial support between finite-dimensional complex normed spaces, its
quantization `Op(a)` extends from Schwartz functions to a compact operator
`H^s(ℝⁿ; V) → H^r(ℝⁿ; W)` for all real `s` and `r`. -/
theorem IsSmoothing.exists_isCompactOperator_quantizeSobolev {a : Symbol n V W m}
    (ha : a.IsSmoothing) (hc : a.HasCompactSpatialSupport) (s r : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W), IsCompactOperator T ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  obtain ⟨b, hb⟩ := isSmoothing_iff.mp ha (s - r - 1)
  rw [← hb]
  exact b.exists_isCompactOperator_quantizeSobolev (hc.of_coefficient_eq hb) (by linarith)

end FiniteDimensional

end Symbol

end TauCeti
