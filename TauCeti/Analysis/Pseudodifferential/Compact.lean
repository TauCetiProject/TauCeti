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
Its quantization `Op(a)` is bounded from `H^s` to `H^{s - m}` (`TauCeti.Symbol.quantizeSobolev`),
and every output `Op(a) u` is supported in `K`. By Rellich's theorem for a common compact support
(`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`), `Op(a)` is therefore a
**compact** operator `H^s → H^r` for every `r < s - m`, that is, whenever the target order is
strictly below the order `s - m` that `Op(a)` reaches.

Two cases are the local building blocks of the compactness statements for operators on compact
manifolds:

* an operator of **negative order** `m < 0` is compact from `H^s` to `H^s`
  (`TauCeti.Symbol.exists_isCompactOperator_quantizeSobolev_of_neg`);
* a **smoothing** operator is compact from `H^s` to `H^t` for all real `s` and `t`
  (`TauCeti.Symbol.IsSmoothing.exists_isCompactOperator_quantizeSobolev`).

Compact spatial support is essential here. The constant symbol `1` of order `0`, which does not
have it, quantizes to the identity, and the inclusion `H^s ⊆ H^r` on all of `ℝⁿ` is not compact:
translates of a fixed bump function have no convergent subsequence.

## Main results

* `TauCeti.Symbol.smulLeftCLM_comp_quantizeSobolev`: multiplying `Op(a) u` by a Schwartz function
  equal to `1` wherever `a` does not vanish leaves it unchanged.
* `TauCeti.Symbol.isCompactOperator_inclusion_comp_quantizeSobolev`: for complex Hilbert spaces
  `V` and `W` with `W` finite-dimensional, `Op(a) : H^s → H^r` is compact for `r < s - m`.
* `TauCeti.Symbol.exists_isCompactOperator_quantizeSobolev`: the same for finite-dimensional
  complex normed `V` and `W`, as an operator agreeing with `Op(a)` on Schwartz functions.

## References

* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (Rellich's theorem).
* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  (5.2): operators of negative order are compact.
-/

public section

noncomputable section

open MeasureTheory Metric TemperedDistribution
open scoped SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Hilbert

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

/-- **Output support of `Op(a)` on `H^s`.** If a scalar Schwartz function `φ` equals `1` at every
position where the symbol `a` does not vanish, then `φ Op(a) u = Op(a) u` for every `u ∈ H^s`. -/
theorem smulLeftCLM_comp_quantizeSobolev (ha : a.HasCompactSpatialSupport) (s : ℝ)
    {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : ∀ x ξ, a.coefficient (x, ξ) ≠ 0 → φ x = 1) :
    BesselPotentialSpace.smulLeftCLM (s - m) φ ∘L a.quantizeSobolev ha s =
      a.quantizeSobolev ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext ψ
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_smulLeftCLM,
    smulLeftCLM_apply_apply, toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp only
  rw [SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth]
  by_cases hx : ∃ ξ, a.coefficient (x, ξ) ≠ 0
  · obtain ⟨ξ, hξ⟩ := hx
    rw [hφ x ξ hξ, one_smul]
  · push Not at hx
    rw [quantizeSchwartzValue_congr_left (b := 0) hx, quantizeSchwartzValue_zero_left, smul_zero,
      smul_zero]

/-- **Compactness of quantizations with compact spatial support.** For a symbol `a` of order `m`
with compact spatial support, with values in operators into a finite-dimensional complex Hilbert
space, and real orders `r < s - m`, the quantization `Op(a)`, followed by the inclusion
`H^{s - m} ⊆ H^r`, is a compact operator `H^s → H^r`. -/
theorem isCompactOperator_inclusion_comp_quantizeSobolev [FiniteDimensional ℂ W]
    (ha : a.HasCompactSpatialSupport) {r s : ℝ} (h : r < s - m) :
    IsCompactOperator
      (BesselPotentialSpace.inclusion h.le ∘L a.quantizeSobolev ha s :
        H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W)) := by
  -- A smooth bump function equal to `1` on a ball containing the spatial support.
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let f : ContDiffBump (0 : CoordinateSpace n) :=
    ⟨max R 1, max R 1 + 1, by positivity, by linarith⟩
  have hfc : HasCompactSupport fun x ↦ (f x : ℂ) :=
    f.hasCompactSupport.comp_left Complex.ofReal_zero
  let φ : 𝓢(CoordinateSpace n, ℂ) :=
    hfc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp f.contDiff)
  have hφ : ∀ x ξ, a.coefficient (x, ξ) ≠ 0 → φ x = 1 := fun x ξ hxξ ↦ by
    have hx : x ∈ closedBall (0 : CoordinateSpace n) f.rIn :=
      closedBall_subset_closedBall (le_max_left R 1) (hR (by_contra fun hx ↦ hxξ (hKa x hx ξ)))
    have hφx : φ x = (f x : ℂ) := HasCompactSupport.toSchwartzMap_toFun _ _ x
    rw [hφx, f.one_of_mem_closedBall hx, Complex.ofReal_one]
  rw [← smulLeftCLM_comp_quantizeSobolev ha s hφ, ← ContinuousLinearMap.comp_assoc]
  exact (BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM φ h).comp_clm _

end Hilbert

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Compactness of quantizations with compact spatial support.** For a symbol `a` of order `m`
with compact spatial support between finite-dimensional complex normed spaces and real orders
`r < s - m`, the quantization `Op(a)` extends from Schwartz functions to a compact operator
`H^s(ℝⁿ; V) → H^r(ℝⁿ; W)`. -/
theorem exists_isCompactOperator_quantizeSobolev (a : Symbol n V W m)
    (ha : a.HasCompactSpatialSupport) {r s : ℝ} (h : r < s - m) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W), IsCompactOperator T ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- As in `exists_quantizeSobolev`, transport along isomorphisms `e₁ : V ≃L[ℂ] ℂ^k` and
  -- `e₂ : W ≃L[ℂ] ℂ^l` to the Hilbert-space statement
  -- `isCompactOperator_inclusion_comp_quantizeSobolev`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Φ := (e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ
  refine ⟨BesselPotentialSpace.postcomp _ _ 2 (e₂.symm : _ →L[ℂ] W) ∘L
    (BesselPotentialSpace.inclusion h.le ∘L (a.map Φ).quantizeSobolev (ha.map Φ) s) ∘L
      BesselPotentialSpace.postcomp _ s 2 (e₁ : V →L[ℂ] _),
    ((isCompactOperator_inclusion_comp_quantizeSobolev (ha.map Φ) h).comp_clm _).clm_comp _,
    fun u φ ↦ ?_⟩
  have hc : (a.map Φ).coefficient = fun p ↦ e₁.arrowCongr e₂ (a.coefficient p) :=
    funext fun p ↦ by simp [Φ]
  have hq (x : CoordinateSpace n) :
      quantizeSchwartzValue (a.map Φ).coefficient (u.postcompCLM (e₁ : V →L[ℂ] _)) x =
        e₂ (quantizeSchwartzValue a.coefficient u x) := by
    rw [hc, quantizeSchwartzValue_arrowCongr]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
    BesselPotentialSpace.toDistr_postcomp_apply, BesselPotentialSpace.toDistr_inclusion,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
  simp only [hq, ← map_smul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- **Operators of negative order are compact.** For a symbol `a` of negative order `m < 0` with
compact spatial support between finite-dimensional complex normed spaces, the quantization
`Op(a)` extends from Schwartz functions to a compact operator `H^s(ℝⁿ; V) → H^s(ℝⁿ; W)`, for
every real `s`. -/
theorem exists_isCompactOperator_quantizeSobolev_of_neg (a : Symbol n V W m)
    (ha : a.HasCompactSpatialSupport) (hm : m < 0) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s}(CoordinateSpace n, W), IsCompactOperator T ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  a.exists_isCompactOperator_quantizeSobolev ha (by linarith)

/-- **Smoothing operators are compact.** For a smoothing symbol `a` with compact spatial support
between finite-dimensional complex normed spaces, the quantization `Op(a)` extends from Schwartz
functions to a compact operator `H^s(ℝⁿ; V) → H^t(ℝⁿ; W)`, for all real `s` and `t`. -/
theorem IsSmoothing.exists_isCompactOperator_quantizeSobolev {a : Symbol n V W m}
    (h : a.IsSmoothing) (ha : a.HasCompactSpatialSupport) (s t : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{t}(CoordinateSpace n, W), IsCompactOperator T ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  obtain ⟨b, hb⟩ := isSmoothing_iff.mp h (s - t - 1)
  rw [← hb]
  exact b.exists_isCompactOperator_quantizeSobolev (ha.of_coefficient_eq hb) (by linarith)

end FiniteDimensional

end Symbol

end TauCeti
