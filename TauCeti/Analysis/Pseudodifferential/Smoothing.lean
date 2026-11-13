/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CompactOperator
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Smoothing operators produce smooth functions

Let `a` be a smoothing symbol on `ℝⁿ` (`TauCeti.Symbol.IsSmoothing`: its coefficient satisfies the
symbol estimates of every real order) that vanishes for positions outside a compact set. Its
quantization `Op(a)` extends from Schwartz functions to a bounded operator
`T : H^s(ℝⁿ; V) → H^r(ℝⁿ; W)` for all real `s` and `r`. This file shows that `T u` is a smooth
function for every `u ∈ H^s`, however negative `s` is: smoothing operators send distributions of
finite Sobolev order to smooth functions. Moreover `T u` vanishes at every position at which the
symbol vanishes for all frequencies, so it is compactly supported.

This is the property that makes the smoothing remainders of a parametrix harmless in elliptic
regularity: if `Q P = 1 + R` with `R` smoothing, then `u = Q (P u) - R u` differs from `Q (P u)`
by a smooth function.

Since `a` has every real order `m'`, the same operator also maps `H^s` into `H^{s - m'}` for every
`m'`: the Sobolev extension of `Op(a)` depends only on the coefficient of `a`
(`TauCeti.Symbol.toDistr_quantizeSobolev_congr`,
`TauCeti.Symbol.toDistr_apply_eq_toDistr_quantizeSobolev`), because two continuous extensions that
agree on the dense subspace of Schwartz functions agree everywhere. Hence `Op(a) u` lies in `H^t`
for every real `t` (`TauCeti.Symbol.IsSmoothing.memSobolev_toDistr_quantizeSobolev`), and the
Sobolev embedding `H^t ⊆ C^k`, `t > k + n / 2`
(`TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev`), makes it a smooth
function. For the support, if `a` vanishes outside a closed set `L` and `x ∉ L`, a smooth cutoff
`φ` equal to `1` near the part of `L` where `a` lives and vanishing at `x` satisfies
`φ · T u = T u` (`TauCeti.Symbol.smulLeftCLM_comp_quantizeSobolev`), so the smooth function
vanishes at `x`.

## Main results

* `TauCeti.Symbol.IsSmoothing.exists_contDiff_quantizeSobolev`: `Op(a) u` is a smooth function.
* `TauCeti.Symbol.IsSmoothing.exists_contDiff_hasCompactSupport_quantizeSobolev`: for complex
  Hilbert spaces `V` and `W`, `Op(a) u` is a smooth compactly supported function vanishing outside
  every closed set outside which `a` vanishes.
* `TauCeti.Symbol.IsSmoothing.exists_contDiff_toDistr_apply_eq`: the same for every bounded
  extension `H^s → H^r` of `Op(a)` between finite-dimensional complex normed fibres.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (operators
  with symbols of order `-∞`).
* G. B. Folland, *Real Analysis*, 2nd ed., §9.3 (the Sobolev embedding `H_s ⊆ C^k` for
  `s > k + n / 2`).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3
  (operators of order `-∞` map `H^s` into `H^∞`).
-/

public section

noncomputable section

open MeasureTheory Set TemperedDistribution
open scoped SchwartzMap BesselPotentialSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Hilbert

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

/-- **Smoothing operators produce smooth functions.** For a smoothing symbol `a` with compact
spatial support and every `u ∈ H^s`, `s` real, the quantization `Op(a) u` is a smooth function
`g`: it pairs with every Schwartz function `φ` as `∫ φ • g`. Taking `s` negative, this applies to
distributions that are not functions. -/
theorem IsSmoothing.exists_contDiff_quantizeSobolev (ha : a.IsSmoothing)
    (hc : a.HasCompactSpatialSupport) (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ∃ g : CoordinateSpace n → W, ContDiff ℝ ∞ g ∧
      ∀ φ : 𝓢(CoordinateSpace n, ℂ), (a.quantizeSobolev hc s u).toDistr φ = ∫ x, φ x • g x :=
  exists_contDiff_eq_integral_of_forall_memSobolev fun t ↦
    ha.memSobolev_toDistr_quantizeSobolev hc s t u

/-- A continuous representative of `Op(a) u` vanishes at every position `x` outside a closed set
`L` outside which `a` vanishes: a cutoff `φ` equal to `1` near the part of `L` where `a` lives and
vanishing at `x` satisfies `φ · Op(a) u = Op(a) u`. -/
private theorem eq_zero_of_toDistr_quantizeSobolev_apply_eq (hc : a.HasCompactSpatialSupport)
    {L : Set (CoordinateSpace n)} (hL : IsClosed L) (hLa : ∀ x ∉ L, ∀ ξ, a.coefficient (x, ξ) = 0)
    {s : ℝ} {u : H^{s}(CoordinateSpace n, V)} {v : Lp W 2 (volume : Measure (CoordinateSpace n))}
    (hv : (a.quantizeSobolev hc s u).toDistr = v) {g : CoordinateSpace n → W} (hg : Continuous g)
    (hvg : v =ᵐ[volume] g) {x : CoordinateSpace n} (hx : x ∉ L) : g x = 0 := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp hc
  -- A smooth compactly supported cutoff equal to `1` near `L ∩ K` whose support misses `x`.
  obtain ⟨ψ, hψ, -, hψ1, hψc, hψx⟩ := (hK.inter_left hL).exists_contDiff_cutoff
    isOpen_compl_singleton fun y hy ↦ ne_of_mem_of_not_mem hy.1 hx
  let φ : 𝓢(CoordinateSpace n, ℂ) :=
    (hψc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hψ)
  have hφ (y : CoordinateSpace n) : φ y = ψ y := HasCompactSupport.toSchwartzMap_toFun _ _ y
  have hφ1 : EqOn φ 1 (L ∩ K) := fun y hy ↦ by
    rw [hφ, Pi.one_apply, interior_subset (hψ1 hy), Complex.ofReal_one]
  have hloc := DFunLike.congr_fun (smulLeftCLM_comp_quantizeSobolev hc s (K := L ∩ K)
    (fun y hy ξ ↦ (not_and_or.1 hy).elim (fun h ↦ hLa y h ξ) (fun h ↦ hKa y h ξ)) hφ1) u
  -- Hence `v = φ v` as distributions, so `g = φ g` almost everywhere, hence everywhere.
  have hφg : Continuous fun y ↦ φ y • g y := φ.continuous.smul hg
  have hvφ : v =ᵐ[volume] fun y ↦ φ y • g y :=
    Lp.ae_eq_of_toTemperedDistribution_apply_eq v hφg.locallyIntegrable fun ψ' ↦ by
      rw [← hv, ← hloc, ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_smulLeftCLM,
        hv, Lp.smulLeftCLM_toTemperedDistribution_apply φ.hasTemperateGrowth]
      exact integral_congr_ae (hvg.mono fun y hy ↦ by simp only [hy])
  have hgφ := congrFun ((hg.ae_eq_iff_eq volume hφg).1 (hvg.symm.trans hvφ)) x
  rwa [hφ, image_eq_zero_of_notMem_tsupport fun h ↦ hψx h rfl, Complex.ofReal_zero, zero_smul]
    at hgφ

/-- **Smoothing operators produce smooth compactly supported functions.** Let `a` be a smoothing
symbol with compact spatial support between complex Hilbert spaces. For every `u ∈ H^s(ℝⁿ; V)`,
whatever the real order `s`, the distribution `Op(a) u` is a smooth compactly supported function
`g`, which vanishes outside every closed set `K` outside which the symbol vanishes. -/
theorem IsSmoothing.exists_contDiff_hasCompactSupport_quantizeSobolev (ha : a.IsSmoothing)
    (hc : a.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)} (hK : IsClosed K)
    (hKa : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ∃ g : CoordinateSpace n → W, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ K ∧
      ∀ φ : 𝓢(CoordinateSpace n, ℂ),
        (a.quantizeSobolev hc s u).toDistr φ = ∫ x, φ x • g x := by
  obtain ⟨g, hg, hgφ⟩ := ha.exists_contDiff_quantizeSobolev hc s u
  obtain ⟨v, hv⟩ := memSobolev_zero_iff.1 (ha.memSobolev_toDistr_quantizeSobolev hc s 0 u)
  have hvg : v =ᵐ[volume] g :=
    Lp.ae_eq_of_toTemperedDistribution_apply_eq v hg.continuous.locallyIntegrable fun φ ↦ by
      rw [← hv, hgφ]
  have hsupp {L : Set (CoordinateSpace n)} (hL : IsClosed L)
      (hLa : ∀ x ∉ L, ∀ ξ, a.coefficient (x, ξ) = 0) : tsupport g ⊆ L :=
    closure_minimal (fun x hx ↦ by_contra fun hxL ↦ hx
      (eq_zero_of_toDistr_quantizeSobolev_apply_eq hc hL hLa hv hg.continuous hvg hxL)) hL
  obtain ⟨K₀, hK₀, hK₀a⟩ := hasCompactSpatialSupport_iff.mp hc
  exact ⟨g, hg, hK₀.of_isClosed_subset (isClosed_tsupport g) (hsupp hK₀.isClosed hK₀a),
    hsupp hK hKa, hgφ⟩

end Hilbert

section Map

variable {V W V' W' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

/-- The image of a smoothing symbol under a continuous linear map of the coefficient spaces is
smoothing. -/
theorem IsSmoothing.map {a : Symbol n V W m} (ha : a.IsSmoothing)
    (Φ : (V →L[ℂ] W) →L[ℝ] (V' →L[ℂ] W')) : (a.map Φ).IsSmoothing := by
  refine isSmoothing_iff.2 fun m' ↦ ?_
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨b.map Φ, funext fun p ↦ by rw [coefficient_map, coefficient_map, hb]⟩

end Map

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W] {a : Symbol n V W m}

/-- **Smoothing operators produce smooth functions.** Let `a` be a smoothing symbol with compact
spatial support between finite-dimensional complex normed spaces, and let
`T : H^s(ℝⁿ; V) → H^r(ℝⁿ; W)` be a bounded operator agreeing with `Op(a)` on Schwartz functions,
for any real orders `s` and `r` (such an operator exists by
`TauCeti.Symbol.IsSmoothing.exists_isCompactOperator_quantizeSobolev`). Then for every
`u ∈ H^s` the distribution `T u` is a smooth compactly supported function `g`, which vanishes
outside every closed set `K` outside which the symbol vanishes.

As in `TauCeti.Symbol.exists_quantizeSobolev`, isomorphisms `e₁ : V ≃L[ℂ] ℂ^k` and
`e₂ : W ≃L[ℂ] ℂ^l` reduce this to the Hilbert-space statement
`TauCeti.Symbol.IsSmoothing.exists_contDiff_hasCompactSupport_quantizeSobolev`. -/
theorem IsSmoothing.exists_contDiff_toDistr_apply_eq (ha : a.IsSmoothing)
    (hc : a.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)} (hK : IsClosed K)
    (hKa : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) {s r : ℝ}
    {T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W)}
    (hT : ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
      (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
        ∫ x, φ x • quantizeSchwartzValue a.coefficient u x)
    (u : H^{s}(CoordinateSpace n, V)) :
    ∃ g : CoordinateSpace n → W, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ K ∧
      ∀ φ : 𝓢(CoordinateSpace n, ℂ), (T u).toDistr φ = ∫ x, φ x • g x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Φ := (e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ
  let S := BesselPotentialSpace.postcomp _ r 2 e₂.toContinuousLinearMap ∘L T ∘L
    BesselPotentialSpace.postcomp _ s 2 e₁.symm.toContinuousLinearMap
  -- The transported operator `S = e₂ ∘ T ∘ e₁⁻¹` agrees with the quantization of `e₂ a e₁⁻¹`.
  have hS (w : 𝓢(CoordinateSpace n, EuclideanSpace ℂ (Fin (Module.finrank ℂ V))))
      (φ : 𝓢(CoordinateSpace n, ℂ)) :
      (S (SchwartzMap.toBesselPotentialSpaceCLM s 2 w)).toDistr φ =
        ∫ x, φ x • quantizeSchwartzValue (a.map Φ).coefficient w x := by
    have hw :
        (w.postcompCLM e₁.symm.toContinuousLinearMap).postcompCLM e₁.toContinuousLinearMap = w := by
      ext x
      simp
    have hq (x : CoordinateSpace n) :
        e₂ (quantizeSchwartzValue a.coefficient (w.postcompCLM e₁.symm.toContinuousLinearMap) x) =
          quantizeSchwartzValue (a.map Φ).coefficient w x := by
      rw [coefficient_map_arrowCongr, ← quantizeSchwartzValue_arrowCongr e₁ e₂ a.coefficient, hw]
    simp only [S, ContinuousLinearMap.comp_apply,
      ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
      BesselPotentialSpace.toDistr_postcomp_apply, hT, ContinuousLinearEquiv.coe_coe, ← hq,
      ← map_smul, ContinuousLinearEquiv.integral_comp_comm]
  have he₁ : BesselPotentialSpace.postcomp _ s 2 e₁.symm.toContinuousLinearMap
      (BesselPotentialSpace.postcomp _ s 2 e₁.toContinuousLinearMap u) = u :=
    BesselPotentialSpace.ext (by ext φ; simp)
  have hu : T u = BesselPotentialSpace.postcomp _ r 2 e₂.symm.toContinuousLinearMap
      (S (BesselPotentialSpace.postcomp _ s 2 e₁.toContinuousLinearMap u)) :=
    BesselPotentialSpace.ext (by ext φ; simp [S, he₁])
  obtain ⟨g, hg, hgc, hgK, hgφ⟩ := (ha.map Φ).exists_contDiff_hasCompactSupport_quantizeSobolev
    (hc.map Φ) hK (fun x hx ξ ↦ by rw [coefficient_map, hKa x hx ξ, map_zero]) s
    (BesselPotentialSpace.postcomp _ s 2 e₁.toContinuousLinearMap u)
  refine ⟨e₂.symm ∘ g, (e₂.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hg,
    hgc.comp_left (map_zero e₂.symm), (tsupport_comp_subset (map_zero e₂.symm) g).trans hgK,
    fun φ ↦ ?_⟩
  rw [hu, BesselPotentialSpace.toDistr_postcomp_apply,
    toDistr_apply_eq_toDistr_quantizeSobolev (hc.map Φ) hS, hgφ]
  simp only [ContinuousLinearEquiv.coe_coe, Function.comp_apply, ← map_smul,
    ContinuousLinearEquiv.integral_comp_comm]

end FiniteDimensional

end Symbol

end TauCeti
