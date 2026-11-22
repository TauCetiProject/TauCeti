/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.FiniteOrder
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication

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
function. For the vanishing, if `a(x, ·) = 0` then `Op(a) w` vanishes at `x` for every Schwartz
function `w`. The quantitative embedding `|f(x)| ≤ C ‖f‖_{H^t}`, `t > n / 2`
(`TemperedDistribution.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace`), bounds the
value of `Op(a) u` at `x` by `C ‖Op(a) (u - w)‖_{H^t}`, which is small for Schwartz functions `w`
close to `u` in `H^s`.

The same conclusion holds for every tempered distribution `T`, of arbitrary order and growth: a
smoothing symbol `r` with compact spatial support maps `T` into every Sobolev space `H^t`
(`TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`), so `Op(r) T` is a smooth function. The
proof writes `T = (1 + ‖y‖ ^ 2) ^ K S` with `S` of finite Sobolev order
(`TemperedDistribution.exists_memSobolev_eq_smulLeftCLM_one_add_norm_sq_pow`) and moves each
coordinate factor through `Op(r)` with the commutator rule
`y_j Op(r) U = Op(r) (y_j U) + i Op(∂_{ξ_j} r) U` (`TauCeti.Symbol.smulLeftCLM_quantizeTempered`):
`y_j Op(r) U` equals `(ψ y_j) Op(r) U` for a cutoff `ψ` equal to `1` on the spatial support of `r`
(`TauCeti.Symbol.smulLeftCLM_quantizeTempered_of_eq_one`), and multiplication by the Schwartz
function `ψ y_j` preserves every `H^t`.

## Main results

* `TauCeti.Symbol.IsSmoothing.exists_contDiff_hasCompactSupport_quantizeSobolev`: for complex
  Hilbert spaces `V` and `W`, `Op(a) u` is a smooth compactly supported function vanishing at
  every position at which `a` vanishes for all frequencies.
* `TauCeti.Symbol.IsSmoothing.exists_contDiff_toDistr_apply_eq`: the same for every bounded
  extension `H^s → H^r` of `Op(a)` between finite-dimensional complex normed fibres.
* `TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`: for a scalar smoothing symbol `r` with
  compact spatial support, `Op(r) T` lies in every `H^t` for every tempered distribution `T`.
* `TauCeti.Symbol.IsSmoothing.exists_contDiff_quantizeTempered_apply_eq_integral`: hence
  `Op(r) T` is a smooth function.

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

/-- A continuous function `g` representing `Op(a) u` vanishes at every position `x` at which the
smoothing symbol `a` vanishes for all frequencies. -/
private theorem IsSmoothing.apply_eq_zero_of_coefficient_eq_zero (ha : a.IsSmoothing)
    (hc : a.HasCompactSpatialSupport) {s : ℝ} (u : H^{s}(CoordinateSpace n, V))
    {g : CoordinateSpace n → W} (hg : Continuous g)
    (hgφ : ∀ φ : 𝓢(CoordinateSpace n, ℂ), (a.quantizeSobolev hc s u).toDistr φ = ∫ y, φ y • g y)
    {x : CoordinateSpace n} (hx : ∀ ξ, a.coefficient (x, ξ) = 0) : g x = 0 := by
  -- `Op(a)` maps `H^s` boundedly into `H^t`, `t = n + 1 > n / 2`, where continuous
  -- representatives are bounded everywhere by `C ‖·‖_{H^t}`.
  obtain ⟨B, hB⟩ := ha.exists_continuousLinearMap_toDistr_quantizeSobolev_eq hc s (n + 1)
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace (F := W)
    (E := CoordinateSpace n) (s := n + 1) (k := 0) (by simp; linarith)
  obtain ⟨v, hv⟩ := memSobolev_zero_iff.1 (ha.memSobolev_toDistr_quantizeSobolev hc s 0 u)
  have hvg : v =ᵐ[volume] g :=
    Lp.ae_eq_of_toTemperedDistribution_apply_eq v hg.locallyIntegrable fun φ ↦ by rw [← hv, hgφ]
  -- On a Schwartz function `w`, `Op(a) w` is a continuous function vanishing at `x`, so
  -- `‖g x‖ ≤ C ‖B (u - w)‖`; Schwartz functions are dense in `H^s`.
  have key (w : 𝓢(CoordinateSpace n, V)) :
      ‖g x‖ ≤ C * ‖B (u - SchwartzMap.toBesselPotentialSpaceCLM s 2 w)‖ := by
    set q := quantizeSchwartzValue a.coefficient w
    have hq : Continuous q := (contDiff_quantizeSchwartzValue a w).continuous
    have hqx : q x = 0 :=
      (quantizeSchwartzValue_congr_left (b := 0) hx w).trans (quantizeSchwartzValue_zero_left w x)
    obtain ⟨v', hv'⟩ := memSobolev_zero_iff.1
      (ha.memSobolev_toDistr_quantizeSobolev hc s 0 (SchwartzMap.toBesselPotentialSpaceCLM s 2 w))
    have hv'q : v' =ᵐ[volume] q :=
      Lp.ae_eq_of_toTemperedDistribution_apply_eq v' hq.locallyIntegrable fun φ ↦ by
        rw [← hv', toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
    have hd : ((v - v' : Lp W 2 volume) : 𝓢'(CoordinateSpace n, W)) =
        (a.quantizeSobolev hc s (u - SchwartzMap.toBesselPotentialSpaceCLM s 2 w)).toDistr := by
      rw [Lp.toTemperedDistribution_sub, ← hv, ← hv', map_sub, BesselPotentialSpace.toDistr_sub]
    have hS : MemSobolev (n + 1) 2 ((v - v' : Lp W 2 volume) : 𝓢'(CoordinateSpace n, W)) :=
      hd ▸ ha.memSobolev_toDistr_quantizeSobolev hc s _ _
    have hSB : hS.toBesselPotentialSpace = B (u - SchwartzMap.toBesselPotentialSpaceCLM s 2 w) :=
      BesselPotentialSpace.ext (by rw [MemSobolev.toBesselPotentialSpace_toDistr, hd, hB rfl])
    have h := hC hS (hg.sub hq) ((Lp.coeFn_sub v v').trans (hvg.sub hv'q)) 0 le_rfl x
    rwa [norm_iteratedFDeriv_zero, Pi.sub_apply, hqx, sub_zero, hSB] at h
  have h := (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V)
    (p := 2) s ENNReal.ofNat_ne_top).induction_on (p := fun y ↦ ‖g x‖ ≤ C * ‖B (u - y)‖) u
    (isClosed_le continuous_const (by fun_prop)) key
  simpa using h

/-- **Smoothing operators produce smooth compactly supported functions.** Let `a` be a smoothing
symbol with compact spatial support between complex Hilbert spaces. For every `u ∈ H^s(ℝⁿ; V)`,
`s` real, the quantization `Op(a) u` is a smooth compactly supported function `g`: it pairs with
every Schwartz function `φ` as `∫ φ • g`. Moreover `g x = 0` at every position `x` at which the
symbol vanishes for all frequencies. Taking `s` negative, this applies to distributions that are
not functions. -/
theorem IsSmoothing.exists_contDiff_hasCompactSupport_quantizeSobolev (ha : a.IsSmoothing)
    (hc : a.HasCompactSpatialSupport) (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ∃ g : CoordinateSpace n → W, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, (∀ ξ, a.coefficient (x, ξ) = 0) → g x = 0) ∧
      ∀ φ : 𝓢(CoordinateSpace n, ℂ), (a.quantizeSobolev hc s u).toDistr φ = ∫ x, φ x • g x := by
  obtain ⟨g, hg, hgφ⟩ := exists_contDiff_eq_integral_of_forall_memSobolev fun t ↦
    ha.memSobolev_toDistr_quantizeSobolev hc s t u
  have hz (x : CoordinateSpace n) (hx : ∀ ξ, a.coefficient (x, ξ) = 0) : g x = 0 :=
    ha.apply_eq_zero_of_coefficient_eq_zero hc u hg.continuous hgφ hx
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp hc
  exact ⟨g, hg, HasCompactSupport.intro hK fun x hx ↦ hz x (hKa x hx), hz, hgφ⟩

end Hilbert

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W] {a : Symbol n V W m}

/-- **Smoothing operators produce smooth compactly supported functions.** Let `a` be a smoothing
symbol with compact spatial support between finite-dimensional complex normed spaces, and let
`T : H^s(ℝⁿ; V) → H^r(ℝⁿ; W)` be a bounded operator agreeing with `Op(a)` on Schwartz functions,
for any real orders `s` and `r` (such an operator exists by
`TauCeti.Symbol.IsSmoothing.exists_isCompactOperator_quantizeSobolev`). Then for every
`u ∈ H^s` the distribution `T u` is a smooth compactly supported function `g`, and `g x = 0` at
every position `x` at which the symbol vanishes for all frequencies. -/
theorem IsSmoothing.exists_contDiff_toDistr_apply_eq (ha : a.IsSmoothing)
    (hc : a.HasCompactSpatialSupport) {s r : ℝ}
    {T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W)}
    (hT : ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
      (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
        ∫ x, φ x • quantizeSchwartzValue a.coefficient u x)
    (u : H^{s}(CoordinateSpace n, V)) :
    ∃ g : CoordinateSpace n → W, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, (∀ ξ, a.coefficient (x, ξ) = 0) → g x = 0) ∧
      ∀ φ : 𝓢(CoordinateSpace n, ℂ), (T u).toDistr φ = ∫ x, φ x • g x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`, as in
  -- `TauCeti.Symbol.exists_quantizeSobolev`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Φ := (e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ
  let S := BesselPotentialSpace.postcomp _ r 2 e₂.symm.symm.toContinuousLinearMap ∘L T ∘L
    BesselPotentialSpace.postcomp _ s 2 e₁.symm.toContinuousLinearMap
  -- The transported operator `S = e₂ ∘ T ∘ e₁⁻¹` agrees with the quantization of `e₂ a e₁⁻¹`.
  have hc' : ((a.map Φ).map
      ((e₁.symm.arrowCongr e₂.symm).toContinuousLinearMap.restrictScalars ℝ)).coefficient =
        a.coefficient :=
    funext fun p ↦ by ext y; simp [Φ]
  have hS := toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply (a.map Φ)
    e₁.symm e₂.symm (T := T) fun v φ ↦ hc' ▸ hT v φ
  have he₁ : BesselPotentialSpace.postcomp _ s 2 e₁.symm.toContinuousLinearMap
      (BesselPotentialSpace.postcomp _ s 2 e₁.toContinuousLinearMap u) = u :=
    BesselPotentialSpace.ext (by ext φ; simp)
  have hu : T u = BesselPotentialSpace.postcomp _ r 2 e₂.symm.toContinuousLinearMap
      (S (BesselPotentialSpace.postcomp _ s 2 e₁.toContinuousLinearMap u)) :=
    BesselPotentialSpace.ext (by ext φ; simp [S, he₁])
  obtain ⟨g, hg, hgc, hgz, hgφ⟩ := (ha.map Φ).exists_contDiff_hasCompactSupport_quantizeSobolev
    (hc.map Φ) s (BesselPotentialSpace.postcomp _ s 2 e₁.toContinuousLinearMap u)
  refine ⟨e₂.symm ∘ g, (e₂.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hg,
    hgc.comp_left (map_zero e₂.symm), fun x hx ↦ ?_, fun φ ↦ ?_⟩
  · rw [Function.comp_apply, hgz x fun ξ ↦ by rw [coefficient_map, hx ξ, map_zero], map_zero]
  rw [hu, BesselPotentialSpace.toDistr_postcomp_apply,
    toDistr_apply_eq_toDistr_quantizeSobolev (hc.map Φ) hS, hgφ]
  simp only [ContinuousLinearEquiv.coe_coe, Function.comp_apply, ← map_smul,
    ContinuousLinearEquiv.integral_comp_comm]

end FiniteDimensional

section Tempered

variable {r : Symbol n ℂ ℂ m}

/-- A smoothing symbol with compact spatial support maps every tempered distribution of some Sobolev
order `s` into every Sobolev space `H^t`. -/
private theorem IsSmoothing.memSobolev_quantizeTempered_of_memSobolev (hsm : r.IsSmoothing)
    (hr : r.HasCompactSpatialSupport) {s : ℝ} {T : 𝓢'(CoordinateSpace n, ℂ)}
    (hT : T.MemSobolev s 2) (t : ℝ) : (quantizeTempered ℂ r hr.isUniform T).MemSobolev t 2 := by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 hsm (s - t)
  have hbK := hr.of_coefficient_eq hb
  rw [quantizeTempered_congr hr.isUniform hbK.isUniform hb.symm]
  simpa using memSobolev_quantizeTempered hbK hT

/-- The tempered distributions `U` such that `Op(r) U` lies in every Sobolev space `H^t` for every
smoothing symbol `r` with compact spatial support. -/
private def SmoothedBy (U : 𝓢'(CoordinateSpace n, ℂ)) : Prop :=
  ∀ (m : ℝ) (r : Symbol n ℂ ℂ m), r.IsSmoothing → ∀ (hr : r.HasCompactSpatialSupport) (t : ℝ),
    (quantizeTempered ℂ r hr.isUniform U).MemSobolev t 2

private theorem smoothedBy_of_memSobolev {U : 𝓢'(CoordinateSpace n, ℂ)} {s : ℝ}
    (hU : U.MemSobolev s 2) : SmoothedBy U :=
  fun _ _ hsm hr t ↦ hsm.memSobolev_quantizeTempered_of_memSobolev hr hU t

private theorem SmoothedBy.add {U V : 𝓢'(CoordinateSpace n, ℂ)} (hU : SmoothedBy U)
    (hV : SmoothedBy V) : SmoothedBy (U + V) := fun m r hsm hr t ↦ by
  rw [map_add]
  exact (hU m r hsm hr t).add (hV m r hsm hr t)

/-- The coordinate function `y ↦ y_j`, as a complex function, has temperate growth. -/
private theorem hasTemperateGrowth_coord (j : Fin n) :
    (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)).HasTemperateGrowth :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth

/-- Multiplying by a coordinate keeps the class: `Op(r) (y_j U) = y_j Op(r) U - i Op(∂_{ξ_j} r) U`,
and `y_j Op(r) U = (y_j ψ) Op(r) U` for a cutoff `ψ` equal to `1` on the spatial support of `r`. -/
private theorem SmoothedBy.smulLeftCLM_coord {U : 𝓢'(CoordinateSpace n, ℂ)} (hU : SmoothedBy U)
    (j : Fin n) :
    SmoothedBy (TemperedDistribution.smulLeftCLM ℂ
      (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) U) := fun m r hsm hr t ↦ by
  rw [eq_sub_of_add_eq (smulLeftCLM_quantizeTempered r hr.isUniform j U).symm]
  refine TemperedDistribution.MemSobolev.sub ?_
    ((hU _ _ (hsm.frequencyDeriv j) (hr.frequencyDeriv j) t).smul Complex.I)
  obtain ⟨K, hK, hKr⟩ := hasCompactSpatialSupport_iff.1 hr
  obtain ⟨ψ, -, -, hψ⟩ := hK.exists_schwartzMap_cutoff isOpen_univ (Set.subset_univ K)
  have hψ1 (x : CoordinateSpace n) (ξ : CoordinateSpace n) (hx : r.coefficient (x, ξ) ≠ 0) :
      ψ x = 1 := by
    by_contra hψx
    exact hx (hKr x (fun hxK ↦ hψx (hψ.self_of_nhdsSet x hxK)) ξ)
  rw [← smulLeftCLM_quantizeTempered_of_eq_one hr.isUniform ψ.hasTemperateGrowth hψ1,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth
      (hasTemperateGrowth_coord j), mul_comm (ψ : CoordinateSpace n → ℂ)]
  exact (hU m r hsm hr t).smulLeftCLM_mul (hasTemperateGrowth_coord j) ψ

/-- Multiplying by `1 + ‖y‖ ^ 2 = 1 + ∑ⱼ y_j ^ 2` keeps the class. -/
private theorem SmoothedBy.smulLeftCLM_one_add_norm_sq {U : 𝓢'(CoordinateSpace n, ℂ)}
    (hU : SmoothedBy U) :
    SmoothedBy (TemperedDistribution.smulLeftCLM ℂ
      (fun y : CoordinateSpace n ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) U) := by
  set c : Fin n → CoordinateSpace n → ℂ := fun j y ↦ ((y j : ℝ) : ℂ)
  have hc (j : Fin n) : (c j).HasTemperateGrowth := hasTemperateGrowth_coord j
  have hp : (fun y : CoordinateSpace n ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  have hid : TemperedDistribution.smulLeftCLM ℂ
      (fun y : CoordinateSpace n ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) U =
        U + ∑ j, TemperedDistribution.smulLeftCLM ℂ (c j)
          (TemperedDistribution.smulLeftCLM ℂ (c j) U) := by
    have hφ (φ : 𝓢(CoordinateSpace n, ℂ)) :
        SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) φ =
          φ + ∑ j, SchwartzMap.smulLeftCLM ℂ (c j) (SchwartzMap.smulLeftCLM ℂ (c j) φ) := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply hp]
      simp only [add_apply, sum_apply, SchwartzMap.smulLeftCLM_apply_apply (hc _), c, smul_eq_mul,
        EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
      push_cast
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    ext φ
    rw [TemperedDistribution.smulLeftCLM_apply_apply, hφ, map_add, map_sum]
    simp [TemperedDistribution.smulLeftCLM_apply_apply]
  rw [hid]
  refine hU.add ?_
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact smoothedBy_of_memSobolev (s := 0) (TemperedDistribution.memSobolev_fun_zero _ _ 0 2)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact SmoothedBy.add ((hU.smulLeftCLM_coord j).smulLeftCLM_coord j) ih

/-- **Smoothing operators on tempered distributions.** A smoothing symbol `r` with compact spatial
support maps every tempered distribution `T`, of any order and growth, into every Sobolev space
`H^t`. -/
theorem IsSmoothing.memSobolev_quantizeTempered (hsm : r.IsSmoothing)
    (hr : r.HasCompactSpatialSupport) (T : 𝓢'(CoordinateSpace n, ℂ)) (t : ℝ) :
    (quantizeTempered ℂ r hr.isUniform T).MemSobolev t 2 := by
  obtain ⟨K, s, S, hS, rfl⟩ :=
    TemperedDistribution.exists_memSobolev_eq_smulLeftCLM_one_add_norm_sq_pow T
  set p : CoordinateSpace n → ℂ := fun y ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)
  have hp : p.HasTemperateGrowth := by fun_prop
  -- Each factor `1 + ‖y‖ ^ 2` keeps the class.
  have hpow (k : ℕ) (U : 𝓢'(CoordinateSpace n, ℂ)) (hU : SmoothedBy U) :
      SmoothedBy (TemperedDistribution.smulLeftCLM ℂ (p ^ k) U) := by
    induction k generalizing U with
    | zero =>
      rw [show p ^ 0 = fun _ ↦ (1 : ℂ) from funext fun _ ↦ by simp,
        TemperedDistribution.smulLeftCLM_const, one_smul]
      exact hU
    | succ k ih =>
      rw [pow_succ, ← TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (hp.pow k) hp]
      exact (ih U hU).smulLeftCLM_one_add_norm_sq
  have hpK : p ^ K = fun y : CoordinateSpace n ↦ (((1 + ‖y‖ ^ 2) ^ K : ℝ) : ℂ) :=
    funext fun y ↦ by simp [p]
  exact hpK ▸ hpow K S (smoothedBy_of_memSobolev hS) m r hsm hr t

/-- **Smoothing operators produce smooth functions.** For a smoothing symbol `r` with compact
spatial support and every tempered distribution `T`, the tempered distribution `Op(r) T` is a
smooth function `g`. -/
theorem IsSmoothing.exists_contDiff_quantizeTempered_apply_eq_integral (hsm : r.IsSmoothing)
    (hr : r.HasCompactSpatialSupport) (T : 𝓢'(CoordinateSpace n, ℂ)) :
    ∃ g : CoordinateSpace n → ℂ, ContDiff ℝ ∞ g ∧
      ∀ φ : 𝓢(CoordinateSpace n, ℂ), quantizeTempered ℂ r hr.isUniform T φ = ∫ x, φ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev
    (hsm.memSobolev_quantizeTempered hr T)

end Tempered

end Symbol

end TauCeti
