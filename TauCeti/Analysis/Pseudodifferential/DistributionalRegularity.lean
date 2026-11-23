/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.EllipticRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
public import TauCeti.Analysis.Sobolev.BesselPotential.Local
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic
import TauCeti.Analysis.Distribution.LineDeriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Pseudodifferential.InteriorRegularity
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution

/-!
# Elliptic regularity of differential operators on distributions

Let `P = ∑ i ∈ t, c i g i ∂^(m i)` be a linear differential operator on an open set `Ω ⊆ ℝⁿ`, with
smooth real coefficients `g i`, complex constants `c i` and iterated directional derivatives
`∂^(m i)` of orders `k i ≤ M`, acting on complex distributions `T : 𝓓'(Ω, ℂ)`. It is *elliptic
at `x`* if its principal symbol of order `M` with the coefficients frozen at `x`,
`constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M`, vanishes at no `ξ ≠ 0`. This file proves
**interior elliptic regularity** on the `Lᵖ` Bessel-potential scale, for `1 < p < ∞`:

`P T ∈ H^{s,p}` near `x` and `P` elliptic at `x` ⟹ `T ∈ H^{s + M,p}` near `x`

(`Distribution.IsLocallyMemSobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`), for an
arbitrary distribution `T` and every real `s`. For `p = 2` this is the statement on the Sobolev
scale `H^s` (`Distribution.IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`).
Together with the mapping property of differential operators
(`Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`), an operator elliptic
at every point of `Ω` shifts the `H^s` singular support exactly by its order:
`singsupp_s(P T) = singsupp_(s + M)(T)`
(`Distribution.sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero`),
for instance `singsupp_s(Δ T) = singsupp_(s + 2)(T)` for the Laplacian
(`Distribution.sobolevSingularSupport_laplacianCLM`).

## The argument

The statement is reduced to interior elliptic regularity on the Bessel-potential spaces `H^{r,p}`
(`IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeBesselPotentialSpace` in the
namespace `TauCeti.Symbol`), which rests on the parametrix of the pseudodifferential calculus.

* **Finite order.** For a cutoff `χ` equal to one near `x`, the tempered distribution `χ T` lies in
  some `H^{r,p}` (`Distribution.exists_memSobolev_cutoffTempered_of_one_lt`).
* **Localizing `P`.** For a cutoff `ψ` supported where `χ = 1`, the operator with coefficients
  `c i g i ψ` sends `χ T` to `ψ P T`: where `ψ ≠ 0` the derivatives of `χ T` are those of `T`
  (`Distribution.smulLeftCLM_iteratedLineDerivOp_cutoffTempered`). Its classical symbol has
  compact spatial support, and on `H^{r,p}` its quantization is the differential operator itself
  (`TauCeti.ClassicalSymbol.toDistr_quantizeBesselPotentialSpace_ofDifferentialSymbol_smul_id`).
* **Freezing the coefficients.** Ellipticity is an open condition
  (`TauCeti.eventually_forall_constCoeffPrincipalSymbol_ne_zero`), so `P` is elliptic on a ball
  around `x`. Composing the coefficients with a smooth map `ρ` that is the identity near `x`, maps
  into that ball and is constant outside it gives a differential symbol elliptic above a radius
  independent of the position (`TauCeti.ClassicalSymbol.IsElliptic.exists_isEllipticAbove`), whose
  coefficients agree with those of `P` near `x`.

The regularity theorem on `H^{r,p}` then gives `φ (χ T) = φ T ∈ H^{s + M,p}` for every cutoff `φ`
supported where `ψ = 1`.

## Main results

* `TauCeti.differentialSymbol_filter_smul_id`,
  `TauCeti.ClassicalSymbol.isElliptic_ofDifferentialSymbol_smul_id_iff`: for scalar coefficients,
  the top-order differential symbol is `i ^ M` times the principal symbol
  `TauCeti.constCoeffPrincipalSymbol` of the operator with frozen coefficients, so the classical
  symbol is elliptic exactly when that principal symbol vanishes at no `ξ ≠ 0` at every position.
* `Distribution.IsLocallyMemSobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`,
  `Distribution.IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`: interior elliptic
  regularity on `H^{s,p}` and on `H^s`, and
  `Distribution.isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff`, its combination
  with the mapping property.
* `Distribution.sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero`,
  `Distribution.sobolevSingularSupport_laplacianCLM`: elliptic operators shift the `H^s` singular
  support by their order.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11), and Lecture II, (3.1)–(3.8) (the `H^{s,p}` version).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Complex Filter LineDeriv MeasureTheory Set TopologicalSpace TestFunction
open scoped BesselPotentialSpace ContDiff Distributions ENNReal LineDeriv SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {ι : Type*} {t : Finset ι} {k : ι → ℕ} {m : ∀ i, Fin (k i) → CoordinateSpace n}

/-- The top-order part of the differential symbol with scalar coefficients `β i y` is `i ^ M`
times the principal symbol of the operator with coefficients frozen at `y`. -/
theorem differentialSymbol_filter_smul_id (M : ℕ) (β : ι → CoordinateSpace n → ℂ)
    (y ξ : CoordinateSpace n) :
    differentialSymbol {i ∈ t | k i = M} m (fun i z ↦ β i z • ContinuousLinearMap.id ℂ ℂ)
        (y, ξ) =
      (Complex.I ^ M * constCoeffPrincipalSymbol t (fun i ↦ β i y) m M ξ) •
        ContinuousLinearMap.id ℂ ℂ := by
  refine ContinuousLinearMap.ext_ring ?_
  simp only [differentialSymbol_eq_sum_pow_mul, constCoeffPrincipalSymbol_def, sum_apply,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [← (Finset.mem_filter.1 hi).2]
  simp only [real_inner_comm]
  ring

/-- **Ellipticity of a scalar differential operator.** The classical symbol of a differential
operator with scalar coefficients `β i` is elliptic exactly when, at every position `y`, the
principal symbol of the operator with coefficients frozen at `y` vanishes at no `ξ ≠ 0`. -/
theorem ClassicalSymbol.isElliptic_ofDifferentialSymbol_smul_id_iff (M : ℕ)
    {β : ι → CoordinateSpace n → ℂ}
    (hβ : ∀ i ∈ t, ContDiff ℝ ∞ fun y ↦ β i y • ContinuousLinearMap.id ℂ ℂ)
    (hk : ∀ i ∈ t, k i ≤ M) :
    (ofDifferentialSymbol M t m (fun i y ↦ β i y • ContinuousLinearMap.id ℂ ℂ) hβ hk).IsElliptic ↔
      ∀ y ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ β i y) m M ξ ≠ 0 := by
  rw [isElliptic_ofDifferentialSymbol_iff]
  refine forall_congr' fun y ↦ forall_congr' fun ξ ↦ forall_congr' fun _ ↦ ?_
  rw [differentialSymbol_filter_smul_id]
  refine ⟨fun ⟨e, he⟩ h0 ↦ ?_, fun h ↦ ?_⟩
  · -- A multiple `0 • id` of the identity is not an isomorphism of `ℂ`.
    have he1 := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) he
    simp [h0] at he1
  · rw [ContinuousLinearMap.isInvertible_smul_iff
      (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) h)]
    exact ⟨ContinuousLinearEquiv.refl ℂ ℂ, rfl⟩

open Metric in
/-- **Freezing the coefficients away from a point.** If the principal symbol of
`∑ i ∈ t, c i g i ∂^(m i)` with coefficients frozen at `y` vanishes at no `ξ ≠ 0`, for every `y`
in the ball `B(x, ε)`, then for `0 < r < ε` some differential symbol with smooth coefficients,
equal to those of the operator on the closed ball `closedBall x r` and constant outside
`B(x, ε)`, is elliptic above some radius. -/
private theorem exists_isEllipticAbove_ofDifferentialSymbol {c : ι → ℂ}
    {g : ι → CoordinateSpace n → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) {x : CoordinateSpace n} {r ε : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hσ : ∀ y ∈ ball x ε, ∀ ξ, ξ ≠ 0 →
      constCoeffPrincipalSymbol t (fun i ↦ c i * g i y) m M ξ ≠ 0) :
    ∃ (b : ι → CoordinateSpace n → ℂ →L[ℂ] ℂ) (hb : ∀ i ∈ t, ContDiff ℝ ∞ (b i)) (R : ℝ),
      (ClassicalSymbol.ofDifferentialSymbol M t m b hb hk).toSymbol.IsEllipticAbove R ∧
        ∀ y ∈ closedBall x r, ∀ i, b i y = (c i * g i y) • ContinuousLinearMap.id ℂ ℂ := by
  -- `ρ y = x + θ(y) (y - x)` is the identity on `closedBall x r`, maps into `B(x, ε)` and is
  -- constant outside it.
  let θ : ContDiffBump x := ⟨r, ε, hr, hrε⟩
  let ρ : CoordinateSpace n → CoordinateSpace n := fun y ↦ x + θ y • (y - x)
  have hρ : ContDiff ℝ ∞ ρ := contDiff_const.add (θ.contDiff.smul (contDiff_id.sub contDiff_const))
  have hρε (y : CoordinateSpace n) : ρ y ∈ ball x ε := by
    by_cases hy : y ∈ ball x ε
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg θ.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) θ.le_one).trans_lt (mem_ball_iff_norm.1 hy)
    · simpa [ρ, θ.zero_of_le_dist (not_lt.1 hy)] using mem_ball_self (x := x) (hr.trans hrε)
  set β : ι → CoordinateSpace n → ℂ := fun i y ↦ c i * g i (ρ y)
  have hβ (i : ι) : ContDiff ℝ ∞ (β i) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ((hg i).comp hρ))
  have hb (i : ι) (_ : i ∈ t) :
      ContDiff ℝ ∞ fun y ↦ β i y • ContinuousLinearMap.id ℂ ℂ := (hβ i).smul contDiff_const
  set a := ClassicalSymbol.ofDifferentialSymbol M t m _ hb hk
  have ha : a.IsElliptic :=
    (ClassicalSymbol.isElliptic_ofDifferentialSymbol_smul_id_iff M hb hk).2
      fun y ξ hξ ↦ hσ _ (hρε y) ξ hξ
  have hρx (y : CoordinateSpace n) (hy : y ∉ closedBall x ε) : ρ y = ρ x := by
    simp [ρ, θ.zero_of_le_dist (le_of_lt (not_le.1 hy))]
  obtain ⟨R, hR⟩ := ha.exists_isEllipticAbove (isCompact_closedBall x ε) fun y hy ↦
    ⟨x, mem_closedBall_self (hr.trans hrε).le, fun ξ ↦ by
      simp only [a, ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol,
        differentialSymbol_def, β, hρx y hy]⟩
  refine ⟨_, hb, R, hR, fun y hy i ↦ ?_⟩
  simp [β, ρ, θ.one_of_mem_closedBall hy]

end TauCeti

namespace Distribution

open TauCeti Metric

variable {n : ℕ} {Ω : Opens (CoordinateSpace n)} {ι : Type*} {t : Finset ι} {c : ι → ℂ}
  {g : ι → CoordinateSpace n → ℝ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → CoordinateSpace n}

/-- Cutting off a differential operator: if `χ = 1` on the support of `ψ`, the operator
`∑ i ∈ t, c i (g i ψ) ∂^(m i)`, whose coefficients are cut off by `ψ`, applied to `χ T` is `ψ P T`
for `P = ∑ i ∈ t, c i g i ∂^(m i)`. -/
private theorem sum_smulLeftCLM_iteratedLineDerivOp_cutoffTempered
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (T : 𝓓'(Ω, ℂ)) {χ ψ : 𝓓(Ω, ℂ)}
    (h : ∀ x ∈ tsupport ψ, χ x = 1) :
    ∑ i ∈ t, TemperedDistribution.smulLeftCLM ℂ
        (fun x ↦ c i * TestFunction.smulLeftCLM (hg i) ψ x) (∂^{m i} (T.cutoffTempered χ)) =
      (∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered ψ := by
  rw [cutoffTempered_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  set ψi := TestFunction.smulLeftCLM (hg i) ψ
  have hψi : tsupport ψi ⊆ tsupport ψ :=
    (TestFunction.tsupport_smulLeftCLM_subset (hg i) ψ).trans inter_subset_right
  rw [show (fun x ↦ c i * ψi x) = c i • (ψi : CoordinateSpace n → ℂ) from
      funext fun x ↦ (smul_eq_mul _ _).symm,
    TemperedDistribution.smulLeftCLM_smul (ψi.hasCompactSupport.hasTemperateGrowth ψi.contDiff),
    smul_apply,
    smulLeftCLM_iteratedLineDerivOp_cutoffTempered T fun x hx ↦ h x (hψi hx)]
  simp [ψi, cutoffTempered_smulLeftCLM]

/-- The analytic core of elliptic regularity: given cutoffs `χ = 1` on the supports of `ψ` and
`φ`, and a symbol elliptic above some radius whose coefficients are those of `P` where `ψ = 1`
near the support of `φ`, `ψ P T ∈ H^{s,p}` implies `φ T ∈ H^{s + M,p}`, for `1 < p < ∞`. -/
private theorem memSobolev_cutoffTempered_of_isEllipticAbove {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (T : 𝓓'(Ω, ℂ)) {χ ψ φ : 𝓓(Ω, ℂ)}
    (hχψ : ∀ y ∈ tsupport ψ, χ y = 1) (hχφ : ∀ y ∈ tsupport φ, χ y = 1)
    {b : ι → CoordinateSpace n → ℂ →L[ℂ] ℂ} (hb : ∀ i ∈ t, ContDiff ℝ ∞ (b i)) {R : ℝ}
    (hR : (ClassicalSymbol.ofDifferentialSymbol M t m b hb hk).toSymbol.IsEllipticAbove R)
    (hbψ : ∀ᶠ y in 𝓝ˢ (tsupport φ),
      ψ y = 1 ∧ ∀ i, b i y = (c i * g i y) • ContinuousLinearMap.id ℂ ℂ) {s : ℝ}
    (hPψ : TemperedDistribution.MemSobolev s p
      ((∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered ψ)) :
    TemperedDistribution.MemSobolev (s + M) p (T.cutoffTempered φ) := by
  -- `u = χ T` has finite order on the `Lᵖ` scale.
  obtain ⟨r, hr⟩ := T.exists_memSobolev_cutoffTempered_of_one_lt hp hp_top χ
  -- The operator with coefficients cut off by `ψ`, acting on `u`.
  set β : ι → CoordinateSpace n → ℂ := fun i y ↦ c i * TestFunction.smulLeftCLM (hg i) ψ y
  have hβ (i : ι) (_ : i ∈ t) : ContDiff ℝ ∞ (β i) :=
    contDiff_const.mul (TestFunction.smulLeftCLM (hg i) ψ).contDiff
  have hβc (i : ι) (_ : i ∈ t) : HasCompactSupport (β i) :=
    (TestFunction.smulLeftCLM (hg i) ψ).hasCompactSupport.mul_left
  have hu := ClassicalSymbol.toDistr_quantizeBesselPotentialSpace_ofDifferentialSymbol_smul_id M t
    m hk hβ hβc _ hp hp_top hr.toBesselPotentialSpace
  rw [hr.toBesselPotentialSpace_toDistr, sum_smulLeftCLM_iteratedLineDerivOp_cutoffTempered hg T
    hχψ] at hu
  set φS : 𝓢(CoordinateSpace n, ℂ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  have hφS : (φS : CoordinateSpace n → ℂ) = φ :=
    funext (φ.hasCompactSupport.toSchwartzMap_toFun φ.contDiff)
  have hreg := hR.memSobolev_smulLeftCLM_of_memSobolev_quantizeBesselPotentialSpace
    (hφS ▸ φ.hasCompactSupport)
    (ClassicalSymbol.hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol M t m
      (fun i x ↦ β i x • ContinuousLinearMap.id ℂ ℂ) (fun i hi ↦ (hβ i hi).smul contDiff_const)
      hk fun i hi ↦ (hβc i hi).smul_right) (by
    rw [hφS]
    filter_upwards [hbψ] with y ⟨hψy, hby⟩ ξ
    simp only [ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_def,
      hby, β, TestFunction.smulLeftCLM_apply, hψy, Complex.real_smul, mul_one])
    hp hp_top (s := s) hr.toBesselPotentialSpace (by rw [hu]; exact hPψ)
  rwa [hφS, hr.toBesselPotentialSpace_toDistr, smulLeftCLM_cutoffTempered T hχφ] at hreg

/-- **Interior elliptic regularity for differential operators on `H^{s,p}`.** Let `1 < p < ∞`, let
`P = ∑ i ∈ t, c i g i ∂^(m i)` have smooth real coefficients `g i`, complex constants `c i` and
orders `k i ≤ M`, and let `P` be elliptic at `x`: its principal symbol of order `M` with the
coefficients frozen at `x` vanishes at no `ξ ≠ 0`. If `P T` is `H^{s,p}` near `x`, then `T` is
`H^{s + M,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)} {x : CoordinateSpace n} {s : ℝ}
    (hσ : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    (hPT : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallyMemSobolevAt s
      p x) :
    T.IsLocallyMemSobolevAt (s + M) p x := by
  obtain ⟨U, hU, hUΩ, hPU⟩ := isLocallyMemSobolevAt_iff.1 hPT
  have hell := eventually_forall_constCoeffPrincipalSymbol_ne_zero (c := fun y i ↦ c i * g i y)
    (fun i _ ↦ (continuous_const.mul
      (Complex.continuous_ofReal.comp (hg i).continuous)).continuousAt) hσ
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (inter_mem hU hell)
  have hεΩ : ball x ε ⊆ Ω := hεU.trans (inter_subset_left.trans hUΩ)
  -- Nested cutoffs: `ψ = 1` near `closedBall x (ε/4)` with support in `B(x, ε/2)`, and `χ = 1`
  -- near `closedBall x (ε/2)`. The conclusion holds for every `φ` supported in `B(x, ε/4)`.
  obtain ⟨ψ, -, hψ1, hψs⟩ := TestFunction.exists_cutoff_tsupport_subset (n := ⊤)
    (isCompact_closedBall x (ε / 4)) isOpen_ball (closedBall_subset_ball (by linarith))
    ((ball_subset_ball (by linarith : ε / 2 ≤ ε)).trans hεΩ)
  obtain ⟨χ, -, hχ1, -⟩ := TestFunction.exists_cutoff_tsupport_subset (n := ⊤)
    (isCompact_closedBall x (ε / 2)) isOpen_ball (closedBall_subset_ball (by linarith)) hεΩ
  set ψ' : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) Complex.ofRealCLM ψ
  have hψ' : tsupport ψ' ⊆ ball x (ε / 2) := by
    rw [postcompCLM_apply]
    exact (tsupport_comp_subset (map_zero _) _).trans hψs
  have hχ (K : Set (CoordinateSpace n)) (hK : K ⊆ closedBall x (ε / 2)) :
      ∀ y ∈ K, (postcompCLM (𝕜 := ℝ) Complex.ofRealCLM χ) y = 1 := fun y hy ↦ by
    simp [(hχ1.self_of_nhdsSet y (hK hy))]
  obtain ⟨b, hb, R, hR, hbx⟩ := exists_isEllipticAbove_ofDifferentialSymbol hg hk
    (by positivity : 0 < ε / 4) (by linarith) fun y hy ↦ (hεU hy).2
  refine isLocallyMemSobolevAt_iff.2 ⟨ball x (ε / 4), ball_mem_nhds x (by positivity),
    (ball_subset_ball (by linarith)).trans hεΩ, fun φ hφs ↦
    memSobolev_cutoffTempered_of_isEllipticAbove hp hp_top hg hk T
      (hχ _ (hψ'.trans ball_subset_closedBall))
      (hχ _ (hφs.trans ((ball_subset_ball (by linarith)).trans ball_subset_closedBall))) hb hR
      ?_ (hPU ψ' (hψ'.trans ((ball_subset_ball (by linarith)).trans
        (hεU.trans inter_subset_left))))⟩
  -- Near the support of `φ`, `ψ = 1` and the frozen coefficients are those of `P`.
  filter_upwards [nhdsSet_mono (hφs.trans ball_subset_closedBall) hψ1,
    (isOpen_ball.mem_nhdsSet.2 hφs)] with y hy hyb
  exact ⟨by simp [ψ', hy], hbx y (ball_subset_closedBall hyb)⟩

/-- **Interior elliptic regularity for differential operators.** Let
`P = ∑ i ∈ t, c i g i ∂^(m i)` have smooth real coefficients `g i`, complex constants `c i` and
orders `k i ≤ M`, and let `P` be elliptic at `x`: its principal symbol of order `M` with the
coefficients frozen at `x` vanishes at no `ξ ≠ 0`. If `P T` is `H^s` near `x`, then `T` is
`H^(s + M)` near `x`. -/
theorem IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {x : CoordinateSpace n} {s : ℝ}
    (hσ : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    (hPT : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt s
      x) :
    T.IsLocallySobolevAt (s + M) x :=
  isLocallyMemSobolevAt_two_iff.1 <|
    IsLocallyMemSobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
      ENNReal.one_lt_two ENNReal.ofNat_ne_top hg hk hσ (isLocallyMemSobolevAt_two_iff.2 hPT)

/-- **Elliptic operators shift local Sobolev regularity by exactly their order.** If
`P = ∑ i ∈ t, c i g i ∂^(m i)`, with smooth real coefficients `g i` and orders `k i ≤ M`, is
elliptic at `x`, then `P T` is `H^s` near `x` exactly when `T` is `H^(s + M)` near `x`. -/
theorem isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {x : CoordinateSpace n} {s : ℝ}
    (hσ : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt s x ↔
      T.IsLocallySobolevAt (s + M) x :=
  ⟨.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk hσ, fun h ↦ by
    simpa using h.sum_smul_smulLeftCLM_iteratedLineDerivOp t c hg m hk⟩

/-- **Elliptic differential operators shift the `H^s` singular support by their order.** If
`P = ∑ i ∈ t, c i g i ∂^(m i)`, with smooth real coefficients `g i` and orders `k i ≤ M`, is
elliptic at every point of `Ω`, then `T` is `H^(s + M)` exactly where `P T` is `H^s`. -/
theorem sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero
    (s : ℝ) (t : Finset ι) (c : ι → ℂ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (m : ∀ i, Fin (k i) → CoordinateSpace n) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (hσ : ∀ x ∈ Ω, ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).sobolevSingularSupport s =
      T.sobolevSingularSupport (s + M) := by
  ext x
  simp only [mem_sobolevSingularSupport_iff, and_congr_right_iff]
  exact fun hx ↦ not_congr (isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff hg hk
    (hσ x hx))

/-- **Elliptic regularity for the Laplacian.** `T` is `H^(s + 2)` exactly where `Δ T` is `H^s`. -/
@[simp]
theorem sobolevSingularSupport_laplacianCLM (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (laplacianCLM ℝ (CoordinateSpace n) 𝓓'(Ω, ℂ) T).sobolevSingularSupport s =
      T.sobolevSingularSupport (s + 2) := by
  set b := stdOrthonormalBasis ℝ (CoordinateSpace n)
  have h := sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero s
    Finset.univ (fun _ ↦ 1) (g := fun _ _ ↦ 1) (fun _ ↦ contDiff_const) (k := fun _ ↦ 2)
    (fun i ↦ ![b i, b i]) (M := 2) (fun _ _ ↦ le_rfl) (fun _ _ ξ hξ ↦ ?_) T
  · simpa [laplacianCLM_eq_sum_iteratedLineDerivOp b] using h
  simp only [ofReal_one, one_mul]
  rw [constCoeffPrincipalSymbol_laplacian]
  exact_mod_cast (pow_pos (norm_pos_iff.2 hξ) 2).ne'

end Distribution
