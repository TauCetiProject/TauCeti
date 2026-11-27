/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.EllipticRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
public import TauCeti.Analysis.Holder.Distribution
public import TauCeti.Analysis.Sobolev.BesselPotential.Local
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic
import TauCeti.Analysis.Distribution.LineDeriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
import TauCeti.Analysis.Pseudodifferential.Microlocal
import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Elliptic
import TauCeti.Analysis.Pseudodifferential.InteriorRegularity
import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
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

Elliptic regularity also holds **microlocally**. Let `ξ` be noncharacteristic for `P` at `x`: the
principal symbol with the coefficients frozen at `x`, `TauCeti.principalSymbol`, does not vanish at
`ξ`. If `P T` is microlocally `H^s` at `(x, ξ)`, then `T` is microlocally `H^(s + M)` there
(`Distribution.IsMicrolocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`). In terms of
the `H^s` wave front sets,

`WF_(s + M)(T) ⊆ WF_s(P T) ∪ Char(P)`

(`sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`
in the namespace `Distribution`), where `Char(P)` is the characteristic set
`TauCeti.characteristicSet`. Together with the mapping property `WF_s(P T) ⊆ WF_(s + M)(T)`, an
operator elliptic at every point of `Ω` shifts the `H^s` wave front set exactly by its order. These
are the variable-coefficient forms of the statements for constant coefficients, such as
`sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_iteratedLineDerivOp_union`, and the
`H^s` refinements of the statements for the wave front set, such as
`waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`, all in the
namespace `Distribution`.

## The argument

The statement is reduced to interior elliptic regularity on the Bessel-potential spaces `H^{r,p}`
(`IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeUniformBesselPotentialSpace` in
the namespace `TauCeti.Symbol`), which rests on the parametrix of the pseudodifferential calculus.

* **Finite order.** For a cutoff `χ` equal to one near `x`, the tempered distribution `χ T` lies in
  some `H^{r,p}` (`Distribution.exists_memSobolev_cutoffTempered_of_one_lt`).
* **Localizing `P`.** For a cutoff `ψ` supported where `χ = 1`, the operator with coefficients
  `c i g i ψ` sends `χ T` to `ψ P T`: where `ψ ≠ 0` the derivatives of `χ T` are those of `T`
  (`Distribution.smulLeftCLM_iteratedLineDerivOp_cutoffTempered`). Its classical symbol has
  compact spatial support, and on `H^{r,p}` its quantization is the differential operator itself
  (`toDistr_quantizeUniformBesselPotentialSpace_ofDifferentialSymbol_smul_id` in the namespace
  `TauCeti.ClassicalSymbol`).
* **Freezing the coefficients.** Ellipticity is an open condition
  (`TauCeti.eventually_forall_constCoeffPrincipalSymbol_ne_zero`), so `P` is elliptic on a ball
  around `x`. Composing the coefficients with a smooth map `ρ` that is the identity near `x`, maps
  into that ball and is constant outside it gives a differential symbol elliptic above a radius
  independent of the position (`TauCeti.ClassicalSymbol.IsElliptic.exists_isEllipticAbove`), whose
  coefficients agree with those of `P` near `x`.

The regularity theorem on `H^{r,p}` then gives `φ (χ T) = φ T ∈ H^{s + M,p}` for every cutoff `φ`
supported where `ψ = 1`.

For the microlocal statement at `(x, ξ)` no freezing is needed. If `ψ = 1` near `x`, the principal
symbol of the cut-off operator at `(x, ξ)` is that of `P`, so it is elliptic in a conic
neighbourhood of `(x, ξ)` at large frequencies
(`TauCeti.ClassicalSymbol.exists_isEllipticOn_of_isInvertible_coefficient_principal`). Microlocal
elliptic regularity on `H^r` for symbols with compact spatial support
(`HasCompactSpatialSupport.isMicrolocallySobolevAt_toDistribution_of_quantizeSobolev` in the
namespace `TauCeti.Symbol`) then passes from `ψ P T` to `χ T`, which agree with `P T` and `T` near
`x`.

The same cutoffs give **interior elliptic regularity on the Besov scale** `B^s_{p,q}`, for
`1 < p ≤ ∞` and `1 ≤ q ≤ ∞`
(`Distribution.IsLocallyMemBesovAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`), from interior
regularity on Besov spaces (`TauCeti.Symbol.memBesov_smulLeftCLM_of_memBesov_quantizeTempered`);
here `χ T` lies in some `B^r_{p,q}` (`Distribution.exists_memBesov_cutoffTempered`), and the
cut-off operator acts on it as on an element of some `H^r`. For `p = q = ∞` this is the
Hölder–Zygmund scale, and through `Distribution.isLocallyMemBesovAt_iff_isLocallyCkHolderAt` it
gives the **local Schauder theorem**: for `0 < α < 1`,

`P T ∈ C^{j,α}` near `x` and `P` elliptic at `x` ⟹ `T ∈ C^{j + M,α}` near `x`

(`Distribution.IsLocallyCkHolderAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`).

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
* `Distribution.IsMicrolocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`,
  `Distribution.isMicrolocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff`: microlocal
  elliptic regularity on `H^s`, and its combination with the mapping property.
* `sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`
  and `sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero`, in the
  namespace `Distribution`:
  `WF_(s + M)(T) ⊆ WF_s(P T) ∪ Char(P)`, and `WF_s(P T) = WF_(s + M)(T)` for elliptic `P`.
* `Distribution.IsLocallyMemBesovAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`,
  `Distribution.IsLocallyCkHolderAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`: interior elliptic
  regularity on `B^s_{p,q}` and the local Schauder theorem on `C^{j,α}`, `0 < α < 1`.
* `Distribution.sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero`,
  `Distribution.sobolevSingularSupport_laplacianCLM`: elliptic operators shift the `H^s` singular
  support by their order.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (3.32)–(3.34) (the Zygmund and Hölder spaces) and (4.6)–(4.11), and Lecture II,
  (3.1)–(3.8) (the `H^{s,p}` version).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Complex Filter LineDeriv MeasureTheory Set TopologicalSpace TestFunction
open scoped BesselPotentialSpace ContDiff Distributions ENNReal LineDeriv NNReal SchwartzMap
  Topology

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
  · exact ContinuousLinearMap.isInvertible_smul_id_iff.2
      (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) h)

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

/-- The operator `P = ∑ i ∈ t, c i g i ∂^(m i)` with coefficients cut off by `ψ`: its coefficients
`c i (g i ψ)` are smooth and compactly supported, and so its symbol has compact spatial support. -/
private theorem exists_hasCompactSpatialSupport_cutoff (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (ψ : 𝓓(Ω, ℂ)) :
    ∃ hβ : ∀ i ∈ t, ContDiff ℝ ∞ fun y ↦ c i * TestFunction.smulLeftCLM (hg i) ψ y,
      (∀ i ∈ t, HasCompactSupport fun y ↦ c i * TestFunction.smulLeftCLM (hg i) ψ y) ∧
      (ClassicalSymbol.ofDifferentialSymbol M t m
        (fun i y ↦ (c i * TestFunction.smulLeftCLM (hg i) ψ y) • ContinuousLinearMap.id ℂ ℂ)
        (fun i hi ↦ (hβ i hi).smul contDiff_const) hk).toSymbol.HasCompactSpatialSupport := by
  have hβc (i : ι) (_ : i ∈ t) :
      HasCompactSupport fun y ↦ c i * TestFunction.smulLeftCLM (hg i) ψ y :=
    (TestFunction.smulLeftCLM (hg i) ψ).hasCompactSupport.mul_left
  exact ⟨fun i _ ↦ contDiff_const.mul (TestFunction.smulLeftCLM (hg i) ψ).contDiff, hβc,
    ClassicalSymbol.hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol M t m _ _ hk
      fun i hi ↦ (hβc i hi).smul_right⟩

/-- The operator `P = ∑ i ∈ t, c i g i ∂^(m i)` with coefficients cut off by `ψ`: its coefficients
`c i (g i ψ)` are smooth and compactly supported, and where `ψ = 1` and the coefficients of `b`
are those of `P` near the support of `φ`, its symbol agrees with that of `b` there. -/
private theorem exists_cutoff_coefficient_eq (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) (ψ : 𝓓(Ω, ℂ)) {φ : 𝓓(Ω, ℂ)}
    {b : ι → CoordinateSpace n → ℂ →L[ℂ] ℂ} (hb : ∀ i ∈ t, ContDiff ℝ ∞ (b i))
    (hbψ : ∀ᶠ y in 𝓝ˢ (tsupport φ),
      ψ y = 1 ∧ ∀ i, b i y = (c i * g i y) • ContinuousLinearMap.id ℂ ℂ) :
    ∃ hβ : ∀ i ∈ t, ContDiff ℝ ∞ fun y ↦ c i * TestFunction.smulLeftCLM (hg i) ψ y,
      (∀ i ∈ t, HasCompactSupport fun y ↦ c i * TestFunction.smulLeftCLM (hg i) ψ y) ∧
      (ClassicalSymbol.ofDifferentialSymbol M t m
        (fun i y ↦ (c i * TestFunction.smulLeftCLM (hg i) ψ y) • ContinuousLinearMap.id ℂ ℂ)
        (fun i hi ↦ (hβ i hi).smul contDiff_const) hk).toSymbol.HasCompactSpatialSupport ∧
      ∀ᶠ y in 𝓝ˢ (tsupport φ), ∀ ξ,
        (ClassicalSymbol.ofDifferentialSymbol M t m
          (fun i y ↦ (c i * TestFunction.smulLeftCLM (hg i) ψ y) • ContinuousLinearMap.id ℂ ℂ)
          (fun i hi ↦ (hβ i hi).smul contDiff_const) hk).toSymbol.coefficient (y, ξ) =
        (ClassicalSymbol.ofDifferentialSymbol M t m b hb hk).toSymbol.coefficient (y, ξ) := by
  obtain ⟨hβ, hβc, hc⟩ := exists_hasCompactSpatialSupport_cutoff (c := c) (m := m) hg hk ψ
  refine ⟨hβ, hβc, hc, ?_⟩
  filter_upwards [hbψ] with y ⟨hψy, hby⟩ ξ
  simp only [ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_def,
    hby, TestFunction.smulLeftCLM_apply, hψy, Complex.real_smul, mul_one]

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
  obtain ⟨hβ, hβc, hc, hcoef⟩ := exists_cutoff_coefficient_eq hg hk ψ hb hbψ
  have hu :=
    ClassicalSymbol.toDistr_quantizeUniformBesselPotentialSpace_ofDifferentialSymbol_smul_id M t m
      hk hβ hβc _ hp hp_top hr.toBesselPotentialSpace
  rw [hr.toBesselPotentialSpace_toDistr, sum_smulLeftCLM_iteratedLineDerivOp_cutoffTempered hg T
    hχψ] at hu
  set φS : 𝓢(CoordinateSpace n, ℂ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  have hφS : (φS : CoordinateSpace n → ℂ) = φ :=
    funext (φ.hasCompactSupport.toSchwartzMap_toFun φ.contDiff)
  have hreg := hR.memSobolev_smulLeftCLM_of_memSobolev_quantizeUniformBesselPotentialSpace
    (hφS ▸ φ.hasCompactSupport) hc (by rwa [hφS]) hp hp_top (s := s) hr.toBesselPotentialSpace
    (by rw [hu]; exact hPψ)
  rwa [hφS, hr.toBesselPotentialSpace_toDistr, smulLeftCLM_cutoffTempered T hχφ] at hreg

/-- The cutoffs of the regularity argument at a point `x` where `P = ∑ i ∈ t, c i g i ∂^(m i)` is
elliptic, inside a neighbourhood `U ⊆ Ω` of `x`: test functions `χ` and `ψ` with `ψ` supported in
`U` and `χ = 1` on its support, a differential symbol elliptic above some radius, and a
neighbourhood `V ⊆ Ω` of `x` such that every test function `φ` supported in `V` has `χ = 1` on its
support, while `ψ = 1` and the coefficients of the symbol are those of `P` near its support. -/
private theorem exists_cutoffs_isEllipticAbove (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ}
    (hk : ∀ i ∈ t, k i ≤ M) {x : CoordinateSpace n}
    (hσ : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    {U : Set (CoordinateSpace n)} (hU : U ∈ 𝓝 x) (hUΩ : U ⊆ Ω) :
    ∃ V ∈ 𝓝 x, V ⊆ Ω ∧ ∃ (χ ψ : 𝓓(Ω, ℂ)) (b : ι → CoordinateSpace n → ℂ →L[ℂ] ℂ)
      (hb : ∀ i ∈ t, ContDiff ℝ ∞ (b i)) (R : ℝ),
      (ClassicalSymbol.ofDifferentialSymbol M t m b hb hk).toSymbol.IsEllipticAbove R ∧
      tsupport ψ ⊆ U ∧ (∀ y ∈ tsupport ψ, χ y = 1) ∧
      ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ V → (∀ y ∈ tsupport φ, χ y = 1) ∧
        ∀ᶠ y in 𝓝ˢ (tsupport φ),
          ψ y = 1 ∧ ∀ i, b i y = (c i * g i y) • ContinuousLinearMap.id ℂ ℂ := by
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
  refine ⟨ball x (ε / 4), ball_mem_nhds x (by positivity),
    (ball_subset_ball (by linarith)).trans hεΩ, _, ψ', b, hb, R, hR,
    hψ'.trans ((ball_subset_ball (by linarith)).trans (hεU.trans inter_subset_left)),
    hχ _ (hψ'.trans ball_subset_closedBall), fun φ hφs ↦
      ⟨hχ _ (hφs.trans ((ball_subset_ball (by linarith)).trans ball_subset_closedBall)), ?_⟩⟩
  -- Near the support of `φ`, `ψ = 1` and the frozen coefficients are those of `P`.
  filter_upwards [nhdsSet_mono (hφs.trans ball_subset_closedBall) hψ1,
    (isOpen_ball.mem_nhdsSet.2 hφs)] with y hy hyb
  exact ⟨by simp [ψ', hy], hbx y (ball_subset_closedBall hyb)⟩

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
  obtain ⟨V, hV, hVΩ, χ, ψ, b, hb, R, hR, hψU, hχψ, hφ⟩ :=
    exists_cutoffs_isEllipticAbove hg hk hσ hU hUΩ
  exact isLocallyMemSobolevAt_iff.2 ⟨V, hV, hVΩ, fun φ hφs ↦
    memSobolev_cutoffTempered_of_isEllipticAbove hp hp_top hg hk T hχψ (hφ φ hφs).1 hb hR
      (hφ φ hφs).2 (hPU ψ hψU)⟩

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

/-! ### Microlocal Sobolev regularity -/

/-- **Microlocal Sobolev elliptic regularity for differential operators.** Let
`P = ∑ i ∈ t, c i g i ∂^(m i)` have smooth real coefficients `g i`, complex constants `c i` and
orders `k i ≤ M`, and let `ξ` be noncharacteristic for `P` at `x`: the principal symbol with the
coefficients frozen at `x`, `principalSymbol t (fun i y ↦ c i * g i y) m M x`, does not vanish at
`ξ`. If `P T` is microlocally `H^s` at `(x, ξ)`, then `T` is microlocally `H^(s + M)` there. -/
theorem IsMicrolocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {x ξ : CoordinateSpace n} {s : ℝ}
    (hPT : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsMicrolocallySobolevAt s
      x ξ)
    (hξ : principalSymbol t (fun i y ↦ c i * g i y) m M x ξ ≠ 0) :
    T.IsMicrolocallySobolevAt (s + M) x ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · -- At `ξ = 0` this is local regularity: the principal symbol at `0` is `0 ^ M` times its value
    -- at any `η`, so it vanishes nowhere.
    refine (IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk (fun η _ ↦ ?_)
      (isMicrolocallySobolevAt_zero_covector_iff.1 hPT)).isMicrolocallySobolevAt 0
    have h0 := principalSymbol_smul t (fun i y ↦ c i * g i y) m M x 0 η
    rw [zero_smul] at h0
    have hη := right_ne_zero_of_mul (h0 ▸ hξ)
    rwa [principalSymbol_def] at hη
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hPT.mem
  -- Nested cutoffs: `ψ = 1` near `closedBall x (ε / 4)` with support in `B(x, ε / 2)`, and
  -- `χ = 1` near `closedBall x (ε / 2)`.
  obtain ⟨ψ, hψ1, hψs⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    (isCompact_closedBall x (ε / 4)) isOpen_ball (closedBall_subset_ball (by linarith))
    ((ball_subset_ball (by linarith : ε / 2 ≤ ε)).trans hεΩ)
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    (isCompact_closedBall x (ε / 2)) isOpen_ball (closedBall_subset_ball (by linarith)) hεΩ
  have hψx (y : CoordinateSpace n) (hy : y ∈ ball x (ε / 4)) : ψ y = 1 :=
    hψ1.self_of_nhdsSet y (ball_subset_closedBall hy)
  have hχx (y : CoordinateSpace n) (hy : y ∈ ball x (ε / 4)) : χ y = 1 :=
    hχ1.self_of_nhdsSet y (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy))
  have hx4 : x ∈ ball x (ε / 4) := mem_ball_self (by positivity)
  -- `χ T` is some `u ∈ H^r`, and the operator with coefficients cut off by `ψ` sends it to `ψ P T`.
  obtain ⟨r, hr⟩ := T.exists_memSobolev_cutoffTempered χ
  obtain ⟨hβ, hβc, hc⟩ := exists_hasCompactSpatialSupport_cutoff (c := c) (m := m) hg hk ψ
  have hu := ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol M t m hk
    (fun i hi ↦ (hβc i hi).hasTemperateGrowth (hβ i hi)) hc r hr.toBesselPotentialSpace
  rw [hr.toBesselPotentialSpace_toDistr, sum_smulLeftCLM_iteratedLineDerivOp_cutoffTempered hg T
    fun y hy ↦ hχ1.self_of_nhdsSet y (ball_subset_closedBall (hψs hy))] at hu
  -- Since `ψ x = 1`, the cut-off symbol has the principal symbol of `P` at `(x, ξ)`.
  have hprin : ((ClassicalSymbol.ofDifferentialSymbol M t m
      (fun i y ↦ (c i * TestFunction.smulLeftCLM (hg i) ψ y) • ContinuousLinearMap.id ℂ ℂ)
      (fun i hi ↦ (hβ i hi).smul contDiff_const) hk).principal.coefficient
        (x, ξ)).IsInvertible := by
    rw [ClassicalSymbol.coefficient_principal_ofDifferentialSymbol _ _ _ _ _ _ hξ0,
      differentialSymbol_filter_smul_id]
    exact ContinuousLinearMap.isInvertible_smul_id_iff.2 (mul_ne_zero (pow_ne_zero _ I_ne_zero)
      (by simpa [principalSymbol_def, hψx x hx4] using hξ))
  obtain ⟨U, hU, Γ, hΓ, hξΓ, hcone, R, hell⟩ :=
    ClassicalSymbol.exists_isEllipticOn_of_isInvertible_coefficient_principal hξ0 hprin
  -- `ψ P T` agrees with `P T` near `x`, and `χ T` with `T`.
  have hD := hc.isMicrolocallySobolevAt_toDistribution_of_quantizeSobolev hU hΓ hcone hξΓ hell
    (by rw [hu]; exact (isMicrolocallySobolevAt_iff_of_isVanishingOn_sub isOpen_ball hx4
      (isVanishingOn_sub_toDistribution_cutoffTempered _ hψx)).1 hPT)
  rw [hr.toBesselPotentialSpace_toDistr] at hD
  exact (isMicrolocallySobolevAt_iff_of_isVanishingOn_sub isOpen_ball hx4
    (isVanishingOn_sub_toDistribution_cutoffTempered T hχx)).2 hD

/-- At a noncharacteristic covector `(x, ξ)` of `P = ∑ i ∈ t, c i g i ∂^(m i)`, with smooth real
coefficients `g i` and orders `k i ≤ M`, `P T` is microlocally `H^s` exactly when `T` is
microlocally `H^(s + M)`. -/
theorem isMicrolocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {x ξ : CoordinateSpace n} {s : ℝ}
    (hξ : principalSymbol t (fun i y ↦ c i * g i y) m M x ξ ≠ 0) :
    (∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).IsMicrolocallySobolevAt s x ξ ↔
      T.IsMicrolocallySobolevAt (s + M) x ξ :=
  ⟨fun h ↦ h.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk hξ, fun h ↦ by
    simpa using h.sum_smul_smulLeftCLM_iteratedLineDerivOp t c hg m hk⟩

/-- **Microlocal Sobolev elliptic regularity for differential operators**:
`WF_(s + M)(T) ⊆ WF_s(P T) ∪ Char(P)` for `P = ∑ i ∈ t, c i g i ∂^(m i)` with smooth real
coefficients `g i` and orders `k i ≤ M`, where
`Char(P) = characteristicSet t (fun i y ↦ c i * g i y) m M` is the set of `(x, ξ)` with `ξ ≠ 0` at
which the principal symbol with the coefficients frozen at `x` vanishes. -/
theorem
    sobolevWaveFrontSet_subset_sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union
    (s : ℝ) (t : Finset ι) (c : ι → ℂ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (m : ∀ i, Fin (k i) → CoordinateSpace n) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevWaveFrontSet (s + M) ⊆
      (∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).sobolevWaveFrontSet s ∪
        characteristicSet t (fun i y ↦ c i * g i y) m M := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  by_contra h
  rw [mem_union, not_or, mem_sobolevWaveFrontSet_iff, mem_characteristicSet_iff] at h
  exact hT (IsMicrolocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk
    (by simpa [hx, hξ] using h.1) fun h0 ↦ h.2 ⟨hξ, h0⟩)

/-- **Elliptic differential operators shift the `H^s` wave front set by their order.** If the
principal symbol of `P = ∑ i ∈ t, c i g i ∂^(m i)` of order `M`, with smooth real coefficients
`g i` frozen at any point of `Ω`, vanishes at no `ξ ≠ 0`, then `WF_s(P T) = WF_(s + M)(T)`. -/
theorem sobolevWaveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero (s : ℝ)
    (t : Finset ι) (c : ι → ℂ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (m : ∀ i, Fin (k i) → CoordinateSpace n) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M)
    (hσ : ∀ x ∈ Ω, ∀ ξ, ξ ≠ 0 → principalSymbol t (fun i y ↦ c i * g i y) m M x ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).sobolevWaveFrontSet s =
      T.sobolevWaveFrontSet (s + M) := by
  ext ⟨x, ξ⟩
  simp only [mem_sobolevWaveFrontSet_iff, and_congr_right_iff]
  exact fun hx hξ ↦ not_congr
    (isMicrolocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff hg hk (hσ x hx ξ hξ))

/-! ### Besov and Hölder regularity -/

/-- The analytic core of elliptic regularity on Besov spaces: given cutoffs `χ = 1` on the supports
of `ψ` and `φ`, and a symbol elliptic above some radius whose coefficients are those of `P` where
`ψ = 1` near the support of `φ`, `ψ P T ∈ B^s_{p,q}` implies `φ T ∈ B^{s + M}_{p,q}`, for
`1 < p ≤ ∞`. -/
private theorem memBesov_cutoffTempered_of_isEllipticAbove
    {ρ : ContDiffBump (0 : CoordinateSpace n)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 1 < p) (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) (T : 𝓓'(Ω, ℂ))
    {χ ψ φ : 𝓓(Ω, ℂ)}
    (hχψ : ∀ y ∈ tsupport ψ, χ y = 1) (hχφ : ∀ y ∈ tsupport φ, χ y = 1)
    {b : ι → CoordinateSpace n → ℂ →L[ℂ] ℂ} (hb : ∀ i ∈ t, ContDiff ℝ ∞ (b i)) {R : ℝ}
    (hR : (ClassicalSymbol.ofDifferentialSymbol M t m b hb hk).toSymbol.IsEllipticAbove R)
    (hbψ : ∀ᶠ y in 𝓝ˢ (tsupport φ),
      ψ y = 1 ∧ ∀ i, b i y = (c i * g i y) • ContinuousLinearMap.id ℂ ℂ) {s : ℝ}
    (hPψ : ((∑ i ∈ t, c i • smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered ψ).MemBesov ρ s p q) :
    (T.cutoffTempered φ).MemBesov ρ (s + M) p q := by
  -- `u = χ T` has finite order on the Besov scale and on the Sobolev scale `H^r`.
  obtain ⟨r, hr⟩ := exists_memBesov_cutoffTempered ρ hp
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' T χ
  obtain ⟨r₂, hr₂⟩ := T.exists_memSobolev_cutoffTempered χ
  -- The operator with coefficients cut off by `ψ`, acting on `u`, is `ψ P T`.
  obtain ⟨hβ, hβc, hc, hcoef⟩ := exists_cutoff_coefficient_eq hg hk ψ hb hbψ
  have hu := ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol M t m hk
    (fun i hi ↦ (hβc i hi).hasTemperateGrowth (hβ i hi)) hc r₂ hr₂.toBesselPotentialSpace
  rw [Symbol.toDistr_quantizeSobolev, hr₂.toBesselPotentialSpace_toDistr,
    sum_smulLeftCLM_iteratedLineDerivOp_cutoffTempered hg T hχψ] at hu
  set φS : 𝓢(CoordinateSpace n, ℂ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  have hφS : (φS : CoordinateSpace n → ℂ) = φ :=
    funext (φ.hasCompactSupport.toSchwartzMap_toFun φ.contDiff)
  obtain ⟨_, hab, -⟩ := hR.exists_isAsymptoticSum_sharpTerm
  have hreg := Symbol.memBesov_smulLeftCLM_of_memBesov_quantizeTempered hab
    (hφS ▸ φ.hasCompactSupport) hc (by rwa [hφS]) hr (by rw [hu]; exact hPψ)
  rwa [hφS, smulLeftCLM_cutoffTempered T hχφ] at hreg

/-- **Interior elliptic regularity for differential operators on Besov spaces.** Let
`1 < p ≤ ∞` and `1 ≤ q ≤ ∞`, let `P = ∑ i ∈ t, c i g i ∂^(m i)` have smooth real coefficients `g i`,
complex constants `c i` and orders `k i ≤ M`, and let `P` be elliptic at `x`: its principal symbol
of order `M` with the coefficients frozen at `x` vanishes at no `ξ ≠ 0`. If `P T` is `B^s_{p,q}`
near `x`, then `T` is `B^{s + M}_{p,q}` near `x`. For `p = q = ∞` this is regularity on the
Hölder–Zygmund scale `𝒞^s`. -/
theorem IsLocallyMemBesovAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    {ρ : ContDiffBump (0 : CoordinateSpace n)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 1 < p) (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {x : CoordinateSpace n} {s : ℝ}
    (hσ : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    (hPT : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallyMemBesovAt ρ s
      p q x) :
    T.IsLocallyMemBesovAt ρ (s + M) p q x := by
  obtain ⟨U, hU, hUΩ, hPU⟩ := isLocallyMemBesovAt_iff.1 hPT
  obtain ⟨V, hV, hVΩ, χ, ψ, b, hb, R, hR, hψU, hχψ, hφ⟩ :=
    exists_cutoffs_isEllipticAbove hg hk hσ hU hUΩ
  exact isLocallyMemBesovAt_iff.2 ⟨V, hV, hVΩ, fun φ hφs ↦
    memBesov_cutoffTempered_of_isEllipticAbove hp hg hk T hχψ (hφ φ hφs).1 hb hR (hφ φ hφs).2
      (hPU ψ hψU)⟩

/-- **Local Schauder regularity for differential operators.** Let `0 < α < 1`, let
`P = ∑ i ∈ t, c i g i ∂^(m i)` have smooth real coefficients `g i`, complex constants `c i` and
orders `k i ≤ M`, and let `P` be elliptic at `x`: its principal symbol of order `M` with the
coefficients frozen at `x` vanishes at no `ξ ≠ 0`. If `P T` is a `C^{j,α}` function near `x`, then
`T` is a `C^{j + M,α}` function near `x`. -/
theorem IsLocallyCkHolderAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ} (hk : ∀ i ∈ t, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {x : CoordinateSpace n} {j : ℕ} {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (hσ : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m M ξ ≠ 0)
    (hPT : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallyCkHolderAt j α
      x) :
    T.IsLocallyCkHolderAt (j + M) α x := by
  have hreg := (hPT.isLocallyMemBesovAt default).of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    ENNReal.one_lt_top hg hk hσ
  rw [add_right_comm, ← Nat.cast_add] at hreg
  exact hreg.isLocallyCkHolderAt hα0 hα1

end Distribution
