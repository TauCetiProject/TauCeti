/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.CoordinateDeriv
public import TauCeti.Analysis.Distribution.WaveFrontSet.EllipticRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic
import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Pseudodifferential.EllipticRegularity

/-!
# Local elliptic regularity for differential operators with smooth coefficients

Let `P = ∑ i ∈ t, c i g i ∂^(m i)` be a linear differential operator on an open set `Ω ⊆ ℝⁿ`,
with complex constants `c i`, smooth real coefficients `g i` and iterated directional derivatives
`∂^(m i)` of orders `k i ≤ N`. It acts on complex distributions `T ∈ 𝓓'(Ω)`. Its principal symbol
at a point `x₀`, in the geometric convention without factors of `i`, is the principal symbol of the
operator with coefficients frozen at `x₀`,

`σ_N(P)(x₀, ξ) = ∑ i ∈ t with k i = N, c i g i (x₀) ∏ₗ ⟪m i l, ξ⟫`

(`TauCeti.constCoeffPrincipalSymbol t (fun i ↦ c i * g i x₀) m N`), and `P` is *elliptic at `x₀`*
when it vanishes at no `ξ ≠ 0`. This file proves **local elliptic regularity** in the scale of
Bessel-potential spaces: if `P` is elliptic at `x₀` and `P T` is `H^s` near `x₀`, then `T` is
`H^(s + N)` near `x₀`
(`Distribution.IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`).
Together with the reverse statement, that `P` costs at most `N` orders
(`Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`), this gives

* `Distribution.isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff`: at a point where
  `P` is elliptic, `P T` is `H^s` exactly when `T` is `H^(s + N)`;
* `Distribution.sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp`: if `P` is
  elliptic at every point of `Ω`, the `H^s` singular support of `P T` is the `H^(s + N)` singular
  support of `T`. That is, `P T ∈ H^s_loc(U) ⇔ T ∈ H^(s + N)_loc(U)` on every open `U ⊆ Ω`.

The distribution `T` is only assumed to be a distribution: it has some finite Sobolev order near
`x₀`, and no a priori regularity is required. The statements are on open subsets of
`ℝⁿ = CoordinateSpace n`, where the symbol calculus lives.

On the way, `TauCeti.ClassicalSymbol.isElliptic_ofDifferentialSymbol_smul_id_iff` shows that a
scalar differential operator is elliptic as a classical symbol exactly when its principal symbol
with coefficients frozen at each position vanishes at no `ξ ≠ 0`.

## The argument

The statement is reduced to interior elliptic regularity of pseudodifferential operators on the
Bessel-potential spaces of `ℝⁿ` (`TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`). Choose
cutoffs `φ, χ, ψ` around `x₀`, each equal to `1` near the support of the previous one, inside a
small ball around `x₀`.

* The tempered distribution `u = ψ T` lies in some `H^t`
  (`Distribution.exists_memSobolev_cutoffTempered`).
* The differential operator `∑ i ∈ t, c i (χ g i) ∂^(m i)` with compactly supported coefficients is
  the quantization of a symbol `a` with compact spatial support, and its action on `u ∈ H^t` is
  the action on tempered distributions
  (`TauCeti.ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol_smul_id`). Since `ψ = 1`
  near the support of `χ`, `Op(a) u` is the cut-off `χ P T`
  (`Distribution.smulLeftCLM_iteratedLineDerivOp_cutoffTempered`), which is `H^s`.
* The symbol `a` agrees near the support of `φ` with the symbol `p` of the operator whose
  coefficients are frozen outside a small ball: `g i (x₀) + θ (g i - g i (x₀))` for a bump
  `θ` equal to `1` near `x₀`. Ellipticity is open in the coefficients
  (`TauCeti.exists_pos_forall_constCoeffPrincipalSymbol_ne_zero`), so for a small enough ball the
  principal symbol of `p` vanishes at no `(x, ξ)` with `ξ ≠ 0`; since the coefficients of `p` only
  take the values they take on a compact set, `p` is elliptic above some radius
  (`TauCeti.ClassicalSymbol.IsElliptic.exists_isUniformlyEllipticAbove_of_forall_exists_mem`).
* Interior regularity then gives `φ u = φ T ∈ H^(s + N)`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Complex Filter Metric Set TopologicalSpace LineDeriv TauCeti
open scoped Distributions Topology SchwartzMap BesselPotentialSpace ContDiff RealInnerProductSpace

namespace TauCeti.ClassicalSymbol

variable {n : ℕ} {ι : Type*} {t : Finset ι} {k : ι → ℕ} {m : ∀ i, Fin (k i) → CoordinateSpace n}
  {N : ℕ}

/-- **Ellipticity of a scalar differential operator.** The classical symbol of the differential
operator `∑ i ∈ t, d i ∂^(m i)` of order at most `N`, with smooth complex coefficients `d i`, is
elliptic exactly when at every position `x` the principal symbol of the operator with coefficients
frozen at `x` vanishes at no `ξ ≠ 0`. -/
theorem isElliptic_ofDifferentialSymbol_smul_id_iff {d : ι → CoordinateSpace n → ℂ}
    (hd : ∀ i ∈ t, ContDiff ℝ ∞ fun x ↦ d i x • ContinuousLinearMap.id ℂ ℂ)
    (hk : ∀ i ∈ t, k i ≤ N) :
    (ofDifferentialSymbol N t m (fun i x ↦ d i x • ContinuousLinearMap.id ℂ ℂ) hd hk).IsElliptic ↔
      ∀ x ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ d i x) m N ξ ≠ 0 := by
  rw [isElliptic_ofDifferentialSymbol_iff]
  refine forall_congr' fun x ↦ forall_congr' fun ξ ↦ forall_congr' fun _ ↦ ?_
  -- The differential symbol of the top-order part is `i ^ N σ_N(x, ξ)` times the identity.
  have hsym : differentialSymbol {i ∈ t | k i = N} m
      (fun i x ↦ d i x • ContinuousLinearMap.id ℂ ℂ) (x, ξ) =
      (Complex.I ^ N * constCoeffPrincipalSymbol t (fun i ↦ d i x) m N ξ) •
        ContinuousLinearMap.id ℂ ℂ := by
    refine ContinuousLinearMap.ext_ring ?_
    simp only [differentialSymbol_eq_sum_pow_mul, constCoeffPrincipalSymbol_def,
      FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← (Finset.mem_filter.1 hi).2]
    simp_rw [real_inner_comm ξ]
    ring
  have hid : (ContinuousLinearMap.id ℂ ℂ).IsInvertible := by
    simpa using ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ ℂ)
  rw [hsym]
  refine ⟨fun h h0 ↦ ?_, fun h ↦ ?_⟩
  · -- With `σ_N(x, ξ) = 0` the symbol is the zero map, which is not invertible on `ℂ`.
    rw [h0, mul_zero, zero_smul ℂ (ContinuousLinearMap.id ℂ ℂ)] at h
    exact not_subsingleton ℂ (ContinuousLinearMap.isInvertible_zero_iff.1 h).1
  · rw [ContinuousLinearMap.isInvertible_smul_iff
      (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) h)]
    exact hid

end TauCeti.ClassicalSymbol

namespace Distribution

variable {n : ℕ} {Ω : Opens (CoordinateSpace n)}

/-- Interpolating between the coefficients `c i g i` and their values at `x₀` with a weight
`θ x ∈ [0, 1]` moves them by at most `ε` times the size of the operator, when the coefficients are
`ε`-close to their values at `x₀` wherever `θ ≠ 0`. -/
private theorem sum_norm_sub_mul_prod_le {ι : Type*} {t : Finset ι} (c : ι → ℂ)
    (g : ι → CoordinateSpace n → ℝ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → CoordinateSpace n)
    {x₀ x : CoordinateSpace n} {θ ε : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ 1) (hε : 0 ≤ ε)
    (hg : θ ≠ 0 → ∀ i ∈ t, |g i x - g i x₀| ≤ ε) :
    ∑ i ∈ t, ‖c i * ((g i x₀ + θ * (g i x - g i x₀) : ℝ) : ℂ) - c i * g i x₀‖ * ∏ l, ‖m i l‖ ≤
      ε * ∑ i ∈ t, ‖c i‖ * ∏ l, ‖m i l‖ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hdi : c i * ((g i x₀ + θ * (g i x - g i x₀) : ℝ) : ℂ) - c i * g i x₀ =
      c i * ((θ * (g i x - g i x₀) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hdi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    show ε * (‖c i‖ * ∏ l, ‖m i l‖) = ‖c i‖ * ε * ∏ l, ‖m i l‖ by ring]
  gcongr
  rcases eq_or_ne θ 0 with h0 | h0
  · simp [h0, hε]
  · calc |θ| * |g i x - g i x₀| ≤ 1 * ε := by
          gcongr
          · exact (abs_of_nonneg hθ.1).trans_le hθ.2
          · exact hg h0 i hi
      _ = ε := one_mul ε

/-- **Freezing the coefficients away from a point.** A differential operator of order at most `N`
elliptic at `x₀` agrees near `x₀` with the quantization of a symbol of order `N` elliptic above some
radius at every position: freeze its coefficients at their values at `x₀` outside a small ball, on
which they stay close enough to these values for the principal symbol not to vanish. -/
private theorem exists_isEllipticAbove_eventually_coefficient_eq {ι : Type*} {t : Finset ι}
    {c : ι → ℂ} {g : ι → CoordinateSpace n → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {k : ι → ℕ}
    {m : ∀ i, Fin (k i) → CoordinateSpace n} {N : ℕ} (hk : ∀ i ∈ t, k i ≤ N)
    {x₀ : CoordinateSpace n}
    (hell : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x₀) m N ξ ≠ 0) :
    ∃ (p : Symbol n ℂ ℂ N) (R : ℝ), p.IsEllipticAbove R ∧ ∀ᶠ x in 𝓝 x₀, ∀ ξ,
      p.coefficient (x, ξ) =
        differentialSymbol t m (fun i x ↦ (c i * g i x) • ContinuousLinearMap.id ℂ ℂ) (x, ξ) := by
  classical
  -- Coefficients within `ε` of their values at `x₀` keep the principal symbol elliptic.
  obtain ⟨δ, hδ, hδell⟩ := exists_pos_forall_constCoeffPrincipalSymbol_ne_zero hell
  set A := ∑ i ∈ t, ‖c i‖ * ∏ l, ‖m i l‖
  set ε := δ / (2 * (A + 1))
  have hε : 0 < ε := by positivity
  have hεA : ε * A < δ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [show 0 ≤ A by positivity]
  obtain ⟨ρ, hρ, hρg⟩ := Metric.eventually_nhds_iff_ball.1
    ((Filter.eventually_all_finset t).2 fun i _ ↦ by
      simpa [Real.dist_eq] using
        ((hg i).continuous.tendsto x₀).eventually (Metric.ball_mem_nhds (g i x₀) hε))
  -- The frozen coefficients `c i (g i (x₀) + θ (g i - g i (x₀)))`, for a bump `θ` which is `1`
  -- on `closedBall x₀ (ρ / 3)` and `0` outside `ball x₀ (ρ / 2)`.
  let θ : ContDiffBump x₀ := ⟨ρ / 3, ρ / 2, by positivity, by linarith⟩
  set d : ι → CoordinateSpace n → ℂ :=
    fun i x ↦ c i * ((g i x₀ + θ x * (g i x - g i x₀) : ℝ) : ℂ)
  have hd (i : ι) (_ : i ∈ t) : ContDiff ℝ ∞ (fun x ↦ d i x • ContinuousLinearMap.id ℂ ℂ) :=
    (contDiff_const.mul (ofRealCLM.contDiff.comp (contDiff_const.add
      (θ.contDiff.mul ((hg i).sub contDiff_const))))).smul contDiff_const
  set p := ClassicalSymbol.ofDifferentialSymbol N t m _ hd hk
  -- At every position the frozen coefficients are `ε`-close to their values at `x₀`, so the
  -- principal symbol of `p` vanishes at no `ξ ≠ 0`.
  have hpell : p.IsElliptic :=
    (ClassicalSymbol.isElliptic_ofDifferentialSymbol_smul_id_iff hd hk).2 fun x ξ hξ ↦
      hδell _ ((sum_norm_sub_mul_prod_le c g m ⟨θ.nonneg, θ.le_one⟩ hε.le fun hx i hi ↦
        (hρg x (ball_subset_ball (show ρ / 2 ≤ ρ by linarith)
          (θ.support_eq ▸ hx : x ∈ ball x₀ (ρ / 2))) i hi).le).trans_lt hεA) ξ hξ
  -- Outside `closedBall x₀ (ρ / 2)` the symbol of `p` is its symbol at `x₀`.
  have hθx₀ : θ x₀ = 1 := θ.one_of_mem_closedBall (mem_closedBall_self (by positivity))
  obtain ⟨R, hR⟩ := hpell.exists_isUniformlyEllipticAbove_of_forall_exists_mem
    (isCompact_closedBall x₀ (ρ / 2)) fun x ↦ by
      by_cases hx : x ∈ closedBall x₀ (ρ / 2)
      · exact ⟨x, hx, fun _ ↦ rfl⟩
      · have hθx : θ x = 0 := θ.zero_of_le_dist (le_of_lt (by simpa using hx))
        refine ⟨x₀, mem_closedBall_self (by positivity), fun ξ ↦ ?_⟩
        simp only [p, ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol,
          differentialSymbol_def]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [d, hθx, hθx₀]
  refine ⟨p.toSymbol, R, hR.isEllipticAbove, ?_⟩
  -- Near `x₀` the bump is `1`, and the frozen coefficients are the original ones.
  filter_upwards [Metric.ball_mem_nhds x₀ (by positivity : 0 < ρ / 3)] with x hx ξ
  have hθx : θ x = 1 := θ.one_of_mem_closedBall (ball_subset_closedBall hx)
  simp only [p, ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol,
    differentialSymbol_def]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [d, hθx]

/-- **Localizing a differential operator.** Let `χ` and `ψ` be cutoffs with `ψ = 1` on the support
of `χ`. The differential operator `∑ i ∈ t, c i (χ g i) ∂^(m i)`, with compactly supported
coefficients, is the quantization of a symbol `a` with compact spatial support, and on any element
`u` of a Bessel-potential space representing the cut-off `ψ T` its quantization is the cut-off
`χ P T` of `P T`, for `P = ∑ i ∈ t, c i g i ∂^(m i)`. -/
private theorem exists_toDistr_quantizeSobolev_eq_cutoffTempered (T : 𝓓'(Ω, ℂ)) {ι : Type*}
    {t : Finset ι} (c : ι → ℂ) {g : ι → CoordinateSpace n → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {k : ι → ℕ} (m : ∀ i, Fin (k i) → CoordinateSpace n) {N : ℕ} (hk : ∀ i ∈ t, k i ≤ N)
    {χ ψ : 𝓓(Ω, ℂ)} (hψ : EqOn (ψ : CoordinateSpace n → ℂ) 1 (tsupport χ)) :
    ∃ (a : Symbol n ℂ ℂ N) (ha : a.HasCompactSpatialSupport),
      (∀ x ξ, a.coefficient (x, ξ) = differentialSymbol t m
        (fun i x ↦ (c i * (g i x * χ x)) • ContinuousLinearMap.id ℂ ℂ) (x, ξ)) ∧
      ∀ (r : ℝ) (u : H^{r}(CoordinateSpace n)), u.toDistr = T.cutoffTempered ψ →
        (a.quantizeSobolev ha r u).toDistr =
          (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered χ := by
  set χg : ι → 𝓓(Ω, ℂ) := fun i ↦ TestFunction.smulLeftCLM (hg i) χ
  have hχg (i : ι) (x : CoordinateSpace n) : χg i x = g i x * χ x := by
    simp [χg, Complex.real_smul]
  set β : ι → CoordinateSpace n → ℂ := fun i x ↦ c i * χg i x
  have hβc (i : ι) (_ : i ∈ t) : HasCompactSupport (β i) := (χg i).hasCompactSupport.mul_left
  have hβ (i : ι) (hi : i ∈ t) : (β i).HasTemperateGrowth :=
    (hβc i hi).hasTemperateGrowth (contDiff_const.mul (χg i).contDiff)
  set a := ClassicalSymbol.ofDifferentialSymbol N t m
    (fun i x ↦ β i x • ContinuousLinearMap.id ℂ ℂ) (fun i hi ↦ (hβ i hi).1.smul contDiff_const)
    hk
  have ha : a.toSymbol.HasCompactSpatialSupport :=
    ClassicalSymbol.hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol _ _ _ _ _ _
      fun i hi ↦ (hβc i hi).smul_right
  refine ⟨a.toSymbol, ha, fun x ξ ↦ ?_, fun r u hu ↦ ?_⟩
  · simp only [a, ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol, β, hχg]
  rw [ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol_smul_id N t m hk hβ ha,
    hu, cutoffTempered_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hψi : EqOn (ψ : CoordinateSpace n → ℂ) 1 (tsupport (χg i)) :=
    hψ.mono ((TestFunction.tsupport_smulLeftCLM_subset _ _).trans inter_subset_right)
  have hβi : β i = c i • (χg i : CoordinateSpace n → ℂ) := funext fun x ↦ by simp [β]
  rw [cutoffTempered_smul, cutoffTempered_smulLeftCLM,
    ← smulLeftCLM_iteratedLineDerivOp_cutoffTempered T hψi, hβi,
    TemperedDistribution.smulLeftCLM_smul
      ((χg i).hasCompactSupport.hasTemperateGrowth (χg i).contDiff), smul_apply]

/-- **Local elliptic regularity.** Let `P = ∑ i ∈ t, c i g i ∂^(m i)` be a differential operator
of order at most `N` with smooth coefficients, elliptic at `x₀`: its principal symbol
`∑ i ∈ t with k i = N, c i g i (x₀) ∏ₗ ⟪m i l, ξ⟫` vanishes at no `ξ ≠ 0`. If `P T` is `H^s`
near `x₀`, then `T` is `H^(s + N)` near `x₀`. -/
theorem IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp {T : 𝓓'(Ω, ℂ)}
    {ι : Type*} {t : Finset ι} {c : ι → ℂ} {g : ι → CoordinateSpace n → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {k : ι → ℕ} {m : ∀ i, Fin (k i) → CoordinateSpace n} {N : ℕ}
    (hk : ∀ i ∈ t, k i ≤ N) {x₀ : CoordinateSpace n}
    (hell : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x₀) m N ξ ≠ 0) {s : ℝ}
    (hP : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt s x₀) :
    T.IsLocallySobolevAt (s + N) x₀ := by
  obtain ⟨U, hU, hPU⟩ := hP.exists_nhds_forall_memSobolev_cutoffTempered
  obtain ⟨p, R, hp, hpP⟩ := exists_isEllipticAbove_eventually_coefficient_eq hg hk hell
  -- A radius `ρ` such that `ball x₀ ρ` lies in `Ω` and in `U`, and on which `p` is the symbol of
  -- `P`.
  have hΩ : ∀ᶠ x in 𝓝 x₀, x ∈ Ω := Ω.isOpen.mem_nhds hP.mem
  have hU' : ∀ᶠ x in 𝓝 x₀, x ∈ U := hU
  obtain ⟨ρ, hρ, hρG⟩ := Metric.eventually_nhds_iff_ball.1 (hΩ.and (hU'.and hpP))
  have hρΩ : ball x₀ ρ ⊆ Ω := fun x hx ↦ (hρG x hx).1
  -- Real cutoffs in `ball x₀ ρ`: `φ'` around `x₀`, `χ' = 1` near `tsupport φ'` and `ψ' = 1` near
  -- `tsupport χ'`, and their complex versions `φ`, `χ` and `ψ`.
  obtain ⟨φ', -, hφ1, hφ⟩ := TestFunction.exists_cutoff_tsupport_subset (n := ⊤)
    (isCompact_singleton (x := x₀))
    isOpen_ball (singleton_subset_iff.2 (mem_ball_self hρ)) hρΩ
  obtain ⟨χ', -, hχ1, hχ⟩ :=
    TestFunction.exists_cutoff_tsupport_subset (n := ⊤) φ'.hasCompactSupport isOpen_ball hφ hρΩ
  obtain ⟨ψ', -, hψ1, -⟩ :=
    TestFunction.exists_cutoff_tsupport_subset (n := ⊤) χ'.hasCompactSupport isOpen_ball hχ hρΩ
  let φ : 𝓓(Ω, ℂ) := TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM φ'
  let χ : 𝓓(Ω, ℂ) := TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM χ'
  let ψ : 𝓓(Ω, ℂ) := TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM ψ'
  have hts (θ : 𝓓(Ω, ℝ)) :
      tsupport (TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM θ) ⊆ tsupport θ := by
    rw [TestFunction.postcompCLM_apply]; exact tsupport_comp_subset (by simp) θ
  have hφχ : tsupport φ' ⊆ tsupport χ' := fun x hx ↦
    subset_tsupport _ (by simp [hχ1.self_of_nhdsSet x hx])
  have hψ : EqOn (ψ : CoordinateSpace n → ℂ) 1 (tsupport χ') := fun x hx ↦ by
    simp [ψ, hψ1.self_of_nhdsSet x hx]
  obtain ⟨a, ha, haP, hOp⟩ :=
    exists_toDistr_quantizeSobolev_eq_cutoffTempered T c hg m hk (hψ.mono (hts χ'))
  -- Near `tsupport φ`, `χ = 1` and `a` agrees with `p`.
  have hap : ∀ᶠ x in 𝓝ˢ (tsupport φ), ∀ ξ, a.coefficient (x, ξ) = p.coefficient (x, ξ) := by
    filter_upwards [nhdsSet_mono (hts φ') (hχ1.and (isOpen_ball.mem_nhdsSet.2 hφ))]
      with x ⟨hχx, hx⟩ ξ
    rw [haP, (hρG x hx).2.2 ξ]
    simp [differentialSymbol_def, hχx]
  -- The cut-off distribution `u = ψ T` lies in some `H^t₀`, and `Op(a) u = χ P T` lies in `H^s`.
  obtain ⟨t₀, ht₀⟩ := T.exists_memSobolev_cutoffTempered ψ
  have hmem : (a.quantizeSobolev ha t₀ ht₀.toBesselPotentialSpace).toDistr.MemSobolev
      (s + N - N) 2 := by
    rw [hOp t₀ _ ht₀.toBesselPotentialSpace_toDistr, add_sub_cancel_right]
    exact hPU χ ((hts χ').trans (hχ.trans fun x hx ↦ (hρG x hx).2.1))
  -- Interior elliptic regularity: `φ u ∈ H^(s + N)`, and `φ u = φ T`.
  have hreg := hp.memSobolev_smulLeftCLM ha (φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    φ.hasCompactSupport hap hmem
  have hφψ := smulLeftCLM_cutoffTempered_of_eqOn_one T (hψ.mono ((hts φ').trans hφχ))
  rw [BesselPotentialSpace.toDistr_smulLeftCLM,
    TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr,
    funext (HasCompactSupport.toSchwartzMap_toFun φ.hasCompactSupport φ.contDiff), hφψ] at hreg
  exact isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2
    ⟨φ, by simp [φ, hφ1.self_of_nhdsSet x₀ rfl], hreg⟩

/-- **Elliptic operators shift local Sobolev regularity by exactly their order.** At a point where
the differential operator `P = ∑ i ∈ t, c i g i ∂^(m i)` of order at most `N` is elliptic, `P T` is
`H^s` exactly when `T` is `H^(s + N)`. -/
theorem isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff {T : 𝓓'(Ω, ℂ)}
    {ι : Type*} {t : Finset ι} {c : ι → ℂ} {g : ι → CoordinateSpace n → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {k : ι → ℕ} {m : ∀ i, Fin (k i) → CoordinateSpace n} {N : ℕ}
    (hk : ∀ i ∈ t, k i ≤ N) {x₀ : CoordinateSpace n}
    (hell : ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x₀) m N ξ ≠ 0) {s : ℝ} :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt s x₀ ↔
      T.IsLocallySobolevAt (s + N) x₀ :=
  ⟨IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk hell, fun h ↦ by
    simpa using h.sum_smul_smulLeftCLM_iteratedLineDerivOp t c hg m hk⟩

/-- **Elliptic regularity on an open set.** If the differential operator
`P = ∑ i ∈ t, c i g i ∂^(m i)` of order at most `N` is elliptic at every point of `Ω`, the `H^s`
singular support of `P T` is the `H^(s + N)` singular support of `T`: on every open subset of `Ω`,
`P T ∈ H^s_loc` exactly when `T ∈ H^(s + N)_loc`. -/
theorem sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp {ι : Type*}
    {t : Finset ι} {c : ι → ℂ} {g : ι → CoordinateSpace n → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → CoordinateSpace n} {N : ℕ} (hk : ∀ i ∈ t, k i ≤ N)
    (hell : ∀ x ∈ Ω, ∀ ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i x) m N ξ ≠ 0)
    (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).sobolevSingularSupport s =
      T.sobolevSingularSupport (s + N) := by
  ext x
  simp only [mem_sobolevSingularSupport_iff, and_congr_right_iff]
  exact fun hx ↦ not_congr
    (isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff hg hk (hell x hx))

end Distribution
