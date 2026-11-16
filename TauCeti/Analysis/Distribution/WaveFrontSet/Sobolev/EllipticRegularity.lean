/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
public import TauCeti.Analysis.Calculus.CoordinateDeriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.InteriorRegularity
import TauCeti.Analysis.Pseudodifferential.Symbol.Differential

/-!
# Local elliptic regularity of distributions

Let `P = ∑ i ∈ t, c i g i ∂^{m i}` be a linear differential operator of order at most `k` on an
open subset `Ω` of `ℝⁿ`, with smooth real coefficient functions `g i`, complex constants `c i` and
iterated derivatives `∂^{m i}` of orders `n i ≤ k`. It is *elliptic* at `x` if its top-order
symbol

`∑ i ∈ t with n i = k, c i g i (x) ∏ⱼ ⟪ξ, m i j⟫`

vanishes at no nonzero covector `ξ`. This file proves **local elliptic regularity** for
distributions: if `P` is elliptic near `x₀` and `P T` is `H^s` near `x₀`, then `T` is `H^(s + k)`
near `x₀` (`Distribution.IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`), whatever
the real number `s` and however singular `T` is elsewhere. With the converse
`Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`, an elliptic operator
of order `k` maps exactly the distributions that are `H^(s + k)` near `x₀` to those that are `H^s`
near `x₀` (`Distribution.isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff`), and an
operator elliptic on all of `Ω` shifts the `H^s` singular support by exactly its order
(`Distribution.sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp`).

## Proof outline

Freeze the coefficients outside a small ball around `x₀`, by composing them with a smooth map `y`
equal to the identity near `x₀` and with values in that ball. The frozen operator is elliptic at
every point, so its classical symbol `a` has a left parametrix symbol
(`TauCeti.ClassicalSymbol.IsElliptic.exists_isAsymptoticSum_sharpTerm_left`). Take test functions
`ψ`, `χ` and `φ`, each equal to `1` near the support of the previous one, with `P T` of class
`H^s` after cutoff by `χ`. The cut-off `u = φ T` is a tempered distribution of some finite Sobolev
order (`Distribution.exists_memSobolev_cutoffTempered`). The symbol `p` of the operator with the
compactly supported coefficients `χ c i g i` agrees with `a` near the support of `ψ`, and on `u`
its quantization is that operator acting on tempered distributions
(`TauCeti.ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol`). Since `φ = 1` near the
support of `χ`, this is the cut-off `χ P T`
(`Distribution.smulLeftCLM_iteratedLineDerivOp_cutoffTempered`), which lies in `H^s`. Interior
regularity on Bessel-potential spaces
(`TauCeti.Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev`) then puts `ψ u = ψ T` in
`H^(s + k)`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1
  (local Sobolev regularity of distributions).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Complex Filter Metric Set TopologicalSpace LineDeriv TauCeti
open scoped Distributions Topology RealInnerProductSpace ContDiff SchwartzMap

namespace Distribution

variable {d : ℕ} {Ω : Opens (CoordinateSpace d)} {ι : Type*} {t : Finset ι} {c : ι → ℂ}
  {g : ι → CoordinateSpace d → ℝ} {n : ι → ℕ} {m : ∀ i, Fin (n i) → CoordinateSpace d} {k : ℕ}

/-- **Freezing the coefficients.** If `P` is elliptic near `x₀`, there are a closed ball around `x₀`
and a classical symbol of order `k`, elliptic at every point, that agrees on that ball with the
symbol of `P`. Its coefficients are those of `P` composed with a smooth map equal to the identity
on the ball and with values where `P` is elliptic. -/
private theorem exists_isElliptic_coefficient_eq (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hk : ∀ i ∈ t, n i ≤ k) {x₀ : CoordinateSpace d}
    (hP : ∀ᶠ x in 𝓝 x₀, ∀ ξ, ξ ≠ 0 →
      ∑ i ∈ t with n i = k, c i * g i x * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0) :
    ∃ δ > 0, ∃ a : ClassicalSymbol d ℂ ℂ k, a.IsElliptic ∧ ∀ x ∈ closedBall x₀ δ, ∀ ξ,
      a.toSymbol.coefficient (x, ξ) =
        differentialSymbol t m (fun i x ↦ (c i * g i x : ℂ) • ContinuousLinearMap.id ℂ ℂ)
          (x, ξ) := by
  classical
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff_ball.1 hP
  -- `y x = x₀ + β x • (x - x₀)` is the identity on the ball of radius `δ / 2` and takes values in
  -- the ball of radius `δ`.
  let β : ContDiffBump x₀ := ⟨δ / 2, δ, by positivity, by linarith⟩
  let y (x : CoordinateSpace d) : CoordinateSpace d := x₀ + β x • (x - x₀)
  have hy : ContDiff ℝ ∞ y := contDiff_const.add (β.contDiff.smul (contDiff_id.sub contDiff_const))
  have hyx (x) (hx : x ∈ closedBall x₀ (δ / 2)) : y x = x := by
    simp [y, β.one_of_mem_closedBall hx]
  have hyδ (x) : y x ∈ ball x₀ δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg β.nonneg]
    by_cases hx : x ∈ ball x₀ δ
    · calc β x * ‖x - x₀‖ ≤ 1 * ‖x - x₀‖ := by gcongr; exact β.le_one
        _ < δ := by rwa [one_mul, ← dist_eq_norm]
    · rwa [β.zero_of_le_dist (not_lt.1 hx), zero_mul]
  let a := ClassicalSymbol.ofDifferentialSymbol k t m
    (fun i x ↦ (c i * g i (y x) : ℂ) • ContinuousLinearMap.id ℂ ℂ)
    (fun i _ ↦ (contDiff_const.mul (ofRealCLM.contDiff.comp ((hg i).comp hy))).smul
      contDiff_const) hk
  have haC : a.toSymbol.coefficient = differentialSymbol t m
      (fun i x ↦ (c i * g i (y x) : ℂ) • ContinuousLinearMap.id ℂ ℂ) :=
    ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol ..
  refine ⟨δ / 2, half_pos hδ, a, (ClassicalSymbol.isElliptic_ofDifferentialSymbol_iff ..).2
    fun x ξ hξ ↦ isInvertible_differentialSymbol_filter_smul_id t m _ k (hδP (y x) (hyδ x) ξ hξ),
    fun x hx ξ ↦ ?_⟩
  simp only [haC, differentialSymbol_def, hyx x hx]

/-- The cut-off by `χ` of `P T` is the operator with the coefficients `χ c i g i` applied to `φ T`,
when `φ = 1` on the support of `χ`. -/
private theorem sum_smulLeftCLM_iteratedLineDerivOp_cutoffTempered (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {T : 𝓓'(Ω, ℂ)} {φ χ : 𝓓(Ω, ℂ)} (hφ : ∀ x ∈ tsupport χ, φ x = 1) :
    ∑ i ∈ t, TemperedDistribution.smulLeftCLM ℂ (fun x ↦ c i * (χ x * g i x))
        (∂^{m i} (T.cutoffTempered φ)) =
      (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered χ := by
  rw [cutoffTempered_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have htg : (fun x ↦ χ x * (g i x : ℂ)).HasTemperateGrowth :=
    χ.hasTemperateGrowth_mul (ofRealCLM.contDiff.comp (hg i))
  rw [cutoffTempered_smul, ← smulLeftCLM_iteratedLineDerivOp_cutoffTempered hφ (hg i),
    show (fun x ↦ c i * (χ x * g i x)) = c i • fun x ↦ χ x * (g i x : ℂ) from
      funext fun x ↦ by rw [Pi.smul_apply, smul_eq_mul],
    TemperedDistribution.smulLeftCLM_smul htg, _root_.smul_apply]

variable {T : 𝓓'(Ω, ℂ)} {x₀ : CoordinateSpace d} {s : ℝ}

/-- **The local parametrix applied to `φ T`.** Let `a` be an elliptic classical symbol of order
`k` agreeing near the support of a test function `ψ` with the symbol of the operator with the
coefficients `χ c i g i`, and let `φ = 1` on the supports of `χ` and `ψ`. If the cut-off `χ P T`
lies in `H^s`, then `ψ T` lies in `H^(s + k)`. -/
private theorem memSobolev_cutoffTempered_of_isElliptic (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hk : ∀ i ∈ t, n i ≤ k) {a : ClassicalSymbol d ℂ ℂ k} (ha : a.IsElliptic) {φ χ ψ : 𝓓(Ω, ℂ)}
    (hχ : ∀ x ∈ tsupport χ, φ x = 1) (hψ : ∀ x ∈ tsupport ψ, φ x = 1)
    (haψ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, a.toSymbol.coefficient (x, ξ) = differentialSymbol t m
      (fun i x ↦ (c i * (χ x * g i x)) • ContinuousLinearMap.id ℂ ℂ) (x, ξ))
    (hs : ((∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered
      χ).MemSobolev s 2) :
    (T.cutoffTempered ψ).MemSobolev (s + k) 2 := by
  obtain ⟨b, hab⟩ := ha.exists_isAsymptoticSum_sharpTerm_left
  let ψS : 𝓢(CoordinateSpace d, ℂ) := ψ.hasCompactSupport.toSchwartzMap ψ.contDiff
  have hψS (x : CoordinateSpace d) : ψS x = ψ x :=
    HasCompactSupport.toSchwartzMap_toFun ψ.hasCompactSupport ψ.contDiff x
  -- The symbol `p` of the operator with the coefficients `χ c i g i`, with compact spatial support.
  have htg (i : ι) : (fun x ↦ c i * (χ x * g i x)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (c i)).fun_mul
      (χ.hasTemperateGrowth_mul (ofRealCLM.contDiff.comp (hg i)))
  let p := ClassicalSymbol.ofDifferentialSymbol k t m
    (fun i x ↦ (c i * (χ x * g i x)) • ContinuousLinearMap.id ℂ ℂ)
    (fun i _ ↦ (htg i).1.smul contDiff_const) hk
  have hp : p.toSymbol.HasCompactSpatialSupport :=
    ClassicalSymbol.hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol _ _ _ _ _ _
      fun i _ ↦ χ.hasCompactSupport.mul_right.mul_left.smul_right
  have hpC : p.toSymbol.coefficient = differentialSymbol t m
      (fun i x ↦ (c i * (χ x * g i x)) • ContinuousLinearMap.id ℂ ℂ) :=
    ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol ..
  -- The cut-off `u = φ T` has some finite Sobolev order `r`, and `Op(p) u = χ P T` lies in `H^s`.
  obtain ⟨r, hr⟩ := exists_memSobolev_cutoffTempered T φ
  have hpu : (p.toSymbol.quantizeSobolev hp r hr.toBesselPotentialSpace).toDistr =
      ∑ i ∈ t, TemperedDistribution.smulLeftCLM ℂ (fun x ↦ c i * (χ x * g i x))
        (∂^{m i} hr.toBesselPotentialSpace.toDistr) :=
    ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol _ _ _ _ (fun i _ ↦ htg i) hp _ _
  rw [hr.toBesselPotentialSpace_toDistr, sum_smulLeftCLM_iteratedLineDerivOp_cutoffTempered hg hχ]
    at hpu
  -- Interior regularity puts `ψ u = ψ T` in `H^(s + k)`.
  have hreg := Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev hab
    (ψ := ψS) ψ.hasCompactSupport hp (haψ.mono fun x hx ξ ↦ by rw [hpC, hx ξ]) _ (hpu ▸ hs)
  rwa [hr.toBesselPotentialSpace_toDistr, show (ψS : CoordinateSpace d → ℂ) = ψ from funext hψS,
    smulLeftCLM_cutoffTempered hψ] at hreg

/-- **Local elliptic regularity.** Let `P = ∑ i ∈ t, c i g i ∂^{m i}` be a differential operator
of order at most `k` with smooth real coefficient functions `g i` and complex constants `c i`,
elliptic near `x₀`: its top-order symbol `∑ i ∈ t with n i = k, c i g i (x) ∏ⱼ ⟪ξ, m i j⟫` is
nonzero at every nonzero `ξ`, for all `x` near `x₀`. If `P T` is `H^s` near `x₀`, then `T` is
`H^(s + k)` near `x₀`. -/
theorem IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hk : ∀ i ∈ t, n i ≤ k)
    (hP : ∀ᶠ x in 𝓝 x₀, ∀ ξ, ξ ≠ 0 →
      ∑ i ∈ t with n i = k, c i * g i x * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0)
    (h : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt s x₀) :
    T.IsLocallySobolevAt (s + k) x₀ := by
  obtain ⟨U, hU, hUs⟩ := h.exists_nhds_forall_memSobolev_cutoffTempered
  obtain ⟨δ, hδ, a, ha, haP⟩ := exists_isElliptic_coefficient_eq hg hk hP
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_ball.mem_iff.1
    (inter_mem (inter_mem hU (Ω.isOpen.mem_nhds h.mem)) (closedBall_mem_nhds x₀ hδ))
  have hεΩ : ball x₀ ε ⊆ Ω := fun x hx ↦ (hεU hx).1.2
  -- Cutoffs `ψ`, `χ`, `φ` around `x₀`, each equal to `1` near the support of the previous one.
  obtain ⟨ψ, hψ1, hψs⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    (isCompact_singleton (x := x₀)) isOpen_ball (singleton_subset_iff.2 (mem_ball_self hε)) hεΩ
  obtain ⟨χ, hχ1, hχs⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    ψ.hasCompactSupport.isCompact isOpen_ball hψs hεΩ
  obtain ⟨φ, hφ1, -⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    χ.hasCompactSupport.isCompact Ω.isOpen χ.tsupport_subset subset_rfl
  -- Near the support of `ψ`, `χ = 1` and `a` is the symbol of `P`.
  have haψ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ,
      a.toSymbol.coefficient (x, ξ) = differentialSymbol t m
        (fun i x ↦ (c i * (χ x * g i x)) • ContinuousLinearMap.id ℂ ℂ) (x, ξ) := by
    filter_upwards [hχ1, isOpen_ball.mem_nhdsSet.2 hψs] with x hx hxε ξ
    rw [haP x (hεU hxε).2]
    simp only [differentialSymbol_def, hx, one_mul]
  have hψχ (x) (hx : x ∈ tsupport ψ) : x ∈ tsupport χ :=
    subset_tsupport _ (by simp [hχ1.self_of_nhdsSet x hx])
  refine isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2 ⟨ψ, ?_,
    memSobolev_cutoffTempered_of_isElliptic hg hk ha hφ1.self_of_nhdsSet
      (fun x hx ↦ hφ1.self_of_nhdsSet x (hψχ x hx)) haψ
      (hUs _ (hχs.trans fun x hx ↦ (hεU hx).1.1))⟩
  rw [hψ1.self_of_nhdsSet x₀ rfl]
  exact one_ne_zero

/-- **Elliptic operators shift local Sobolev regularity by exactly their order.** For a
differential operator `P = ∑ i ∈ t, c i g i ∂^{m i}` of order at most `k`, elliptic near `x₀`,
`P T` is `H^s` near `x₀` exactly when `T` is `H^(s + k)` near `x₀`. -/
theorem isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hk : ∀ i ∈ t, n i ≤ k)
    (hP : ∀ᶠ x in 𝓝 x₀, ∀ ξ, ξ ≠ 0 →
      ∑ i ∈ t with n i = k, c i * g i x * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt s x₀ ↔
      T.IsLocallySobolevAt (s + k) x₀ :=
  ⟨.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk hP, fun h ↦ by
    simpa using h.sum_smul_smulLeftCLM_iteratedLineDerivOp t c hg m hk⟩

/-- **Elliptic operators shift the `H^s` singular support by exactly their order.** For a
differential operator `P = ∑ i ∈ t, c i g i ∂^{m i}` of order at most `k`, elliptic at every point
of `Ω`, `singsupp_s(P T) = singsupp_(s + k)(T)`. -/
theorem sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hk : ∀ i ∈ t, n i ≤ k)
    (hP : ∀ x ∈ Ω, ∀ ξ, ξ ≠ 0 → ∑ i ∈ t with n i = k, c i * g i x * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0)
    (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).sobolevSingularSupport s =
      T.sobolevSingularSupport (s + k) := by
  ext x
  simp only [mem_sobolevSingularSupport_iff]
  exact and_congr_right fun hx ↦ not_congr
    (isLocallySobolevAt_sum_smul_smulLeftCLM_iteratedLineDerivOp_iff hg hk
      (Filter.mem_of_superset (Ω.isOpen.mem_nhds hx) hP))

end Distribution
