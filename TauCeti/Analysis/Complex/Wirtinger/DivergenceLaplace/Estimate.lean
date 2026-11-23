/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace.Basic
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Complex.Pompeiu.DivergenceForm
import TauCeti.Analysis.Complex.Wirtinger.Beurling.Lp
import TauCeti.Analysis.InnerProductSpace.Harmonic.InteriorLp
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# The interior estimate for the divergence-form Laplace equation in the plane

Write `z = s + i t` on `ℂ`. Let `V` be a finite-dimensional real normed space, `Ω ⊆ ℂ` open,
`1 < r < ∞` and `1 ≤ q ≤ ∞`, and let `U ⊆ ℂ` have compact closure in `Ω`. There is a constant
`C` such that for every `ξ : ℂ → V` locally integrable on `Ω` and all `f, g : ℂ → V` locally `Lʳ`
on `Ω` with `Δξ = ∂ₛf + ∂ₜg` weakly on `Ω`, that is

`∫ Δφ • ξ = -∫ (∂ₛφ • f + ∂ₜφ • g)` for every real test function `φ` on `Ω`,

the `W^{1,r}(U)` norm of `ξ` is bounded by

`‖ξ‖_{W^{1,r}(U)} ≤ C (‖f‖_{Lʳ(Ω)} + ‖g‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})`

(`TauCeti.exists_eLpNormWkp_one_le_of_integral_laplacian_smul_eq`). The constant depends only on
`r`, `q`, `U`, `Ω` and `V`. For bounded `Ω` the case `q = 1` is the strongest, since then
`‖ξ‖_{L¹(Ω)}` is bounded by a multiple of `‖ξ‖_{L^q(Ω)}`; for unbounded `Ω` one first shrinks `Ω`
to a bounded open neighbourhood of the closure of `U`. The case `r ≤ q` is the form in which the
estimate is used for a solution `ξ ∈ L^q_loc`. The membership `ξ ∈ W^{1,r}_loc(Ω)` is
`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq`; this file adds the estimate. The same
bound holds for the `Lʳ(U)` norm of every weak derivative of `ξ` on `Ω`
(`TauCeti.exists_eLpNorm_le_of_integral_laplacian_smul_eq_of_hasWeakFDerivOn`).

The term `‖ξ‖_{L^q(Ω)}` cannot be dropped: the constant function `1` is harmonic, solves the
equation with `f = g = 0`, and has positive `W^{1,r}` norm on every set of positive measure
(`TauCeti.not_exists_eLpNormWkp_one_le_eLpNorm_add_eLpNorm_of_integral_laplacian_smul_eq`).

## The argument

Coordinates in a basis reduce to `V = ℝ`. Cover the closure of `U` by finitely many discs
`B(c, ρ)` whose concentric closed discs `D = closedBall c R`, `ρ < R`, lie in `Ω`. On each, with
`h = 1_D (f + I g)`, the particular solution `ξ₀ = ½ Re T h` solves `Δξ₀ = ∂ₛf + ∂ₜg` on `B(c, R)`
(`TauCeti.integral_laplacian_smul_half_re_cauchyTransform`), and the boundedness of the Cauchy and
Beurling transforms bounds `‖ξ₀‖_{W^{1,r}(D)}` by a multiple of `‖h‖_{Lʳ}`
(`TauCeti.eLpNorm_cauchyTransform_add_eLpNorm_wirtingerPartsCLM_beurlingLp_le`). The remainder
`ξ - ξ₀` is weakly harmonic on `B(c, R)`
(`TauCeti.weaklyHarmonicOn_sub_half_re_cauchyTransform`), so by Weyl's lemma it agrees almost
everywhere with a harmonic `v` (`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq`), and by the
mean value property the `Lʳ(B(c, ρ))` norms of `v` and its derivative are bounded by a multiple of
`‖ξ - ξ₀‖_{L¹(B(c, R))}`
(`TauCeti.exists_eLpNorm_and_eLpNorm_fderiv_le_integral_norm_of_harmonicOnNhd`), which Hölder's
inequality on `D` bounds by `‖ξ‖_{L^q(D)}` and `‖ξ₀‖_{Lʳ(D)}`. Summing over the discs gives the
estimate.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (the proof of Lemma B.4.6).
-/

public section

open Complex Function MeasureTheory Metric Set TopologicalSpace Laplacian
open scoped Distributions Topology ENNReal NNReal

namespace TauCeti

variable {r q : ℝ≥0∞} {Ω : Opens ℂ}

section Scalar

/-- The particular solution on one disc: for `f, g ∈ Lʳ(closedBall c R)` and
`h = 1_{closedBall c R} (f + I g)`, the `W^{1,r}` norm of `½ Re T h` on `closedBall c R` is
bounded by a multiple of `‖f‖_{Lʳ} + ‖g‖_{Lʳ}` on `closedBall c R`. -/
private theorem exists_eLpNormWkp_one_closedBall_half_re_cauchyTransform_le (hr : 1 < r)
    (hr_top : r ≠ ⊤) (c : ℂ) (R : ℝ≥0) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f g : ℂ → ℝ, MemLp f r (volume.restrict (closedBall c R)) →
      MemLp g r (volume.restrict (closedBall c R)) →
      eLpNormWkp r (closedBall c R) 1 (fun w ↦ (2 : ℝ)⁻¹ *
        (cauchyTransform ((closedBall c R).indicator fun z ↦ (f z : ℂ) + I * g z) w).re) ≤
      C * (eLpNorm f r (volume.restrict (closedBall c R)) +
        eLpNorm g r (volume.restrict (closedBall c R))) := by
  have : Fact (1 ≤ r) := ⟨hr.le⟩
  set K : Set ℂ := closedBall c R
  let A : ℂ →L[ℝ] ℝ := (2⁻¹ : ℝ) • reCLM
  set KB : ℝ≥0∞ := ((2 * (R + R) + ‖beurlingLp (F := ℂ) r hr hr_top‖₊ + 1 : ℝ≥0) : ℝ≥0∞)
  refine ⟨‖A‖ₑ * KB, by finiteness, fun f g hfK hgK ↦ ?_⟩
  have hfgK : MemLp (fun z ↦ (f z : ℂ) + I * g z) r (volume.restrict K) :=
    hfK.ofReal.add (hgK.ofReal.const_mul I)
  set h : ℂ → ℂ := K.indicator fun z ↦ (f z : ℂ) + I * g z
  have hhLp : MemLp h r volume :=
    (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).2 hfgK
  have hH : eLpNorm h r volume ≤ eLpNorm f r (volume.restrict K) +
      eLpNorm g r (volume.restrict K) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall.nullMeasurableSet]
    refine (eLpNorm_add_le hr.le).trans (le_of_eq ?_)
    congr 1
    · exact eLpNorm_congr_norm_ae hfK.ofReal.aestronglyMeasurable hfK.aestronglyMeasurable
        (.of_forall fun z ↦ by simp)
    · exact eLpNorm_congr_norm_ae (hgK.ofReal.const_mul I).aestronglyMeasurable
        hgK.aestronglyMeasurable (.of_forall fun z ↦ by simp)
  have hTw : eLpNormWkp r K 1 (cauchyTransform h) ≤ KB * eLpNorm h r volume := by
    refine (eLpNormWkp_succ_le (hasWeakFDerivOn_cauchyTransform_of_memLp hr hr_top hhLp
      support_indicator_subset (Opens.interior K))).trans ?_
    rw [eLpNormWkp_zero]
    exact eLpNorm_cauchyTransform_add_eLpNorm_wirtingerPartsCLM_beurlingLp_le hr hr_top hhLp
      support_indicator_subset R
  have hA : (fun w ↦ (2 : ℝ)⁻¹ * (cauchyTransform h w).re) = fun w ↦ A (cauchyTransform h w) := by
    ext w
    simp [A]
  rw [hA, mul_assoc]
  exact (eLpNormWkp_clm_comp_le A).trans (by gcongr; exact hTw.trans (by gcongr))

/-- The harmonic part on one disc: if `u - w` is weakly harmonic on `B(c, R)`, its `W^{1,r}` norm
on the smaller disc `B(c, ρ)` is bounded by a multiple of `‖u‖_{L^q} + ‖w‖_{Lʳ}` on
`closedBall c R`. -/
private theorem exists_eLpNormWkp_one_ball_sub_le_of_weaklyHarmonicOn (hr : 1 ≤ r) (hq : 1 ≤ q)
    (c : ℂ) {ρ R : ℝ} (hρR : ρ < R) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u w : ℂ → ℝ, WeaklyHarmonicOn volume ⟨ball c R, isOpen_ball⟩ (u - w) →
      IntegrableOn u (closedBall c R) → IntegrableOn w (closedBall c R) →
      eLpNormWkp r (ball c ρ) 1 (u - w) ≤ C * (eLpNorm u q (volume.restrict (closedBall c R)) +
        eLpNorm w r (volume.restrict (closedBall c R))) := by
  set K : Set ℂ := closedBall c R
  have hμK : volume K ≠ ∞ := measure_closedBall_lt_top.ne
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hμK
  obtain ⟨Ch, hCh⟩ := exists_eLpNorm_and_eLpNorm_fderiv_le_integral_norm_of_harmonicOnNhd
    (F := ℝ) (μ := volume) c hρR
  set M : ℝ≥0∞ := volume (ball c ρ) ^ r.toReal⁻¹
  set E₁ : ℝ≥0∞ := volume K ^ (1 / (1 : ℝ≥0∞).toReal - 1 / q.toReal)
  set E₂ : ℝ≥0∞ := volume K ^ (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal)
  have hM : M ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_ball_lt_top.ne
  have hE₁ : E₁ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg
    (ENNReal.one_div_toReal_sub_one_div_toReal_nonneg one_ne_zero hq) hμK
  have hE₂ : E₂ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg
    (ENNReal.one_div_toReal_sub_one_div_toReal_nonneg one_ne_zero hr) hμK
  refine ⟨2 * (M * Ch) * (E₁ + E₂), by finiteness, fun u w hu hui hwi ↦ ?_⟩
  have hint : IntegrableOn (u - w) (ball c R) := (hui.sub hwi).mono_set ball_subset_closedBall
  obtain ⟨v, hv, huv⟩ := hu.exists_harmonicOnNhd_ae_eq
  have hI : ∫ z in ball c R, ‖v z‖ = ∫ z in ball c R, ‖(u - w) z‖ :=
    integral_congr_ae (huv.mono fun _ h ↦ congrArg norm h.symm)
  obtain ⟨hv₀, hv₁⟩ := hCh hv (hint.congr huv) r
  rw [hI, ENNReal.ofReal_mul Ch.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ofReal_integral_norm_eq_lintegral_eNorm hint,
    ← eLpNorm_one_eq_lintegral_eNorm hint.aestronglyMeasurable] at hv₀ hv₁
  have hρB : Opens.interior (ball c ρ) ≤ ⟨ball c R, isOpen_ball⟩ := by
    rw [← SetLike.coe_subset_coe, Opens.coe_interior]
    exact interior_subset.trans (ball_subset_ball hρR.le)
  calc eLpNormWkp r (ball c ρ) 1 (u - w) = eLpNormWkp r (ball c ρ) 1 v :=
        eLpNormWkp_congr_ae (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρR.le) huv)
    _ ≤ eLpNorm v r (volume.restrict (ball c ρ)) +
        eLpNorm (fderiv ℝ v) r (volume.restrict (ball c ρ)) := by
        refine (eLpNormWkp_succ_le ((hv.contDiffOn.of_le (by norm_num)).hasWeakFDerivOn_fderiv.mono
          hρB)).trans ?_
        rw [eLpNormWkp_zero]
    _ ≤ 2 * (M * Ch) * eLpNorm (u - w) 1 (volume.restrict (ball c R)) :=
        (add_le_add hv₀ hv₁).trans_eq (by ring)
    _ ≤ 2 * (M * Ch) * (eLpNorm u q (volume.restrict K) * E₁ +
        eLpNorm w r (volume.restrict K) * E₂) := by
        gcongr
        refine (eLpNorm_mono_measure _ (Measure.restrict_mono ball_subset_closedBall le_rfl)).trans
          ((eLpNorm_sub_le (f := u) (g := w) le_rfl).trans ?_)
        gcongr
        · simpa only [Measure.restrict_apply_univ] using
            eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hui.aestronglyMeasurable
        · simpa only [Measure.restrict_apply_univ] using
            eLpNorm_le_eLpNorm_mul_rpow_measure_univ hr hwi.aestronglyMeasurable
    _ ≤ 2 * (M * Ch) * ((eLpNorm u q (volume.restrict K) + eLpNorm w r (volume.restrict K)) * E₁ +
        (eLpNorm u q (volume.restrict K) + eLpNorm w r (volume.restrict K)) * E₂) := by
        gcongr
        exacts [le_self_add, le_add_self]
    _ = _ := by ring

/-- The scalar estimate on one disc: the `W^{1,r}` norm of `ξ` on `B(c, ρ)` is bounded in terms of
the data on `Ω ⊇ closedBall c R`. -/
private theorem exists_eLpNormWkp_one_ball_le_real (hr : 1 < r) (hr_top : r ≠ ⊤) (hq : 1 ≤ q)
    (c : ℂ) {ρ : ℝ} {R : ℝ≥0} (hρR : ρ < R) (hRΩ : closedBall c R ⊆ Ω) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ ξ f g : ℂ → ℝ, LocallyIntegrableOn ξ Ω volume → MemLpLoc r Ω f →
      MemLpLoc r Ω g →
      (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) →
      eLpNormWkp r (ball c ρ) 1 ξ ≤ C * (eLpNorm f r (volume.restrict Ω) +
        eLpNorm g r (volume.restrict Ω) + eLpNorm ξ q (volume.restrict Ω)) := by
  set K : Set ℂ := closedBall c R
  have hKc : IsCompact K := isCompact_closedBall c R
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
  obtain ⟨Cp, hCp, hCpb⟩ :=
    exists_eLpNormWkp_one_closedBall_half_re_cauchyTransform_le hr hr_top c R
  obtain ⟨Ch, hCh, hChb⟩ :=
    exists_eLpNormWkp_one_ball_sub_le_of_weaklyHarmonicOn hr.le hq c hρR
  refine ⟨Cp + Ch * (1 + Cp), by finiteness, fun ξ f g hξ hf hg hdiv ↦ ?_⟩
  set X := eLpNorm f r (volume.restrict Ω) + eLpNorm g r (volume.restrict Ω) +
    eLpNorm ξ q (volume.restrict Ω)
  have hfK : MemLp f r (volume.restrict K) := memLpLoc_iff.1 hf K hRΩ hKc
  have hgK : MemLp g r (volume.restrict K) := memLpLoc_iff.1 hg K hRΩ hKc
  -- The particular solution `ξ₀ = ½ Re T (1_K (f + I g))`.
  set ξ₀ : ℂ → ℝ := fun w ↦ (2 : ℝ)⁻¹ *
    (cauchyTransform (K.indicator fun z ↦ (f z : ℂ) + I * g z) w).re
  have hξ₀K : MemLp ξ₀ r (volume.restrict K) := memLp_of_eLpNormWkp_ne_top (ne_top_of_le_ne_top
    (by finiteness [hfK.eLpNorm_ne_top, hgK.eLpNorm_ne_top]) (hCpb f g hfK hgK))
  have hξ₀w : eLpNormWkp r K 1 ξ₀ ≤ Cp * X := (hCpb f g hfK hgK).trans (by
    gcongr
    refine le_trans ?_ le_self_add
    gcongr)
  -- The harmonic remainder `ξ - ξ₀`.
  have hξK : IntegrableOn ξ K := hξ.integrableOn_compact_subset hRΩ hKc
  have hBΩ : (⟨ball c R, isOpen_ball⟩ : Opens ℂ) ≤ Ω := ball_subset_closedBall.trans hRΩ
  have hwh := weaklyHarmonicOn_sub_half_re_cauchyTransform hBΩ hξ hdiv
    ((integrable_indicator_iff measurableSet_closedBall).2
      ((hfK.ofReal.add (hgK.ofReal.const_mul I)).integrable hr.le))
    (ae_restrict_of_forall_mem isOpen_ball.measurableSet fun z hz ↦
      indicator_of_mem (ball_subset_closedBall hz) _)
  calc eLpNormWkp r (ball c ρ) 1 ξ = eLpNormWkp r (ball c ρ) 1 (ξ₀ + (ξ - ξ₀)) := by
        rw [add_sub_cancel]
    _ ≤ eLpNormWkp r K 1 ξ₀ +
        Ch * (eLpNorm ξ q (volume.restrict K) + eLpNorm ξ₀ r (volume.restrict K)) :=
        (eLpNormWkp_add_le hr.le).trans (add_le_add (eLpNormWkp_mono_set
          (ball_subset_closedBall.trans (closedBall_subset_closedBall hρR.le)))
          (hChb ξ ξ₀ hwh hξK (hξ₀K.integrable hr.le)))
    _ ≤ Cp * X + Ch * (X + Cp * X) := by
        gcongr
        · exact (eLpNorm_mono_measure _ (Measure.restrict_mono hRΩ le_rfl)).trans le_add_self
        · exact eLpNorm_le_eLpNormWkp.trans hξ₀w
    _ = (Cp + Ch * (1 + Cp)) * X := by ring

end Scalar

/-- The estimate on one disc for finite-dimensional coefficients, by reduction to coordinates. -/
private theorem exists_eLpNormWkp_one_ball_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hr : 1 < r) (hr_top : r ≠ ⊤) (hq : 1 ≤ q)
    (c : ℂ) {ρ : ℝ} {R : ℝ≥0} (hρR : ρ < R) (hRΩ : closedBall c R ⊆ Ω) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ ξ f g : ℂ → V, LocallyIntegrableOn ξ Ω volume → MemLpLoc r Ω f →
      MemLpLoc r Ω g →
      (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) →
      eLpNormWkp r (ball c ρ) 1 ξ ≤ C * (eLpNorm f r (volume.restrict Ω) +
        eLpNorm g r (volume.restrict Ω) + eLpNorm ξ q (volume.restrict Ω)) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  obtain ⟨C, hC, hCb⟩ := exists_eLpNormWkp_one_ball_le_real hr hr_top hq c hρR hRΩ
  let b := Module.finBasis ℝ V
  let L : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun i ↦ LinearMap.toContinuousLinearMap
    (b.coord i)
  let S : Fin (Module.finrank ℝ V) → ℝ →L[ℝ] V := fun i ↦
    ContinuousLinearMap.toSpanSingleton ℝ (b i)
  refine ⟨(∑ i, ‖S i‖ₑ * ‖L i‖ₑ) * C,
    ENNReal.mul_ne_top (ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top eNorm_ne_top eNorm_ne_top)
      hC, fun ξ f g hξ hf hg hdiv ↦ ?_⟩
  set X := eLpNorm f r (volume.restrict Ω) + eLpNorm g r (volume.restrict Ω) +
    eLpNorm ξ q (volume.restrict Ω)
  have hfloc := hf.locallyIntegrableOn hr.le Ω.isOpen.isLocallyClosed
  have hgloc := hg.locallyIntegrableOn hr.le Ω.isOpen.isLocallyClosed
  have hcoord (i) : eLpNormWkp r (ball c ρ) 1 (fun z ↦ L i (ξ z)) ≤ C * (‖L i‖ₑ * X) := by
    refine (hCb _ _ _ ((L i).locallyIntegrableOn_comp hξ) (hf.clm_comp (L i))
      (hg.clm_comp (L i)) fun φ ↦
        (L i).integral_laplacian_smul_comp_eq_neg_integral_fderiv_smul_add hξ hfloc hgloc
          (hdiv φ)).trans ?_
    gcongr
    calc _ ≤ ‖L i‖ₑ * eLpNorm f r (volume.restrict Ω) + ‖L i‖ₑ * eLpNorm g r (volume.restrict Ω) +
          ‖L i‖ₑ * eLpNorm ξ q (volume.restrict Ω) := by
          gcongr <;> exact (L i).eLpNorm_comp_le
      _ = ‖L i‖ₑ * X := by ring
  have hξsum : ξ = ∑ i, fun z ↦ S i (L i (ξ z)) := by
    ext z
    simp only [Finset.sum_apply, S, L, ContinuousLinearMap.toSpanSingleton_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    exact (b.sum_repr (ξ z)).symm
  calc eLpNormWkp r (ball c ρ) 1 ξ
      ≤ ∑ i, eLpNormWkp r (ball c ρ) 1 (fun z ↦ S i (L i (ξ z))) := by
        conv_lhs => rw [hξsum]
        exact eLpNormWkp_sum_le hr.le
    _ ≤ ∑ i, ‖S i‖ₑ * (C * (‖L i‖ₑ * X)) := by
        gcongr with i
        exact (eLpNormWkp_clm_comp_le (S i)).trans (by gcongr; exact hcoord i)
    _ = (∑ i, ‖S i‖ₑ * ‖L i‖ₑ) * C * X := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The covering step: on a set with compact closure in `Ω`, the `Lʳ` norms of `ξ` and of any weak
derivative of `ξ` on `Ω` are bounded in terms of the data. -/
private theorem exists_eLpNorm_add_eLpNorm_le_of_hasWeakFDerivOn {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hr : 1 < r) (hr_top : r ≠ ⊤)
    (hq : 1 ≤ q) {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ ξ f g : ℂ → V, LocallyIntegrableOn ξ Ω volume → MemLpLoc r Ω f →
      MemLpLoc r Ω g →
      (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) →
      ∀ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume Ω ξ D →
        eLpNorm ξ r (volume.restrict U) + eLpNorm D r (volume.restrict U) ≤
          C * (eLpNorm f r (volume.restrict Ω) + eLpNorm g r (volume.restrict Ω) +
            eLpNorm ξ q (volume.restrict Ω)) := by
  -- Radii `R x` with `closedBall x (R x) ⊆ Ω`, and a finite cover of `closure U` by the discs of
  -- half that radius.
  have hrad (x : ℂ) : ∃ R : ℝ≥0, x ∈ Ω → 0 < R ∧ closedBall x R ⊆ Ω := by
    by_cases hx : x ∈ Ω
    · obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
      refine ⟨(ε / 2).toNNReal, fun _ ↦ ⟨Real.toNNReal_pos.2 (by positivity), ?_⟩⟩
      exact (closedBall_subset_ball (by rw [Real.coe_toNNReal _ (by positivity)]; linarith)).trans
        hεΩ
    · exact ⟨0, fun h ↦ (hx h).elim⟩
  choose R hR using hrad
  obtain ⟨t, htU, hcover⟩ := hUc.elim_nhds_subcover (fun x ↦ ball x ((R x : ℝ) / 2))
    fun x hx ↦ ball_mem_nhds x (by have := (hR x (hUΩ hx)).1; positivity)
  have hball (x : ℂ) : ∃ C : ℝ≥0∞, x ∈ closure U → C ≠ ∞ ∧
      ∀ ξ f g : ℂ → V, LocallyIntegrableOn ξ Ω volume → MemLpLoc r Ω f → MemLpLoc r Ω g →
      (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) →
      eLpNormWkp r (ball x ((R x : ℝ) / 2)) 1 ξ ≤ C * (eLpNorm f r (volume.restrict Ω) +
        eLpNorm g r (volume.restrict Ω) + eLpNorm ξ q (volume.restrict Ω)) := by
    by_cases hx : x ∈ closure U
    · obtain ⟨C, hC, h⟩ := exists_eLpNormWkp_one_ball_le (V := V) hr hr_top hq x
        (half_lt_self (hR x (hUΩ hx)).1) (hR x (hUΩ hx)).2
      exact ⟨C, fun _ ↦ ⟨hC, h⟩⟩
    · exact ⟨0, fun h ↦ (hx h).elim⟩
  choose C hC using hball
  have hCt : ∑ x ∈ t, C x ≠ ∞ := ENNReal.sum_ne_top.2 fun x hx ↦ (hC x (htU x hx)).1
  refine ⟨(∑ x ∈ t, C x).toNNReal, fun ξ f g hξ hf hg hdiv D hD ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hCt]
  have hU : U ⊆ ⋃ x ∈ t, ball x ((R x : ℝ) / 2) := subset_closure.trans hcover
  calc eLpNorm ξ r (volume.restrict U) + eLpNorm D r (volume.restrict U)
      ≤ ∑ x ∈ t, eLpNorm ξ r (volume.restrict (ball x ((R x : ℝ) / 2))) +
          ∑ x ∈ t, eLpNorm D r (volume.restrict (ball x ((R x : ℝ) / 2))) :=
        add_le_add
          ((eLpNorm_mono_measure _ (Measure.restrict_mono hU le_rfl)).trans
            (eLpNorm_restrict_biUnion_finset_le _ hr.le t _))
          ((eLpNorm_mono_measure _ (Measure.restrict_mono hU le_rfl)).trans
            (eLpNorm_restrict_biUnion_finset_le _ hr.le t _))
    _ = ∑ x ∈ t, eLpNormWkp r (ball x ((R x : ℝ) / 2)) 1 ξ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        have hxΩ : ball x ((R x : ℝ) / 2) ⊆ Ω :=
          (ball_subset_closedBall.trans (closedBall_subset_closedBall
            (half_le_self (R x).coe_nonneg))).trans (hR x (hUΩ (htU x hx))).2
        have h := eLpNormWkp_succ_eq_of_hasWeakFDerivOn (p := r) (k := 0)
          (Ω := ⟨ball x ((R x : ℝ) / 2), isOpen_ball⟩) (hD.mono hxΩ)
        rw [eLpNormWkp_zero] at h
        exact h.symm
    _ ≤ ∑ x ∈ t, C x * (eLpNorm f r (volume.restrict Ω) + eLpNorm g r (volume.restrict Ω) +
          eLpNorm ξ q (volume.restrict Ω)) :=
        Finset.sum_le_sum fun x hx ↦ (hC x (htU x hx)).2 ξ f g hξ hf hg hdiv
    _ = _ := (Finset.sum_mul ..).symm

/-- **The interior estimate for the divergence-form Laplace equation.** Let `V` be
finite-dimensional, `1 < r < ∞`, `1 ≤ q ≤ ∞`, and let `U` have compact closure in the open set
`Ω`. There is a constant `C` such that whenever `ξ` is locally integrable on `Ω`, `f` and `g` are
locally `Lʳ` on `Ω`, and `Δξ = ∂ₛf + ∂ₜg` weakly on `Ω`, that is
`∫ Δφ • ξ = -∫ (∂ₛφ • f + ∂ₜφ • g)` for every real test function `φ` on `Ω`,
then `‖ξ‖_{W^{1,r}(U)} ≤ C (‖f‖_{Lʳ(Ω)} + ‖g‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})`. -/
theorem exists_eLpNormWkp_one_le_of_integral_laplacian_smul_eq {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hr : 1 < r) (hr_top : r ≠ ⊤)
    (hq : 1 ≤ q) {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ ξ f g : ℂ → V, LocallyIntegrableOn ξ Ω volume → MemLpLoc r Ω f →
      MemLpLoc r Ω g →
      (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) →
      eLpNormWkp r U 1 ξ ≤ C * (eLpNorm f r (volume.restrict Ω) +
        eLpNorm g r (volume.restrict Ω) + eLpNorm ξ q (volume.restrict Ω)) := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_add_eLpNorm_le_of_hasWeakFDerivOn (V := V) hr hr_top hq hUc hUΩ
  refine ⟨C, fun ξ f g hξ hf hg hdiv ↦ ?_⟩
  obtain ⟨D, hD, -⟩ := (memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr hr_top hξ hf hg
    hdiv).exists_weakFDeriv_of_isOpen
  refine (eLpNormWkp_succ_le (hD.mono ?_)).trans ?_
  · rw [← SetLike.coe_subset_coe, Opens.coe_interior]
    exact interior_subset.trans (subset_closure.trans hUΩ)
  · rw [eLpNormWkp_zero]
    exact hC ξ f g hξ hf hg hdiv D hD

/-- **The derivative bound for the divergence-form Laplace equation.** Under the hypotheses of
`TauCeti.exists_eLpNormWkp_one_le_of_integral_laplacian_smul_eq`, the `Lʳ(U)` norm of every weak
derivative `D` of `ξ` on `Ω` is at most `C (‖f‖_{Lʳ(Ω)} + ‖g‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})`. Unlike the
`W^{1,r}(U)` norm, which only sees the derivative on the interior of `U`, this bounds the
derivative on all of `U`. -/
theorem exists_eLpNorm_le_of_integral_laplacian_smul_eq_of_hasWeakFDerivOn {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hr : 1 < r) (hr_top : r ≠ ⊤)
    (hq : 1 ≤ q) {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ ξ f g : ℂ → V, LocallyIntegrableOn ξ Ω volume → MemLpLoc r Ω f →
      MemLpLoc r Ω g →
      (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) →
      ∀ D : ℂ → ℂ →L[ℝ] V, HasWeakFDerivOn volume Ω ξ D →
        eLpNorm D r (volume.restrict U) ≤ C * (eLpNorm f r (volume.restrict Ω) +
          eLpNorm g r (volume.restrict Ω) + eLpNorm ξ q (volume.restrict Ω)) := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_add_eLpNorm_le_of_hasWeakFDerivOn (V := V) hr hr_top hq hUc hUΩ
  exact ⟨C, fun ξ f g hξ hf hg hdiv D hD ↦ le_add_self.trans (hC ξ f g hξ hf hg hdiv D hD)⟩

/-- **Check: the `L^q` term is needed.** On no set `U` of positive measure does an estimate
`‖ξ‖_{W^{1,r}(U)} ≤ C (‖f‖_{Lʳ(Ω)} + ‖g‖_{Lʳ(Ω)})` hold for solutions of `Δξ = ∂ₛf + ∂ₜg` on `Ω`:
the harmonic function `ξ = 1` solves the equation with `f = g = 0` and has positive norm. -/
theorem not_exists_eLpNormWkp_one_le_eLpNorm_add_eLpNorm_of_integral_laplacian_smul_eq
    (hr : r ≠ 0) {U : Set ℂ} (hU : volume U ≠ 0) :
    ¬ ∃ C : ℝ≥0, ∀ ξ f g : ℂ → ℝ, LocallyIntegrableOn ξ Ω volume → MemLpLoc r Ω f →
      MemLpLoc r Ω g →
      (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) →
      eLpNormWkp r U 1 ξ ≤ C * (eLpNorm f r (volume.restrict Ω) +
        eLpNorm g r (volume.restrict Ω)) := by
  rintro ⟨C, hC⟩
  have hdiv (φ : 𝓓(Ω, ℝ)) : ∫ z, Δ (φ : ℂ → ℝ) z • (fun _ ↦ (1 : ℝ)) z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (0 : ℂ → ℝ) z + fderiv ℝ (φ : ℂ → ℝ) z I •
        (0 : ℂ → ℝ) z) := by
    simpa using integral_laplacian_eq_zero_of_hasCompactSupport (μ := volume)
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  have h := hC (fun _ ↦ 1) 0 0 (locallyIntegrableOn_const 1) memLpLoc_zero memLpLoc_zero hdiv
  simp only [eLpNorm_zero, add_zero, mul_zero, nonpos_iff_eq_zero] at h
  have : (ae (volume.restrict U)).NeBot := ae_neBot.2 (by simpa using hU)
  obtain ⟨_, hz⟩ := (ae_eq_zero_of_eLpNormWkp_eq_zero hr h).exists
  exact one_ne_zero hz

end TauCeti
