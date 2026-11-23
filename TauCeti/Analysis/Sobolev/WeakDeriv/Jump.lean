/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Sobolev.WeakDeriv.Haar
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Topology.Algebra.Support

/-!
# Non-existence of weak derivatives across a hyperplane jump

The indicator `{x | 0 < ℓ x}.indicator (fun _ => (1 : ℝ))` of an open half-space defined by a
nonzero continuous linear functional `ℓ : E →L[ℝ] ℝ` on a finite-dimensional real normed space `E`
admits no weak derivative on any open set `Ω` meeting `ker ℓ`
(`TauCeti.not_hasWeakFDerivOn_indicator_pos`).

By linear splitting along `ℓ`, the problem reduces to the model product `ℝ × ℝ^d`, where any weak
derivative vanishes almost everywhere off the hyperplane `{q | q.1 = 0}` and hence almost
everywhere; testing against a product of bump functions centered on `{q | q.1 = 0}` then yields a
nonzero boundary integral via `ContDiffBump.integral_Ioi_deriv`.

## Main declarations

* `TauCeti.not_hasWeakFDerivOn_indicator_pos`: the indicator of `{x | 0 < ℓ x}` (`ℓ ≠ 0`) has no
  weak Fréchet derivative on any open set meeting `ker ℓ`.
-/

public noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Distributions Topology

namespace TauCeti

section HalfSpaceJump

private def prodBumpTestFunction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {Ω : Opens (ℝ × H)} {x₀ : ℝ} {y₀ : H}
    (a : ContDiffBump x₀) (b : ContDiffBump y₀)
    (hΩ : (Metric.closedBall x₀ a.rOut ×ˢ Metric.closedBall y₀ b.rOut : Set (ℝ × H)) ⊆ Ω) :
    𝓓(Ω, ℝ) :=
  let f : ℝ × H → ℝ := ((a : ℝ → ℝ) ∘ Prod.fst) * ((b : H → ℝ) ∘ Prod.snd)
  have hfs : tsupport f ⊆ Metric.closedBall x₀ a.rOut ×ˢ Metric.closedBall y₀ b.rOut := by
    simpa only [f, Pi.mul_def, Function.comp_def, smul_eq_mul, mul_comm,
      a.tsupport_eq, b.tsupport_eq] using
      tsupport_snd_smul_fst_subset (b : H → ℝ) (a : ℝ → ℝ)
  ⟨f, (a.contDiff.comp (ContinuousLinearMap.fst ℝ ℝ H).contDiff).mul
      (b.contDiff.comp (ContinuousLinearMap.snd ℝ ℝ H).contDiff),
    ((isCompact_closedBall x₀ a.rOut).prod
      (isCompact_closedBall y₀ b.rOut)).of_isClosed_subset (isClosed_tsupport f) hfs,
    hfs.trans hΩ⟩

private theorem prodBumpTestFunction_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {Ω : Opens (ℝ × H)} {x₀ : ℝ} {y₀ : H}
    (a : ContDiffBump x₀) (b : ContDiffBump y₀)
    (hΩ : (Metric.closedBall x₀ a.rOut ×ˢ Metric.closedBall y₀ b.rOut : Set (ℝ × H)) ⊆ Ω)
    (q : ℝ × H) :
    (prodBumpTestFunction a b hΩ : ℝ × H → ℝ) q = a q.1 * b q.2 :=
  rfl

private theorem lineDeriv_prodBumpTestFunction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {Ω : Opens (ℝ × H)} {x₀ : ℝ} {y₀ : H}
    (a : ContDiffBump x₀) (b : ContDiffBump y₀)
    (hΩ : (Metric.closedBall x₀ a.rOut ×ˢ Metric.closedBall y₀ b.rOut : Set (ℝ × H)) ⊆ Ω)
    (q : ℝ × H) :
    lineDeriv ℝ (prodBumpTestFunction a b hΩ : ℝ × H → ℝ) q ((1 : ℝ), (0 : H)) =
      deriv (a : ℝ → ℝ) q.1 * b q.2 := by
  have hda : HasDerivAt (a : ℝ → ℝ) (deriv (a : ℝ → ℝ) q.1) (0 + q.1) := by
    simpa only [zero_add] using ((a.contDiff (n := 1)).differentiable one_ne_zero q.1).hasDerivAt
  refine HasLineDerivAt.lineDeriv
    (?_ : HasDerivAt
      (fun t : ℝ => (prodBumpTestFunction a b hΩ : ℝ × H → ℝ) (q + t • ((1 : ℝ), (0 : H))))
      (deriv (a : ℝ → ℝ) q.1 * b q.2) 0)
  have h := (hda.comp_add_const 0 q.1).mul_const (b q.2)
  simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero, Prod.fst_add, Prod.snd_add,
    add_zero, add_comm q.1, prodBumpTestFunction_apply] using h

private theorem ae_zero_of_hasWeakFDerivOn_indicator_fst_pos {d : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin d))}
    {D : (ℝ × EuclideanSpace ℝ (Fin d)) → (ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ}
    (hD : HasWeakFDerivOn volume Ω ({q | 0 < q.1}.indicator fun _ => (1 : ℝ)) D) :
    D =ᵐ[volume.restrict Ω] 0 := by
  let H := EuclideanSpace ℝ (Fin d)
  have : (volume : Measure (ℝ × H)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  set u : ℝ × H → ℝ := {q | 0 < q.1}.indicator fun _ => (1 : ℝ) with hu
  set Ωp : Opens (ℝ × H) :=
    Ω ⊓ ⟨{q | 0 < q.1}, isOpen_lt continuous_const continuous_fst⟩
  set Ωn : Opens (ℝ × H) :=
    Ω ⊓ ⟨{q | q.1 < 0}, isOpen_lt continuous_fst continuous_const⟩
  have hconst : HasWeakFDerivOn volume Ωp (fun _ => (1 : ℝ)) 0 :=
    hasWeakFDerivOn_iff.2 fun v => by
      simpa using (hasWeakLineDerivOn_const (1 : ℝ) :
        HasWeakLineDerivOn volume Ωp (fun _ => (1 : ℝ)) (fun _ => 0) v)
  have hp : HasWeakFDerivOn volume Ωp u 0 := hconst.congr_ae <|
    (ae_restrict_iff' Ωp.isOpen.measurableSet).2 <| Eventually.of_forall fun q hq => by
      have hq' : q ∈ {q : ℝ × H | 0 < q.1} := hq.2
      simp [hu, hq']
  have hn : HasWeakFDerivOn volume Ωn u 0 := (hasWeakFDerivOn_zero (μ := volume)).congr_ae <|
    (ae_restrict_iff' Ωn.isOpen.measurableSet).2 <| Eventually.of_forall fun q hq => by
      have hq' : ¬ 0 < q.1 := not_lt.2 (le_of_lt hq.2)
      simp [hu, hq']
  have hDp := (ae_restrict_iff' Ωp.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hp)
  have hDn := (ae_restrict_iff' Ωn.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hn)
  have hhyper : volume ({q : ℝ × H | q.1 = 0}) = 0 := by
    have hset :
        ({q : ℝ × H | q.1 = 0} : Set (ℝ × H)) = ({0} : Set ℝ) ×ˢ (univ : Set H) := by
      ext q; simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
  filter_upwards [hDp, hDn, measure_eq_zero_iff_ae_notMem.1 hhyper] with q hqp hqn hq0 hqΩ
  rcases lt_or_gt_of_ne hq0 with h | h
  · exact hqn ⟨hqΩ, h⟩
  · exact hqp ⟨hqΩ, h⟩

private theorem not_hasWeakFDerivOn_indicator_fst_pos {d : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin d))} {p₀ : ℝ × EuclideanSpace ℝ (Fin d)}
    (hp₀ : p₀ ∈ Ω) (hp₀1 : p₀.1 = 0)
    (D : (ℝ × EuclideanSpace ℝ (Fin d)) →
      (ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω ({q | 0 < q.1}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  let H := EuclideanSpace ℝ (Fin d)
  set u : ℝ × H → ℝ := {q | 0 < q.1}.indicator fun _ => (1 : ℝ) with hu
  have hD0 : D =ᵐ[volume.restrict Ω] 0 :=
    ae_zero_of_hasWeakFDerivOn_indicator_fst_pos hD
  have hline := (hD.congr_ae_deriv hD0).hasWeakLineDerivOn ((1 : ℝ), (0 : H))
  rcases p₀ with ⟨p₀1, p₀2⟩
  dsimp only at hp₀1
  subst hp₀1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen (0, p₀2) hp₀
  let a : ContDiffBump (0 : ℝ) := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  let b : ContDiffBump p₀2 := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  have hΩsupp : (Metric.closedBall (0 : ℝ) a.rOut ×ˢ Metric.closedBall p₀2 b.rOut :
      Set (ℝ × H)) ⊆ Ω := by
    intro q hq
    have hq1 : dist q.1 0 ≤ ε / 3 := by simpa [a] using hq.1
    have hq2 : dist q.2 p₀2 ≤ ε / 3 := by simpa [b] using hq.2
    have hqball : q ∈ Metric.closedBall ((0 : ℝ), p₀2) (ε / 3) := by
      rw [Metric.mem_closedBall, Prod.dist_eq]
      exact max_le hq1 hq2
    exact hball (Metric.closedBall_subset_ball (by linarith) hqball)
  let φ : 𝓓(Ω, ℝ) := prodBumpTestFunction a b hΩsupp
  have hkey := hline.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [Pi.zero_apply, zero_apply, smul_zero, integral_zero, neg_zero] at hkey
  have hint : (∫ q : ℝ × H, lineDeriv ℝ (φ : ℝ × H → ℝ) q (1, 0) • u q) =
      ∫ q : ℝ × H, (Ioi (0 : ℝ)).indicator (deriv (a : ℝ → ℝ)) q.1 * b q.2 := by
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    dsimp only [φ]
    rw [lineDeriv_prodBumpTestFunction (H := H) a b hΩsupp q]
    simp only [smul_eq_mul, hu]
    by_cases hq : 0 < q.1 <;> simp [Set.indicator, hq]
  have hprod := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure H))
    ((Ioi (0 : ℝ)).indicator (deriv (a : ℝ → ℝ))) (fun y => b y)
  rw [hint, Measure.volume_eq_prod, hprod, integral_indicator measurableSet_Ioi,
    a.integral_Ioi_deriv] at hkey
  have hb := b.integral_pos (μ := volume)
  linarith

/-- The indicator of an open half-space `{x | 0 < ℓ x}` (for a nonzero continuous linear
functional `ℓ`) admits no weak derivative on any open set meeting `ker ℓ`. -/
theorem not_hasWeakFDerivOn_indicator_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {Ω : Opens E} {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) (hx₀' : ℓ x₀ = 0) (D : E → E →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  obtain ⟨w, hw⟩ : ∃ w : E, ℓ w ≠ 0 := by
    by_contra! h
    exact hℓ (ContinuousLinearMap.ext h)
  let v : E := (ℓ w)⁻¹ • w
  have hℓv : ℓ v = 1 := by simp [v, inv_mul_cancel₀ hw]
  have hrinv : Function.RightInverse ((ContinuousLinearMap.id ℝ ℝ).smulRight v) ℓ :=
    fun c => by simp [hℓv]
  let e₁ := ContinuousLinearEquiv.equivOfRightInverse ℓ
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v) hrinv
  let H := EuclideanSpace ℝ (Fin (Module.finrank ℝ ℓ.ker))
  let e : (ℝ × H) ≃L[ℝ] E :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (toEuclidean (E := ℓ.ker)).symm).trans e₁.symm
  have : (volume : Measure (ℝ × H)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let Ω' : Opens (ℝ × H) := ⟨e ⁻¹' Ω, Ω.isOpen.preimage e.continuous⟩
  have hpull := hD.comp_continuousLinearEquiv_of_isAddHaarMeasure (μ := volume) (U := Ω') e
    (mapsTo_preimage e Ω)
  have hefst (q : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ ℓ.ker))) : ℓ (e q) = q.1 := by
    rw [← ContinuousLinearEquiv.fst_equivOfRightInverse ℓ _ hrinv (e q)]
    simp [e, e₁, hℓv]
  have hsymmfst : (e.symm x₀).1 = ℓ x₀ := by
    simp [e, e₁]
  have hcomp : ({x : E | 0 < ℓ x}.indicator (fun _ => (1 : ℝ))) ∘ e =
      {q | 0 < q.1}.indicator fun _ => (1 : ℝ) := by
    funext q
    simp only [Function.comp_apply, Set.indicator_apply, Set.mem_ofPred_eq, hefst q]
  rw [hcomp] at hpull
  exact not_hasWeakFDerivOn_indicator_fst_pos (Ω := Ω') (p₀ := e.symm x₀)
    (by simpa [Ω'] using hx₀) (hsymmfst.trans hx₀') _ hpull

end HalfSpaceJump

end TauCeti
