/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Canonical Schrödinger potentials and softmin regularity

At positive temperature `ε ≠ 0` and for a bounded measurable cost `c ≤ B`, entropic duality
(`TauCeti.exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost`) furnishes bounded
measurable potentials `(φ₀, ψ₀)` whose Gibbs density couples two probability measures `μ` and `ν`,
so that `(φ₀, ψ₀)` satisfy the Schrödinger marginal equations `μ`- and `ν`-almost everywhere.

Applying two Sinkhorn softmin half-steps and shifting by the log-partition constant
`-ε * log ∫ exp (ψ₁ / ε) dν` upgrades an almost-everywhere optimal pair to *canonical Schrödinger
potentials* `(φ, ψ)` (Feydy–Séjourné–Vialard–Amari–Trouvé–Peyré, Proposition 1; Nutz, §2):

1. **Everywhere marginal normalisation and uniform `L^∞` bounds
   (`TauCeti.exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le`).**
   The canonical potentials satisfy both marginal equations
   `∫ y, exp ((φ x + ψ y - c(x, y)) / ε) dν(y) = 1` and
   `∫ x, exp ((φ x + ψ y - c(x, y)) / ε) dμ(x) = 1` *pointwise everywhere* on `X` and `Y` (including
   off the supports of `μ` and `ν`), together with the temperature-independent bounds `0 ≤ φ ≤ B`
   and `|ψ| ≤ B`, while attaining the regularised transport cost in both the Kantorovich and
   entropic dual objectives.
2. **Slicewise Lipschitz regularity, uniformly in the temperature
   (`TauCeti.exists_lipschitzWith_left_entropicDualValue_eq_toReal_entropicTransportCost`,
   `TauCeti.exists_lipschitzWith_entropicDualValue_eq_toReal_entropicTransportCost`).**
   Because the entropic softmin operator preserves slice Lipschitz constants independently of `ε`,
   `φ` inherits any Lipschitz constant `K₁` of `x ↦ (c (x, y)).toReal`, and `ψ` inherits any
   Lipschitz constant `K₂` of `y ↦ (c (x, y)).toReal`.

## Main statements

* `TauCeti.exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le`: existence of canonical
  Schrödinger potentials bounded by `B` (`0 ≤ φ ≤ B` and `|ψ| ≤ B`) and normalised pointwise
  everywhere on `X` and `Y`.
* `TauCeti.exists_lipschitzWith_left_entropicDualValue_eq_toReal_entropicTransportCost`: canonical
  Schrödinger potentials inherit a Lipschitz constant in the source variable without requiring a
  metric on the target space.
* `TauCeti.exists_lipschitzWith_entropicDualValue_eq_toReal_entropicTransportCost`: canonical
  Schrödinger potentials inherit the slice Lipschitz constants of the cost in both variables,
  uniformly in `ε ≠ 0`.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*,
  AISTATS 2019, Proposition 1.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  §2, for uniform bounds and equicontinuity of Schrödinger potentials.
-/

public section

noncomputable section

open InformationTheory MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

section Softmin

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure Y} {f : X × Y → ℝ} {ε : ℝ≥0} {u u' : Y → ℝ}

/-- The entropic softmin transform `-ε * log ∫ exp ((u y - f(x, y)) / ε) dν(y)` of a potential `u`
against a measure `ν`. -/
private def entropicSoftmin (f : X × Y → ℝ) (ε : ℝ≥0) (ν : Measure Y) (u : Y → ℝ) (x : X) : ℝ :=
  -(ε : ℝ) * Real.log (∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν)

private theorem integrable_exp_sub_div [IsFiniteMeasure ν] (hf : Measurable f)
    {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u) (huC : ∀ y, |u y| ≤ Cu) (x : X) :
    Integrable (fun y ↦ Real.exp ((u y - f (x, y)) / ε)) ν := by
  refine Integrable.of_bound (by fun_prop) (Real.exp ((Cu + Bf) / ε)) (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  refine div_le_div_of_nonneg_right ?_ ε.coe_nonneg
  linarith [(abs_le.1 (huC y)).2, (abs_le.1 (hfB (x, y))).1]

private theorem measurable_entropicSoftmin [SFinite ν] (hf : Measurable f) (hu : Measurable u) :
    Measurable (entropicSoftmin f ε ν u) := by
  have h : StronglyMeasurable fun z : X × Y ↦ Real.exp ((u z.2 - f z) / ε) :=
    (by fun_prop : Measurable fun z : X × Y ↦ Real.exp ((u z.2 - f z) / ε)).stronglyMeasurable
  exact h.integral_prod_right'.measurable.log.const_mul _

omit [MeasurableSpace X] in
private theorem entropicSoftmin_congr_ae (hu : u =ᵐ[ν] u') :
    entropicSoftmin f ε ν u = entropicSoftmin f ε ν u' := by
  funext x
  unfold entropicSoftmin
  congr 2
  exact integral_congr_ae (hu.mono fun y hy ↦ by dsimp only; rw [hy])

private theorem entropicSoftmin_add_const [IsFiniteMeasure ν] [NeZero ν] (hf : Measurable f)
    {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u) (huC : ∀ y, |u y| ≤ Cu)
    (hε : ε ≠ 0) (a : ℝ) (x : X) :
    entropicSoftmin f ε ν (fun y ↦ u y + a) x = entropicSoftmin f ε ν u x - a := by
  have : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  have hint := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x
  have hZ : 0 < ∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν := integral_exp_pos hint
  have hsplit : (fun y ↦ Real.exp ((u y + a - f (x, y)) / ε)) =
      fun y ↦ Real.exp (a / ε) * Real.exp ((u y - f (x, y)) / ε) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [entropicSoftmin, entropicSoftmin, hsplit, integral_const_mul,
    Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  field_simp
  ring

private theorem abs_entropicSoftmin_le [IsProbabilityMeasure ν] (hf : Measurable f)
    {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u) (huC : ∀ y, |u y| ≤ Cu)
    (hε : ε ≠ 0) (x : X) :
    |entropicSoftmin f ε ν u x| ≤ Cu + Bf := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hint := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x
  have hlo : Real.exp (-(Cu + Bf) / ε) ≤ ∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν := by
    simpa using integral_mono (integrable_const _) hint fun y ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right
        (by linarith [(abs_le.1 (huC y)).1, (abs_le.1 (hfB (x, y))).2]) ε.coe_nonneg
  have hhi : ∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν ≤ Real.exp ((Cu + Bf) / ε) := by
    simpa using integral_mono hint (integrable_const _) fun y ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right
        (by linarith [(abs_le.1 (huC y)).2, (abs_le.1 (hfB (x, y))).1]) ε.coe_nonneg
  have h₁ := Real.log_le_log (Real.exp_pos _) hlo
  have h₂ := Real.log_le_log ((Real.exp_pos _).trans_le hlo) hhi
  rw [Real.log_exp, div_le_iff₀ hε0] at h₁
  rw [Real.log_exp, le_div_iff₀ hε0] at h₂
  rw [entropicSoftmin, abs_le]
  constructor <;> linarith

private theorem integral_exp_entropicSoftmin [IsFiniteMeasure ν] [NeZero ν] (hf : Measurable f)
    {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u) (huC : ∀ y, |u y| ≤ Cu)
    (hε : ε ≠ 0) (x : X) :
    ∫ y, Real.exp ((entropicSoftmin f ε ν u x + u y - f (x, y)) / ε) ∂ν = 1 := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hint := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x
  have hZ : 0 < ∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν := integral_exp_pos hint
  have hsplit : (fun y ↦ Real.exp ((entropicSoftmin f ε ν u x + u y - f (x, y)) / ε)) =
      fun y ↦ Real.exp (entropicSoftmin f ε ν u x / ε) * Real.exp ((u y - f (x, y)) / ε) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, integral_const_mul, entropicSoftmin, neg_mul, neg_div,
    mul_div_cancel_left₀ _ hε0.ne', Real.exp_neg, Real.exp_log hZ, inv_mul_cancel₀ hZ.ne']

private theorem lipschitzWith_entropicSoftmin [PseudoEMetricSpace X] [IsFiniteMeasure ν] [NeZero ν]
    (hf : Measurable f) {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u)
    (huC : ∀ y, |u y| ≤ Cu) (hε : ε ≠ 0) {K : ℝ≥0}
    (hL : ∀ y, LipschitzWith K fun x ↦ f (x, y)) :
    LipschitzWith K (entropicSoftmin f ε ν u) := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  intro x x'
  rcases eq_or_ne K 0 with rfl | hK
  · have hfx : ∀ y, f (x, y) = f (x', y) := fun y ↦ by
      have := (hL y) x x'
      rwa [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at this
    have heq : entropicSoftmin f ε ν u x = entropicSoftmin f ε ν u x' := by
      simp only [entropicSoftmin, hfx]
    simp [heq]
  rcases eq_or_ne (edist x x') ∞ with htop | hfin
  · rw [htop, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hK)]
    exact le_top
  set d := (edist x x').toReal
  have hKd_ne_top : (K : ℝ≥0∞) * edist x x' ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hKd_toReal : ((K : ℝ≥0∞) * edist x x').toReal = K * d := by
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hf_diff : ∀ y, |f (x, y) - f (x', y)| ≤ K * d := fun y ↦ by
    have hy := (hL y) x x'
    rw [edist_dist, Real.dist_eq] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hKd_ne_top).1 hy |>.trans_eq hKd_toReal
  have hdir (x₁ x₂ : X) (hd : ∀ y, |f (x₁, y) - f (x₂, y)| ≤ K * d) :
      entropicSoftmin f ε ν u x₁ - entropicSoftmin f ε ν u x₂ ≤ K * d := by
    have hi₁ := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x₁
    have hi₂ := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x₂
    have hZ₁ : 0 < ∫ y, Real.exp ((u y - f (x₁, y)) / ε) ∂ν := integral_exp_pos hi₁
    have hZ₂ : 0 < ∫ y, Real.exp ((u y - f (x₂, y)) / ε) ∂ν := integral_exp_pos hi₂
    have hle : ∫ y, Real.exp ((u y - f (x₂, y)) / ε) ∂ν ≤
        Real.exp (K * d / ε) * ∫ y, Real.exp ((u y - f (x₁, y)) / ε) ∂ν := by
      rw [← integral_const_mul]
      refine integral_mono hi₂ (hi₁.const_mul _) fun y ↦ ?_
      rw [← Real.exp_add, Real.exp_le_exp]
      have hy := (abs_le.1 (hd y)).2
      calc (u y - f (x₂, y)) / ε
          = (f (x₁, y) - f (x₂, y)) / ε + (u y - f (x₁, y)) / ε := by ring
        _ ≤ K * d / ε + (u y - f (x₁, y)) / ε := by
            gcongr
    have hlog := Real.log_le_log hZ₂ hle
    rw [Real.log_mul (Real.exp_pos _).ne' hZ₁.ne', Real.log_exp] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hε0.le
    rw [mul_add, mul_div_cancel₀ _ hε0.ne'] at hmul
    unfold entropicSoftmin
    linarith
  have habs : |entropicSoftmin f ε ν u x - entropicSoftmin f ε ν u x'| ≤ K * d :=
    abs_sub_le_iff.2 ⟨hdir x x' hf_diff,
      hdir x' x fun y ↦ by rw [abs_sub_comm]; exact hf_diff y⟩
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_toReal hKd_ne_top, hKd_toReal]
  exact ENNReal.ofReal_le_ofReal habs

end Softmin

private theorem abs_toReal_le_of_le {α : Type*} {c : α → ℝ≥0∞} {B : ℝ≥0} (hcB : ∀ z, c z ≤ B)
    (z : α) : |(c z).toReal| ≤ B := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top (hcB z)).trans_eq (ENNReal.coe_toReal B)

section CanonicalPotentials

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε B : ℝ≥0} {μ : Measure X} {ν : Measure Y}

/-- If a Gibbs density couples two probability measures, the source potential agrees `μ`-almost
everywhere with the entropic softmin of the target potential. -/
private theorem ae_eq_entropicSoftmin_of_isCoupling [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    {φ : X → ℝ} {ψ : Y → ℝ} {Cφ Cψ : ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (_ : ∀ x, |φ x| ≤ Cφ) (hψC : ∀ y, |ψ y| ≤ Cψ)
    (hπ : IsCoupling ((μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε))) μ ν) :
    φ =ᵐ[μ] entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hfB := abs_toReal_le_of_le hcB
  set g : X × Y → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε))
  have hg : Measurable g := by fun_prop
  have hrow : (fun x ↦ ∫⁻ y, g (x, y) ∂ν) =ᵐ[μ] fun _ ↦ (1 : ℝ≥0∞) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hg.lintegral_prod_right' measurable_const
      fun s hs _ ↦ ?_
    calc ∫⁻ x in s, (∫⁻ y, g (x, y) ∂ν) ∂μ
        = ((μ.prod ν).withDensity g) (s ×ˢ univ) := by
          rw [withDensity_apply _ (hs.prod MeasurableSet.univ),
            setLIntegral_prod _ hg.aemeasurable]
          simp only [Measure.restrict_univ]
      _ = μ s := hπ.measure_prod_univ hs
      _ = ∫⁻ _ in s, 1 ∂μ := by simp
  filter_upwards [hrow] with x hx
  have hint := integrable_exp_sub_div (ν := ν) (ε := ε) hc.ennreal_toReal hfB hψ hψC x
  have hZ : 0 < ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν := integral_exp_pos hint
  have hsplit : (fun y ↦ Real.exp ((φ x + ψ y - (c (x, y)).toReal) / ε)) =
      fun y ↦ Real.exp (φ x / ε) * Real.exp ((ψ y - (c (x, y)).toReal) / ε) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  have hl : ∫⁻ y, g (x, y) ∂ν =
      ENNReal.ofReal (Real.exp (φ x / ε) * ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hsplit ▸ hint.const_mul _)
      (ae_of_all _ fun _ ↦ (Real.exp_pos _).le), hsplit, integral_const_mul]
  rw [hl] at hx
  have hmul_pos : 0 < Real.exp (φ x / ε) * ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν :=
    mul_pos (Real.exp_pos _) hZ
  have hprod : Real.exp (φ x / ε) * ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν = 1 := by
    have := congrArg ENNReal.toReal hx
    rwa [ENNReal.toReal_ofReal hmul_pos.le, ENNReal.toReal_one] at this
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp, Real.log_one] at hlog
  have hφdiv : φ x / ε = -Real.log (∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν) := by
    linarith
  rw [entropicSoftmin, (div_eq_iff hε0.ne').1 hφdiv]
  ring

/-- Two Sinkhorn half-steps turn an almost-everywhere optimal potential pair `(φ₀, ψ₀)` into a
measurable softmin fixed-point pair `(φ₁, ψ₁)` agreeing with `(φ₀, ψ₀)` modulo `μ` and `ν`. -/
private theorem exists_softmin_fixed_point_of_isCoupling [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    {π : Measure (X × Y)} (hπ : IsCoupling π μ ν) {φ₀ : X → ℝ} {ψ₀ : Y → ℝ} {C₀ : ℝ}
    (hφ₀ : Measurable φ₀) (hψ₀ : Measurable ψ₀) (hφ₀C : ∀ x, |φ₀ x| ≤ C₀)
    (hψ₀C : ∀ y, |ψ₀ y| ≤ C₀)
    (hπeq : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ₀ z.1 + ψ₀ z.2 - (c z).toReal) / ε))) :
    ∃ (φ₁ : X → ℝ) (ψ₁ : Y → ℝ) (C₁ : ℝ), Measurable φ₁ ∧ Measurable ψ₁ ∧
      (∀ x, |φ₁ x| ≤ C₁) ∧ (∀ y, |ψ₁ y| ≤ C₁) ∧ φ₀ =ᵐ[μ] φ₁ ∧ ψ₀ =ᵐ[ν] ψ₁ ∧
      φ₁ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ₁ ∧
      ψ₁ = entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ₁ := by
  have hfB := abs_toReal_le_of_le hcB
  have hswap : ⇑(MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X) = Prod.swap := rfl
  have hπswap_eq : π.map Prod.swap = (ν.prod μ).withDensity fun w ↦
      ENNReal.ofReal (Real.exp ((ψ₀ w.1 + φ₀ w.2 - (c w.swap).toReal) / ε)) := by
    rw [hπeq, ← hswap, MeasurableEquiv.map_withDensity, hswap, Measure.prod_swap]
    refine withDensity_congr_ae (ae_of_all _ fun w ↦ ?_)
    have hw : (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).symm w = w.swap := rfl
    simp only [hw, Prod.fst_swap, Prod.snd_swap]
    congr 2; ring
  have hψ₀₁ : ψ₀ =ᵐ[ν] entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ₀ :=
    ae_eq_entropicSoftmin_of_isCoupling (hc.comp measurable_swap) (fun w ↦ hcB w.swap) hε
      hψ₀ hφ₀ hψ₀C hφ₀C (hπswap_eq ▸ hπ.swap)
  set ψ₁ := entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ₀
  have hψ₁ : Measurable ψ₁ :=
    measurable_entropicSoftmin (hc.comp measurable_swap).ennreal_toReal hφ₀
  have hψ₁C : ∀ y, |ψ₁ y| ≤ C₀ + B :=
    abs_entropicSoftmin_le (hc.comp measurable_swap).ennreal_toReal (fun w ↦ hfB w.swap)
      hφ₀ hφ₀C hε
  have hπ₁ : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ₀ z.1 + ψ₁ z.2 - (c z).toReal) / ε)) := by
    rw [hπeq]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq_comp hψ₀₁] with z hz
    simp only [Function.comp_apply] at hz; rw [hz]
  have hφ₀₁ : φ₀ =ᵐ[μ] entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ₁ :=
    ae_eq_entropicSoftmin_of_isCoupling hc hcB hε hφ₀ hψ₁ hφ₀C hψ₁C (hπ₁ ▸ hπ)
  set φ₁ := entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ₁
  have hφ₁ : Measurable φ₁ := measurable_entropicSoftmin hc.ennreal_toReal hψ₁
  have hφ₁C : ∀ x, |φ₁ x| ≤ C₀ + B + B :=
    abs_entropicSoftmin_le hc.ennreal_toReal hfB hψ₁ hψ₁C hε
  refine ⟨φ₁, ψ₁, C₀ + B + B, hφ₁, hψ₁, hφ₁C,
    fun y ↦ (hψ₁C y).trans (le_add_of_nonneg_right B.coe_nonneg), hφ₀₁, hψ₀₁, rfl,
    entropicSoftmin_congr_ae hφ₀₁⟩

/-- If `0 ≤ f ≤ B` and `0 ≤ φ ≤ B`, then `|entropicSoftmin f ε μ φ y| ≤ B`. -/
private theorem abs_entropicSoftmin_le_of_nonneg_le [IsProbabilityMeasure μ] {f : Y × X → ℝ}
    (hf : Measurable f) (hf₀ : ∀ w, 0 ≤ f w) (hfB : ∀ w, f w ≤ B) {φ : X → ℝ}
    (hφ : Measurable φ) (hφB : ∀ x, 0 ≤ φ x ∧ φ x ≤ B) (hε : ε ≠ 0) (y : Y) :
    |entropicSoftmin f ε μ φ y| ≤ B := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hf_abs : ∀ w, |f w| ≤ B :=
    fun w ↦ abs_le.2 ⟨by linarith [hf₀ w, B.coe_nonneg], hfB w⟩
  have hφ_abs : ∀ x, |φ x| ≤ B :=
    fun x ↦ abs_le.2 ⟨by linarith [(hφB x).1, B.coe_nonneg], (hφB x).2⟩
  have hint_y := integrable_exp_sub_div (ν := μ) (ε := ε) hf hf_abs hφ hφ_abs y
  have hlo : Real.exp (-(B : ℝ) / ε) ≤ ∫ x, Real.exp ((φ x - f (y, x)) / ε) ∂μ := by
    simpa using integral_mono (integrable_const _) hint_y fun x ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right (by linarith [(hφB x).1, hfB (y, x)]) ε.coe_nonneg
  have hhi : ∫ x, Real.exp ((φ x - f (y, x)) / ε) ∂μ ≤ Real.exp ((B : ℝ) / ε) := by
    simpa using integral_mono hint_y (integrable_const _) fun x ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right (by linarith [(hφB x).2, hf₀ (y, x)]) ε.coe_nonneg
  have h₁ := Real.log_le_log (Real.exp_pos _) hlo
  have h₂ := Real.log_le_log (integral_exp_pos hint_y) hhi
  rw [Real.log_exp, div_le_iff₀ hε0] at h₁
  rw [Real.log_exp, le_div_iff₀ hε0] at h₂
  dsimp only [entropicSoftmin]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Shifting a softmin fixed-point pair `(φ₁, ψ₁)` by `a = -ε * log ∫ exp (ψ₁ / ε) dν` produces
canonical bounds `0 ≤ φ ≤ B` and `|ψ| ≤ B` while preserving the softmin fixed-point equations. -/
private theorem entropicSoftmin_shift_bounds [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) {φ₁ : X → ℝ} {ψ₁ : Y → ℝ} {C₁ : ℝ}
    (hφ₁ : Measurable φ₁) (hψ₁ : Measurable ψ₁) (hφ₁C : ∀ x, |φ₁ x| ≤ C₁)
    (hψ₁C : ∀ y, |ψ₁ y| ≤ C₁) (hφ₁eq : φ₁ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ₁)
    (hψ₁eq : ψ₁ = entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ₁) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (a : ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, φ x = φ₁ x - a) ∧ (∀ y, ψ y = ψ₁ y + a) ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      φ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ ∧
      ψ = entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hfB := abs_toReal_le_of_le hcB
  have hint_a : Integrable (fun y ↦ Real.exp (ψ₁ y / ε)) ν := by
    simpa using integrable_exp_sub_div (X := Unit) (f := fun _ ↦ 0) (ν := ν) (ε := ε)
      measurable_const (Bf := 0) (fun _ ↦ by simp) hψ₁ hψ₁C ()
  have hZa : 0 < ∫ y, Real.exp (ψ₁ y / ε) ∂ν := integral_exp_pos hint_a
  set a : ℝ := -(ε : ℝ) * Real.log (∫ y, Real.exp (ψ₁ y / ε) ∂ν)
  set φ : X → ℝ := fun x ↦ φ₁ x - a
  set ψ : Y → ℝ := entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ
  have hψ_shift : ∀ y, ψ y = ψ₁ y + a := fun y ↦ by
    simpa only [sub_neg_eq_add, ← sub_eq_add_neg, ← hψ₁eq] using
      entropicSoftmin_add_const (f := fun w : Y × X ↦ (c w.swap).toReal) (ν := μ) (ε := ε)
        (hc.comp measurable_swap).ennreal_toReal (fun w ↦ hfB w.swap) hφ₁ hφ₁C hε (-a) y
  have hφ_fixed : φ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ := funext fun x ↦ by
    simpa only [← hψ_shift, φ, hφ₁eq] using (entropicSoftmin_add_const
      (f := fun z : X × Y ↦ (c z).toReal) (ν := ν) (ε := ε) hc.ennreal_toReal hfB hψ₁ hψ₁C hε
      a x).symm
  have hφ_bounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ B := fun x ↦ by
    have hint_x := integrable_exp_sub_div (ν := ν) (ε := ε) hc.ennreal_toReal hfB hψ₁ hψ₁C x
    have hZx : 0 < ∫ y, Real.exp ((ψ₁ y - (c (x, y)).toReal) / ε) ∂ν := integral_exp_pos hint_x
    have hhi : ∫ y, Real.exp ((ψ₁ y - (c (x, y)).toReal) / ε) ∂ν ≤
        ∫ y, Real.exp (ψ₁ y / ε) ∂ν := integral_mono hint_x hint_a fun y ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right (sub_le_self _ ENNReal.toReal_nonneg) ε.coe_nonneg
    have hlo : Real.exp (-(B : ℝ) / ε) * ∫ y, Real.exp (ψ₁ y / ε) ∂ν ≤
        ∫ y, Real.exp ((ψ₁ y - (c (x, y)).toReal) / ε) ∂ν := by
      rw [← integral_const_mul]
      refine integral_mono (hint_a.const_mul _) hint_x fun y ↦ ?_
      rw [← Real.exp_add, Real.exp_le_exp]
      calc (-(B : ℝ)) / ε + ψ₁ y / ε = (ψ₁ y - B) / ε := by ring
        _ ≤ (ψ₁ y - (c (x, y)).toReal) / ε :=
          div_le_div_of_nonneg_right (by linarith [(abs_le.1 (hfB (x, y))).2]) ε.coe_nonneg
    have hm₁ := mul_le_mul_of_nonneg_left (Real.log_le_log hZx hhi) hε0.le
    have hlog_lo := Real.log_le_log (mul_pos (Real.exp_pos _) hZa) hlo
    rw [Real.log_mul (Real.exp_pos _).ne' hZa.ne', Real.log_exp] at hlog_lo
    have hm₂ := mul_le_mul_of_nonneg_left hlog_lo hε0.le
    rw [mul_add, mul_div_cancel₀ _ hε0.ne'] at hm₂
    dsimp only [φ, a]
    rw [hφ₁eq, entropicSoftmin]
    exact ⟨by linarith, by linarith⟩
  have hφ : Measurable φ := hφ₁.sub_const _
  have hψ : Measurable ψ :=
    measurable_entropicSoftmin (hc.comp measurable_swap).ennreal_toReal hφ
  have hψ_bounds : ∀ y, |ψ y| ≤ B :=
    abs_entropicSoftmin_le_of_nonneg_le (hc.comp measurable_swap).ennreal_toReal
      (fun _ ↦ ENNReal.toReal_nonneg) (fun w ↦ (abs_le.1 (hfB w.swap)).2) hφ hφ_bounds hε
  exact ⟨φ, ψ, a, hφ, hψ, fun _ ↦ rfl, hψ_shift, hφ_bounds, hψ_bounds, hφ_fixed, rfl⟩

/-- Internal helper retaining the softmin fixed-point identities alongside the public properties of
canonical Schrödinger potentials. -/
private theorem exists_canonical_potentials [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      φ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ ∧
      ψ = entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ := by
  have hfin : ∀ z, c z ≠ ∞ := fun z ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  have hfB := abs_toReal_le_of_le hcB
  obtain ⟨π, hπ, hopt, φ₀, ψ₀, C₀, hφ₀, hψ₀, hφ₀C, hψ₀C, hπeq⟩ :=
    exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost (μ := μ) (ν := ν) hc hcB hε
  obtain ⟨φ₁, ψ₁, C₁, hφ₁, hψ₁, hφ₁C, hψ₁C, hφ₀₁, hψ₀₁, hφ₁eq, hψ₁eq⟩ :=
    exists_softmin_fixed_point_of_isCoupling hc hcB hε hπ hφ₀ hψ₀ hφ₀C hψ₀C hπeq
  obtain ⟨φ, ψ, a, hφ, hψ, hφ_shift, hψ_shift, hφ_bounds, hψ_bounds, hφ_fixed, hψ_fixed⟩ :=
    entropicSoftmin_shift_bounds (μ := μ) (ν := ν) hc hcB hε hφ₁ hψ₁ hφ₁C hψ₁C hφ₁eq hψ₁eq
  have hφ_abs : ∀ x, |φ x| ≤ B := fun x ↦
    abs_le.2 ⟨by linarith [(hφ_bounds x).1, B.coe_nonneg], (hφ_bounds x).2⟩
  have hrow_eq : ∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1 := fun x ↦ by
    simp_rw [entropicGibbsFactor_of_ne_top (hfin _)]
    conv_lhs => rw [hφ_fixed]
    exact integral_exp_entropicSoftmin hc.ennreal_toReal hfB hψ hψ_bounds hε x
  have hcol_eq : ∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1 := fun y ↦ by
    simp_rw [entropicGibbsFactor_of_ne_top (hfin _)]
    have heq : (fun x ↦ Real.exp ((φ x + ψ y - (c (x, y)).toReal) / ε)) =
        fun x ↦ Real.exp ((ψ y + φ x - (c (y, x).swap).toReal) / ε) :=
      funext fun x ↦ by simp only [Prod.swap_prod_mk, add_comm (φ x)]
    rw [heq, hψ_fixed]
    exact integral_exp_entropicSoftmin (hc.comp measurable_swap).ennreal_toReal
      (fun w ↦ hfB w.swap) hφ hφ_abs hε y
  have hφ_ae : φ =ᵐ[μ] fun x ↦ φ₀ x - a := hφ₀₁.symm.mono fun x hx ↦ by rw [hφ_shift x, hx]
  have hψ_ae : ψ =ᵐ[ν] fun y ↦ ψ₀ y + a := hψ₀₁.symm.mono fun y hy ↦ by rw [hψ_shift y, hy]
  have hπ_new : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z) := by
    rw [hπeq, entropicGibbsFactor_eq_exp_of_forall_ne_top hfin]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hφ_ae,
      Measure.quasiMeasurePreserving_snd.ae_eq_comp hψ_ae] with z hz₁ hz₂
    simp only [Function.comp_apply] at hz₁ hz₂
    rw [hz₁, hz₂]; congr 3; ring
  have hφi : Integrable φ μ := .of_bound hφ.aestronglyMeasurable B (ae_of_all _ hφ_abs)
  have hψi : Integrable ψ ν := .of_bound hψ.aestronglyMeasurable B (ae_of_all _ hψ_bounds)
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hφ hψ
    (fun x ↦ (hφ_bounds x).2) (fun y ↦ le_of_abs_le (hψ_bounds y))
  have hent_val : entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
    rw [← hopt]
    exact (hπ.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff hc.aemeasurable hε hφi hψi
      hexp (hopt ▸ entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)).2 hπ_new
  have hkant_val : kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
    rw [← hπ.entropicDualValue_eq_of_eq_withDensity hπ_new hexp, hent_val]
  exact ⟨φ, ψ, hφ, hψ, hφ_bounds, hψ_bounds, hrow_eq, hcol_eq, hkant_val, hent_val, hφ_fixed,
    hψ_fixed⟩

/-- **Canonical Schrödinger potentials for a bounded cost.** For probability measures `μ` and `ν`,
a measurable cost bounded by `B` and a positive temperature `ε`, there exist measurable potentials
`φ` and `ψ` that satisfy `0 ≤ φ ≤ B` and `|ψ| ≤ B` everywhere, solve both Schrödinger marginal
equations pointwise everywhere on `X` and `Y`, and attain the regularised transport cost in both
the Kantorovich and entropic dual objectives.

This is the uniform `L^∞` part of Proposition 1 of Feydy–Séjourné–Vialard–Amari–Trouvé–Peyré
(2019), together with the everywhere fixed-point equations. -/
theorem exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  obtain ⟨φ, ψ, hφ, hψ, hφB, hψB, hrow, hcol, hkant, hent, -, -⟩ :=
    exists_canonical_potentials (μ := μ) (ν := ν) hc hcB hε
  exact ⟨φ, ψ, hφ, hψ, hφB, hψB, hrow, hcol, hkant, hent⟩

/-- **One-sided Lipschitz regularity of canonical Schrödinger potentials.** When `X` is an extended
pseudometric space and the source slices `x ↦ (c (x, y)).toReal` are `K₁`-Lipschitz (with no metric
structure required on `Y`), the canonical source potential `φ` of
`exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le` is `K₁`-Lipschitz, uniformly in
the temperature `ε ≠ 0`. -/
theorem exists_lipschitzWith_left_entropicDualValue_eq_toReal_entropicTransportCost
    [PseudoEMetricSpace X] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K₁ : ℝ≥0} (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧ LipschitzWith K₁ φ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  obtain ⟨φ, ψ, hφ, hψ, hφB, hψB, hrow, hcol, hkant, hent, hφeq, -⟩ :=
    exists_canonical_potentials (μ := μ) (ν := ν) hc hcB hε
  refine ⟨φ, ψ, hφ, hψ, ?_, hφB, hψB, hrow, hcol, hkant, hent⟩
  rw [hφeq]
  exact lipschitzWith_entropicSoftmin (ν := ν) hc.ennreal_toReal (abs_toReal_le_of_le hcB)
    hψ hψB hε hL₁

/-- **Regularity of canonical Schrödinger potentials (Feydy et al., Proposition 1).** On extended
pseudometric spaces, when the cost is bounded by `B` and its slices are `K₁`- and `K₂`-Lipschitz,
the canonical Schrödinger potentials of
`exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le` are themselves `K₁`- and
`K₂`-Lipschitz, uniformly in the temperature `ε ≠ 0`. -/
theorem exists_lipschitzWith_entropicDualValue_eq_toReal_entropicTransportCost
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K₁ K₂ : ℝ≥0} (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K₂ fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      LipschitzWith K₁ φ ∧ LipschitzWith K₂ ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  have hfB := abs_toReal_le_of_le hcB
  obtain ⟨φ, ψ, hφ, hψ, hφB, hψB, hrow, hcol, hkant, hent, hφeq, hψeq⟩ :=
    exists_canonical_potentials (μ := μ) (ν := ν) hc hcB hε
  have hφ_abs : ∀ x, |φ x| ≤ B := fun x ↦
    abs_le.2 ⟨by linarith [(hφB x).1, B.coe_nonneg], (hφB x).2⟩
  have hφL : LipschitzWith K₁ φ := by
    rw [hφeq]
    exact lipschitzWith_entropicSoftmin (ν := ν) hc.ennreal_toReal hfB hψ hψB hε hL₁
  have hψL : LipschitzWith K₂ ψ := by
    rw [hψeq]
    exact lipschitzWith_entropicSoftmin (f := fun w : Y × X ↦ (c w.swap).toReal) (ν := μ)
      (hc.comp measurable_swap).ennreal_toReal (fun w ↦ hfB w.swap) hφ hφ_abs hε hL₂
  exact ⟨φ, ψ, hφ, hψ, hφL, hψL, hφB, hψB, hrow, hcol, hkant, hent⟩

end CanonicalPotentials

end TauCeti
