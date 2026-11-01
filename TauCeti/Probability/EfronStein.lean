/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Efron–Stein inequality

This file proves the Efron–Stein inequality for a square-integrable measurable function of
independent coordinates, stated on `Measure.pi`. If `X` has law `Measure.pi μ`, then
`Var f(X) ≤ ∑ i, E[Var_i f(X)]`, where `Var_i f(x)` is the variance of
`y ↦ f (Function.update x i y)` under `μ i`, i.e. the variance of `f` in the `i`-th coordinate
with all other coordinates frozen.

The proof is by induction on the number of coordinates. The two-factor step is the law of total
variance, `evariance_prod_eq`, combined with Jensen's inequality for the variance of an average,
`evariance_integral_prod_le`; together they give the two-variable inequality
`evariance_prod_le`.

## Main results

* `TauCeti.Probability.evariance_prod_eq`: the law of total variance on a product of two
  probability spaces;
* `TauCeti.Probability.evariance_integral_prod_le`: Jensen's inequality for the variance of an
  average;
* `TauCeti.Probability.evariance_prod_le`: the two-factor Efron–Stein inequality;
* `TauCeti.Probability.measurable_evariance_update`: measurability of the coordinatewise variance;
* `TauCeti.Probability.efronStein_fin`: the Efron–Stein inequality on `Measure.pi` over `Fin n`,
  with arbitrary (dependent) coordinate spaces.

## References

* B. Efron and C. Stein, *The jackknife estimate of variance*, Ann. Statist. 9 (1981), 586–596.
* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press
  (2013), Theorem 3.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti.Probability

/-- Jensen's inequality in `ℝ≥0∞` form: on a probability space, the square of the integral of
`‖u‖ₑ` is at most the integral of `‖u‖ₑ ^ 2`. -/
theorem sq_lintegral_enorm_le {β : Type*} [MeasurableSpace β] {π : Measure β}
    [IsProbabilityMeasure π] {u : β → ℝ} (hu : AEStronglyMeasurable u π) :
    (∫⁻ w, ‖u w‖ₑ ∂π) ^ 2 ≤ ∫⁻ w, ‖u w‖ₑ ^ 2 ∂π := by
  have h := eLpNorm_le_eLpNorm_of_exponent_le (μ := π) (f := u) one_le_two
  rw [eLpNorm_one_eq_lintegral_enorm hu,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hu] at h
  have h' : ∫⁻ w, ‖u w‖ₑ ∂π ≤ (∫⁻ w, ‖u w‖ₑ ^ 2 ∂π) ^ ((1 : ℝ) / 2) := by
    simpa [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h
  calc (∫⁻ w, ‖u w‖ₑ ∂π) ^ 2 ≤ ((∫⁻ w, ‖u w‖ₑ ^ 2 ∂π) ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left' h' 2
    _ = ∫⁻ w, ‖u w‖ₑ ^ 2 ∂π := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α} {π : Measure β}
  [IsProbabilityMeasure ν] [IsProbabilityMeasure π] {F : α × β → ℝ}

/-- For a square integrable measurable `F` on a product, almost every section `w ↦ F (a, w)` is
square integrable. -/
theorem ae_memLp_two_prod_left (hF : Measurable F) (hL : MemLp F 2 (ν.prod π)) :
    ∀ᵐ a ∂ν, MemLp (fun w => F (a, w)) 2 π := by
  filter_upwards [hL.integrable_sq.prod_right_ae] with a ha
  exact (memLp_two_iff_integrable_sq
    (hF.comp measurable_prodMk_left).aestronglyMeasurable).2 ha

/-- The law of total variance on a product of probability spaces: the variance of a square
integrable `F` splits into the average of the variances in the second coordinate and the variance
of the average over the second coordinate. -/
theorem evariance_prod_eq (hF : Measurable F) (hL : MemLp F 2 (ν.prod π)) :
    evariance F (ν.prod π) = ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν +
      evariance (fun a => ∫ w, F (a, w) ∂π) ν := by
  have hint : Integrable F (ν.prod π) := hL.integrable one_le_two
  have hsq : Integrable (fun p => F p ^ 2) (ν.prod π) := hL.integrable_sq
  have hslice : ∀ᵐ a ∂ν, MemLp (fun w => F (a, w)) 2 π := ae_memLp_two_prod_left hF hL
  have hgm : StronglyMeasurable (fun a => ∫ w, F (a, w) ∂π) :=
    hF.stronglyMeasurable.integral_prod_right'
  have hs : Integrable (fun a => ∫ w, F (a, w) ^ 2 ∂π) ν := hsq.integral_prod_left
  have hvar : ∀ᵐ a ∂ν, variance (fun w => F (a, w)) π =
      (∫ w, F (a, w) ^ 2 ∂π) - (∫ w, F (a, w) ∂π) ^ 2 := by
    filter_upwards [hslice] with a ha
    simpa [Pi.pow_apply] using variance_eq_sub ha
  have hg2 : Integrable (fun a => (∫ w, F (a, w) ∂π) ^ 2) ν := by
    refine hs.mono' (hgm.aestronglyMeasurable.pow 2) ?_
    filter_upwards [hslice, hvar] with a ha hv
    have := variance_nonneg (fun w => F (a, w)) π
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    linarith
  have hgL : MemLp (fun a => ∫ w, F (a, w) ∂π) 2 ν :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hg2
  have hvarint : Integrable (fun a => variance (fun w => F (a, w)) π) ν :=
    (hs.sub hg2).congr (by filter_upwards [hvar] with a ha using ha.symm)
  have hE1 : ∫ p, F p ^ 2 ∂(ν.prod π) = ∫ a, ∫ w, F (a, w) ^ 2 ∂π ∂ν := integral_prod _ hsq
  have hE2 : ∫ p, F p ∂(ν.prod π) = ∫ a, ∫ w, F (a, w) ∂π ∂ν := integral_prod _ hint
  have hE3 : ∫ a, variance (fun w => F (a, w)) π ∂ν =
      (∫ a, ∫ w, F (a, w) ^ 2 ∂π ∂ν) - ∫ a, (∫ w, F (a, w) ∂π) ^ 2 ∂ν := by
    rw [integral_congr_ae hvar, integral_sub hs hg2]
  have hE4 := variance_eq_sub hgL
  have hE5 := variance_eq_sub hL
  simp only [Pi.pow_apply] at hE4 hE5
  have hlint : ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν =
      ENNReal.ofReal (∫ a, variance (fun w => F (a, w)) π ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hvarint
      (Filter.Eventually.of_forall fun a => variance_nonneg _ _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hslice] with a ha
    exact (ofReal_variance ha).symm
  rw [hlint, ← ofReal_variance hL, ← ofReal_variance hgL,
    ← ENNReal.ofReal_add (integral_nonneg fun a => variance_nonneg _ _) (variance_nonneg _ _)]
  congr 1
  rw [hE5, hE4, hE3, hE1, hE2]
  ring

/-- Jensen's inequality for the variance of an average: the variance of the average over the
second coordinate is at most the average over the second coordinate of the variances in the first
coordinate. -/
theorem evariance_integral_prod_le (hF : Measurable F) (hL : MemLp F 2 (ν.prod π)) :
    evariance (fun a => ∫ w, F (a, w) ∂π) ν ≤
      ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
  have hint : Integrable F (ν.prod π) := hL.integrable one_le_two
  have hmm : StronglyMeasurable (fun w => ∫ a, F (a, w) ∂ν) :=
    (hF.comp measurable_swap).stronglyMeasurable.integral_prod_right'
  have hmint : Integrable (fun w => ∫ a, F (a, w) ∂ν) π := hint.integral_prod_right
  have hm_eq : ∫ w, ∫ a, F (a, w) ∂ν ∂π = ∫ a, ∫ w, F (a, w) ∂π ∂ν := by
    rw [← integral_prod_symm _ hint, integral_prod _ hint]
  have hae : ∀ᵐ a ∂ν, ‖(∫ w, F (a, w) ∂π) - ∫ a', ∫ w, F (a', w) ∂π ∂ν‖ₑ ^ 2 ≤
      ∫⁻ w, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ^ 2 ∂π := by
    filter_upwards [hint.prod_right_ae] with a ha
    have hsub : (∫ w, F (a, w) ∂π) - ∫ a', ∫ w, F (a', w) ∂π ∂ν =
        ∫ w, (F (a, w) - ∫ a', F (a', w) ∂ν) ∂π := by
      rw [integral_sub ha hmint, hm_eq]
    rw [hsub]
    calc ‖∫ w, (F (a, w) - ∫ a', F (a', w) ∂ν) ∂π‖ₑ ^ 2
        ≤ (∫⁻ w, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ∂π) ^ 2 := by
          gcongr
          exact enorm_integral_le_lintegral_enorm _
      _ ≤ _ := sq_lintegral_enorm_le
          (((hF.comp measurable_prodMk_left).sub hmm.measurable).aestronglyMeasurable)
  calc evariance (fun a => ∫ w, F (a, w) ∂π) ν
      ≤ ∫⁻ a, ∫⁻ w, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ^ 2 ∂π ∂ν := lintegral_mono_ae hae
    _ = ∫⁻ w, ∫⁻ a, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ^ 2 ∂ν ∂π :=
        lintegral_lintegral_swap
          ((hF.sub (hmm.measurable.comp measurable_snd)).enorm.pow_const 2).aemeasurable
    _ = ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := rfl

/-- The two-factor Efron–Stein inequality. -/
theorem evariance_prod_le (hF : Measurable F) (hL : MemLp F 2 (ν.prod π)) :
    evariance F (ν.prod π) ≤ ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν +
      ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
  rw [evariance_prod_eq hF hL]
  gcongr
  exact evariance_integral_prod_le hF hL

end Prod

universe u

/-- The variance of `f` in coordinate `i`, with the other coordinates frozen at `x`, is a
measurable function of `x`. -/
theorem measurable_evariance_update {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SFinite (μ i)] (i : ι)
    {f : (∀ i, α i) → ℝ} (hf : Measurable f) :
    Measurable fun x => evariance (fun y => f (Function.update x i y)) (μ i) := by
  have hu : Measurable fun p : (∀ i, α i) × α i => f (Function.update p.1 i p.2) :=
    hf.comp measurable_update'
  have hm : StronglyMeasurable fun x => ∫ y, f (Function.update x i y) ∂μ i :=
    hu.stronglyMeasurable.integral_prod_right'
  exact Measurable.lintegral_prod_right'
    (f := fun p : (∀ i, α i) × α i =>
      ‖f (Function.update p.1 i p.2) - ∫ y, f (Function.update p.1 i y) ∂μ i‖ₑ ^ 2)
    ((hu.sub (hm.measurable.comp measurable_fst)).enorm.pow_const 2)

/-- The Efron–Stein inequality on `Measure.pi` over `Fin n`: for a square integrable measurable
function `f` of independent coordinates, the variance of `f` is at most the sum over `i` of the
average variance of `f` in coordinate `i` with the other coordinates frozen. -/
theorem efronStein_fin : ∀ {n : ℕ} {α : Fin n → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] {f : (∀ i, α i) → ℝ},
    Measurable f → MemLp f 2 (Measure.pi μ) →
    evariance f (Measure.pi μ) ≤
      ∑ i, ∫⁻ x, evariance (fun y => f (Function.update x i y)) (μ i) ∂Measure.pi μ
  | 0, α, _, μ, _, f, _, _ => by
    have hc : ∀ ω, ∫ x, f x ∂Measure.pi μ = f ω := fun ω => by
      rw [show f = fun _ => f ω from funext fun x => by rw [Subsingleton.elim x ω]]
      simp
    have h0 : ∀ ω, ‖f ω - f default‖ₑ ^ 2 = 0 := fun ω => by
      rw [Subsingleton.elim ω default]
      simp
    rw [evariance, hc default]
    simp [h0]
  | n + 1, α, _, μ, _, f, hf, hL => by
    set e := MeasurableEquiv.piFinSuccAbove α 0 with he
    have mp : MeasurePreserving e (Measure.pi μ)
        ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
      measurePreserving_piFinSuccAbove μ 0
    have mps := mp.symm e
    set F : α 0 × (∀ j, α (Fin.succAbove 0 j)) → ℝ := fun p => f (e.symm p) with hFdef
    have hFm : Measurable F := hf.comp e.symm.measurable
    have hFL : MemLp F 2 ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
      hL.comp_measurePreserving mps
    set G : Fin (n + 1) → (∀ i, α i) → ℝ≥0∞ :=
      fun i x => evariance (fun y => f (Function.update x i y)) (μ i) with hGdef
    have hGm : ∀ i, Measurable (G i) := fun i => measurable_evariance_update μ i hf
    have hT : ∀ g : (∀ i, α i) → ℝ≥0∞,
        ∫⁻ p, g (e.symm p) ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) =
          ∫⁻ x, g x ∂Measure.pi μ := fun g =>
      mps.lintegral_comp_emb e.symm.measurableEmbedding g
    have hEv : evariance f (Measure.pi μ) =
        evariance F ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) := by
      have hI : ∫ p, F p ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) =
          ∫ x, f x ∂Measure.pi μ := mps.integral_comp' f
      rw [evariance, evariance, hI]
      exact (hT fun x => ‖f x - ∫ x', f x' ∂Measure.pi μ‖ₑ ^ 2).symm
    have hG : ∀ (j : Fin n) (a : α 0) (w : ∀ j, α (Fin.succAbove 0 j)),
        evariance (fun y => F (a, Function.update w j y)) (μ (Fin.succAbove 0 j)) =
          G (Fin.succAbove 0 j) (e.symm (a, w)) := by
      intro j a w
      simp only [hGdef, hFdef, he, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_update]
    have hG0 : ∀ (a : α 0) (w : ∀ j, α (Fin.succAbove 0 j)),
        G 0 (e.symm (a, w)) = evariance (fun a' => F (a', w)) (μ 0) := by
      intro a w
      simp only [hGdef, hFdef, he, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.update_insertNth]
    have hslice := ae_memLp_two_prod_left hFm hFL
    have hGp : ∀ j, Measurable fun p => G j (e.symm p) := fun j =>
      (hGm j).comp e.symm.measurable
    have h1 : ∫⁻ a, evariance (fun w => F (a, w)) (Measure.pi fun j => μ (Fin.succAbove 0 j))
          ∂(μ 0) ≤ ∑ j : Fin n, ∫⁻ x, G (Fin.succAbove 0 j) x ∂Measure.pi μ := by
      calc _ ≤ ∫⁻ a, ∑ j : Fin n, ∫⁻ w, G (Fin.succAbove 0 j) (e.symm (a, w))
              ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) ∂(μ 0) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hslice] with a ha
            have := efronStein_fin (α := fun j => α (Fin.succAbove 0 j))
              (fun j => μ (Fin.succAbove 0 j)) (f := fun w => F (a, w))
              (hFm.comp measurable_prodMk_left) ha
            simpa only [hG] using this
        _ = ∑ j : Fin n, ∫⁻ a, ∫⁻ w, G (Fin.succAbove 0 j) (e.symm (a, w))
              ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) ∂(μ 0) :=
            lintegral_finsetSum' _ fun j _ =>
              (Measurable.lintegral_prod_right' (hGp _)).aemeasurable
        _ = _ := Finset.sum_congr rfl fun j _ => by
            rw [← hT, lintegral_prod _ (hGp _).aemeasurable]
    have h2 : ∫⁻ w, evariance (fun a => F (a, w)) (μ 0)
        ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) = ∫⁻ x, G 0 x ∂Measure.pi μ := by
      rw [← hT, lintegral_prod _ (hGp 0).aemeasurable]
      simp_rw [hG0]
      rw [lintegral_const, measure_univ, mul_one]
    calc evariance f (Measure.pi μ) = evariance F _ := hEv
      _ ≤ _ := evariance_prod_le hFm hFL
      _ ≤ (∑ j : Fin n, ∫⁻ x, G (Fin.succAbove 0 j) x ∂Measure.pi μ) +
          ∫⁻ x, G 0 x ∂Measure.pi μ := add_le_add h1 h2.le
      _ = ∑ i, ∫⁻ x, G i x ∂Measure.pi μ := by rw [Fin.sum_univ_succAbove _ 0, add_comm]

end TauCeti.Probability
