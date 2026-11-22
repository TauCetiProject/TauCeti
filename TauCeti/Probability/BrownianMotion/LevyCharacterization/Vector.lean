/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.Vector.Basic
public import TauCeti.Probability.Process.Predictable.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.Process.Basic
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Basic
import TauCeti.Probability.BrownianMotion.Basic
import TauCeti.Probability.BrownianMotion.LevyCharacterization.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Independence.CharacteristicFunction
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Independence.Pi
import TauCeti.Probability.Martingale.Exponential.Local
import TauCeti.Probability.Martingale.Local.Linear
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.LocalProperty

/-!
# Vector Lévy characterization of Brownian motion

Multivariate Lévy characterization for a family `M : ι → ℝ≥0 → Ω → ℝ` of almost-surely continuous
real local martingales on a raw filtration `ℱ` with local-martingale cross-brackets
`M i t * M j t - M i 0 * M j 0 - C i j * t`: Cramér–Wold characteristic-function factorization
(set-integral and conditional-expectation forms), joint increment independence from `ℱ s`, product
Gaussian increment laws, global pathwise coordinate independence, coordinate vector Brownian law
(`IsBrownianVector`), strongly predictable indistinguishable vector Brownian versions (both
arbitrary index coordinatewise and countable-index jointly predictable `Pi` versions), the adapted
combined filtered characterization, and the converse cross-product martingale
(`ProbabilityTheory.IsBrownianReal.martingale_mul_of_indepFun`) and vector increment independence
theorems for independent Brownian local martingales.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 3.3.16.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Theorem 3.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

namespace ProbabilityTheory.IsBrownianReal

/-- **Cross-product martingale property for independent Brownian local martingales.**
If `B₁` and `B₂` are independent real Brownian motions that are adapted local martingales on `ℱ`,
then their product `t ↦ B₁ t * B₂ t` is a true `ℱ`-martingale. -/
theorem martingale_mul_of_indepFun {B₁ B₂ : ℝ≥0 → Ω → ℝ}
    (hB₁ : IsBrownianReal B₁ P) (hB₂ : IsBrownianReal B₂ P)
    (hind : IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) P)
    (hA₁ : Adapted ℱ B₁) (hA₂ : Adapted ℱ B₂)
    (hloc₁ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B₁ P)
    (hloc₂ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B₂ P) :
    Martingale (fun t ω ↦ B₁ t ω * B₂ t ω) ℱ P := by
  have hFB₁ := hB₁.isFilteredPreBrownianReal_of_locally_martingale hA₁ hloc₁
  have hFB₂ := hB₂.isFilteredPreBrownianReal_of_locally_martingale hA₂ hloc₂
  have hFW := (hB₁.const_mul_add_const_mul_of_indepFun hB₂ hind (a := 1 / √2) (b := 1 / √2)
      (by rw [div_pow, one_pow, Real.sq_sqrt zero_le_two]; norm_num))
    |>.isFilteredPreBrownianReal_of_locally_martingale
      (fun t ↦ (measurable_const.mul (hA₁ t)).add (measurable_const.mul (hA₂ t)))
      (Locally.of_prop (by
        convert (hFB₁.martingale.smul (1 / √2)).add (hFB₂.martingale.smul (1 / √2))))
  convert (hFW.martingale_sq_sub.sub (hFB₁.martingale_sq_sub.smul (1 / 2))).sub
    (hFB₂.martingale_sq_sub.smul (1 / 2)) using 1
  ext t ω; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← mul_add, mul_pow, div_pow,
    one_pow, Real.sq_sqrt zero_le_two]; ring

end ProbabilityTheory.IsBrownianReal

namespace TauCeti.Probability

/-- **Cramér–Wold characteristic-function factorization for vector continuous local martingales.**
If `M : ι → ℝ≥0 → Ω → ℝ` is a finite family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets `M i t * M j t - M i 0 * M j 0 - C i j * t` are local martingales, then for
every frequency vector `v : ι → ℝ`, every `s ≤ t`, and every `A ∈ ℱ s`, the complex exponential
of the linear combination `∑ i, v i * (M i t - M i s)` integrates over `A` to
`(P A).toReal * exp (-(∑ i, ∑ j, v i * v j * C i j) * (t - s) / 2)`. -/
theorem setIntegral_exp_I_mul_sum_sub_of_locally_martingale [IsFiniteMeasure P] {ι : Type*}
    [Fintype ι] {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (v : ι → ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, exp (I * ∑ i, v i * (M i t ω - M i s ω)) ∂P =
      ((P A).toReal : ℂ) *
        exp (-((∑ i, ∑ j, v i * v j * C i j) * ((t : ℝ) - s) / 2 : ℝ)) := by
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQp, hQY⟩ :=
    exists_isStronglyPredictable_indist_prod_sub_initialValue_sub
      (A := fun i j t _ ↦ C i j * (t : ℝ)) hM hQ
      (fun i j ↦ (continuous_const.mul NNReal.continuous_coe).isStronglyPredictable_fst) hcont
      (fun _ _ ↦ ae_of_all P fun _ _ ↦ rfl)
  have hYv_l := Finset.locally_martingale_sum (Finset.univ : Finset ι)
    (fun i _ ↦ by simpa only [smul_eq_mul] using (hYl i).martingale_smul (v i))
    (fun i _ ↦ ((hYp i).const_mul (v i)).isStronglyProgressive)
    (fun i _ ↦ (hYc i).mono fun _ h ↦ (continuous_const.mul h).isRightContinuous)
  have hQsum := Finset.locally_martingale_sum (Finset.univ : Finset (ι × ι))
    (fun p _ ↦ by simpa only [smul_eq_mul] using (hQY p.1 p.2).martingale_smul (v p.1 * v p.2))
    (fun p _ ↦ ((hQp p.1 p.2).const_mul (v p.1 * v p.2)).isStronglyProgressive)
    (fun p _ ↦ (hYc p.1).mp <|
      (hYc p.2).mono fun _ h₂ h₁ ↦ (by fun_prop : Continuous _).isRightContinuous)
  have hQeq : (fun u ω ↦ (∑ i, v i * Y i u ω) ^ 2 - (∑ i, v i * Y i 0 ω) ^ 2 -
        (∑ i, ∑ j, v i * v j * C i j) * (u : ℝ)) = fun u ω ↦ ∑ p : ι × ι, (v p.1 * v p.2) *
        (Y p.1 u ω * Y p.2 u ω - Y p.1 0 ω * Y p.2 0 ω - C p.1 p.2 * (u : ℝ)) := by
    ext u ω; rw [Fintype.sum_prod_type]
    simp only [sq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [setIntegral_congr_ae (ℱ.le s A hA)
      (g := fun ω ↦ exp (I * (1 : ℝ) * ((∑ i, v i * Y i t ω) - ∑ i, v i * Y i s ω)))
      ((ae_all_iff.2 hYM).mono fun _ hω _ ↦ by
        simp only [ofReal_one, mul_one, ← ofReal_sub, ← Finset.sum_sub_distrib]
        congr 3; exact Finset.sum_congr rfl fun i _ ↦ by rw [hω i t, hω i s, mul_sub]),
    Locally.setIntegral_exp_I_mul_sub hYv_l (hQeq ▸ hQsum)
      ((ae_all_iff.2 hYc).mono fun _ h ↦ by fun_prop) 1 hst hA, one_pow, one_mul]

/-- **Joint conditional characteristic function for vector continuous local martingales.**
If `M : ι → ℝ≥0 → Ω → ℝ` is a finite family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets `M i t * M j t - M i 0 * M j 0 - C i j * t` are local martingales, then for
every frequency vector `v : ι → ℝ` and every `s ≤ t`, the conditional characteristic function of
`∑ i, v i * (M i t - M i s)` given `ℱ s` is almost surely
`exp (-(∑ i, ∑ j, v i * v j * C i j) * (t - s) / 2)`. -/
theorem condExp_exp_I_mul_sum_sub_of_locally_martingale [IsFiniteMeasure P] {ι : Type*}
    [Fintype ι] {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (v : ι → ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ exp (I * ∑ i, v i * (M i t ω - M i s ω)) | ℱ s] =ᵐ[P]
      fun _ ↦ exp (-((∑ i, ∑ j, v i * v j * C i j) * ((t : ℝ) - s) / 2 : ℝ)) := by
  have hsm : AEMeasurable (fun ω i ↦ M i t ω - M i s ω) P := aemeasurable_pi_iff.2 fun i ↦
    ((hM i).aestronglyMeasurable_sub (fun _ h ↦ h.stronglyAdapted) s t).aemeasurable
  let e := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hint : Integrable (fun ω ↦ exp (I * ∑ i, v i * (M i t ω - M i s ω))) P := by
    convert (e.measurable.comp_aemeasurable hsm).integrable_exp_inner_mul_I (e v) using 1
    ext ω; exact (TauCeti.exp_inner_toLp_mul_I (fun i ↦ M i t ω - M i s ω) (e v)).symm
  refine (TauCeti.MeasureTheory.condExp_ae_eq_const_iff (ℱ.le s) hint _).2 fun A hA _ ↦ ?_
  rw [Measure.real, Complex.real_smul,
    setIntegral_exp_I_mul_sum_sub_of_locally_martingale hM hQ hcont v hst hA]

/-- **Joint increment independence from the past for vector continuous local martingales.**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets `M i t * M j t - M i 0 * M j 0 - C i j * t` are local martingales, then for
every `s ≤ t`, the vector increment `ω ↦ (M i t ω - M i s ω)_i` is independent of `ℱ s`. -/
theorem indep_comap_sub_pi_of_locally_martingale [IsZeroOrProbabilityMeasure P] {ι : Type*}
    {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (.comap (fun ω i ↦ M i t ω - M i s ω) inferInstance) (ℱ s) P := by
  have hmeas i := ((hM i).aestronglyMeasurable_sub (fun _ h ↦ h.stronglyAdapted) s t).aemeasurable
  simpa only [IndepFun_iff_Indep, @MeasurableSpace.comap_id _ (ℱ s)] using
    @IndepFun.process_indepFun₀ ι Ω mΩ P (fun _ ↦ ℝ) Ω (fun _ ↦ inferInstance) (ℱ s)
      (fun i ω ↦ M i t ω - M i s ω) id hmeas
      (@Measurable.aemeasurable Ω Ω mΩ (ℱ s) id P fun _ hA ↦ ℱ.le s _ hA) (fun S ↦ by
        rw [IndepFun_iff_Indep (mγ := ℱ s), @MeasurableSpace.comap_id _ (ℱ s)]
        let e := MeasurableEquiv.toLp 2 (S → ℝ)
        rw [← e.measurableEmbedding.comap_eq, MeasurableSpace.comap_comp]
        refine indep_comap_of_setIntegral_exp_inner_mul_I (ℱ.le s)
          (e.measurable.comp_aemeasurable (aemeasurable_pi_iff.2 fun i ↦ hmeas i))
          (φ := fun v : EuclideanSpace ℝ S ↦
            exp (-((∑ i : S, ∑ j : S, v i * v j * C i j) * ((t : ℝ) - s) / 2 : ℝ))) fun v _ hA ↦ by
          simp_rw [e, Function.comp_apply, TauCeti.exp_inner_toLp_mul_I]
          exact setIntegral_exp_I_mul_sum_sub_of_locally_martingale (M := fun i : S ↦ M i)
            (C := fun i j : S ↦ C i j) (fun i ↦ hM i) (fun i j ↦ hQ i j) (fun i ↦ hcont i)
            (fun i ↦ v i) hst hA) _

/-- **Product Gaussian increment law under orthogonal vector Lévy hypotheses.**
If `M : ι → ℝ≥0 → Ω → ℝ` is a finite family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets satisfy `M i t * M j t - M i 0 * M j 0 - δ_{ij} c_i t` is a local
martingale (`c : ι → ℝ≥0`), then for `s ≤ t` the vector increment `ω ↦ (M i t ω - M i s ω)_i` has
product Gaussian law `Measure.pi (fun i ↦ gaussianReal 0 (c i * (t - s)))`. -/
theorem hasLaw_sub_pi_gaussianReal_of_locally_martingale [IsProbabilityMeasure P] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ} {c : ι → ℝ≥0}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω -
        (if i = j then (c i : ℝ) * (t : ℝ) else 0)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω i ↦ M i t ω - M i s ω)
      (Measure.pi fun i : ι ↦ gaussianReal 0 (c i * (t - s))) P := by
  have hX : AEMeasurable (fun ω i ↦ M i t ω - M i s ω) P := aemeasurable_pi_iff.2 fun i ↦
    ((hM i).aestronglyMeasurable_sub (fun _ h ↦ h.stronglyAdapted) s t).aemeasurable
  refine ⟨hX, ?_⟩
  have : IsFiniteMeasure (P.map (fun ω i ↦ M i t ω - M i s ω)) := Measure.isFiniteMeasure_map P _
  rw [← charFun_eq_pi_iff]; intro v
  have hset := setIntegral_exp_I_mul_sum_sub_of_locally_martingale hM
    (C := fun i j ↦ if i = j then (c i : ℝ) else 0)
    (fun i j ↦ by simpa only [ite_mul, zero_mul] using hQ i j) hcont (fun i ↦ v i) hst .univ
  simp only [Measure.restrict_univ, measure_univ, ENNReal.toReal_one, ofReal_one, one_mul] at hset
  let e := MeasurableEquiv.toLp 2 (ι → ℝ)
  rw [← MeasurableEquiv.coe_toLp (p := 2) (X := ι → ℝ),
    e.measurable.aemeasurable.map_map_of_aemeasurable hX,
    charFun_map_eq_integral (e.measurable.comp_aemeasurable hX) v]
  simp_rw [e, Function.comp_apply, TauCeti.exp_inner_toLp_mul_I, hset, charFun_gaussianReal,
    ← exp_sum]
  congr 1; simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    NNReal.coe_mul, NNReal.coe_sub hst, ofReal_zero, zero_mul, zero_sub,
    Finset.sum_neg_distrib, ← Finset.sum_div]
  push_cast; rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div]
  congr 1; exact Finset.sum_congr rfl fun i _ ↦ by ring

private lemma iIndepFun_grid_increments [IsProbabilityMeasure P] {ι : Type*} [DecidableEq ι]
    {Y : ι → ℝ≥0 → Ω → ℝ} {c : ι → ℝ≥0} (hYp : ∀ i, IsStronglyPredictable ℱ (Y i))
    (hYc : ∀ i, ∀ᵐ ω ∂P, Continuous (Y i · ω))
    (hYl : ∀ i, Locally (fun U ↦ Martingale U ℱ P) ℱ (Y i) P)
    (hQY : ∀ i j, Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦
      Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω - (if i = j then (c i : ℝ) else 0) * (t : ℝ)) P)
    (S : Finset ι) {m : ℕ} {g : Fin (m + 1) → ℝ≥0} (hg : Monotone g) :
    iIndepFun (fun (i : S) ω (k : Fin m) ↦ Y i (g k.succ) ω - Y i (g k.castSucc) ω) P := by
  have hm i t : Measurable[ℱ t] (Y i t) :=
    ((hYp i).isStronglyProgressive.stronglyAdapted t).measurable
  have hV_adapt : Adapted ℱ (fun t ω i ↦ Y i t ω - Y i 0 ω) := fun t ↦
    @measurable_pi_iff _ _ _ (ℱ t) _ _ |>.2 fun i ↦
      (hm i t).sub ((hm i 0).mono (ℱ.mono bot_le) le_rfl)
  -- Swap row independence (across grid steps) and column independence (across coordinates `S`).
  have hrow := ((hV_adapt.hasIndepIncrements fun _ _ hst ↦ by
      simpa only [Pi.sub_def, sub_sub_sub_cancel_right] using
        indep_comap_sub_pi_of_locally_martingale hYl hQY hYc hst) m g hg).comp
    (fun _ (f : ι → ℝ) (i : S) ↦ f i)
    (fun _ ↦ measurable_pi_iff.2 fun i ↦ measurable_pi_apply i.val)
  refine iIndepFun.swap
    (by simpa only [Function.comp_def, Pi.sub_apply, sub_sub_sub_cancel_right] using hrow)
    (fun k ↦ (iIndepFun_iff_hasLaw_pi_pi fun i : S ↦ Locally.hasLaw_sub_gaussianReal (hYl i)
        (by simpa only [↓reduceIte, sq] using hQY i i) (hYc i) (hg (Fin.castSucc_le_succ k))).2
      (hasLaw_sub_pi_gaussianReal_of_locally_martingale (M := fun i : S ↦ Y i)
        (c := fun i : S ↦ c i) (fun i ↦ hYl i)
        (fun i j ↦ by simpa only [Subtype.ext_iff, ite_mul, zero_mul] using hQY i.val j.val)
        (fun i ↦ hYc i) (hg (Fin.castSucc_le_succ k))))
    (fun k i ↦ (((hm i (g k.succ)).mono (ℱ.le _) le_rfl).sub
      ((hm i (g k.castSucc)).mono (ℱ.le _) le_rfl)).aemeasurable)

/-- **Global pathwise coordinate independence under orthogonal vector Lévy hypotheses (arbitrary
start).**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets `M i t * M j t - M i 0 * M j 0 - δ_{ij} c_i t` are local martingales
(`c : ι → ℝ≥0`), then the centered coordinate processes `i ↦ (t ↦ M i t - M i 0)` are mutually
independent as random paths `Ω → (ℝ≥0 → ℝ)`. -/
theorem iIndepFun_sub_initialValue_of_locally_martingale [IsProbabilityMeasure P] {ι : Type*}
    [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ} {c : ι → ℝ≥0}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω -
        (if i = j then (c i : ℝ) * (t : ℝ) else 0)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    iIndepFun (fun i ω t ↦ M i t ω - M i 0 ω) P := by
  obtain ⟨Y, hYp, hYM, hYc, hYl, _, hQY⟩ :=
    exists_isStronglyPredictable_indist_prod_sub_initialValue_sub
      (A := fun i j t _ ↦ (if i = j then (c i : ℝ) else 0) * (t : ℝ)) hM hQ
      (fun _ _ ↦ (continuous_const.mul NNReal.continuous_coe).isStronglyPredictable_fst) hcont
      (fun _ _ ↦ ae_of_all P fun _ _ ↦ by simp)
  have hYm i t : Measurable (Y i t) :=
    ((hYp i).isStronglyProgressive.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl
  refine (iIndepFun.iIndepFun_process (fun i t ↦ (hYm i t).sub (hYm i 0))
    fun S J ↦ ?_).process_congr fun i t ↦ (hYM i).mono fun _ hω ↦ by simp [hω t, hω 0]
  let T : Finset ℝ≥0 := insert 0 (Finset.univ.biUnion J)
  have h0T : (0 : ℝ≥0) ∈ T := Finset.mem_insert_self 0 _
  let e : Fin (T.card - 1 + 1) ≃o T :=
    T.orderIsoOfFin (Nat.sub_add_cancel (Finset.card_pos.2 ⟨0, h0T⟩)).symm
  let idx (i : S) (t : J i) : Fin (T.card - 1 + 1) :=
    e.symm ⟨t.val,
      Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, t.property⟩)⟩
  let g (i : S) (d : Fin (T.card - 1) → ℝ) (t : J i) : ℝ :=
    Fin.cases 0 (fun k ↦ ∑ j ∈ Finset.Iic k, d j) (idx i t)
  convert (iIndepFun_grid_increments hYp hYc hYl hQY S fun _ _ h ↦ e.monotone h).comp g
    (fun i ↦ measurable_pi_iff.2 fun t ↦ by
      dsimp only [g]; cases idx i t using Fin.cases with
      | zero => exact measurable_const
      | succ k => exact Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _) using 1
  ext i ω t
  have hg0 : (e 0 : ℝ≥0) = 0 := le_antisymm (Subtype.coe_le_coe.2
    ((e.monotone (Fin.zero_le _)).trans_eq (e.apply_symm_apply ⟨0, h0T⟩))) bot_le
  have ht : (e (idx i t) : ℝ≥0) = t.val := congrArg Subtype.val (e.apply_symm_apply _)
  dsimp only [g, Function.comp_apply]; cases hk : idx i t using Fin.cases with
  | zero => rw [hk] at ht; simp [← ht, hg0]
  | succ k => rw [hk] at ht; simpa only [Fin.cases_succ, Pi.sub_apply, ← ht, hg0] using
      (Fin.sum_Iic_sub k fun j ↦ Y i (e j) ω).symm

/-- **Global pathwise coordinate independence under orthogonal vector Lévy hypotheses (started at
zero).**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous local martingales on `ℱ`
with `M i 0 = 0` almost surely and cross-brackets `M i t * M j t - δ_{ij} c_i t` local
martingales (`c : ι → ℝ≥0`), then the coordinate processes `i ↦ M i` are mutually independent. -/
theorem iIndepFun_of_locally_martingale [IsProbabilityMeasure P] {ι : Type*} [DecidableEq ι]
    {M : ι → ℝ≥0 → Ω → ℝ} {c : ι → ℝ≥0}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - if i = j then (c i : ℝ) * (t : ℝ) else 0) P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0) (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    iIndepFun (fun i ω t ↦ M i t ω) P := by
  obtain ⟨Y, _, hYM, hYc, hYl, _, hQY⟩ :=
    exists_isStronglyPredictable_indist_prod_sub_initialValue_sub
      (A := fun i j t _ ↦ (if i = j then (c i : ℝ) else 0) * (t : ℝ)) hM hQ
      (fun _ _ ↦ (continuous_const.mul NNReal.continuous_coe).isStronglyPredictable_fst) hcont
      (fun i j ↦ (h0 i).mp ((h0 j).mono fun _ h0j h0i _ ↦ by simp [h0i, h0j]))
  exact (iIndepFun_sub_initialValue_of_locally_martingale hYl
    (fun i j ↦ by simpa only [ite_mul, zero_mul] using hQY i j) hYc).process_congr fun i t ↦
    (h0 i).mp <| (hYM i).mono fun _ hω h0ω ↦ by simp [hω t, hω 0, h0ω]

/-- **Predictable vector Brownian version under bare native locality (coordinatewise).**
Without assuming literal adaptation of `M`, if `M : ι → ℝ≥0 → Ω → ℝ` is a family of
almost-surely continuous local martingales on `ℱ` with `M i 0 = 0` almost surely and
`M i t * M j t - δ_{ij} t` a local martingale for all `i, j`, then `M` admits a family `W` that
is coordinatewise strongly predictable (`∀ i, IsStronglyPredictable ℱ (W i)`) and
coordinatewise indistinguishable (`∀ i, W i ≡ᵐ[P] M i`), is a coordinate vector Brownian motion
(`IsBrownianVector W P`), has coordinates that are filtered pre-Brownian motions relative to `ℱ`,
and has vector increments independent of `ℱ s`.

For countable `ι`, see
`exists_isStronglyPredictable_indist_pi_isBrownianVector_of_locally_martingale`
for a jointly predictable `Pi`-valued version agreeing with `M` outside a single common null set. -/
theorem exists_isStronglyPredictable_indist_isBrownianVector_of_locally_martingale
    [IsProbabilityMeasure P] {ι : Type*} [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - if i = j then (t : ℝ) else 0) P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0) (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    ∃ W : ι → ℝ≥0 → Ω → ℝ, (∀ i, IsStronglyPredictable ℱ (W i)) ∧ (∀ i, W i ≡ᵐ[P] M i) ∧
      IsBrownianVector W P ∧ (∀ i, IsFilteredPreBrownianReal ℱ (W i) P) ∧
      (∀ s t, s ≤ t → Indep (.comap (fun ω i ↦ W i t ω - W i s ω) inferInstance) (ℱ s) P) := by
  obtain ⟨W, hWp, hWM, hWc, hWl, _, hQW⟩ :=
    exists_isStronglyPredictable_indist_prod_sub_initialValue_sub
      (A := fun i j t _ ↦ (if i = j then (1 : ℝ) else 0) * (t : ℝ)) hM hQ
      (fun _ _ ↦ (continuous_const.mul NNReal.continuous_coe).isStronglyPredictable_fst) hcont
      (fun i j ↦ (h0 i).mp ((h0 j).mono fun _ h0j h0i _ ↦ by simp [h0i, h0j]))
  have hW0 i : ∀ᵐ ω ∂P, W i 0 ω = 0 := (h0 i).mp <| (hWM i).mono fun _ heq h0ω ↦ by rw [heq 0, h0ω]
  have hWa i := (hWp i).isStronglyProgressive.stronglyAdapted.adapted
  have hFB i : IsFilteredPreBrownianReal ℱ (W i) P :=
    (Locally.isFilteredPreBrownianReal_sub_initialValue (hWl i)
      (by simpa only [sq, ↓reduceIte, one_mul] using hQW i i) (hWc i) (hWa i)).congr (hWa i)
      fun _ ↦ (hW0 i).mono fun _ h0ω ↦ by simp [h0ω]
  have hWind : iIndepFun (fun i ω t ↦ W i t ω) P :=
    (iIndepFun_sub_initialValue_of_locally_martingale (c := fun _ ↦ 1) hWl
      (fun i j ↦ by simpa only [NNReal.coe_one, one_mul, ite_mul, zero_mul] using hQW i j)
      hWc).process_congr fun i _ ↦ (hW0 i).mono fun _ h0ω ↦ by simp [h0ω]
  exact ⟨W, hWp, hWM, .of_isBrownianReal (fun i ↦ ⟨(hFB i).toIsPreBrownianReal, hWc i⟩) hWind,
    hFB, fun _ _ hst ↦ indep_comap_sub_pi_of_locally_martingale hWl hQW hWc hst⟩

/-- **Jointly predictable vector Brownian version for countable index types.**
On a countable index type `ι`, if `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous
local martingales on `ℱ` with `M i 0 = 0` almost surely and `M i t * M j t - δ_{ij} t` a local
martingale for all `i, j`, then `M` admits a jointly strongly predictable `Pi`-valued version
`W : ℝ≥0 → Ω → (ι → ℝ)` indistinguishable from `fun t ω i ↦ M i t ω` outside a single common
null set, whose coordinate processes `(i, t, ω) ↦ W t ω i` form a coordinate vector Brownian
motion (`IsBrownianVector`), are filtered pre-Brownian motions relative to `ℱ`, and have
vector increments independent of `ℱ s`. -/
theorem exists_isStronglyPredictable_indist_pi_isBrownianVector_of_locally_martingale
    [IsProbabilityMeasure P] {ι : Type*} [Countable ι] [DecidableEq ι]
    {M : ι → ℝ≥0 → Ω → ℝ} (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - if i = j then (t : ℝ) else 0) P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0) (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    ∃ W : ℝ≥0 → Ω → (ι → ℝ),
      IsStronglyPredictable ℱ W ∧ W ≡ᵐ[P] (fun t ω i ↦ M i t ω) ∧
      IsBrownianVector (fun i t ω ↦ W t ω i) P ∧
      (∀ i, IsFilteredPreBrownianReal ℱ (fun t ω ↦ W t ω i) P) ∧
      (∀ s t, s ≤ t → Indep (.comap (fun ω i ↦ W t ω i - W s ω i) inferInstance) (ℱ s) P) := by
  obtain ⟨W, hWp, hWM, hBW, hFB, hind⟩ :=
    exists_isStronglyPredictable_indist_isBrownianVector_of_locally_martingale hM hQ h0 hcont
  refine ⟨fun t ω i ↦ W i t ω, ?_, ?_, hBW, hFB, hind⟩
  · exact (@measurable_pi_iff (ℝ≥0 × Ω) ι (fun _ ↦ ℝ) ℱ.predictable _ _ |>.2
      fun i ↦ (hWp i).measurable).stronglyMeasurable
  · exact (ae_all_iff.2 hWM).mono fun ω hω t ↦ funext fun i ↦ hω i t

/-- **Vector Lévy characterization (law form, started at zero, no literal adaptation).**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous local martingales on `ℱ` with
`M i 0 = 0` almost surely and cross-brackets `M i t * M j t - δ_{ij} t` local martingales for all
`i, j`, then `M` is a coordinate vector Brownian motion (`IsBrownianVector M P`). -/
theorem isBrownianVector_of_locally_martingale [IsProbabilityMeasure P] {ι : Type*}
    [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - if i = j then (t : ℝ) else 0) P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0) (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    IsBrownianVector M P :=
  let ⟨_, _, hWM, hBW, _, _⟩ :=
    exists_isStronglyPredictable_indist_isBrownianVector_of_locally_martingale hM hQ h0 hcont
  hBW.congr_indist hWM

/-- **Filtered vector Brownian-law corollary.**
If `B : ι → ℝ≥0 → Ω → ℝ` is a family of mutually independent real Brownian motions that
are adapted local martingales on `ℱ`, then for every `s ≤ t` the vector increment
`ω ↦ (B i t ω - B i s ω)_i` is independent of `ℱ s`. -/
theorem indep_comap_sub_pi_of_iIndepFun_isBrownianReal_locally_martingale
    {ι : Type*} {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t ↦ B i t ω) P) (hA : ∀ i, Adapted ℱ (B i))
    (hloc : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (B i) P) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (.comap (fun ω i ↦ B i t ω - B i s ω) inferInstance) (ℱ s) P := by
  classical
  have := hind.isProbabilityMeasure; let C : ι → ι → ℝ := fun i j ↦ if i = j then 1 else 0
  refine indep_comap_sub_pi_of_locally_martingale (C := C) hloc (fun i j ↦ ?_)
    (fun i ↦ (hB i).cont) hst
  have hsm : StronglyAdapted ℱ
      (fun u ω ↦ B i u ω * B j u ω - B i 0 ω * B j 0 ω - C i j * (u : ℝ)) := fun u ↦
    ((((hA i u).mul (hA j u)).sub (((hA i 0).mul (hA j 0)).mono
      (ℱ.mono bot_le) le_rfl)).sub measurable_const).stronglyMeasurable
  have h0ae : ∀ᵐ ω ∂P, B i 0 ω * B j 0 ω = 0 :=
    (hB i).eval_zero_ae_eq_zero.mono fun ω hω ↦ by simp [hω]
  refine Locally.of_prop ?_; by_cases hij : i = j
  · subst hij; exact ((hB i).isFilteredPreBrownianReal_of_locally_martingale (hA i)
      (hloc i)).martingale_sq_sub.congr hsm fun _ ↦ h0ae.mono fun _ h0ω ↦ by simp [C, sq, h0ω]
  · exact ((hB i).martingale_mul_of_indepFun (hB j) (hind.indepFun hij) (hA i) (hA j) (hloc i)
      (hloc j)).congr hsm fun _ ↦ h0ae.mono fun _ h0ω ↦ by simp [C, hij, h0ω]

/-- **Vector Lévy characterization for adapted continuous local martingales.**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of adapted, almost-surely continuous local martingales on `ℱ`
with `M i 0 = 0` almost surely and cross-brackets `M i t * M j t - δ_{ij} t` local martingales
for all `i, j`, then `M` is a coordinate vector Brownian motion (`IsBrownianVector M P`), each
coordinate `M i` is a filtered pre-Brownian motion relative to `ℱ`, and every vector increment
`ω ↦ (M i t ω - M i s ω)_i` (`s ≤ t`) is independent of `ℱ s`. -/
theorem isBrownianVector_and_isFilteredPreBrownianReal_of_locally_martingale
    [IsProbabilityMeasure P] {ι : Type*} [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - if i = j then (t : ℝ) else 0) P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0) (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (hA : ∀ i, Adapted ℱ (M i)) :
    IsBrownianVector M P ∧ (∀ i, IsFilteredPreBrownianReal ℱ (M i) P) ∧
      (∀ s t, s ≤ t → Indep (.comap (fun ω i ↦ M i t ω - M i s ω) inferInstance) (ℱ s) P) := by
  obtain ⟨W, _, hWM, hBW, hFB, hind⟩ :=
    exists_isStronglyPredictable_indist_isBrownianVector_of_locally_martingale hM hQ h0 hcont
  refine ⟨hBW.congr_indist hWM, fun i ↦ (hFB i).congr (hA i) fun t ↦ (hWM i).mono fun _ hω ↦ hω t,
    fun s t hst ↦ ?_⟩
  have h1 : @IndepFun Ω (ι → ℝ) Ω mΩ MeasurableSpace.pi (ℱ s)
      (fun ω i ↦ W i t ω - W i s ω) id P := by
    simpa only [IndepFun_iff_Indep, @MeasurableSpace.comap_id _ (ℱ s)] using hind s t hst
  have h2 := @IndepFun.process_congr_left ι Ω mΩ P (fun _ ↦ ℝ) Ω _ (ℱ s)
    (fun i ω ↦ W i t ω - W i s ω) (fun i ω ↦ M i t ω - M i s ω) id h1
    (fun i ↦ (hWM i).mono fun _ hω ↦ by simp [hω t, hω s])
  simpa only [IndepFun_iff_Indep, @MeasurableSpace.comap_id _ (ℱ s)] using h2

end TauCeti.Probability
