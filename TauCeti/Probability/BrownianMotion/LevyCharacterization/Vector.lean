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
public import TauCeti.Probability.Process.Predictable.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.Process.Basic
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Basic
import TauCeti.Probability.BrownianMotion.LevyCharacterization.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Independence.CharacteristicFunction
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Independence.Pi
import TauCeti.Probability.Martingale.Exponential.Local
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.Linear
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.LocalProperty

/-!
# Vector Lévy characterization of Brownian motion

Multivariate Lévy characterization for a family `M : ι → ℝ≥0 → Ω → ℝ` of almost-surely continuous
real local martingales on a raw filtration `ℱ` with local-martingale cross-brackets
`M i t * M j t - M i 0 * M j 0 - C i j * t`: Cramér–Wold characteristic-function factorization,
joint increment independence from `ℱ s`, product Gaussian increment laws, global pathwise
coordinate independence, strongly predictable indistinguishable vector Brownian versions, and the
converse cross-product martingale (`ProbabilityTheory.IsBrownianReal.martingale_mul_of_indepFun`)
and vector increment independence theorems for independent Brownian local martingales.

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

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

private lemma isStronglyPredictable_prod_sub_zero_sub_linear {U V : ℝ≥0 → Ω → ℝ}
    (hU : IsStronglyPredictable ℱ U) (hV : IsStronglyPredictable ℱ V) (c : ℝ) :
    IsStronglyPredictable ℱ (fun t ω ↦ U t ω * V t ω - U 0 ω * V 0 ω - c * (t : ℝ)) := by
  convert (hU.mul hV).add (StronglyAdapted.isStronglyPredictable_of_continuous (fun t ↦
    ((((hU.isStronglyProgressive.stronglyAdapted 0).mul
      (hV.isStronglyProgressive.stronglyAdapted 0)).mono (ℱ.mono bot_le)).neg).sub
      (stronglyMeasurable_const (b := c * (t : ℝ)))) fun _ ↦ by fun_prop) using 1
  ext _ _; simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]; ring

private lemma exists_predictable_rep {ι : Type*} {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    {Q : ι → ι → ℝ≥0 → Ω → ℝ} (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (Q i j) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (hQM : ∀ i j, ∀ᵐ ω ∂P, ∀ t,
      M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ) = Q i j t ω) :
    ∃ Y : ι → ℝ≥0 → Ω → ℝ, (∀ i, IsStronglyPredictable ℱ (Y i)) ∧ (∀ i, Y i ≡ᵐ[P] M i) ∧
      (∀ i, ∀ᵐ ω ∂P, Continuous (Y i · ω)) ∧ (∀ i, Locally (fun U ↦ Martingale U ℱ P) ℱ (Y i) P) ∧
      (∀ i j, Locally (fun U ↦ Martingale U ℱ P) ℱ
        (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω - C i j * (t : ℝ)) P) := by
  choose Y hYp hYM hYl using fun i ↦
    (hM i).exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      ((hcont i).mono fun _ h ↦ h.isLeftContinuous)
  exact ⟨Y, hYp, hYM,
    fun i ↦ (hcont i).mp <| (hYM i).mono fun _ heq hω ↦ by simpa only [funext heq] using hω,
    hYl, fun i j ↦ (isStronglyPredictable_prod_sub_zero_sub_linear (hYp i) (hYp j)
      (C i j)).isStronglyProgressive.locally_martingale_of_indist (hQ i j) <| (hYM i).mp <|
      (hYM j).mp <| (hQM i j).mono fun _ hq hj hi t ↦ by simpa [hi t, hj t, hi 0, hj 0] using
        (hq t).symm⟩

private lemma fin_eq_sum_increments {m : ℕ} {f : Fin (m + 1) → ℝ} (hf0 : f 0 = 0)
    (k : Fin (m + 1)) :
    f k = ∑ j ∈ Finset.univ.filter (fun j : Fin m ↦ j.val < k.val), (f j.succ - f j.castSucc) := by
  induction k using Fin.induction with
  | zero => simp [hf0]
  | succ k ih =>
    rw [show Finset.univ.filter (fun j : Fin m ↦ j.val < k.succ.val) =
        insert k (Finset.univ.filter (fun j : Fin m ↦ j.val < k.castSucc.val)) by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_iff, le_iff_lt_or_eq, Fin.ext_iff]; tauto,
      Finset.sum_insert (by simp), ← ih]; ring

private lemma exp_inner_toLp_I {κ : Type*} [Fintype κ] (x : κ → ℝ) (v : EuclideanSpace ℝ κ) :
    exp ((⟪MeasurableEquiv.toLp 2 (κ → ℝ) x, v⟫ : ℂ) * I) = exp (I * ∑ i, v i * x i) := by
  simp only [MeasurableEquiv.toLp_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  congr 1; push_cast; ring

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
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQY⟩ :=
    exists_predictable_rep hM hQ hcont (fun _ _ ↦ ae_of_all P fun _ _ ↦ rfl)
  -- Form the scalar linear combination `∑ i, v i * Y i` and its compensated quadratic bracket.
  have hYv_l := Finset.locally_martingale_sum (Finset.univ : Finset ι)
    (fun i _ ↦ by simpa only [smul_eq_mul] using (hYl i).martingale_smul (v i))
    (fun i _ ↦ ((hYp i).const_mul (v i)).isStronglyProgressive)
    (fun i _ ↦ (hYc i).mono fun _ h ↦ (continuous_const.mul h).isRightContinuous)
  have hQsum := Finset.locally_martingale_sum (Finset.univ : Finset (ι × ι))
    (fun p _ ↦ by simpa only [smul_eq_mul] using (hQY p.1 p.2).martingale_smul (v p.1 * v p.2))
    (fun p _ ↦ ((isStronglyPredictable_prod_sub_zero_sub_linear (hYp p.1) (hYp p.2)
      (C p.1 p.2)).const_mul (v p.1 * v p.2)).isStronglyProgressive)
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
        simp only [Complex.ofReal_one, mul_one, ← Complex.ofReal_sub, ← Finset.sum_sub_distrib]
        congr 3; exact Finset.sum_congr rfl fun i _ ↦ by rw [hω i t, hω i s, mul_sub]),
    Locally.setIntegral_exp_I_mul_sub hYv_l (hQeq ▸ hQsum)
      ((ae_all_iff.2 hYc).mono fun _ h ↦ by fun_prop) 1 hst hA, one_pow, one_mul]

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
        let e : (S → ℝ) ≃ᵐ EuclideanSpace ℝ S := MeasurableEquiv.toLp 2 (S → ℝ)
        rw [← e.measurableEmbedding.comap_eq, MeasurableSpace.comap_comp]
        refine indep_comap_of_setIntegral_exp_inner_I (ℱ.le s)
          (e.measurable.comp_aemeasurable (aemeasurable_pi_iff.2 fun i ↦ hmeas i))
          (φ := fun v : EuclideanSpace ℝ S ↦
            exp (-((∑ i : S, ∑ j : S, v i * v j * C i j) * ((t : ℝ) - s) / 2 : ℝ))) fun v _ hA ↦ by
          simp_rw [e, Function.comp_apply, exp_inner_toLp_I]
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
    (fun i j ↦ by simpa only [ite_mul, zero_mul] using hQ i j) hcont
    (fun i ↦ v i) hst MeasurableSet.univ
  simp only [Measure.restrict_univ, measure_univ, ENNReal.toReal_one, Complex.ofReal_one,
    one_mul] at hset
  let e := MeasurableEquiv.toLp 2 (ι → ℝ)
  rw [← MeasurableEquiv.coe_toLp (p := 2) (X := ι → ℝ),
    e.measurable.aemeasurable.map_map_of_aemeasurable hX,
    charFun_map_eq_integral (e.measurable.comp_aemeasurable hX) v]
  simp_rw [e, Function.comp_apply, exp_inner_toLp_I, hset, charFun_gaussianReal, ← Complex.exp_sum]
  congr 1; simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    NNReal.coe_mul, NNReal.coe_sub hst, Complex.ofReal_zero, zero_mul, zero_sub,
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
  have hm : ∀ i t, Measurable[ℱ t] (Y i t) :=
    fun i t ↦ ((hYp i).isStronglyProgressive.stronglyAdapted t).measurable
  have hV_adapt : Adapted ℱ (fun t ω i ↦ Y i t ω - Y i 0 ω) := fun t ↦
    @measurable_pi_iff _ _ _ (ℱ t) _ _ |>.2 fun i ↦
      (hm i t).sub ((hm i 0).mono (ℱ.mono bot_le) le_rfl)
  -- Swap row independence (across grid steps) and column independence (across coordinates `S`).
  have hrow := ((hV_adapt.hasIndepIncrements fun _ _ hst ↦ by
      simpa only [Pi.sub_def, sub_sub_sub_cancel_right] using
        indep_comap_sub_pi_of_locally_martingale hYl hQY hYc hst) m g hg).comp
    (fun _ (f : ι → ℝ) (i : S) ↦ f i) (fun _ ↦ measurable_pi_iff.2 fun i ↦ measurable_pi_apply i.1)
  refine iIndepFun.swap
    (by simpa only [Function.comp_def, Pi.sub_apply, sub_sub_sub_cancel_right] using hrow)
    (fun k ↦ (iIndepFun_iff_hasLaw_pi_pi fun i : S ↦ Locally.hasLaw_sub_gaussianReal (hYl i)
        (by simpa only [↓reduceIte, sq] using hQY i i) (hYc i) (hg (Fin.castSucc_le_succ k))).2
      (hasLaw_sub_pi_gaussianReal_of_locally_martingale (M := fun i : S ↦ Y i)
        (c := fun i : S ↦ c i) (fun i ↦ hYl i)
        (fun i j ↦ by simpa only [Subtype.ext_iff, ite_mul, zero_mul] using hQY i.1 j.1)
        (fun i ↦ hYc i) (hg (Fin.castSucc_le_succ k))))
    (fun k i ↦ (((hm i (g k.succ)).mono (ℱ.le _) le_rfl).sub
      ((hm i (g k.castSucc)).mono (ℱ.le _) le_rfl)).aemeasurable)

/-- **Global pathwise coordinate independence under orthogonal vector Lévy hypotheses (arbitrary
start).**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets `M i t * M j t - M i 0 * M j 0 - δ_{ij} c_i t` are local martingales
(`c : ι → ℝ≥0`), then the centered coordinate processes `i ↦ (t ↦ M i t - M i 0)` are mutually
independent as random paths `Ω → (ℝ≥0 → ℝ)`. -/
theorem iIndepFun_sub_zero_of_locally_martingale [IsProbabilityMeasure P] {ι : Type*}
    [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ} {c : ι → ℝ≥0}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω -
        (if i = j then (c i : ℝ) * (t : ℝ) else 0)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    iIndepFun (fun i ω t ↦ M i t ω - M i 0 ω) P := by
  -- Pass to predictable versions `Y` and reduce path independence to finite grids `T`.
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQY⟩ := exists_predictable_rep
    (C := fun i j ↦ if i = j then (c i : ℝ) else 0) hM hQ hcont
    (fun _ _ ↦ ae_of_all P fun _ _ ↦ by simp)
  have hYm i t : Measurable (Y i t) :=
    ((hYp i).isStronglyProgressive.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl
  refine (iIndepFun.iIndepFun_process (fun i t ↦ (hYm i t).sub (hYm i 0))
    fun S J ↦ ?_).process_congr fun i t ↦ (hYM i).mono fun _ hω ↦ by simp [hω t, hω 0]
  let T : Finset ℝ≥0 := insert 0 (Finset.univ.biUnion J)
  have h0T : (0 : ℝ≥0) ∈ T := Finset.mem_insert_self 0 _
  let e : Fin (T.card - 1 + 1) ≃o T :=
    T.orderIsoOfFin (Nat.sub_add_cancel (Finset.card_pos.2 ⟨0, h0T⟩)).symm
  -- Reconstruct each centered coordinate evaluation as a partial sum of grid increments.
  let idx (i : S) (t : J i) : Fin (T.card - 1 + 1) :=
    e.symm ⟨t.1, Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, t.2⟩)⟩
  convert (iIndepFun_grid_increments hYp hYc hYl hQY S fun _ _ h ↦ e.monotone h).comp
    (fun (i : S) (d : Fin (T.card - 1) → ℝ) (t : J i) ↦
      ∑ j ∈ Finset.univ.filter (fun j : Fin (T.card - 1) ↦ j.val < (idx i t).val), d j)
    (fun _ ↦ measurable_pi_iff.2 fun _ ↦
      Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _) using 1
  ext i ω t
  have hg0 : (e 0 : ℝ≥0) = 0 := le_antisymm (Subtype.coe_le_coe.2
    ((e.monotone (Fin.zero_le _)).trans_eq (e.apply_symm_apply ⟨0, h0T⟩))) bot_le
  simpa only [show (e (idx i t) : ℝ≥0) = t.1 from congrArg Subtype.val (e.apply_symm_apply _),
    Function.comp_apply, Pi.sub_apply, sub_sub_sub_cancel_right] using
    fin_eq_sum_increments (f := fun k ↦ Y i (e k) ω - Y i 0 ω) (by simp [hg0]) (idx i t)

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
  obtain ⟨Y, _, hYM, hYc, hYl, hQY⟩ := exists_predictable_rep
    (C := fun i j ↦ if i = j then (c i : ℝ) else 0) hM hQ hcont
    (fun i j ↦ (h0 i).mp ((h0 j).mono fun _ h0j h0i _ ↦ by simp [h0i, h0j]))
  exact (iIndepFun_sub_zero_of_locally_martingale hYl
    (fun i j ↦ by simpa only [ite_mul, zero_mul] using hQY i j) hYc).process_congr fun i t ↦
    (h0 i).mp <| (hYM i).mono fun _ hω h0ω ↦ by simp [hω t, hω 0, h0ω]

/-- **Predictable vector Brownian version under bare native locality.**
Without assuming literal adaptation of `M`, if `M : ι → ℝ≥0 → Ω → ℝ` is a family of
almost-surely continuous local martingales on `ℱ` with `M i 0 = 0` almost surely and
`M i t * M j t - δ_{ij} t` a local martingale for all `i, j`, then `M` admits a strongly
predictable indistinguishable family `W` whose coordinates are mutually independent
filtered Brownian motions relative to `ℱ` with vector increments independent of `ℱ s`. -/
theorem exists_isStronglyPredictable_indist_pi_isFilteredPreBrownianReal_of_locally_martingale
    [IsProbabilityMeasure P] {ι : Type*} [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - if i = j then (t : ℝ) else 0) P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0) (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    ∃ W : ι → ℝ≥0 → Ω → ℝ, (∀ i, IsStronglyPredictable ℱ (W i)) ∧ (∀ i, W i ≡ᵐ[P] M i) ∧
      (∀ i, IsBrownianReal (W i) P) ∧ (∀ i, IsFilteredPreBrownianReal ℱ (W i) P) ∧
      iIndepFun (fun i ω t ↦ W i t ω) P ∧
      (∀ s t, s ≤ t → Indep (.comap (fun ω i ↦ W i t ω - W i s ω) inferInstance) (ℱ s) P) := by
  obtain ⟨W, hWp, hWM, hWc, hWl, hQW⟩ := exists_predictable_rep
    (C := fun i j ↦ if i = j then (1 : ℝ) else 0) hM hQ hcont
    (fun i j ↦ (h0 i).mp ((h0 j).mono fun _ h0j h0i _ ↦ by simp [h0i, h0j]))
  have hW0 i : ∀ᵐ ω ∂P, W i 0 ω = 0 := (h0 i).mp <| (hWM i).mono fun _ heq h0ω ↦ by rw [heq 0, h0ω]
  have hWa i := (hWp i).isStronglyProgressive.stronglyAdapted.adapted
  have hFB i : IsFilteredPreBrownianReal ℱ (W i) P :=
    (Locally.isFilteredPreBrownianReal_sub_zero (hWl i)
      (by simpa only [sq, ↓reduceIte, one_mul] using hQW i i) (hWc i) (hWa i)).congr (hWa i)
      fun _ ↦ (hW0 i).mono fun _ h0ω ↦ by simp [h0ω]
  refine ⟨W, hWp, hWM, fun i ↦ ⟨(hFB i).toIsPreBrownianReal, hWc i⟩, hFB,
    (iIndepFun_sub_zero_of_locally_martingale (c := fun _ ↦ 1) hWl
      (fun i j ↦ by simpa only [NNReal.coe_one, one_mul, ite_mul, zero_mul] using hQW i j)
      hWc).process_congr fun i _ ↦ (hW0 i).mono fun _ h0ω ↦ by simp [h0ω],
    fun _ _ hst ↦ indep_comap_sub_pi_of_locally_martingale hWl hQW hWc hst⟩

end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

private lemma isBrownianReal_normalized_add {B₁ B₂ : ℝ≥0 → Ω → ℝ}
    (hB₁ : IsBrownianReal B₁ P) (hB₂ : IsBrownianReal B₂ P)
    (hind : IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) P) :
    IsBrownianReal (fun t ω ↦ (1 / Real.sqrt 2) * (B₁ t ω + B₂ t ω)) P := by
  have : IsProbabilityMeasure P := (hB₁.hasLaw_eval 0).isProbabilityMeasure
  -- Verify one-dimensional Gaussian marginals and independent increments via `iIndepFun.swap`.
  refine ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ ?_) (fun n g hg ↦ ?_),
    hB₁.cont.mp (hB₂.cont.mono fun _ h₂ h₁ ↦ continuous_const.mul (h₁.add h₂))⟩
  · have hsum : HasLaw (B₁ t + B₂ t) (gaussianReal 0 (t + t)) P :=
      ⟨(hB₁.hasLaw_eval t).aemeasurable.add (hB₂.hasLaw_eval t).aemeasurable, by
        simpa only [add_zero, Function.comp_def] using gaussianReal_add_gaussianReal_of_indepFun
          (hind.comp (measurable_pi_apply t) (measurable_pi_apply t))
          (hB₁.hasLaw_eval t) (hB₂.hasLaw_eval t)⟩
    simpa only [Pi.add_apply, mul_zero,
      show NNReal.mk ((1 / Real.sqrt 2) ^ 2) (sq_nonneg _) * (t + t) = t by
        ext; push_cast; rw [div_pow, one_pow, Real.sq_sqrt zero_le_two]; ring] using
      gaussianReal_const_mul hsum (1 / Real.sqrt 2)
  · let Δ : Bool → Fin n → Ω → ℝ := fun b k ω ↦
      _root_.cond b (B₂ (g k.succ) ω - B₂ (g k.castSucc) ω) (B₁ (g k.succ) ω - B₁ (g k.castSucc) ω)
    have hm : Measurable (fun (f : ℝ≥0 → ℝ) (k : Fin n) ↦ f (g k.succ) - f (g k.castSucc)) :=
      measurable_pi_iff.2 fun _ ↦ (measurable_pi_apply _).sub (measurable_pi_apply _)
    have hbool : iIndepFun (fun b ω k ↦ Δ b k ω) P := (iIndepFun_iff _ _ _).2 fun s f hf ↦ by
      rcases (by decide : ∀ s : Finset Bool, (s = ∅ ∨ s = {false} ∨ s = {true}) ∨
          s = {false, true}) s with h | rfl
      · rcases h with rfl | rfl | rfl <;> simp
      · rw [Finset.set_biInter_insert, Finset.set_biInter_singleton, Finset.prod_pair (by decide)]
        exact (Indep_iff ..).1 ((IndepFun_iff_Indep ..).1 (hind.comp hm hm)) _ _
          (hf false (by simp)) (hf true (by simp))
    convert (iIndepFun.swap (X := Δ) hbool
      (fun | false => hB₁.hasIndepIncrements n g hg | true => hB₂.hasIndepIncrements n g hg)
      (fun | false, _ => (hB₁.hasLaw_eval _).aemeasurable.sub (hB₁.hasLaw_eval _).aemeasurable
           | true, _ => (hB₂.hasLaw_eval _).aemeasurable.sub (hB₂.hasLaw_eval _).aemeasurable)
      ).comp (fun _ (f : Bool → ℝ) ↦ (1 / Real.sqrt 2) * (f false + f true))
      (fun _ ↦ by fun_prop) using 1
    ext _ _; simp only [Δ, Function.comp_apply, Bool.cond_false, Bool.cond_true]; ring

/-- **Cross-product martingale property for independent Brownian local martingales.**
If `B₁` and `B₂` are independent real Brownian motions that are adapted local martingales on `ℱ`,
then their product `t ↦ B₁ t * B₂ t` is a true `ℱ`-martingale. The proof polarizes via the
Brownian motion `(B₁ + B₂) / √2`. -/
theorem martingale_mul_of_indepFun {B₁ B₂ : ℝ≥0 → Ω → ℝ}
    (hB₁ : IsBrownianReal B₁ P) (hB₂ : IsBrownianReal B₂ P)
    (hind : IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) P)
    (hA₁ : Adapted ℱ B₁) (hA₂ : Adapted ℱ B₂)
    (hloc₁ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B₁ P)
    (hloc₂ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B₂ P) :
    Martingale (fun t ω ↦ B₁ t ω * B₂ t ω) ℱ P := by
  -- Polarize via the Brownian motion `(B₁ + B₂) / √2` and subtract the half-squares.
  have hFB₁ := hB₁.isFilteredPreBrownianReal_of_locally_martingale hA₁ hloc₁
  have hFB₂ := hB₂.isFilteredPreBrownianReal_of_locally_martingale hA₂ hloc₂
  have hFW := (isBrownianReal_normalized_add hB₁ hB₂ hind)
    |>.isFilteredPreBrownianReal_of_locally_martingale
      (fun t ↦ measurable_const.mul ((hA₁ t).add (hA₂ t)))
      (Locally.of_prop (by convert (hFB₁.martingale.add hFB₂.martingale).smul (1 / Real.sqrt 2)))
  convert (hFW.martingale_sq_sub.sub (hFB₁.martingale_sq_sub.smul (1 / 2))).sub
    (hFB₂.martingale_sq_sub.smul (1 / 2)) using 1
  ext t ω; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_pow, div_pow, one_pow,
    Real.sq_sqrt zero_le_two]; ring

end ProbabilityTheory.IsBrownianReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

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
  have h0ae := (hB i).eval_zero_ae_eq_zero.mono fun ω hω ↦ show B i 0 ω * B j 0 ω = 0 by simp [hω]
  refine Locally.of_prop <| by
    by_cases hij : i = j
    · subst hij
      exact ((hB i).isFilteredPreBrownianReal_of_locally_martingale (hA i)
        (hloc i)).martingale_sq_sub.congr hsm fun _ ↦ h0ae.mono fun _ h0ω ↦ by simp [C, sq, h0ω]
    · exact ((hB i).martingale_mul_of_indepFun (hB j) (hind.indepFun hij) (hA i) (hA j) (hloc i)
        (hloc j)).congr hsm fun _ ↦ h0ae.mono fun _ h0ω ↦ by simp [C, hij, h0ω]

end TauCeti.Probability
