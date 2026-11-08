/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.StickBreaking.Basic
public import TauCeti.Probability.Distributions.Dirichlet.Aggregation

/-!
# Finite Dirichlet stick breaking

Successively allocate a fraction of the remaining stick to each coordinate, leaving the
last coordinate as the remainder. Independent Beta fractions with shapes given by a
concentration and its remaining tail construct a Dirichlet vector. Conversely, the ratios
of each coordinate to the remaining mass recover these independent fractions. The empty
family of fractions constructs the one-coordinate Dirichlet law.

## Main results

* `dirichletStickBreaking_castSucc` and `dirichletStickBreaking_last` give the product formulas.
* `dirichletStickRatios_stickBreaking` and `dirichletStickBreaking_stickRatios` give the inverse
  identities, with reconstruction normalizing vectors that do not already sum to one.
* `map_dirichletStickBreaking_pi_betaMeasure` constructs the law from independent fractions.
* `map_dirichletStickRatios_dirichletMeasure` identifies the joint law of the inverse ratios.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace TauCeti.Probability

/-- Allocate successive fractions of a unit stick, retaining the final remainder.
An empty list of fractions gives the single coordinate one. -/
def dirichletStickBreaking : {n : ℕ} → (Fin n → ℝ) → EuclideanSpace ℝ (Fin (n + 1))
  | 0, _ => (EuclideanSpace.equiv _ ℝ).symm fun _ ↦ 1
  | _n + 1, v => (EuclideanSpace.equiv _ ℝ).symm
      (Fin.cons (v 0) (fun i ↦ (1 - v 0) * dirichletStickBreaking (fun j ↦ v j.succ) i))

/-- With no fractions the entire stick is assigned to the sole coordinate. -/
@[simp]
theorem dirichletStickBreaking_nil (v : Fin 0 → ℝ) (i : Fin 1) :
    dirichletStickBreaking v i = 1 := (rfl)

/-- The first coordinate receives the first fraction. -/
@[simp]
theorem dirichletStickBreaking_zero {n : ℕ} (v : Fin (n + 1) → ℝ) :
    dirichletStickBreaking v 0 = v 0 := (rfl)

/-- Subsequent allocations use the remaining stick. -/
@[simp]
theorem dirichletStickBreaking_succ {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    dirichletStickBreaking v i.succ =
      (1 - v 0) * dirichletStickBreaking (fun j ↦ v j.succ) i := (rfl)

/-- Stick breaking first allocates the head fraction and then rescales the tail construction. -/
theorem dirichletStickBreaking_cons {n : ℕ} (v : Fin (n + 1) → ℝ) :
    dirichletStickBreaking v = (EuclideanSpace.equiv _ ℝ).symm
      (Fin.cons (v 0) (fun i ↦ (1 - v 0) * dirichletStickBreaking (fun j ↦ v j.succ) i)) :=
  (rfl)

/-- The finite stick-breaking map is measurable on all real fractions. -/
@[fun_prop]
theorem measurable_dirichletStickBreaking (n : ℕ) :
    Measurable (@dirichletStickBreaking n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp_rw [funext dirichletStickBreaking_cons]
    apply (EuclideanSpace.equiv _ ℝ).symm.continuous.measurable.comp
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact measurable_pi_apply 0
    · exact (measurable_const.sub (measurable_pi_apply 0)).mul
        ((by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ x j)).comp
          (ih.comp (measurable_pi_iff.mpr fun k ↦ measurable_pi_apply k.succ)))

/-- Each nonfinal coordinate is its fraction times all preceding residual fractions. -/
theorem dirichletStickBreaking_castSucc {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    dirichletStickBreaking v i.castSucc = v i * ∏ j with j < i, (1 - v j) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · simp
    · rw [Fin.castSucc_succ, dirichletStickBreaking_succ, ih]
      simp [Finset.prod_filter, Fin.prod_univ_succ, mul_left_comm]

/-- The final coordinate is the stick left after all allocations. -/
theorem dirichletStickBreaking_last {n : ℕ} (v : Fin n → ℝ) :
    dirichletStickBreaking v (Fin.last n) = ∏ j, (1 - v j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fin.succ_last, dirichletStickBreaking_succ, ih, Fin.prod_univ_succ]

/-- The allocations and the final remainder always sum to one. -/
@[simp]
theorem sum_dirichletStickBreaking {n : ℕ} (v : Fin n → ℝ) :
    ∑ i, dirichletStickBreaking v i = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.sum_univ_succ, dirichletStickBreaking_zero, dirichletStickBreaking_succ,
      ← Finset.mul_sum, ih]
    ring

/-- The mass remaining before an allocation is the product of preceding residual fractions. -/
theorem sum_tail_dirichletStickBreaking {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    ∑ j with i.castSucc ≤ j, dirichletStickBreaking v j = ∏ j with j < i, (1 - v j) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · simp
    · calc
        _ = (1 - v 0) * ∑ j with k.castSucc ≤ j,
            dirichletStickBreaking (fun j ↦ v j.succ) j := by
          simp [Finset.sum_filter, Fin.sum_univ_succ, mul_add, Finset.mul_sum, mul_ite]
        _ = _ := by
          rw [ih]
          simp [Finset.prod_filter, Fin.prod_univ_succ]

/-- Recover the successive fractions by dividing each nonfinal coordinate by the mass
remaining at that step. Division is totalized when the remaining mass vanishes. -/
def dirichletStickRatios {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) : Fin n → ℝ :=
  fun i ↦ x i.castSucc / ∑ j with i.castSucc ≤ j, x j

/-- A stick ratio is the coordinate divided by its inclusive tail mass. -/
@[simp]
theorem dirichletStickRatios_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    dirichletStickRatios x i = x i.castSucc / ∑ j with i.castSucc ≤ j, x j := (rfl)

/-- All the stick ratios are jointly measurable, including their zero-denominator branches. -/
@[fun_prop]
theorem measurable_dirichletStickRatios (n : ℕ) :
    Measurable (@dirichletStickRatios n) := by
  apply measurable_pi_iff.mpr
  intro i
  simp only [dirichletStickRatios_apply]
  fun_prop

/-- Ratios recover all fractions when no allocation consumes the entire remaining stick. -/
@[simp]
theorem dirichletStickRatios_stickBreaking {n : ℕ} {v : Fin n → ℝ}
    (hv : ∀ i, v i ≠ 1) : dirichletStickRatios (dirichletStickBreaking v) = v := by
  funext i
  rw [dirichletStickRatios_apply, dirichletStickBreaking_castSucc,
    sum_tail_dirichletStickBreaking, mul_div_cancel_right₀]
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ sub_ne_zero.mpr (hv j).symm

/-- Reconstructing the ratios of a positive vector normalizes that vector to total one. -/
theorem dirichletStickBreaking_stickRatios {n : ℕ}
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : ∀ i, 0 < x i) :
    dirichletStickBreaking (dirichletStickRatios x) = dirichletNormalize x := by
  induction n with
  | zero =>
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [dirichletNormalize_apply, (hx 0).ne']
  | succ n ih =>
    let y : EuclideanSpace ℝ (Fin (n + 1)) :=
      (EuclideanSpace.equiv _ ℝ).symm fun j ↦ x j.succ
    have ht : (fun i : Fin n ↦ dirichletStickRatios x i.succ) = dirichletStickRatios y := by
      funext i
      simp [dirichletStickRatios_apply, y, Finset.sum_filter, Fin.sum_univ_succ]
    have hs : ∑ j, x j = x 0 + ∑ j, y j := Fin.sum_univ_succ _
    have hS : (∑ j, x j) ≠ 0 := (Finset.sum_pos (fun i _ ↦ hx i)
      Finset.univ_nonempty).ne'
    have hT : (∑ j, y j) ≠ 0 := (Finset.sum_pos (fun i _ ↦ hx i.succ)
      Finset.univ_nonempty).ne'
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [dirichletNormalize_apply]
    · rw [dirichletStickBreaking_succ, ht, ih (fun j ↦ hx j.succ)]
      have hy (k : Fin (n + 1)) : y k = x k.succ := by simp [y]
      simp only [hy] at hT hs
      simp [dirichletNormalize_apply, dirichletStickRatios_apply, hy]
      field_simp [hS, hT]
      rw [hs]
      ring

private theorem map_fin_insert {n : ℕ} {a : Fin (n + 2) → ℝ} (ha : ∀ i, 0 < a i) :
    ((betaMeasure (a 0) (∑ i : Fin (n + 1), a i.succ)).prod
      (dirichletMeasure fun i : Fin (n + 1) ↦ a i.succ)).map
        (fun z ↦ (EuclideanSpace.equiv _ ℝ).symm
          (Fin.cons z.1 (fun i ↦ (1 - z.1) * z.2 i))) = dirichletMeasure a := by
  let e := finSuccEquiv (n + 1)
  have ha' : ∀ i, 0 < a (e.symm i) := fun i ↦ ha _
  have h := map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure ha'
  have hr := map_reindex_dirichletMeasure (e := e.symm) ha'
  rw [← h, Measure.map_map (by fun_prop) measurable_dirichletStickInsert] at hr
  have hf : (fun z : ℝ × EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.equiv _ ℝ).symm
        (fun j ↦ dirichletStickInsert z (e j))) =
      (fun z ↦ (EuclideanSpace.equiv _ ℝ).symm
        (Fin.cons z.1 (fun i ↦ (1 - z.1) * z.2 i))) := by
    funext z
    ext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp [e]
  simpa only [Function.comp_def, hf, e, Equiv.symm_symm, Equiv.symm_apply_apply,
    finSuccEquiv_symm_none, finSuccEquiv_symm_some] using hr

private theorem tail_shape_pos {n : ℕ} {a : Fin (n + 1) → ℝ}
    (ha : ∀ i, 0 < a i) (i : Fin n) :
    0 < ∑ j with i.castSucc < j, a j := by
  apply Finset.sum_pos (fun j _ ↦ ha j)
  exact ⟨i.succ, by simp⟩

/-- Independent Beta fractions, with second shapes equal to the remaining concentration,
construct the Dirichlet law. The case of one coordinate uses an empty product of laws. -/
theorem map_dirichletStickBreaking_pi_betaMeasure {n : ℕ} {a : Fin (n + 1) → ℝ}
    (ha : ∀ i, 0 < a i) :
    (Measure.pi fun i : Fin n ↦
      betaMeasure (a i.castSucc) (∑ j with i.castSucc < j, a j)).map
        dirichletStickBreaking = dirichletMeasure a := by
  induction n with
  | zero =>
    rw [dirichletMeasure_eq_dirac_of_card_eq_one ha (by simp)]
    have hf : @dirichletStickBreaking 0 =
        (fun _ ↦ (EuclideanSpace.equiv (Fin 1) ℝ).symm fun _ ↦ 1) := by
      funext v
      ext i
      simp
    rw [hf, Measure.map_const]
    simp
  | succ n ih =>
    -- Separate the first Beta fraction, construct the tail by induction, and insert it.
    let μ (i : Fin (n + 1)) :=
      betaMeasure (a i.castSucc) (∑ j with i.castSucc < j, a j)
    let _ (i : Fin (n + 1)) : IsProbabilityMeasure (μ i) :=
      isProbabilityMeasureBeta (ha _) (tail_shape_pos ha i)
    have hzero : μ 0 = betaMeasure (a 0) (∑ j : Fin (n + 1), a j.succ) := by
      simp [μ, Finset.sum_filter, Fin.sum_univ_succ]
    have htail : (Measure.pi fun i : Fin n ↦ μ i.succ).map dirichletStickBreaking =
        dirichletMeasure (fun j : Fin (n + 1) ↦ a j.succ) := by
      convert ih (fun j ↦ ha j.succ) using 1
      congr 2
      funext i
      simp [μ, Finset.sum_filter, Fin.sum_univ_succ]
    have hsplit : (Measure.pi μ).map (fun v ↦ (v 0, fun i : Fin n ↦ v i.succ)) =
        (μ 0).prod (Measure.pi fun i : Fin n ↦ μ i.succ) := by
      simpa only [MeasurableEquiv.piFinSuccAbove_apply, Fin.succAbove_zero,
        Fin.insertNthEquiv_zero, Fin.tail_def,
        funext (Fin.consEquiv_symm_apply (fun _ : Fin (n + 1) ↦ ℝ))] using
          (measurePreserving_piFinSuccAbove μ 0).map_eq
    have hp := Measure.map_prod_map (μ 0) (Measure.pi fun i : Fin n ↦ μ i.succ)
      measurable_id (measurable_dirichletStickBreaking n)
    rw [Measure.map_id, htail] at hp
    rw [← map_fin_insert ha, ← hzero, hp, ← hsplit,
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    apply congrArg (fun f ↦ (Measure.pi μ).map f)
    funext v
    exact dirichletStickBreaking_cons v

/-- The successive ratios of a Dirichlet vector have the product of the specified Beta laws.
In particular, this identifies their full joint law rather than only their marginals. -/
theorem map_dirichletStickRatios_dirichletMeasure {n : ℕ} {a : Fin (n + 1) → ℝ}
    (ha : ∀ i, 0 < a i) :
    (dirichletMeasure a).map dirichletStickRatios =
      Measure.pi fun i : Fin n ↦
        betaMeasure (a i.castSucc) (∑ j with i.castSucc < j, a j) := by
  let μ (i : Fin n) := betaMeasure (a i.castSucc) (∑ j with i.castSucc < j, a j)
  let _ (i : Fin n) : IsProbabilityMeasure (μ i) :=
    isProbabilityMeasureBeta (ha _) (tail_shape_pos ha i)
  rw [← map_dirichletStickBreaking_pi_betaMeasure ha,
    Measure.map_map (measurable_dirichletStickRatios n) (measurable_dirichletStickBreaking n)]
  calc
    _ = (Measure.pi μ).map id := by
      apply Measure.map_congr
      have hv : ∀ᵐ v ∂Measure.pi μ, ∀ i, v i ≠ 1 := by
        apply ae_all_iff.mpr
        intro i
        filter_upwards [(measurePreserving_eval μ i).quasiMeasurePreserving.ae
          (ae_mem_Ioo_betaMeasure (a i.castSucc) (∑ j with i.castSucc < j, a j))] with v hv
        exact hv.2.ne
      filter_upwards [hv] with v hv
      exact dirichletStickRatios_stickBreaking hv
    _ = _ := Measure.map_id

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {a : Fin (n + 1) → ℝ}

/-- Independent Beta fractions construct a Dirichlet random vector by finite stick breaking. -/
theorem iIndepFun.hasLaw_dirichletStickBreaking {V : Fin n → Ω → ℝ}
    (hV : iIndepFun V P) (ha : ∀ i, 0 < a i)
    (h : ∀ i, HasLaw (V i) (betaMeasure (a i.castSucc)
      (∑ j with i.castSucc < j, a j)) P) :
    HasLaw (fun ω ↦ dirichletStickBreaking (fun i ↦ V i ω)) (dirichletMeasure a) P := by
  exact (HasLaw.mk (measurable_dirichletStickBreaking n).aemeasurable
    (map_dirichletStickBreaking_pi_betaMeasure ha)).comp (hV.hasLaw_pi h)

/-- The ratios of a Dirichlet random vector have the joint product Beta law. -/
theorem HasLaw.dirichletStickRatios {X : Ω → EuclideanSpace ℝ (Fin (n + 1))}
    (hX : HasLaw X (dirichletMeasure a) P) (ha : ∀ i, 0 < a i) :
    HasLaw (fun ω ↦ dirichletStickRatios (X ω))
      (Measure.pi fun i : Fin n ↦ betaMeasure (a i.castSucc)
        (∑ j with i.castSucc < j, a j)) P :=
  (HasLaw.mk (measurable_dirichletStickRatios n).aemeasurable
    (map_dirichletStickRatios_dirichletMeasure ha)).comp hX

/-- The successive remaining-mass ratios of a Dirichlet vector are jointly independent. -/
theorem HasLaw.iIndepFun_dirichletStickRatios {X : Ω → EuclideanSpace ℝ (Fin (n + 1))}
    (hX : HasLaw X (dirichletMeasure a) P) (ha : ∀ i, 0 < a i) :
    iIndepFun (fun i : Fin n ↦ fun ω ↦ TauCeti.Probability.dirichletStickRatios (X ω) i) P := by
  let μ (i : Fin n) := betaMeasure (a i.castSucc) (∑ j with i.castSucc < j, a j)
  let _ (i : Fin n) : IsProbabilityMeasure (μ i) :=
    isProbabilityMeasureBeta (ha _) (Finset.sum_pos (fun j _ ↦ ha j) ⟨i.succ, by simp⟩)
  let _ := isProbabilityMeasure_dirichletMeasure ha
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have h := hX.dirichletStickRatios ha
  apply (iIndepFun_iff_hasLaw_pi_pi (μ := μ) (fun i ↦ ?_)).mpr h
  exact (measurePreserving_eval μ i).hasLaw.comp h

end ProbabilityTheory
