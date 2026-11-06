/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Algebra.Order.BigOperators.BoundedDifferences

/-!
# McDiarmid's bounded-differences inequality

This file proves the moment-generating-function form of McDiarmid's inequality for a measurable
real-valued function on a finite product of identical probability spaces. If changing coordinate
`i` changes the function by at most `c i`, then the centered function is sub-Gaussian with variance
proxy `∑ i, (c i / 2) ^ 2`.

The proof peels off one coordinate at a time. Hoeffding's lemma controls the peeled coordinate,
and the induction hypothesis controls the function obtained by averaging over it.

## Main results

* `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences` gives the result for an arbitrary
  finite index type;
* `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin` specializes it to `Fin n`.

## References

* C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics 141 (1989),
  148–188.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/McDiarmid.lean`. The
  coordinate-peeling proof and constants are adapted from that file.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- A bounded-differences function is bounded once its value at one base point is fixed. -/
private theorem abs_le_sum_add_abs_of_bounded_differences {ι : Type*} [Fintype ι]
    {β : Type*} (c : ι → ℝ) (f : (ι → β) → ℝ)
    (hbd : ∀ (i : ι) (x x' : ι → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (x₀ x : ι → β) : |f x| ≤ (∑ i, c i) + |f x₀| := by
  have h1 := abs_sub_le_of_bounded_differences c f hbd x x₀
  calc
    |f x| = |(f x - f x₀) + f x₀| := by ring_nf
    _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
    _ ≤ (∑ i, c i) + |f x₀| := by linarith

/-- A measurable bounded-differences function has an integrable centered exponential under any
finite measure on the product. -/
private theorem integrable_exp_mul_sub_of_bounded_differences {ι : Type*} [Finite ι]
    {β : Type*} [MeasurableSpace β] [Nonempty β] {μ : Measure (ι → β)} [IsFiniteMeasure μ]
    (c : ι → ℝ) {f : (ι → β) → ℝ} (hf : AEMeasurable f μ)
    (hbd : ∀ (i : ι) (x x' : ι → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (I t : ℝ) : Integrable (fun x => Real.exp (t * (f x - I))) μ := by
  have : Fintype ι := Fintype.ofFinite ι
  set x₀ : ι → β := fun _ => Classical.arbitrary β
  set K : ℝ := (∑ i, c i) + |f x₀| + |I|
  refine ProbabilityTheory.integrable_exp_mul_of_mem_Icc (a := -K) (b := K) (hf.sub_const I)
    (ae_of_all _ fun x => abs_le.mp ((abs_sub (f x) I).trans ?_))
  linarith [abs_le_sum_add_abs_of_bounded_differences c f hbd x₀ x]

/-- Composing a function on `Fin (n + 1) → β` with `Fin.cons` is measurable on the product of the
first coordinate and the remaining ones. -/
theorem measurable_comp_fin_cons {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ] {n : ℕ}
    {F : (Fin (n + 1) → β) → γ} (hF : Measurable F) :
    Measurable (fun p : β × (Fin n → β) => F (Fin.cons p.1 p.2)) := by
  refine hF.comp (measurable_pi_iff.mpr fun j => ?_)
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero] using measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply i).comp measurable_snd

/-- Integration over the product of `n + 1` copies of a probability space splits into the
integral over the first coordinate inside the integral over the remaining ones. -/
theorem integral_pi_fin_succ_eq_integral_integral_cons {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {n : ℕ} (F : (Fin (n + 1) → β) → ℝ)
    (hF : Integrable (fun p : β × (Fin n → β) => F (Fin.cons p.1 p.2))
      (ν.prod (Measure.pi fun _ : Fin n => ν))) :
    ∫ x, F x ∂Measure.pi (fun _ : Fin (n + 1) => ν) =
      ∫ w, ∫ a, F (Fin.cons a w) ∂ν ∂Measure.pi (fun _ : Fin n => ν) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => β) 0 with he
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
  have hcons : ∀ (a : β) (w : Fin n → β), e.symm (a, w) = Fin.cons a w := by
    intro a w
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [he]
    · intro i
      simp [he]
  have step1 : ∫ x, F x ∂Measure.pi (fun _ : Fin (n + 1) => ν) =
      ∫ p, F (e.symm p) ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) :=
    (mp.symm.integral_comp' F).symm
  rw [step1, integral_prod_symm _ (by simpa only [hcons] using hF)]
  simp_rw [hcons]

/-- A bounded measurable function on `Fin (n + 1) → β`, composed with `Fin.cons`, is integrable
on the product of the first coordinate and the remaining ones. -/
theorem integrable_comp_fin_cons_of_abs_le {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {n : ℕ} {F : (Fin (n + 1) → β) → ℝ} {K : ℝ}
    (hF : Measurable F) (hFb : ∀ x, |F x| ≤ K) :
    Integrable (fun p : β × (Fin n → β) => F (Fin.cons p.1 p.2))
      (ν.prod (Measure.pi fun _ : Fin n => ν)) := by
  refine (integrable_const K).mono' (measurable_comp_fin_cons hF).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  simpa using hFb (Fin.cons p.1 p.2)

/-- Averaging out the first coordinate of a function with bounded differences gives a function
of the remaining coordinates with the same bounded differences. -/
theorem abs_integral_cons_sub_le {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {n : ℕ} {f : (Fin (n + 1) → β) → ℝ}
    {c : Fin (n + 1) → ℝ}
    (hint : ∀ w : Fin n → β, Integrable (fun a => f (Fin.cons a w)) ν)
    (hbd : ∀ (i : Fin (n + 1)) (x x' : Fin (n + 1) → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (i : Fin n) (w w' : Fin n → β) (hww' : ∀ l, l ≠ i → w l = w' l) :
    |(∫ a, f (Fin.cons a w) ∂ν) - ∫ a, f (Fin.cons a w') ∂ν| ≤ c i.succ := by
  have hpt : ∀ a : β, |f (Fin.cons a w) - f (Fin.cons a w')| ≤ c i.succ := by
    intro a
    apply hbd i.succ
    intro j hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
    · simp
    · have hli : l ≠ i := fun h => hj (by rw [h])
      simp only [Fin.cons_succ]
      exact hww' l hli
  rw [← integral_sub (hint w) (hint w')]
  calc
    |∫ a, (f (Fin.cons a w) - f (Fin.cons a w')) ∂ν|
        ≤ ∫ a, |f (Fin.cons a w) - f (Fin.cons a w')| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _a, c i.succ ∂ν := integral_mono ((hint w).sub (hint w')).abs
      (integrable_const (c i.succ)) hpt
    _ = c i.succ := by simp

/-- **Hoeffding's lemma, oscillation form.** If a measurable real function on a probability space
has oscillation at most `C`, then its centered exponential moment is at most
`exp ((C / 2) ^ 2 * t ^ 2 / 2)`. -/
theorem integral_exp_mul_sub_integral_le_of_abs_sub_le {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {X : β → ℝ} (hX : Measurable X) {C : ℝ}
    (hC : 0 ≤ C) (hosc : ∀ a a', |X a - X a'| ≤ C) (t : ℝ) :
    ∫ a, Real.exp (t * (X a - ∫ a', X a' ∂ν)) ∂ν ≤ Real.exp ((C / 2) ^ 2 * t ^ 2 / 2) := by
  have : Nonempty β := nonempty_of_isProbabilityMeasure ν
  set A : ℝ := sInf (Set.range X)
  have hbdd : BddBelow (Set.range X) := by
    refine ⟨X (Classical.arbitrary β) - C, ?_⟩
    rintro _ ⟨a, rfl⟩
    have := hosc (Classical.arbitrary β) a
    rw [abs_sub_le_iff] at this
    linarith [this.1]
  have hmem : ∀ a, X a ∈ Set.Icc A (A + C) := by
    intro a
    refine ⟨csInf_le hbdd ⟨a, rfl⟩, ?_⟩
    have hle : A ≥ X a - C := by
      apply le_csInf (Set.range_nonempty X)
      rintro _ ⟨a', rfl⟩
      have := hosc a a'
      rw [abs_sub_le_iff] at this
      linarith [this.1]
    linarith
  have hml := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := ν)
    hX.aemeasurable (ae_of_all _ hmem)).mgf_le t
  have hexp : ((((‖(A + C) - A‖₊ / 2) ^ 2 : NNReal) : ℝ)) = (C / 2) ^ 2 := by
    rw [add_sub_cancel_left, Real.nnnorm_of_nonneg hC]
    push_cast
    ring
  rw [ProbabilityTheory.mgf, hexp] at hml
  exact hml

/-- A bound on `f` bounds the centered exponential `exp (t * (f x - I))`. -/
theorem abs_exp_mul_sub_le_exp {α : Type*} {f : α → ℝ} {M : ℝ} (hMf : ∀ x, |f x| ≤ M)
    (I t : ℝ) (x : α) : |Real.exp (t * (f x - I))| ≤ Real.exp (|t| * (M + |I|)) := by
  rw [Real.abs_exp]
  apply Real.exp_le_exp.mpr
  calc
    t * (f x - I) ≤ |t * (f x - I)| := le_abs_self _
    _ = |t| * |f x - I| := abs_mul _ _
    _ ≤ |t| * (M + |I|) :=
      mul_le_mul_of_nonneg_left ((abs_sub (f x) I).trans (by linarith [hMf x]))
        (abs_nonneg t)

/-- The peeled-coordinate step of McDiarmid's inequality: Hoeffding's lemma in the first
coordinate, integrated over the remaining coordinates, bounds the centered exponential moment by
a constant times the centered exponential moment of the average over the first coordinate. -/
private theorem integral_integral_exp_cons_le {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {n : ℕ} {f : (Fin (n + 1) → β) → ℝ}
    (hf : Measurable f) {c : Fin (n + 1) → ℝ} (hc0 : 0 ≤ c 0)
    (hbd : ∀ (i : Fin (n + 1)) (x x' : Fin (n + 1) → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (hint : ∀ w : Fin n → β, Integrable (fun a => f (Fin.cons a w)) ν) (I t : ℝ) :
    ∫ w, ∫ a, Real.exp (t * (f (Fin.cons a w) - I)) ∂ν ∂Measure.pi (fun _ : Fin n => ν) ≤
      Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) *
        ∫ w, Real.exp (t * ((∫ a, f (Fin.cons a w) ∂ν) - I)) ∂Measure.pi (fun _ : Fin n => ν) := by
  have : Nonempty β := nonempty_of_isProbabilityMeasure ν
  set πn := Measure.pi (fun _ : Fin n => ν)
  set g : (Fin n → β) → ℝ := fun w => ∫ a, f (Fin.cons a w) ∂ν with hg_def
  have hg_meas : Measurable g :=
    (measurable_comp_fin_cons hf).stronglyMeasurable.integral_prod_left.measurable
  have hsec_meas : ∀ w : Fin n → β, Measurable (fun a => f (Fin.cons a w)) := fun w =>
    (measurable_comp_fin_cons hf).comp (measurable_id.prodMk measurable_const)
  have hg_bd : ∀ (i : Fin n) (w w' : Fin n → β), (∀ l, l ≠ i → w l = w' l) →
      |g w - g w'| ≤ c i.succ := fun i w w' hww' =>
    abs_integral_cons_sub_le ν hint hbd i w w' hww'
  have hHoeff : ∀ w, ∫ a, Real.exp (t * (f (Fin.cons a w) - g w)) ∂ν
      ≤ Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) := fun w =>
    integral_exp_mul_sub_integral_le_of_abs_sub_le ν (hsec_meas w) hc0
      (fun a a' => hbd 0 _ _ (fun l hl => by
        rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨m, rfl⟩
        · exact absurd rfl hl
        · simp)) t
  have hpoint : ∀ w, ∫ a, Real.exp (t * (f (Fin.cons a w) - I)) ∂ν
      ≤ Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) * Real.exp (t * (g w - I)) := by
    intro w
    have hsplit : (fun a => Real.exp (t * (f (Fin.cons a w) - I))) =
        fun a => Real.exp (t * (f (Fin.cons a w) - g w)) * Real.exp (t * (g w - I)) := by
      funext a
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hHoeff w) (Real.exp_nonneg _)
  have hR_int : Integrable (fun w => Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) *
      Real.exp (t * (g w - I))) πn :=
    (integrable_exp_mul_sub_of_bounded_differences (fun i => c i.succ) hg_meas.aemeasurable
      hg_bd I t).const_mul _
  have hLmeas : Measurable (fun w => ∫ a, Real.exp (t * (f (Fin.cons a w) - I)) ∂ν) :=
    ((((measurable_comp_fin_cons hf).sub_const I).const_mul t).exp
      ).stronglyMeasurable.integral_prod_left.measurable
  have hL_int : Integrable
      (fun w => ∫ a, Real.exp (t * (f (Fin.cons a w) - I)) ∂ν) πn := by
    refine hR_int.mono' hLmeas.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun a => Real.exp_nonneg _))]
    exact hpoint w
  rw [← integral_const_mul]
  exact integral_mono hL_int hR_int hpoint

/-- The induction step of the exponential-moment estimate underlying McDiarmid's inequality: the
estimate for the averaged function on `Fin n` gives it for `f` on `Fin (n + 1)`. -/
private theorem integral_exp_mul_centered_le_pi_fin_succ {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {n : ℕ} (f : (Fin (n + 1) → β) → ℝ)
    (hf : Measurable f) (c : Fin (n + 1) → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : Fin (n + 1)) (x x' : Fin (n + 1) → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (t : ℝ)
    (ih : ∀ g : (Fin n → β) → ℝ, Measurable g →
      (∀ (i : Fin n) (w w' : Fin n → β), (∀ l, l ≠ i → w l = w' l) →
        |g w - g w'| ≤ c i.succ) →
      ∫ w, Real.exp (t * (g w - ∫ w', g w' ∂Measure.pi (fun _ : Fin n => ν)))
          ∂Measure.pi (fun _ : Fin n => ν)
        ≤ Real.exp ((∑ i : Fin n, (c i.succ / 2) ^ 2) * t ^ 2 / 2)) :
    ∫ x, Real.exp (t * (f x - ∫ x', f x' ∂Measure.pi (fun _ : Fin (n + 1) => ν)))
        ∂Measure.pi (fun _ : Fin (n + 1) => ν)
      ≤ Real.exp ((∑ i, (c i / 2) ^ 2) * t ^ 2 / 2) := by
  have : Nonempty β := nonempty_of_isProbabilityMeasure ν
  set πn := Measure.pi (fun _ : Fin n => ν)
  set I : ℝ := ∫ x', f x' ∂Measure.pi (fun _ : Fin (n + 1) => ν) with hI_def
  set x₀ : Fin (n + 1) → β := fun _ => Classical.arbitrary β
  set M : ℝ := (∑ i, c i) + |f x₀| with hM
  have hMf : ∀ x, |f x| ≤ M := fun x => by
    rw [hM]
    exact abs_le_sum_add_abs_of_bounded_differences c f hbd x₀ x
  have hint : ∀ w : Fin n → β, Integrable (fun a => f (Fin.cons a w)) ν := fun w =>
    (integrable_const M).mono'
      ((measurable_comp_fin_cons hf).comp (measurable_id.prodMk measurable_const)
        ).aestronglyMeasurable (ae_of_all _ fun a => by simpa using hMf (Fin.cons a w))
  set g : (Fin n → β) → ℝ := fun w => ∫ a, f (Fin.cons a w) ∂ν with hg_def
  have hgf : I = ∫ w, g w ∂πn := by
    rw [hI_def, integral_pi_fin_succ_eq_integral_integral_cons ν f
      (integrable_comp_fin_cons_of_abs_le ν hf hMf)]
  rw [integral_pi_fin_succ_eq_integral_integral_cons ν (fun x => Real.exp (t * (f x - I)))
    (integrable_comp_fin_cons_of_abs_le ν (((hf.sub_const I).const_mul t).exp)
      (abs_exp_mul_sub_le_exp hMf I t))]
  calc
    _ ≤ Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) * ∫ w, Real.exp (t * (g w - I)) ∂πn :=
      integral_integral_exp_cons_le ν hf (hc 0) hbd hint I t
    _ ≤ Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) *
        Real.exp ((∑ i : Fin n, (c i.succ / 2) ^ 2) * t ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      rw [hgf]
      exact ih g (measurable_comp_fin_cons hf).stronglyMeasurable.integral_prod_left.measurable
        (fun i w w' hww' => abs_integral_cons_sub_le ν hint hbd i w w' hww')
    _ = Real.exp ((∑ i : Fin (n + 1), (c i / 2) ^ 2) * t ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      rw [Fin.sum_univ_succ]
      ring

/-- The exponential-moment estimate underlying McDiarmid's inequality, on a product indexed by
`Fin n`. -/
private theorem integral_exp_mul_centered_le_pi_fin {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {n : ℕ} (f : (Fin n → β) → ℝ)
    (hf : Measurable f) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : Fin n) (x x' : Fin n → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (t : ℝ) :
    ∫ x, Real.exp (t * (f x - ∫ x', f x' ∂Measure.pi (fun _ : Fin n => ν)))
        ∂Measure.pi (fun _ : Fin n => ν)
      ≤ Real.exp ((∑ i, (c i / 2) ^ 2) * t ^ 2 / 2) := by
  induction n with
  | zero =>
      -- On the empty product every function is constant, so the centered integrand is one.
      have : Subsingleton (Fin 0 → β) := ⟨fun a b => funext fun i => i.elim0⟩
      have hconst : ∀ x y : Fin 0 → β, f x = f y := fun x y => by rw [Subsingleton.elim x y]
      have hInt : ∀ x : Fin 0 → β,
          (∫ x', f x' ∂Measure.pi (fun _ : Fin 0 => ν)) = f x := by
        intro x
        have hfun : (fun x' => f x') = (fun _ => f x) := funext fun y => hconst y x
        rw [hfun]
        simp
      have hone : (fun x : Fin 0 → β =>
          Real.exp (t * (f x - ∫ x', f x' ∂Measure.pi (fun _ : Fin 0 => ν)))) = fun _ => 1 := by
        funext x
        rw [hInt x]
        simp
      rw [hone]
      simp
  | succ n ih =>
      exact integral_exp_mul_centered_le_pi_fin_succ ν f hf c hc hbd t fun g hg hgbd =>
        ih g hg (fun i => c i.succ) (fun i => hc i.succ) hgbd

/-- The exponential-moment estimate transported from `Fin (Fintype.card ι)` to an arbitrary
finite index type. -/
private theorem integral_exp_mul_centered_le_pi {ι : Type*} [Fintype ι] {β : Type*}
    [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν] (f : (ι → β) → ℝ)
    (hf : Measurable f) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : ι) (x x' : ι → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (t : ℝ) :
    ∫ x, Real.exp (t * (f x - ∫ x', f x' ∂Measure.pi (fun _ : ι => ν)))
        ∂Measure.pi (fun _ : ι => ν)
      ≤ Real.exp ((∑ i, (c i / 2) ^ 2) * t ^ 2 / 2) := by
  set e := Fintype.equivFin ι
  set φ := MeasurableEquiv.piCongrLeft (fun _ : ι => β) e.symm
  have mp : MeasurePreserving φ (Measure.pi (fun _ : Fin (Fintype.card ι) => ν))
      (Measure.pi (fun _ : ι => ν)) :=
    measurePreserving_piCongrLeft (α := fun _ : ι => β) (μ := fun _ : ι => ν) e.symm
  have hcoord : ∀ (w : Fin (Fintype.card ι) → β) (l : ι), φ w l = w (e l) := by
    intro w l
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => β) e.symm w (e l)
    rwa [e.symm_apply_apply] at h
  have hbdF : ∀ (i : Fin (Fintype.card ι)) (w w' : Fin (Fintype.card ι) → β),
      (∀ l, l ≠ i → w l = w' l) → |f (φ w) - f (φ w')| ≤ c (e.symm i) := by
    intro i w w' hww'
    apply hbd (e.symm i)
    intro l hl
    rw [hcoord w l, hcoord w' l]
    refine hww' (e l) (fun hcontra => hl ?_)
    rw [← e.symm_apply_apply l, hcontra]
  have key := integral_exp_mul_centered_le_pi_fin ν (fun w => f (φ w))
    (hf.comp φ.measurable) (fun i => c (e.symm i)) (fun i => hc (e.symm i)) hbdF t
  have hI : (∫ x', f x' ∂Measure.pi (fun _ : ι => ν)) =
      ∫ w', f (φ w') ∂Measure.pi (fun _ : Fin (Fintype.card ι) => ν) :=
    (mp.integral_comp' f).symm
  have hOuter :
      (∫ x, Real.exp (t * (f x - ∫ x', f x' ∂Measure.pi (fun _ : ι => ν)))
          ∂Measure.pi (fun _ : ι => ν)) =
        ∫ w, Real.exp (t * (f (φ w) - ∫ x', f x' ∂Measure.pi (fun _ : ι => ν)))
          ∂Measure.pi (fun _ : Fin (Fintype.card ι) => ν) :=
    (mp.integral_comp'
      (fun x => Real.exp (t * (f x - ∫ x', f x' ∂Measure.pi (fun _ : ι => ν))))).symm
  rw [hOuter, hI]
  rw [e.symm.sum_comp (fun i => (c i / 2) ^ 2)] at key
  exact key

/-- **McDiarmid's bounded-differences inequality at MGF level.** Let `f` be a measurable
real-valued function on a finite i.i.d. product. If two inputs that differ only at coordinate `i`
have outputs differing by at most `c i`, then the centered `f` is sub-Gaussian with variance proxy
`∑ i, (c i)² / 4`.

The result is stated using Mathlib's `ProbabilityTheory.HasSubgaussianMGF`; its
`measure_ge_le` theorem gives the one-sided Chernoff tail, and applying `neg` gives the other side.
-/
theorem hasSubgaussianMGF_of_bounded_differences
    {ι : Type*} [Fintype ι] {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (f : (ι → β) → ℝ) (hf : Measurable f) (c : ι → ℝ)
    (hbd : ∀ (i : ι) (x x' : ι → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun x => f x - ∫ y, f y ∂Measure.pi (fun _ : ι => ν))
      (∑ i, (c i).toNNReal ^ 2 / 4)
      (Measure.pi fun _ : ι => ν) := by
  have : Nonempty β := nonempty_of_isProbabilityMeasure ν
  set π : Measure (ι → β) := Measure.pi (fun _ : ι => ν)
  set I : ℝ := ∫ y, f y ∂π
  set x₀ : ι → β := fun _ => Classical.arbitrary β
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    simpa using hbd i x₀ x₀ (fun _ _ => rfl)
  have hint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * (f x - I))) π := fun t =>
    integrable_exp_mul_sub_of_bounded_differences c hf.aemeasurable hbd I t
  refine ⟨hint, fun t => ?_⟩
  have hkey := integral_exp_mul_centered_le_pi ν f hf c hc hbd t
  have hcoe : (((∑ i, (c i).toNNReal ^ 2 / 4 : ℝ≥0) : ℝ)) =
      ∑ i, (c i / 2) ^ 2 := by
    push_cast [Real.coe_toNNReal (c _) (hc _)]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [ProbabilityTheory.mgf, hcoe]
  exact hkey

/-- McDiarmid's bounded-differences inequality for a product indexed by `Fin n`, stated in the
convenient form where one coordinate is updated explicitly. -/
theorem hasSubgaussianMGF_of_bounded_differences_fin
    {n : ℕ} {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (f : (Fin n → β) → ℝ) (hf : Measurable f) (c : ℝ)
    (hosc : ∀ (x : Fin n → β) (i : Fin n) (b : β),
      |f (Function.update x i b) - f x| ≤ c) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun x => f x - ∫ y, f y ∂Measure.pi (fun _ : Fin n => ν))
      ((n : ℝ≥0) * (c.toNNReal / 2) ^ 2)
      (Measure.pi fun _ : Fin n => ν) := by
  have hbd : ∀ (i : Fin n) (x x' : Fin n → β),
      (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c := by
    intro i x x' hxx'
    have hx' : x' = Function.update x i (x' i) := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp
      · rw [Function.update_of_ne hl]
        exact (hxx' l hl).symm
    rw [hx', abs_sub_comm]
    exact hosc x i (x' i)
  have hvar : (∑ _ : Fin n, c.toNNReal ^ 2 / 4) =
      (n : ℝ≥0) * (c.toNNReal / 2) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← hvar]
  exact hasSubgaussianMGF_of_bounded_differences ν f hf (fun _ => c) hbd

end TauCeti.Probability
