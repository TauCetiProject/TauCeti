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
  have : Nonempty β := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : (Set.univ : Set β) = ∅ := Set.eq_empty_of_isEmpty _
    have h2 : ν Set.univ = 0 := by rw [h1]; simp
    rw [measure_univ] at h2
    exact one_ne_zero h2
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
      -- Identify the successor product with the first coordinate times the remaining product.
      set π1 := Measure.pi (fun _ : Fin (n + 1) => ν) with hπ1
      set πn := Measure.pi (fun _ : Fin n => ν) with hπn
      set I : ℝ := ∫ x', f x' ∂π1 with hI_def
      set x₀ : Fin (n + 1) → β := fun _ => Classical.arbitrary β with hx0
      set M : ℝ := (∑ i, c i) + |f x₀| with hM
      have hMf : ∀ x, |f x| ≤ M := fun x => by
        rw [hM]
        exact abs_le_sum_add_abs_of_bounded_differences c f hbd x₀ x
      have hpair_meas : ∀ (F : (Fin (n + 1) → β) → ℝ), Measurable F →
          Measurable (fun p : β × (Fin n → β) => F (Fin.cons p.1 p.2)) := by
        intro F hF
        apply hF.comp
        apply measurable_pi_iff.mpr
        intro j
        refine Fin.cases ?_ ?_ j
        · simp only [Fin.cons_zero]
          exact measurable_fst
        · intro i
          simp only [Fin.cons_succ]
          exact (measurable_pi_apply i).comp measurable_snd
      have htrans : ∀ (F : (Fin (n + 1) → β) → ℝ),
          Integrable (fun p : β × (Fin n → β) => F (Fin.cons p.1 p.2)) (ν.prod πn) →
          ∫ x, F x ∂π1 = ∫ w, ∫ a, F (Fin.cons a w) ∂ν ∂πn := by
        intro F hFint
        set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => β) 0 with he
        have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
        have hcons : ∀ (a : β) (w : Fin n → β), e.symm (a, w) = Fin.cons a w := by
          intro a w
          ext j
          refine Fin.cases ?_ ?_ j
          · simp [he]
          · intro i
            simp [he]
        have step1 : ∫ x, F x ∂π1 = ∫ p, F (e.symm p) ∂(ν.prod πn) :=
          (mp.symm.integral_comp' F).symm
        rw [step1, integral_prod_symm _ (by simpa only [hcons] using hFint)]
        simp_rw [hcons]
      -- Uniform boundedness supplies all integrability facts needed for the product decomposition.
      have hprodint : ∀ (F : (Fin (n + 1) → β) → ℝ) (K : ℝ), Measurable F →
          (∀ x, |F x| ≤ K) →
          Integrable (fun p : β × (Fin n → β) => F (Fin.cons p.1 p.2)) (ν.prod πn) := by
        intro F K hFm hFb
        refine (integrable_const K).mono' (hpair_meas F hFm).aestronglyMeasurable
          (ae_of_all _ fun p => ?_)
        simpa using hFb (Fin.cons p.1 p.2)
      -- Average out the first coordinate; the resulting function inherits bounded differences.
      set g : (Fin n → β) → ℝ := fun w => ∫ a, f (Fin.cons a w) ∂ν with hg_def
      have hg_meas : Measurable g :=
        (hpair_meas f hf).stronglyMeasurable.integral_prod_left.measurable
      have hsec_meas : ∀ w : Fin n → β, Measurable (fun a => f (Fin.cons a w)) := by
        intro w
        apply hf.comp
        apply measurable_pi_iff.mpr
        intro j
        refine Fin.cases ?_ ?_ j
        · simp only [Fin.cons_zero]
          exact measurable_id
        · intro i
          simp only [Fin.cons_succ]
          exact measurable_const
      have hsec_int : ∀ w : Fin n → β, Integrable (fun a => f (Fin.cons a w)) ν := by
        intro w
        refine (integrable_const M).mono' (hsec_meas w).aestronglyMeasurable
          (ae_of_all _ fun a => ?_)
        simpa using hMf (Fin.cons a w)
      have hg_bd : ∀ (i : Fin n) (w w' : Fin n → β), (∀ l, l ≠ i → w l = w' l) →
          |g w - g w'| ≤ c i.succ := by
        intro i w w' hww'
        have hpt : ∀ a : β, |f (Fin.cons a w) - f (Fin.cons a w')| ≤ c i.succ := by
          intro a
          apply hbd i.succ
          intro j hj
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
          · simp
          · have hli : l ≠ i := fun h => hj (by rw [h])
            simp only [Fin.cons_succ]
            exact hww' l hli
        have hgsub : g w - g w' = ∫ a, (f (Fin.cons a w) - f (Fin.cons a w')) ∂ν := by
          rw [hg_def]
          exact (integral_sub (hsec_int w) (hsec_int w')).symm
        rw [hgsub]
        calc
          |∫ a, (f (Fin.cons a w) - f (Fin.cons a w')) ∂ν|
              ≤ ∫ a, |f (Fin.cons a w) - f (Fin.cons a w')| ∂ν :=
            abs_integral_le_integral_abs
          _ ≤ ∫ _a, c i.succ ∂ν := integral_mono ((hsec_int w).sub (hsec_int w')).abs
            (integrable_const (c i.succ)) hpt
          _ = c i.succ := by simp
      have hgf : I = ∫ w, g w ∂πn := by
        rw [hI_def, htrans f (hprodint f M hf hMf)]
      -- Hoeffding's lemma controls the centered fluctuation in the peeled coordinate.
      have hHoeff : ∀ w, ∫ a, Real.exp (t * (f (Fin.cons a w) - g w)) ∂ν
          ≤ Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) := by
        intro w
        rw [hg_def]
        set X : β → ℝ := fun a => f (Fin.cons a w) with hX
        set A : ℝ := sInf (Set.range X) with hA
        have hosc : ∀ a a', |X a - X a'| ≤ c 0 := by
          intro a a'
          apply hbd (0 : Fin (n + 1))
          intro l hl
          rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨m, rfl⟩
          · exact absurd rfl hl
          · simp
        have hbdd : BddBelow (Set.range X) := by
          refine ⟨X (Classical.arbitrary β) - c 0, ?_⟩
          rintro _ ⟨a, rfl⟩
          have := hosc (Classical.arbitrary β) a
          rw [abs_sub_le_iff] at this
          linarith [this.1]
        have hne : (Set.range X).Nonempty := Set.range_nonempty X
        have hmem : ∀ a, X a ∈ Set.Icc A (A + c 0) := by
          intro a
          refine ⟨csInf_le hbdd ⟨a, rfl⟩, ?_⟩
          have hle : A ≥ X a - c 0 := by
            apply le_csInf hne
            rintro _ ⟨a', rfl⟩
            have := hosc a a'
            rw [abs_sub_le_iff] at this
            linarith [this.1]
          linarith
        have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := ν)
          (hsec_meas w).aemeasurable (ae_of_all _ hmem)
        have hml := hsub.mgf_le t
        have hexp : ((((‖(A + c 0) - A‖₊ / 2) ^ 2 : NNReal) : ℝ)) =
            (c 0 / 2) ^ 2 := by
          rw [add_sub_cancel_left, Real.nnnorm_of_nonneg (hc 0)]
          push_cast
          ring
        rw [ProbabilityTheory.mgf] at hml
        calc
          ∫ a, Real.exp (t * (f (Fin.cons a w) - ∫ a', f (Fin.cons a' w) ∂ν)) ∂ν
              ≤ Real.exp (((‖(A + c 0) - A‖₊ / 2) ^ 2 : NNReal) * t ^ 2 / 2) := hml
          _ = Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) := by rw [hexp]
      -- Split off the averaged function, then integrate the pointwise Hoeffding estimate.
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
      have hexpg_int : Integrable (fun w => Real.exp (t * (g w - I))) πn :=
        integrable_exp_mul_sub_of_bounded_differences (fun i => c i.succ) hg_meas.aemeasurable
          hg_bd I t
      have hR_int : Integrable (fun w => Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) *
          Real.exp (t * (g w - I))) πn := hexpg_int.const_mul _
      have hLmeas : Measurable (fun w => ∫ a, Real.exp (t * (f (Fin.cons a w) - I)) ∂ν) := by
        have hm : Measurable (fun p : β × (Fin n → β) =>
            Real.exp (t * (f (Fin.cons p.1 p.2) - I))) :=
          (((hpair_meas f hf).sub_const I).const_mul t).exp
        exact hm.stronglyMeasurable.integral_prod_left.measurable
      have hL_int : Integrable
          (fun w => ∫ a, Real.exp (t * (f (Fin.cons a w) - I)) ∂ν) πn := by
        refine hR_int.mono' hLmeas.aestronglyMeasurable (ae_of_all _ fun w => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun a => Real.exp_nonneg _))]
        exact hpoint w
      have hFexp_bd : ∀ x, |Real.exp (t * (f x - I))| ≤ Real.exp (|t| * (M + |I|)) := by
        intro x
        rw [Real.abs_exp]
        apply Real.exp_le_exp.mpr
        calc
          t * (f x - I) ≤ |t * (f x - I)| := le_abs_self _
          _ = |t| * |f x - I| := abs_mul _ _
          _ ≤ |t| * (M + |I|) :=
            mul_le_mul_of_nonneg_left ((abs_sub (f x) I).trans (by linarith [hMf x]))
              (abs_nonneg t)
      rw [htrans (fun x => Real.exp (t * (f x - I)))
        (hprodint _ (Real.exp (|t| * (M + |I|))) (((hf.sub_const I).const_mul t).exp)
          hFexp_bd)]
      calc
        ∫ w, ∫ a, Real.exp (t * (f (Fin.cons a w) - I)) ∂ν ∂πn
            ≤ ∫ w, Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) *
                Real.exp (t * (g w - I)) ∂πn := integral_mono hL_int hR_int hpoint
        _ = Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) *
            ∫ w, Real.exp (t * (g w - I)) ∂πn := by rw [integral_const_mul]
        _ ≤ Real.exp ((c 0 / 2) ^ 2 * t ^ 2 / 2) *
            Real.exp ((∑ i : Fin n, (c i.succ / 2) ^ 2) * t ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          rw [hgf]
          exact ih g hg_meas (fun i => c i.succ) (fun i => hc i.succ) hg_bd
        _ = Real.exp ((∑ i : Fin (n + 1), (c i / 2) ^ 2) * t ^ 2 / 2) := by
          rw [← Real.exp_add]
          congr 1
          rw [Fin.sum_univ_succ]
          ring

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
  set e := Fintype.equivFin ι with he
  set φ := MeasurableEquiv.piCongrLeft (fun _ : ι => β) e.symm with hφ
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
  have : Nonempty β := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : (Set.univ : Set β) = ∅ := Set.eq_empty_of_isEmpty _
    have h2 : ν Set.univ = 0 := by rw [h1]; simp
    rw [measure_univ] at h2
    exact one_ne_zero h2
  set π : Measure (ι → β) := Measure.pi (fun _ : ι => ν) with hπ
  set I : ℝ := ∫ y, f y ∂π with hI
  set x₀ : ι → β := fun _ => Classical.arbitrary β with hx0
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
    intro i hi
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
