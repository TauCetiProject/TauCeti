/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.PartialSums
public import TauCeti.Probability.Independence.HasLawWithDensity
public import TauCeti.MeasureTheory.Integral.TransitionDensity

/-!
# Transition densities from independent increments

A finite family of independent real increments with Lebesgue densities has a product-density
joint law. Passing to cumulative sums has Jacobian one: the density at a value tuple is the
product of the increment densities evaluated at successive differences, with the deterministic
initial value adjoined. No stationarity or Gaussian assumption is needed.

The finite-history theorem applies directly to process evaluations on a grid. The rectangle
and nonnegative test-function formulas include empty grids. Rectangle probabilities also have
a fully iterated form, with zero and successor rules in
`TauCeti.MeasureTheory.Integral.TransitionDensity`. Initial-coordinate rectangles are integrated
against the Dirac law rather than a nonexistent time-zero density.

The construction uses `iIndepFun.hasLaw_pi`, `TauCeti.pi_withDensity`, and the determinant-one
partial-sum equivalence `TauCeti.partialSumsLinearEquiv`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 2, finite-dimensional distributions of processes with independent increments.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {n : ℕ} {X : Fin n → Ω → ℝ} {p : Fin n → ℝ → ℝ≥0∞}

/-- Independent real increments with measurable Lebesgue densities give the successive-
difference density for their cumulative values, starting at any deterministic `a`.
The empty tuple is allowed. -/
theorem hasLaw_add_partialSumsLinearEquiv_withDensity (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (a : ℝ) :
    HasLaw (fun ω i ↦ a + TauCeti.partialSumsLinearEquiv ℝ n (fun j ↦ X j ω) i)
      (volume.withDensity fun y : Fin n → ℝ ↦ ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) P := by
  have hjoint := hind.hasLaw_pi_volume_withDensity hX hp
  have hm : Measurable (fun x : Fin n → ℝ ↦
      (fun _ ↦ a) + (TauCeti.partialSumsLinearEquiv ℝ n).toContinuousLinearEquiv x) := by
    fun_prop
  have hm' : Measurable (fun x : Fin n → ℝ ↦
      (fun _ ↦ a) + TauCeti.partialSumsLinearEquiv ℝ n x) := by
    simpa only [LinearEquiv.coe_toContinuousLinearEquiv'] using hm
  exact (HasLaw.mk hm'.aemeasurable
    (Measure.map_add_partialSumsLinearEquiv_withDensity n a
      (fun x : Fin n → ℝ ↦ ∏ i, p i (x i)))).comp hjoint

variable {V : Fin (n + 1) → Ω → ℝ} {a : ℝ}

/-- The finite-dimensional transition density of a real process with independent increments
on a grid. The initial value need only equal `a` almost surely; individual values need not
be literally measurable on an incomplete sample space. -/
theorem hasLaw_succ_withDensity_of_sub
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ V i.succ ω)
      (volume.withDensity fun y : Fin n → ℝ ↦ ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) P := by
  apply (hind.hasLaw_add_partialSumsLinearEquiv_withDensity hinc hp a).congr
  filter_upwards [hzero] with ω hω
  ext i
  simp only [TauCeti.coe_partialSumsLinearEquiv,
    TauCeti.partialSumsLinearMap_apply_eq_sum_Iic]
  simp [Fin.sum_Iic_sub i (fun j ↦ V j ω), hω]

/-- The joint law evaluates any measurable set by integrating the successive-difference
density. Values of the process need only be almost everywhere measurable. -/
theorem measure_setOf_succ_mem_eq_setLIntegral_prod_of_hasLaw_withDensity
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    P {ω | (fun i : Fin n ↦ V i.succ ω) ∈ S} =
      ∫⁻ y in S, ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc) := by
  calc
    _ = (volume.withDensity fun y : Fin n → ℝ ↦ ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) S :=
      (hind.hasLaw_succ_withDensity_of_sub hinc hp hzero).measure_eq hS
    _ = _ := withDensity_apply _ hS

/-- The joint event probability on a Borel rectangle is the product-Lebesgue integral of
the successive-difference density. This includes the empty history. -/
theorem measure_setOf_forall_succ_mem_eq_setLIntegral_prod_of_hasLaw_withDensity
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | ∀ i : Fin n, V i.succ ω ∈ B i} =
      ∫⁻ y in Set.pi univ B, ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc) := by
  simpa using hind.measure_setOf_succ_mem_eq_setLIntegral_prod_of_hasLaw_withDensity
    hinc hp hzero (MeasurableSet.univ_pi hB)

/-- Nonnegative functionals of the whole finite history, including its initial coordinate,
are integrated using a Dirac initial value and the positive-time transition density.
No density for the initial coordinate is assumed, and infinite integrals are permitted. -/
theorem lintegral_comp_eq_lintegral_cons_mul_prod_of_hasLaw_withDensity
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (fun i ↦ V i ω) ∂P = ∫⁻ y : Fin n → ℝ,
      F (Fin.cons a y) * ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc) := by
  have hlaw := hind.hasLaw_succ_withDensity_of_sub hinc hp hzero
  have hcons : Measurable (fun y : Fin n → ℝ ↦
      (Fin.cons a y : Fin (n + 1) → ℝ)) := by fun_prop
  calc
    _ = ∫⁻ ω, F (Fin.cons a (fun i : Fin n ↦ V i.succ ω)) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hzero] with ω hω
      simpa only [hω, Fin.tail_def] using congrArg F (Fin.cons_self_tail (fun i ↦ V i ω)).symm
    _ = ∫⁻ y : Fin n → ℝ, F (Fin.cons a y) ∂(volume.withDensity fun y : Fin n → ℝ ↦
        ∏ i, p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) :=
      hlaw.lintegral_comp (hF.comp hcons).aemeasurable
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul]
      · simp only [Pi.mul_apply, mul_comm]
      · exact Finset.measurable_prod _ fun i _ ↦ (hp i).comp (by fun_prop)
      · exact hF.comp hcons

/-- Splitting off the first positive-time coordinate gives an iterated transition-density
integral. The remaining density is the successive-difference product based at that first
coordinate. Indicator test functions give the corresponding Borel rectangle formula. -/
theorem lintegral_comp_eq_lintegral_lintegral_cons_mul_prod_of_hasLaw_withDensity
    {V : Fin (n + 2) → Ω → ℝ} {p : Fin (n + 1) → ℝ → ℝ≥0∞}
    (hind : iIndepFun (fun i : Fin (n + 1) ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin (n + 1), HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    {F : (Fin (n + 2) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (fun i ↦ V i ω) ∂P = ∫⁻ x : ℝ, p 0 (x - a) * ∫⁻ y : Fin n → ℝ,
      F (Fin.cons a (Fin.cons x y)) * ∏ i : Fin n,
        p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc) := by
  rw [hind.lintegral_comp_eq_lintegral_cons_mul_prod_of_hasLaw_withDensity hinc hp hzero hF]
  exact TauCeti.lintegral_mul_prod_sub_cons_succ hp a (hF.comp (by fun_prop))

/-- The Borel-rectangle probability is the fully iterated transition-density integral.
The zero-increment case reduces to one by `transitionRectangleIntegral_zero`. -/
theorem measure_setOf_forall_succ_mem_eq_transitionRectangleIntegral
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | ∀ i : Fin n, V i.succ ω ∈ B i} =
      TauCeti.transitionRectangleIntegral p a B := by
  rw [hind.measure_setOf_forall_succ_mem_eq_setLIntegral_prod_of_hasLaw_withDensity
    hinc hp hzero B hB]
  exact TauCeti.setLIntegral_prod_sub_cons_eq_transitionRectangleIntegral hp a B hB

/-- Include the initial-coordinate rectangle by integration against its Dirac law,
not by a fictitious time-zero density. This also handles a grid containing only time zero. -/
theorem measure_setOf_forall_mem_eq_setLIntegral_dirac_transitionRectangleIntegral
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    (B : Fin (n + 1) → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | ∀ i, V i ω ∈ B i} =
      ∫⁻ x in B 0, TauCeti.transitionRectangleIntegral p x (fun i ↦ B i.succ)
        ∂Measure.dirac a := by
  classical
  rw [setLIntegral_dirac]
  split_ifs with ha
  · calc
      _ = P {ω | ∀ i : Fin n, V i.succ ω ∈ B i.succ} := by
        apply measure_congr
        filter_upwards [hzero] with ω hω
        simp [Fin.forall_fin_succ, hω, ha]
      _ = _ := hind.measure_setOf_forall_succ_mem_eq_transitionRectangleIntegral
        hinc hp hzero _ (fun i ↦ hB i.succ)
  · calc
      _ = P ∅ := by
        apply measure_congr
        filter_upwards [hzero] with ω hω
        simp [Fin.forall_fin_succ, hω, ha]
      _ = 0 := measure_empty

end ProbabilityTheory.iIndepFun
