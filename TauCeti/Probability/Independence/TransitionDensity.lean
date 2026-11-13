/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.PartialSums
public import TauCeti.MeasureTheory.Measure.PiWithDensity
public import TauCeti.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.HasLaw

/-!
# Transition densities from independent increments

A finite family of independent real increments with Lebesgue densities has a product-density
joint law. Passing to cumulative sums has Jacobian one: the density at a value tuple is the
product of the increment densities evaluated at successive differences, with the deterministic
initial value adjoined. No stationarity or Gaussian assumption is needed.

The finite-history theorem applies directly to process evaluations on a grid. The rectangle
formula and the nonnegative test-function formula include empty grids. The latter also retains
the initial coordinate, integrated against its Dirac law rather than a nonexistent time-zero
density.

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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {n : ℕ} {X : Fin n → Ω → ℝ} {p : Fin n → ℝ → ℝ≥0∞}

/-- Independent real increments with measurable Lebesgue densities give the successive-
difference density for their cumulative values, starting at any deterministic `a`.
The empty tuple is allowed. -/
theorem hasLaw_partialSums_withDensity (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (a : ℝ) :
    HasLaw (fun ω i ↦ a + TauCeti.partialSumsLinearEquiv ℝ n (fun j ↦ X j ω) i)
      (volume.withDensity fun y : Fin n → ℝ ↦ ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) P := by
  have (i : Fin n) : IsFiniteMeasure (volume.withDensity (p i)) :=
    (hX i).isFiniteMeasure_iff.mp inferInstance
  have hjoint := hind.hasLaw_pi hX
  rw [TauCeti.pi_withDensity _ hp, ← volume_pi] at hjoint
  let A := (TauCeti.partialSumsLinearEquiv ℝ n).toContinuousLinearEquiv
  have hm : Measurable (fun x : Fin n → ℝ ↦ (fun _ ↦ a) + A x) := by fun_prop
  have hmap := Measure.map_affine_withDensity (volume : Measure (Fin n → ℝ)) A
    (fun _ ↦ a) (fun x ↦ ∏ i, p i (x i))
  have hdet : LinearMap.det (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = 1 := by
    simp [A]
  simp only [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_mul] at hmap
  have hdiff (y : Fin n → ℝ) (i : Fin n) :
      A.symm (y - fun _ ↦ a) i =
        y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc := by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv_symm',
      TauCeti.partialSumsLinearEquiv_symm_apply]
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      induction i using Fin.cases <;> simp [Fin.cons_zero, Fin.cons_succ]
  simp_rw [hdiff] at hmap
  refine ⟨hm.aemeasurable.comp_aemeasurable hjoint.aemeasurable, ?_⟩
  calc
    _ = (P.map (fun ω i ↦ X i ω)).map (fun x ↦ (fun _ ↦ a) + A x) :=
      (AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hjoint.aemeasurable).symm
    _ = _ := by rw [hjoint.map_eq, hmap]

variable {V : Fin (n + 1) → Ω → ℝ} {a : ℝ}

/-- The finite-dimensional transition density of a real process with independent increments
on a grid. The initial value need only equal `a` almost surely; individual values need not
be literally measurable on an incomplete sample space. -/
theorem hasLaw_values_withDensity
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ V i.succ ω)
      (volume.withDensity fun y : Fin n → ℝ ↦ ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) P := by
  apply (hind.hasLaw_partialSums_withDensity hinc hp a).congr
  filter_upwards [hzero] with ω hω
  ext i
  simp only [TauCeti.partialSumsLinearEquiv_apply, Fin.partialSum, List.sum_take_ofFn]
  have hs := Fin.sum_Iic_sub i (fun j ↦ V j ω)
  have hset : ({j : Fin n | j.val < i.succ.val} : Finset (Fin n)) = Finset.Iic i := by
    ext j
    simp
  rw [hset, hs, hω]
  ring

/-- The joint event probability on a Borel rectangle is the product-Lebesgue integral of
the successive-difference density. This includes the empty history. -/
theorem measure_values_mem_pi
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | ∀ i : Fin n, V i.succ ω ∈ B i} =
      ∫⁻ y in Set.pi univ B, ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc) := by
  have hlaw := hind.hasLaw_values_withDensity hinc hp hzero
  rw [← withDensity_apply _ (MeasurableSet.univ_pi hB), ← hlaw.map_eq,
    Measure.map_apply_of_aemeasurable hlaw.aemeasurable (MeasurableSet.univ_pi hB)]
  congr 1
  ext ω
  simp

/-- Nonnegative functionals of the whole finite history, including its initial coordinate,
are integrated using a Dirac initial value and the positive-time transition density.
No density for the initial coordinate is assumed, and infinite integrals are permitted. -/
theorem lintegral_values
    (hind : iIndepFun (fun i : Fin n ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin n, HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (fun i ↦ V i ω) ∂P = ∫⁻ y : Fin n → ℝ,
      F (Fin.cons a y) * ∏ i,
        p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc) := by
  have hlaw := hind.hasLaw_values_withDensity hinc hp hzero
  have hcons : Measurable (fun y : Fin n → ℝ ↦
      (Fin.cons a y : Fin (n + 1) → ℝ)) := by fun_prop
  calc
    _ = ∫⁻ ω, F (Fin.cons a (fun i : Fin n ↦ V i.succ ω)) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hzero] with ω hω
      congr 1
      ext i
      induction i using Fin.cases <;> simp [hω]
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
theorem lintegral_values_succ
    {V : Fin (n + 2) → Ω → ℝ} {p : Fin (n + 1) → ℝ → ℝ≥0∞}
    (hind : iIndepFun (fun i : Fin (n + 1) ↦ fun ω ↦ V i.succ ω - V i.castSucc ω) P)
    (hinc : ∀ i : Fin (n + 1), HasLaw (fun ω ↦ V i.succ ω - V i.castSucc ω)
      (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) (hzero : V 0 =ᵐ[P] fun _ ↦ a)
    {F : (Fin (n + 2) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (fun i ↦ V i ω) ∂P = ∫⁻ x : ℝ, ∫⁻ y : Fin n → ℝ,
      F (Fin.cons a (Fin.cons x y)) *
        (p 0 (x - a) * ∏ i : Fin n,
          p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc)) := by
  rw [hind.lintegral_values hinc hp hzero hF]
  let g (y : Fin (n + 1) → ℝ) := F (Fin.cons a y) * ∏ i,
    p i (y i - (Fin.cons a y : Fin (n + 2) → ℝ) i.castSucc)
  have hg : Measurable g := by
    apply Measurable.mul (hF.comp (by fun_prop))
    exact Finset.measurable_prod _ fun i _ ↦ (hp i).comp (by fun_prop)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
  calc
    _ = ∫⁻ z : ℝ × (Fin n → ℝ), g (e.symm z) :=
      (he.lintegral_comp hg).symm
    _ = ∫⁻ x : ℝ, ∫⁻ y : Fin n → ℝ, g (e.symm (x, y)) :=
      lintegral_prod _ (hg.comp e.symm.measurable).aemeasurable
    _ = _ := by
      apply lintegral_congr fun x ↦ ?_
      apply lintegral_congr fun y ↦ ?_
      -- The inverse coordinate split inserts the first coordinate; split the density product
      -- at the same index to retain the new initial value in every remaining difference.
      simp [g, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ]

end ProbabilityTheory.iIndepFun
