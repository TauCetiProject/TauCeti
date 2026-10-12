/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
public import TauCeti.NumberTheory.QuadraticOrder.Field
public import Mathlib.RingTheory.FractionalIdeal.Operations
import TauCeti.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# The ideal attached to an integral binary quadratic form

A form `(a, b, c)` of discriminant `D` gives the two-generator order module
`aℤ + ((-b + √D)/2)ℤ` in the rational quadratic algebra. The construction first works
as a module over the actual quadratic order in either the field or split case. In the
nonsquare case it gives a fractional ideal of the existing number-field order.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section

open QuadraticAlgebra
open scoped nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

/-- The second ideal generator `(-b + √D)/2`. -/
def idealGenerator (f : BinaryQuadraticForm ℤ) (D : ℤ) : QuadraticAlgebra ℚ (D : ℚ) 0 :=
  ⟨-(f.b : ℚ) / 2, 1 / 2⟩

/-- The rational coefficient of the second ideal generator. -/
@[simp] theorem idealGenerator_re (f : BinaryQuadraticForm ℤ) (D : ℤ) :
    (f.idealGenerator D).re = -(f.b : ℚ) / 2 := (rfl)

/-- The square-root coefficient of the second ideal generator. -/
@[simp] theorem idealGenerator_im (f : BinaryQuadraticForm ℤ) (D : ℤ) :
    (f.idealGenerator D).im = 1 / 2 := (rfl)

/-- A form's second ideal generator differs integrally from the order generator. -/
theorem generator_eq_idealGenerator_add (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    QuadraticOrder.generator D = f.idealGenerator D + ((D + f.b) / 2) • 1 := by
  have hmod : D % 4 = f.b % 2 := by
    rw [← hf, discrim_def]
    exact Int.discrim_emod_four f.a f.b f.c
  have hdiv : (2 : ℤ) ∣ D + f.b := Int.dvd_iff_emod_eq_zero.mpr (by omega)
  have hmul : (2 : ℚ) * (((D + f.b) / 2 : ℤ) : ℚ) = (D : ℚ) + (f.b : ℚ) := by
    exact_mod_cast Int.mul_ediv_cancel' hdiv
  ext <;> simp [idealGenerator]
  linarith

/-- The second generator belongs to the actual quadratic order. -/
theorem idealGenerator_mem_order (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    f.idealGenerator D ∈
      QuadraticOrder.toSubalgebra D (hf ▸ f.discrim_emod_four_eq_zero_or_one) := by
  rw [QuadraticOrder.mem_toSubalgebra_iff]
  refine ⟨-((D + f.b) / 2), 1, ?_⟩
  rw [generator_eq_idealGenerator_add f D hf]
  simp only [one_smul, neg_smul]
  abel

/-- The quadratic relation of the second ideal generator. -/
@[simp] theorem idealGenerator_mul_self (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    f.idealGenerator D * f.idealGenerator D =
      (-f.b) • f.idealGenerator D - (f.a * f.c) • 1 := by
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  ext <;> simp [idealGenerator]
  · linarith
  · ring

private theorem mul_mem_span_idealGenerators (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D)
    (r : QuadraticOrder.toSubalgebra D (hf ▸ f.discrim_emod_four_eq_zero_or_one))
    {z : QuadraticAlgebra ℚ (D : ℚ) 0}
    (hz : z ∈ Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D}) :
    (r : QuadraticAlgebra ℚ (D : ℚ) 0) * z ∈
      Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D} := by
  obtain ⟨u, v, hr⟩ := (QuadraticOrder.mem_toSubalgebra_iff D
    (hf ▸ f.discrim_emod_four_eq_zero_or_one) r).mp r.property
  obtain ⟨m, n, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [hr, generator_eq_idealGenerator_add f D hf]
  let k := (D + f.b) / 2
  refine Submodule.mem_span_pair.mpr
    ⟨(u + v * k) * m - v * n * f.c, v * m * f.a + (u + v * k - v * f.b) * n, ?_⟩
  have hβ := idealGenerator_mul_self f D hf
  simp only [zsmul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg, mul_one]
    at hβ ⊢
  linear_combination -(v : QuadraticAlgebra ℚ (D : ℚ) 0) *
    (n : QuadraticAlgebra ℚ (D : ℚ) 0) * hβ

/-- The order module `aℤ + ((-b + √D)/2)ℤ`, over the actual quadratic order. -/
def orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    Submodule (QuadraticOrder.toSubalgebra D (hf ▸ f.discrim_emod_four_eq_zero_or_one))
      (QuadraticAlgebra ℚ (D : ℚ) 0) where
  carrier := Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D}
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' r _ hz := by
    simpa [Algebra.smul_def, Subalgebra.algebraMap_eq] using
      mul_mem_span_idealGenerators f D hf r hz

/-- The order ideal has the defining two-generator lattice as its carrier. -/
@[simp] theorem orderIdeal_coe (f : BinaryQuadraticForm ℤ) (D : ℤ) (hf : f.discrim = D) :
    (f.orderIdeal D hf : Set (QuadraticAlgebra ℚ (D : ℚ) 0)) =
      (Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D} :
        Set (QuadraticAlgebra ℚ (D : ℚ) 0)) := (rfl)

/-- Ideal membership is an integral combination of its two generators. -/
theorem mem_orderIdeal_iff (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D)
    (z : QuadraticAlgebra ℚ (D : ℚ) 0) :
    z ∈ f.orderIdeal D hf ↔
      ∃ m n : ℤ, m • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + n • f.idealGenerator D = z :=
  Submodule.mem_span_pair

/-- Restriction to the integers recovers the defining two-generator lattice. -/
theorem orderIdeal_restrictScalars (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    (f.orderIdeal D hf).restrictScalars ℤ =
      Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D} := by
  ext
  rfl

/-- Every member of the form ideal belongs to the order. -/
theorem orderIdeal_le_order (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    (f.orderIdeal D hf).restrictScalars ℤ ≤
      (QuadraticOrder.toSubalgebra D (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubmodule := by
  rw [orderIdeal_restrictScalars]
  refine Submodule.span_le.mpr ?_
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact (QuadraticOrder.toSubalgebra D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).algebraMap_mem f.a
  · exact Set.mem_singleton_iff.mp hz ▸ idealGenerator_mem_order f D hf

private theorem mem_one_of_mem_orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] {z : QuadraticAlgebra ℚ (D : ℚ) 0}
    (hz : z ∈ f.orderIdeal D hf) :
    z ∈ (1 : FractionalIdeal
      (nonZeroDivisors (QuadraticOrder.numberFieldOrder D
        (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0)) := by
  apply (FractionalIdeal.mem_one_iff _).mpr
  refine ⟨⟨z, ?_⟩, rfl⟩
  exact (congrArg (fun O ↦ z ∈ O)
    (QuadraticOrder.numberFieldOrder_toSubalgebra D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one))).mpr (orderIdeal_le_order f D hf hz)

/-- The form ideal as a fractional ideal of the existing quadratic number-field order. -/
def fractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    FractionalIdeal
      (nonZeroDivisors (QuadraticOrder.numberFieldOrder D
        (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0) := by
  let I : Submodule (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra
      (QuadraticAlgebra ℚ (D : ℚ) 0) :=
    { carrier := f.orderIdeal D hf
      zero_mem' := (f.orderIdeal D hf).zero_mem
      add_mem' := (f.orderIdeal D hf).add_mem
      smul_mem' r z hz := by
        have hr : (r : QuadraticAlgebra ℚ (D : ℚ) 0) ∈
            QuadraticOrder.toSubalgebra D (hf ▸ f.discrim_emod_four_eq_zero_or_one) :=
          (congrArg (fun O ↦ (r : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ O)
            (QuadraticOrder.numberFieldOrder_toSubalgebra D
              (hf ▸ f.discrim_emod_four_eq_zero_or_one))).mp r.property
        have hm := mul_mem_span_idealGenerators f D hf ⟨r, hr⟩
          (Submodule.mem_span_pair.mpr ((mem_orderIdeal_iff f D hf z).mp hz))
        rw [orderIdeal_coe]
        simpa only [Algebra.smul_def, Subalgebra.algebraMap_apply, SetLike.mem_coe] using hm }
  refine ⟨I, FractionalIdeal.isFractional_of_le_one I ?_⟩
  intro z hz
  simpa only [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] using
    mem_one_of_mem_orderIdeal f D hf hz

/-- Restriction of the fractional ideal to the integers recovers the defining lattice. -/
theorem fractionalIdeal_restrictScalars (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    (f.fractionalIdeal D hf : Submodule
      (QuadraticOrder.numberFieldOrder D (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra
      (QuadraticAlgebra ℚ (D : ℚ) 0)).restrictScalars ℤ =
      (f.orderIdeal D hf).restrictScalars ℤ := by
  ext
  rfl

/-- The first ideal generator is a member of the ideal. -/
@[simp] theorem a_mem_orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ f.orderIdeal D hf :=
  (mem_orderIdeal_iff f D hf _).mpr ⟨1, 0, by simp⟩

/-- The second ideal generator is a member of the ideal. -/
@[simp] theorem idealGenerator_mem_orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    f.idealGenerator D ∈ f.orderIdeal D hf :=
  (mem_orderIdeal_iff f D hf _).mpr ⟨0, 1, by simp⟩

/-- The two ideal generators are independent if the leading coefficient is nonzero. -/
theorem idealGenerators_linearIndependent (f : BinaryQuadraticForm ℤ) (D : ℤ) (ha : f.a ≠ 0) :
    LinearIndependent ℤ ![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D] := by
  rw [LinearIndependent.pair_iff]
  intro m n h
  have hi := congrArg QuadraticAlgebra.im h
  have hn : n = 0 := by
    have hnQ : (n : ℚ) = 0 := by simpa using hi
    exact_mod_cast hnQ
  subst n
  have hr := congrArg QuadraticAlgebra.re h
  have hmQ : (m : ℚ) * (f.a : ℚ) = 0 := by simpa using hr
  have hm : m = 0 := by
    exact_mod_cast (mul_eq_zero.mp hmQ).resolve_right (by exact_mod_cast ha)
  exact ⟨hm, rfl⟩

/-- The integral basis `a, (-b + √D)/2` of the form ideal. -/
noncomputable def idealBasis (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) :
    Module.Basis (Fin 2) ℤ (f.orderIdeal D hf) := by
  let v : Fin 2 → f.orderIdeal D hf := fun i ↦
    ⟨![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D] i, by fin_cases i <;> simp⟩
  apply Module.Basis.mk (v := v) ?_ ?_
  · apply LinearIndependent.of_comp ((f.orderIdeal D hf).subtype.restrictScalars ℤ)
    exact idealGenerators_linearIndependent f D ha
  · intro x _
    obtain ⟨m, n, hmn⟩ := (mem_orderIdeal_iff f D hf x).mp x.property
    have hx : x = m • v 0 + n • v 1 := Subtype.ext hmn.symm
    rw [hx]
    exact (Submodule.span ℤ (Set.range v)).add_mem
      ((Submodule.span ℤ (Set.range v)).smul_mem m (Submodule.subset_span ⟨0, rfl⟩))
      ((Submodule.span ℤ (Set.range v)).smul_mem n (Submodule.subset_span ⟨1, rfl⟩))

/-- The ideal basis maps to its defining two-generator family in the quadratic algebra. -/
theorem coe_idealBasis_apply (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) (i : Fin 2) :
    (f.idealBasis D hf ha i : QuadraticAlgebra ℚ (D : ℚ) 0) =
      ![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D] i := by
  simp only [idealBasis, Module.Basis.mk_apply]

/-- The first ideal basis vector is the leading coefficient. -/
@[simp] theorem coe_idealBasis_zero (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) :
    (f.idealBasis D hf ha 0 : QuadraticAlgebra ℚ (D : ℚ) 0) = f.a := by
  simpa only [Matrix.cons_val_zero] using coe_idealBasis_apply f D hf ha 0

/-- The second ideal basis vector is `(-b + √D)/2`. -/
@[simp] theorem coe_idealBasis_one (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) :
    (f.idealBasis D hf ha 1 : QuadraticAlgebra ℚ (D : ℚ) 0) = f.idealGenerator D := by
  simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using coe_idealBasis_apply f D hf ha 1

/-- Fractional-ideal membership is the same integral two-generator formula. -/
theorem mem_fractionalIdeal_iff (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)]
    (z : QuadraticAlgebra ℚ (D : ℚ) 0) :
    z ∈ f.fractionalIdeal D hf ↔
      ∃ m n : ℤ, m • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + n • f.idealGenerator D = z := by
  rw [← FractionalIdeal.mem_coe, ← Submodule.restrictScalars_mem ℤ,
    fractionalIdeal_restrictScalars, Submodule.restrictScalars_mem]
  exact mem_orderIdeal_iff f D hf z

/-- The leading coefficient belongs to the fractional form ideal. -/
@[simp] theorem a_mem_fractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ f.fractionalIdeal D hf :=
  (mem_fractionalIdeal_iff f D hf _).mpr ⟨1, 0, by simp⟩

/-- The second generator belongs to the fractional form ideal. -/
@[simp] theorem idealGenerator_mem_fractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    f.idealGenerator D ∈ f.fractionalIdeal D hf :=
  (mem_fractionalIdeal_iff f D hf _).mpr ⟨0, 1, by simp⟩

/-- The fractional ideal is integral, hence contained in the unit fractional ideal. -/
theorem fractionalIdeal_le_one (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    f.fractionalIdeal D hf ≤ 1 := by
  intro z hz
  exact mem_one_of_mem_orderIdeal f D hf
    ((mem_orderIdeal_iff f D hf z).mpr ((mem_fractionalIdeal_iff f D hf z).mp hz))

/-- The form ideal is nonzero. -/
theorem fractionalIdeal_ne_zero (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    f.fractionalIdeal D hf ≠ 0 := by
  intro h
  have hβ := idealGenerator_mem_fractionalIdeal f D hf
  rw [h, FractionalIdeal.mem_zero_iff] at hβ
  have := congrArg QuadraticAlgebra.im hβ
  norm_num at this

/-- Norm on the ideal generators recovers the original form, with the second coordinate negated. -/
theorem norm_idealGenerators (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (m n : ℤ) :
    QuadraticAlgebra.norm (m • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) +
      n • f.idealGenerator D) = (f.a : ℚ) * (f.eval m (-n) : ℚ) := by
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  simp only [QuadraticAlgebra.norm_def, re_add, im_add, re_smul, im_smul,
    re_intCast, im_intCast, idealGenerator_re, idealGenerator_im, add_zero, zero_mul, eval_def,
    Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_neg]
  linear_combination (n : ℚ) ^ 2 / 4 * hd

end TauCeti.BinaryQuadraticForm
