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
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

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
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) :
    f.idealGenerator D ∈ QuadraticOrder.toSubalgebra D hD := by
  rw [QuadraticOrder.mem_toSubalgebra_iff]
  refine ⟨-((D + f.b) / 2), 1, ?_⟩
  rw [generator_eq_idealGenerator_add f D hf]
  simp only [one_smul, neg_smul]
  abel

/-- The quadratic relation of the second ideal generator. -/
theorem idealGenerator_mul_self (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    f.idealGenerator D * f.idealGenerator D =
      (-f.b) • f.idealGenerator D - (f.a * f.c) • 1 := by
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  ext <;> simp [idealGenerator]
  · linarith
  · ring

private theorem mul_mem_span_idealGenerators (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D)
    (r : QuadraticOrder.toSubalgebra D hD) {z : QuadraticAlgebra ℚ (D : ℚ) 0}
    (hz : z ∈ Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D}) :
    (r : QuadraticAlgebra ℚ (D : ℚ) 0) * z ∈
      Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D} := by
  obtain ⟨u, v, hr⟩ := (QuadraticOrder.mem_toSubalgebra_iff D hD r).mp r.property
  obtain ⟨m, n, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [hr, generator_eq_idealGenerator_add f D hf]
  let k := (D + f.b) / 2
  refine Submodule.mem_span_pair.mpr
    ⟨(u + v * k) * m - v * n * f.c, v * m * f.a + (u + v * k - v * f.b) * n, ?_⟩
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  ext <;> simp [idealGenerator, k]
  · linear_combination (v : ℚ) * (n : ℚ) / 4 * hd
  · ring

/-- The order module `aℤ + ((-b + √D)/2)ℤ`, over the actual quadratic order. -/
def orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) :
    Submodule (QuadraticOrder.toSubalgebra D hD) (QuadraticAlgebra ℚ (D : ℚ) 0) where
  carrier := Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D}
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' r _ hz := by
    simpa [Algebra.smul_def, Subalgebra.algebraMap_eq] using
      mul_mem_span_idealGenerators f D hD hf r hz

/-- Ideal membership is an integral combination of its two generators. -/
theorem mem_orderIdeal_iff (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D)
    (z : QuadraticAlgebra ℚ (D : ℚ) 0) :
    z ∈ f.orderIdeal D hD hf ↔
      ∃ m n : ℤ, m • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + n • f.idealGenerator D = z :=
  Submodule.mem_span_pair

/-- Restriction to the integers recovers the defining two-generator lattice. -/
theorem orderIdeal_restrictScalars (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) :
    (f.orderIdeal D hD hf).restrictScalars ℤ =
      Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D} := by
  ext
  rfl

/-- Every member of the form ideal belongs to the order. -/
theorem orderIdeal_le_order (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) :
    (f.orderIdeal D hD hf).restrictScalars ℤ ≤ (QuadraticOrder.toSubalgebra D hD).toSubmodule := by
  rw [orderIdeal_restrictScalars]
  refine Submodule.span_le.mpr ?_
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact (QuadraticOrder.toSubalgebra D hD).algebraMap_mem f.a
  · exact Set.mem_singleton_iff.mp hz ▸ idealGenerator_mem_order f D hD hf

/-- The form ideal as a fractional ideal of the existing quadratic number-field order. -/
def fractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    FractionalIdeal (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0) :=
  ⟨{ carrier := f.orderIdeal D hD hf
     zero_mem' := (f.orderIdeal D hD hf).zero_mem
     add_mem' := (f.orderIdeal D hD hf).add_mem
     smul_mem' r z hz := by
       have hr : (r : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ QuadraticOrder.toSubalgebra D hD := by
         exact (congrArg (fun O ↦ (r : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ O)
           (QuadraticOrder.numberFieldOrder_toSubalgebra D hD)).mp r.property
       change (r : QuadraticAlgebra ℚ (D : ℚ) 0) * z ∈
         Submodule.span ℤ {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D}
       exact mul_mem_span_idealGenerators f D hD hf ⟨r, hr⟩ hz },
    1, one_mem _, fun z hz ↦ by
      refine ⟨⟨z, ?_⟩, ?_⟩
      · exact (congrArg (fun O ↦ z ∈ O)
          (QuadraticOrder.numberFieldOrder_toSubalgebra D hD)).mpr
          (orderIdeal_le_order f D hD hf hz)
      · simp only [one_smul]
        rfl⟩

/-- Restriction of the fractional ideal to the integers recovers the defining lattice. -/
theorem fractionalIdeal_restrictScalars (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    (f.fractionalIdeal D hD hf : Submodule (QuadraticOrder.numberFieldOrder D hD).toSubalgebra
      (QuadraticAlgebra ℚ (D : ℚ) 0)).restrictScalars ℤ =
      (f.orderIdeal D hD hf).restrictScalars ℤ := by
  ext
  rfl

/-- The first ideal generator is a member of the ideal. -/
@[simp] theorem a_mem_orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) :
    (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ f.orderIdeal D hD hf :=
  (mem_orderIdeal_iff f D hD hf _).mpr ⟨1, 0, by simp⟩

/-- The second ideal generator is a member of the ideal. -/
@[simp] theorem idealGenerator_mem_orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) :
    f.idealGenerator D ∈ f.orderIdeal D hD hf :=
  (mem_orderIdeal_iff f D hD hf _).mpr ⟨0, 1, by simp⟩

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
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) (ha : f.a ≠ 0) :
    Module.Basis (Fin 2) ℤ (f.orderIdeal D hD hf) :=
  (Module.Basis.span (idealGenerators_linearIndependent f D ha)).map
    ((LinearEquiv.ofEq _ _ (by
        simp [orderIdeal_restrictScalars, Matrix.range_cons, Set.pair_comm])).trans
      (((f.orderIdeal D hD hf).restrictScalarsEquiv ℤ).restrictScalars ℤ))

/-- The first ideal basis vector is the leading coefficient. -/
@[simp] theorem coe_idealBasis_zero (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) (ha : f.a ≠ 0) :
    (f.idealBasis D hD hf ha 0 : QuadraticAlgebra ℚ (D : ℚ) 0) = f.a := by
  simp only [idealBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, Module.Basis.span_apply]
  rfl

/-- The second ideal basis vector is `(-b + √D)/2`. -/
@[simp] theorem coe_idealBasis_one (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) (ha : f.a ≠ 0) :
    (f.idealBasis D hD hf ha 1 : QuadraticAlgebra ℚ (D : ℚ) 0) = f.idealGenerator D := by
  simp only [idealBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, Module.Basis.span_apply]
  rfl

/-- Fractional-ideal membership is the same integral two-generator formula. -/
theorem mem_fractionalIdeal_iff (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) [Fact (¬ IsSquare D)]
    (z : QuadraticAlgebra ℚ (D : ℚ) 0) :
    z ∈ f.fractionalIdeal D hD hf ↔
      ∃ m n : ℤ, m • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + n • f.idealGenerator D = z := by
  change z ∈ (f.fractionalIdeal D hD hf :
    Submodule (QuadraticOrder.numberFieldOrder D hD).toSubalgebra _).restrictScalars ℤ ↔ _
  rw [fractionalIdeal_restrictScalars]
  exact mem_orderIdeal_iff f D hD hf z

/-- The fractional ideal is integral, hence contained in the unit fractional ideal. -/
theorem fractionalIdeal_le_one (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    f.fractionalIdeal D hD hf ≤ 1 := by
  intro z hz
  apply (FractionalIdeal.mem_one_iff _).mpr
  refine ⟨⟨z, ?_⟩, rfl⟩
  apply (congrArg (fun O ↦ z ∈ O) (QuadraticOrder.numberFieldOrder_toSubalgebra D hD)).mpr
  apply orderIdeal_le_order f D hD hf
  exact (mem_orderIdeal_iff f D hD hf z).mpr ((mem_fractionalIdeal_iff f D hD hf z).mp hz)

/-- The form ideal is nonzero. -/
theorem fractionalIdeal_ne_zero (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    f.fractionalIdeal D hD hf ≠ 0 := by
  intro h
  have hβ : f.idealGenerator D ∈ f.fractionalIdeal D hD hf :=
    (mem_fractionalIdeal_iff f D hD hf _).mpr ⟨0, 1, by simp⟩
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
