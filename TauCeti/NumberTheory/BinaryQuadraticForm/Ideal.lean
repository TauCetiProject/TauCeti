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
@[simp] theorem coe_orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ) (hf : f.discrim = D) :
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
  ext z
  rw [Submodule.restrictScalars_mem]
  exact Set.ext_iff.mp (coe_orderIdeal f D hf) z

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

/-- The form ideal as a fractional ideal of the existing quadratic number-field order. -/
noncomputable def fractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    FractionalIdeal
      (nonZeroDivisors (QuadraticOrder.numberFieldOrder D
        (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0) :=
  FractionalIdeal.spanFinset
    (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra
    (Finset.univ : Finset (Fin 2))
    ![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D]

/-- The fractional ideal has the same carrier as the order ideal. -/
@[simp] theorem coe_fractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    (f.fractionalIdeal D hf : Set (QuadraticAlgebra ℚ (D : ℚ) 0)) =
      (f.orderIdeal D hf : Set (QuadraticAlgebra ℚ (D : ℚ) 0)) := by
  rw [coe_orderIdeal]
  ext z
  simp only [SetLike.mem_coe]
  rw [← FractionalIdeal.mem_coe, fractionalIdeal, FractionalIdeal.spanFinset_coe]
  have hs : ![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D] ''
      (Finset.univ : Finset (Fin 2)) =
        {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D} := by
    simp [Matrix.range_cons, Set.pair_comm]
  rw [hs]
  constructor
  · intro hz
    refine Submodule.span_induction (fun x hx ↦ Submodule.subset_span hx)
      (Submodule.zero_mem _) (fun x y _ _ hx hy ↦ Submodule.add_mem _ hx hy) ?_ hz
    intro r x _ hx
    have hr : (r : QuadraticAlgebra ℚ (D : ℚ) 0) ∈
        QuadraticOrder.toSubalgebra D (hf ▸ f.discrim_emod_four_eq_zero_or_one) :=
      (congrArg (fun O ↦ (r : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ O)
        (QuadraticOrder.numberFieldOrder_toSubalgebra D
          (hf ▸ f.discrim_emod_four_eq_zero_or_one))).mp r.property
    simpa only [Algebra.smul_def, Subalgebra.algebraMap_apply] using
      mul_mem_span_idealGenerators f D hf ⟨r, hr⟩ hx
  · intro hz
    exact Submodule.span_subset_span ℤ
      (QuadraticOrder.numberFieldOrder D
        (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra
      {(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D} hz

/-- Restriction of the fractional ideal to the integers recovers the defining lattice. -/
theorem fractionalIdeal_restrictScalars (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    (f.fractionalIdeal D hf : Submodule
      (QuadraticOrder.numberFieldOrder D (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra
      (QuadraticAlgebra ℚ (D : ℚ) 0)).restrictScalars ℤ =
      (f.orderIdeal D hf).restrictScalars ℤ := by
  ext z
  rw [Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, FractionalIdeal.mem_coe]
  exact Set.ext_iff.mp (coe_fractionalIdeal f D hf) z

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

/-- The form order ideal is nonzero, in both field and split quadratic algebras. -/
theorem orderIdeal_ne_bot (f : BinaryQuadraticForm ℤ) (D : ℤ) (hf : f.discrim = D) :
    f.orderIdeal D hf ≠ ⊥ := by
  intro h
  have hβ := idealGenerator_mem_orderIdeal f D hf
  rw [h, Submodule.mem_bot] at hβ
  have hi := congrArg QuadraticAlgebra.im hβ
  norm_num at hi

/-- The two ideal generators are independent if the leading coefficient is nonzero. -/
theorem linearIndependent_idealGenerators (f : BinaryQuadraticForm ℤ) (D : ℤ) (ha : f.a ≠ 0) :
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

private noncomputable def idealSpanEquiv (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) :
    Submodule.span ℤ (Set.range ![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D]) ≃ₗ[ℤ]
      f.orderIdeal D hf :=
  (LinearEquiv.ofEq _ _ (by
    simp [orderIdeal_restrictScalars, Matrix.range_cons, Set.pair_comm])).trans
    (((f.orderIdeal D hf).restrictScalarsEquiv ℤ).restrictScalars ℤ)

private theorem coe_idealSpanEquiv_apply (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D)
    (z : Submodule.span ℤ
      (Set.range ![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D])) :
    (idealSpanEquiv f D hf z : QuadraticAlgebra ℚ (D : ℚ) 0) = z := by
  simp only [idealSpanEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  exact (congrArg (fun w : f.orderIdeal D hf ↦ (w : QuadraticAlgebra ℚ (D : ℚ) 0))
    (Submodule.restrictScalarsEquiv_apply ℤ _ _ (f.orderIdeal D hf) _)).trans
      (LinearEquiv.coe_ofEq_apply _ z)

/-- The integral basis `a, (-b + √D)/2` of the form ideal. -/
noncomputable def idealBasis (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) :
    Module.Basis (Fin 2) ℤ (f.orderIdeal D hf) :=
  (Module.Basis.span (linearIndependent_idealGenerators f D ha)).map (idealSpanEquiv f D hf)

/-- The ideal basis maps to its defining two-generator family in the quadratic algebra. -/
theorem coe_idealBasis_apply (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) (i : Fin 2) :
    (f.idealBasis D hf ha i : QuadraticAlgebra ℚ (D : ℚ) 0) =
      ![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D] i := by
  rw [idealBasis, Module.Basis.map_apply, coe_idealSpanEquiv_apply, Module.Basis.coe_span_apply]

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
  exact (Set.ext_iff.mp (coe_fractionalIdeal f D hf) z).trans (mem_orderIdeal_iff f D hf z)

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
  apply (FractionalIdeal.mem_one_iff _).mpr
  refine ⟨⟨z, ?_⟩, rfl⟩
  have hzO := (Set.ext_iff.mp (coe_fractionalIdeal f D hf) z).mp hz
  exact (congrArg (fun O ↦ z ∈ O)
    (QuadraticOrder.numberFieldOrder_toSubalgebra D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one))).mpr (orderIdeal_le_order f D hf hzO)

/-- The form ideal is nonzero. -/
theorem fractionalIdeal_ne_zero (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    f.fractionalIdeal D hf ≠ 0 := by
  rw [fractionalIdeal, FractionalIdeal.spanFinset_ne_zero]
  have hspan : Submodule.span
      (QuadraticOrder.numberFieldOrder D
        (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra
      (![(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D] ''
        (Finset.univ : Finset (Fin 2))) ≠ ⊥ := by
    intro h
    apply orderIdeal_ne_bot f D hf
    ext z
    rw [Submodule.mem_bot]
    have hmem := Set.ext_iff.mp (coe_fractionalIdeal f D hf) z
    simp only [SetLike.mem_coe] at hmem
    rw [← FractionalIdeal.mem_coe, fractionalIdeal, FractionalIdeal.spanFinset_coe,
      h, Submodule.mem_bot] at hmem
    exact hmem.symm
  simpa only [ne_eq, Submodule.span_eq_bot, Set.mem_image, Finset.mem_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, exists_prop] using hspan

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
