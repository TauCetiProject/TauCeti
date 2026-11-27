/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Field traces of fractional ideals

For a module-finite extension of domains, the field trace sends a fractional ideal of the
extension to a fractional ideal of the base. Its elements are exactly the traces of elements
of the original ideal. Scaling by a principal fractional ideal from the base commutes with
trace, so integral trace computations also determine traces of ideals with denominators.

See Serre, *Local Fields*, Chapter III, §3, Proposition 7 for the application to powers of
the maximal ideal.
-/

public section

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
  [Module.Finite A B]

variable (A K) in
/-- The fractional ideal consisting of the field traces of elements of `I`. -/
noncomputable def trace (I : FractionalIdeal B⁰ L) : FractionalIdeal A⁰ K where
  val := ((I : Submodule B L).restrictScalars A).map ((Algebra.trace K L).restrictScalars A)
  property := by
    have : IsDomain B := (IsFractionRing.injective B L).isDomain (algebraMap B L)
    obtain ⟨a, J, -, ha⟩ := I.exists_eq_spanSingleton_mul
    let b := (algebraMap B L a)⁻¹
    have hI : I ≤ spanSingleton B⁰ b := by
      rw [ha]
      exact (mul_le_mul_right (a := spanSingleton B⁰ b) coeIdeal_le_one).trans_eq (mul_one _)
    have hfg : (Submodule.span B {b}).FG := Submodule.fg_span_singleton _
    have himg := (hfg.restrictScalars (R := A)).map ((Algebra.trace K L).restrictScalars A)
    exact isFractional_of_le (J := ⟨_, isFractional_of_fg himg⟩)
      (Submodule.map_mono (Submodule.restrictScalars_mono A hI))

/-- The underlying submodule of the fractional trace is the image under the field trace. -/
@[simp]
theorem coeToSubmodule_trace (I : FractionalIdeal B⁰ L) :
    (I.trace A K : Submodule A K) =
      ((I : Submodule B L).restrictScalars A).map ((Algebra.trace K L).restrictScalars A) := (rfl)

/-- Membership in the trace ideal is witnessed by a single element of the source ideal. -/
theorem mem_trace {I : FractionalIdeal B⁰ L} {x : K} :
    x ∈ I.trace A K ↔ ∃ y ∈ I, Algebra.trace K L y = x := Iff.rfl

/-- The trace of the zero fractional ideal is zero. -/
@[simp]
theorem trace_zero : (0 : FractionalIdeal B⁰ L).trace A K = 0 := by
  apply coeToSubmodule_injective
  simp

/-- The trace of a sum of fractional ideals is the sum of their traces. -/
@[simp]
theorem trace_add (I J : FractionalIdeal B⁰ L) :
    (I + J).trace A K = I.trace A K + J.trace A K := by
  apply coeToSubmodule_injective
  simp [Submodule.add_eq_sup, Submodule.restrictScalars_sup]

/-- The trace of a principal multiple by a base-field scalar is the same multiple of the trace. -/
@[simp]
theorem trace_spanSingleton_mul (I : FractionalIdeal B⁰ L) (a : K) :
    (spanSingleton B⁰ (algebraMap K L a) * I).trace A K = spanSingleton A⁰ a * I.trace A K := by
  ext x
  simp only [mem_trace, mem_singleton_mul]
  constructor <;> rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩ <;>
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [← Algebra.smul_def, map_smul, smul_eq_mul]⟩

/-- On integral ideals the fractional trace agrees with the image under the integral trace. -/
@[simp]
theorem trace_coeIdeal [IsDomain B] [IsDomain A] [IsIntegrallyClosed A] [IsIntegrallyClosed B]
    [Module.IsTorsionFree A B] (I : Ideal B) :
    (I : FractionalIdeal B⁰ L).trace A K =
      (((I.restrictScalars A).map (Algebra.intTrace A B) : Ideal A) : FractionalIdeal A⁰ K) := by
  have : IsIntegralClosure B A L := IsIntegralClosure.of_isIntegrallyClosed _ _ _
  have : Algebra.IsAlgebraic K L := isAlgebraic_of_isFractionRing A B K L
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  have : FiniteDimensional K L := Module.Finite.of_isLocalization A B A⁰
  ext x
  simp only [mem_trace, mem_coeIdeal, Submodule.mem_map, Submodule.restrictScalars_mem,
    exists_exists_and_eq_and, Algebra.algebraMap_intTrace (K := K) (L := L)]

end FractionalIdeal
