/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Dual.BaseChange
public import TauCeti.RingTheory.NormTrace.BaseChange
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Localization.Module

/-!
# Complementary modules under scalar extension

For a finite separable field extension `L / K`, the complementary module of a lattice
is its dual for the trace pairing. This file proves that extending a free lattice and
then taking its trace dual gives the span of the original trace dual.

The scalar-extended algebra `K' ⊗[K] L` is allowed to split into several fields. In
particular, the result applies before projecting a semilocal completion to one factor;
it requires no separability of residue fields. The final theorem applies directly to
an integral basis of a finite free algebra whose generic fiber is `L / K`.

The proof uses Mathlib's `Submodule.traceDual`, localization of bases, and the
dual-basis description `LinearMap.BilinForm.dualSubmodule_span_of_basis`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §4, Proposition 10.
-/

public section

open Module
open scoped TensorProduct nonZeroDivisors

namespace TauCeti

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Module.Free R S]

/-- The trace form of a scalar-extended free algebra is the scalar extension
of its trace form. -/
@[simp]
theorem Algebra.traceForm_baseChange :
    Algebra.traceForm T (T ⊗[R] S) = (Algebra.traceForm R S).baseChange T := by
  ext x y
  simp [Algebra.traceForm_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.smul_def, mul_comm]

end TauCeti

namespace Submodule

variable {A A' K K' B L ι : Type*}
  [CommRing A] [CommRing A'] [Field K] [Field K'] [CommRing B] [Field L]
  [Algebra A K] [Algebra A A'] [Algebra A K'] [Algebra A' K'] [Algebra K K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']
  [Algebra A B] [Algebra A L] [Algebra B L] [Algebra K L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [Algebra.IsSeparable K L] [Finite ι]

/-- A trace-dual lattice commutes with scalar extension, including when the generic
scalar extension is a product of fields. The hypothesis presents the lattice by a
basis of the original field extension. -/
theorem traceDual_baseChange_of_basis (I : Submodule B L) (b : Basis ι K L)
    (hb : I.restrictScalars A = span A (Set.range b)) :
    (Algebra.traceForm K' (K' ⊗[K] L)).dualSubmodule
        (span A' ((fun x : L ↦ (1 : K') ⊗ₜ[K] x) '' (I : Set L))) =
      span A' ((fun x : L ↦ (1 : K') ⊗ₜ[K] x) ''
        (traceDual A K I : Set L)) := by
  have := b.finiteDimensional_of_finite
  rw [TauCeti.Algebra.traceForm_baseChange]
  simpa only [← Submodule.restrictScalars_traceDual, Submodule.coe_restrictScalars] using
    LinearMap.BilinForm.dualSubmodule_baseChange_of_basis
      (Algebra.traceForm K L) (traceForm_nondegenerate K L) (I.restrictScalars A) b hb

end Submodule

namespace Module.Basis

variable {A A' K K' B L ι : Type*}
  [CommRing A] [CommRing A'] [Field K] [Field K'] [CommRing B] [Field L]
  [Algebra A K] [Algebra A A'] [Algebra A K'] [Algebra A' K'] [Algebra K K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']
  [Algebra A B] [Algebra A L] [Algebra B L] [Algebra K L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K] [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
  [Algebra.IsSeparable K L] [Finite ι]

/-- For an integral basis of a finite free algebra with finite separable generic
fiber, extending its complementary module gives the trace dual of the extended
algebra lattice. The scalar-extended generic algebra need not be a field. -/
theorem traceDual_one_baseChange (b : Basis ι A B) :
    (Algebra.traceForm K' (K' ⊗[K] L)).dualSubmodule
        (Submodule.span A' (Set.range (fun x : B ↦
          (1 : K') ⊗ₜ[K] algebraMap B L x))) =
      Submodule.span A' ((fun x : L ↦ (1 : K') ⊗ₜ[K] x) ''
        (Submodule.traceDual A K (1 : Submodule B L) : Set L)) := by
  classical
  have hb : (1 : Submodule B L).restrictScalars A =
      Submodule.span A (Set.range (b.localizationLocalization K A⁰ L)) := by
    rw [Basis.localizationLocalization_span]
    ext x
    simp [Submodule.one_eq_range]
  simpa only [Submodule.one_eq_range, LinearMap.coe_range, ← Set.range_comp,
    Function.comp_def, Algebra.linearMap_apply] using
    Submodule.traceDual_baseChange_of_basis (A' := A') (K' := K')
      (1 : Submodule B L) (b.localizationLocalization K A⁰ L) hb

end Module.Basis
