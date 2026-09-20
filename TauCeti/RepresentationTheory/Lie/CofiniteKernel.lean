/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Cofinite kernels of finite-dimensional Lie representations

A representation `ρ : L →ₗ⁅K⁆ Module.End K V` extends along the universal property to an algebra
homomorphism `UniversalEnvelopingAlgebra.lift K ρ`.  When `V` is finite-dimensional, the kernel of
this extension is cofinite: its quotient embeds linearly in the finite-dimensional endomorphism
algebra of `V`.  As a ring-homomorphism kernel it is automatically a two-sided ideal in Mathlib's
ideal API.

The same kernel records nilpotence of the original action.  For `x : L`, the endomorphism `ρ x` is
nilpotent exactly when some power of the canonical generator `ι x` belongs to the kernel.  This is
the form needed when a finite-dimensional representation is replaced by a smaller ideal while
preserving nilpotence of selected operators.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.finiteDimensional_quotient_ker_lift`: its quotient is
  finite-dimensional.
* `TauCeti.UniversalEnvelopingAlgebra.isNilpotent_iff_exists_pow_ι_mem_ker_lift`: nilpotence of an
  operator is equivalent to membership of a power of its enveloping generator in the kernel.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) (L : Type v) [LieRing L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section FiniteDimensional

variable [Field R] [LieAlgebra R L]
variable {V : Type w} [AddCommGroup V] [Module R V]

/-- The quotient by the kernel of the enveloping-algebra extension of a finite-dimensional
representation is finite-dimensional. -/
theorem finiteDimensional_quotient_ker_lift [FiniteDimensional R V]
    (ρ : L →ₗ⁅R⁆ Module.End R V) :
    FiniteDimensional R
      (U ⧸ RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R ρ)) := by
  let q := _root_.UniversalEnvelopingAlgebra.lift R ρ
  let _ : FiniteDimensional R q.range :=
    FiniteDimensional.of_injective q.range.val.toLinearMap Subtype.val_injective
  exact Module.Finite.equiv
    (Ideal.quotientKerEquivRange q).symm.toLinearEquiv

end FiniteDimensional

section Nilpotence

variable [CommRing R] [LieAlgebra R L]
variable {V : Type w} [AddCommGroup V] [Module R V]

/-- A power of the canonical enveloping generator belongs to the kernel of the extended
representation exactly when the corresponding power of the acting endomorphism vanishes. -/
theorem pow_ι_mem_ker_lift_iff (ρ : L →ₗ⁅R⁆ Module.End R V) (x : L) (n : ℕ) :
    (_root_.UniversalEnvelopingAlgebra.ι R x) ^ n ∈
        RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R ρ) ↔
      (ρ x) ^ n = 0 := by
  rw [RingHom.mem_ker, map_pow, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]

/-- An element acts nilpotently in a representation exactly when some power of its canonical
enveloping-algebra generator belongs to the kernel of the extended representation. -/
theorem isNilpotent_iff_exists_pow_ι_mem_ker_lift (ρ : L →ₗ⁅R⁆ Module.End R V) (x : L) :
    IsNilpotent (ρ x) ↔
      ∃ n : ℕ, (_root_.UniversalEnvelopingAlgebra.ι R x) ^ n ∈
        RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R ρ) := by
  simp only [IsNilpotent, pow_ι_mem_ker_lift_iff]

end Nilpotence

end UniversalEnvelopingAlgebra

end TauCeti
