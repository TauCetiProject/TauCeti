/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The scalar-torsion ideal of an algebra

The elements of an algebra killed by a regular scalar form an ideal. Its underlying scalar
submodule is Mathlib's torsion submodule, and its quotient is torsion-free over a domain.
This ideal is useful for constructing flat closures of affine group schemes over Dedekind domains.

The construction uses `Submodule.torsion` and the quotient-torsion argument from
`Mathlib.Algebra.Module.Torsion.Basic`.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

universe u v

section Semiring

variable (R : Type u) [CommSemiring R] (A : Type v) [Semiring A] [Algebra R A]

/-- The ideal of elements annihilated by a non-zero-divisor of the scalar ring. -/
def scalarTorsionIdeal : Ideal A where
  __ := (Submodule.torsion R A).toAddSubmonoid
  smul_mem' a x hx := by
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff x).mp hx
    exact (Submodule.mem_torsion_iff (a * x)).mpr ⟨r, by rw [← mul_smul_comm, hr, mul_zero]⟩

variable {R A} in
/-- Scalar-torsion ideal membership is annihilation by a regular scalar. -/
@[simp]
theorem mem_scalarTorsionIdeal {x : A} :
    x ∈ scalarTorsionIdeal R A ↔ ∃ r : R⁰, r • x = 0 :=
  Submodule.mem_torsion_iff x

/-- The scalar submodule underlying the scalar-torsion ideal is the torsion submodule. -/
@[simp]
theorem restrictScalars_scalarTorsionIdeal :
    (scalarTorsionIdeal R A).restrictScalars R = Submodule.torsion R A := by
  ext
  simp

end Semiring

variable (R : Type u) [CommRing R] [IsDomain R] (A : Type v) [Ring A] [Algebra R A]

/-- Quotienting an algebra by its scalar-torsion ideal gives a torsion-free scalar module. -/
instance isTorsionFree_quotient_scalarTorsionIdeal :
    Module.IsTorsionFree R (A ⧸ scalarTorsionIdeal R A) := by
  let e := (Submodule.Quotient.restrictScalarsEquiv R (scalarTorsionIdeal R A)).trans
    (Submodule.quotEquivOfEq _ _ (restrictScalars_scalarTorsionIdeal R A))
  exact e.injective.moduleIsTorsionFree e e.map_smul

end TauCeti
