/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficient algebras on subrings of formal power series

Any subring `A` of `R⟦X⟧` that contains all constant power series `C r` inherits an `S`-algebra
structure from any `S`-algebra structure on the coefficient ring `R`, without requiring `R` to be
commutative: a scalar `s : S` maps to the constant series `C (algebraMap S R s)` and acts as on the
ambient formal power series, and scalar towers on `R` lift to `A`.

This packages the common algebra structure of `PowerSeries.IsRestricted.subring` and
`PowerSeries.OnOpenDisc.subring`.

## Main definitions

* `PowerSeries.subringAlgebra`: the `Algebra S A` structure on a subring `A : Subring R⟦X⟧`
  containing all constant series `C r`.

## Main results

* `PowerSeries.coe_algebraMap_subringAlgebra`, `PowerSeries.coe_smul_subringAlgebra`: the algebra
  map and scalar action agree with those on `R⟦X⟧`.
* `PowerSeries.subringIsScalarTower`: scalar towers on `R` lift to `A`.
-/

public section

namespace PowerSeries

variable {S : Type*} [CommSemiring S] {R : Type*} [Ring R] [Algebra S R] {A : Subring R⟦X⟧}

/-- An `S`-algebra structure on the coefficients induces one on any subring `A` of `R⟦X⟧` that
contains all constant series `C r`. Scalars act as on the ambient formal series, and the
coefficient ring `R` need not be commutative. -/
@[expose, instance_reducible]
noncomputable def subringAlgebra (hC : ∀ r : R, C r ∈ A) : Algebra S A where
  smul s f := ⟨s • (f : R⟦X⟧), by
    rw [Algebra.smul_def, PowerSeries.algebraMap_apply]
    exact A.mul_mem (hC (algebraMap S R s)) f.2⟩
  algebraMap := (algebraMap S R⟦X⟧).codRestrict A fun s ↦ by
    rw [PowerSeries.algebraMap_apply]
    exact hC _
  commutes' s f := Subtype.ext <| by
    simpa only [Subring.coe_mul, RingHom.codRestrict_apply] using
      Algebra.commutes s (f : R⟦X⟧)
  smul_def' s f := Subtype.ext <| by
    rw [Subring.coe_mul, RingHom.codRestrict_apply]
    exact Algebra.smul_def s (f : R⟦X⟧)

/-- For `PowerSeries.subringAlgebra`, a scalar maps to the constant series of its image in `R`. -/
theorem coe_algebraMap_subringAlgebra (hC : ∀ r : R, C r ∈ A) (s : S) :
    (@algebraMap S A _ _ (subringAlgebra hC) s : R⟦X⟧) = C (algebraMap S R s) := by
  let : Algebra S A := subringAlgebra hC
  exact PowerSeries.algebraMap_apply

/-- For `PowerSeries.subringAlgebra`, scalars act as on the ambient formal power series. -/
theorem coe_smul_subringAlgebra (hC : ∀ r : R, C r ∈ A) (s : S) (f : A) :
    ((@SMul.smul S A (subringAlgebra hC).toSMul s f : A) : R⟦X⟧) = s • (f : R⟦X⟧) :=
  (rfl)

/-- Scalar towers on the coefficients lift to `PowerSeries.subringAlgebra`. -/
theorem subringIsScalarTower {T : Type*} [CommSemiring T] [Algebra T R] [SMul S T]
    [IsScalarTower S T R] (hC : ∀ r : R, C r ∈ A) :
    @IsScalarTower S T A _ (subringAlgebra hC).toSMul (subringAlgebra hC).toSMul := by
  let : Algebra S A := subringAlgebra hC
  let : Algebra T A := subringAlgebra hC
  exact ⟨fun s t f ↦ Subtype.ext (smul_assoc s t (f : R⟦X⟧))⟩

end PowerSeries
