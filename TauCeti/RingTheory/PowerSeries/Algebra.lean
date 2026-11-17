/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficient algebra structures on subsemirings of power series

Any subsemiring (in particular, any subring) of formal power series `R⟦X⟧` that contains all
constant series `PowerSeries.C a` inherits an `S`-algebra structure whenever the coefficient
semiring `R` is an `S`-algebra. The algebra map sends `s : S` to `PowerSeries.C (algebraMap S R s)`,
scalars act coefficientwise as in the ambient ring `R⟦X⟧`, and scalar towers `S → T → R` lift to
scalar towers on the subsemiring. No commutativity of `R` and no analytic or metric structure are
required.

This factors the shared coefficient-algebra construction for subrings of power series such as
restricted, entire, and open-disc power series.

## Main declarations

* `TauCeti.PowerSeries.algebraOfCMem`: the `S`-algebra structure on a subsemiring of `R⟦X⟧`
  containing all constant series.
* `TauCeti.PowerSeries.coe_algebraMap_algebraOfCMem`: under `algebraOfCMem`, a scalar maps to the
  constant series of its image in the coefficient ring.
* `TauCeti.PowerSeries.coe_smul_algebraOfCMem`: under `algebraOfCMem`, scalars act as on the
  ambient formal power series.
* `TauCeti.PowerSeries.isScalarTower_algebraOfCMem`: scalar towers on the coefficients induce
  scalar towers on the subsemiring.
-/

public section

namespace TauCeti.PowerSeries

section

variable {R S σ : Type*} [Semiring R] [CommSemiring S] [Algebra S R]
  [SetLike σ (PowerSeries R)] [SubsemiringClass σ (PowerSeries R)]

/-- An algebra structure on the coefficients induces one on any subsemiring (in particular, any
subring) of `R⟦X⟧` containing all constant series, with scalars acting as on the ambient formal
series. See note [reducible non-instances]. -/
noncomputable abbrev algebraOfCMem (T : σ) (hC : ∀ a : R, PowerSeries.C a ∈ T) : Algebra S T where
  smul s f := ⟨s • (f : PowerSeries R), by
    rw [Algebra.smul_def, PowerSeries.algebraMap_apply]
    exact mul_mem (hC (algebraMap S R s)) f.2⟩
  algebraMap := (algebraMap S (PowerSeries R)).codRestrict T fun s ↦ by
    rw [PowerSeries.algebraMap_apply]
    exact hC _
  commutes' s f := Subtype.ext <| by
    simpa only [MulMemClass.coe_mul, RingHom.codRestrict_apply] using
      Algebra.commutes s (f : PowerSeries R)
  smul_def' s f := Subtype.ext <| by
    rw [MulMemClass.coe_mul, RingHom.codRestrict_apply]
    exact Algebra.smul_def s (f : PowerSeries R)

/-- Under `algebraOfCMem`, a scalar maps to the constant series of its image in the coefficient
ring. -/
theorem coe_algebraMap_algebraOfCMem (T : σ) (hC : ∀ a : R, PowerSeries.C a ∈ T) (s : S) :
    ((@algebraMap S T _ _ (algebraOfCMem T hC) s : T) : PowerSeries R) =
      PowerSeries.C (algebraMap S R s) :=
  (RingHom.codRestrict_apply _ _ _ s).trans PowerSeries.algebraMap_apply

/-- Under `algebraOfCMem`, scalars act as on the ambient formal power series. -/
theorem coe_smul_algebraOfCMem (T : σ) (hC : ∀ a : R, PowerSeries.C a ∈ T) (s : S) (f : T) :
    ((@SMul.smul S T (algebraOfCMem T hC).toSMul s f : T) : PowerSeries R) =
      s • (f : PowerSeries R) := (rfl)

end

/-- Scalar towers on the coefficients induce scalar towers on any subsemiring of `R⟦X⟧` equipped
with `algebraOfCMem`. -/
theorem isScalarTower_algebraOfCMem {R S T σ : Type*} [Semiring R] [CommSemiring S]
    [CommSemiring T] [Algebra S R] [Algebra T R] [SMul S T] [IsScalarTower S T R]
    [SetLike σ (PowerSeries R)] [SubsemiringClass σ (PowerSeries R)] (U : σ)
    (hC : ∀ a : R, PowerSeries.C a ∈ U) :
    @IsScalarTower S T U _ (algebraOfCMem (S := T) U hC).toSMul
      (algebraOfCMem (S := S) U hC).toSMul :=
  @IsScalarTower.mk S T U _ (algebraOfCMem (S := T) U hC).toSMul
    (algebraOfCMem (S := S) U hC).toSMul fun s t f ↦
      Subtype.ext (smul_assoc s t (f : PowerSeries R))

end TauCeti.PowerSeries
