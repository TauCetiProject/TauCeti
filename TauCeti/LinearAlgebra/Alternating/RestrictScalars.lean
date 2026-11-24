/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Restricting scalars of an alternating map

Given a scalar tower `R → S` acting compatibly on `M` and `N`, any `S`-alternating map
`M [⋀^ι]→ₗ[S] N` can be reinterpreted as an `R`-alternating map `M [⋀^ι]→ₗ[R] N` via
`AlternatingMap.restrictScalars`. This extends Mathlib's `MultilinearMap.restrictScalars` to
alternating maps.
-/

public section

namespace AlternatingMap

variable (R : Type*) {S M N ι : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S M] [Module R N] [Module S N]
  [IsScalarTower R S M] [IsScalarTower R S N]

/-- Reinterpret an `S`-alternating map as an `R`-alternating map along scalar towers
`IsScalarTower R S M` and `IsScalarTower R S N`. -/
def restrictScalars (f : M [⋀^ι]→ₗ[S] N) : M [⋀^ι]→ₗ[R] N :=
  { f.toMultilinearMap.restrictScalars R with
    map_eq_zero_of_eq' := fun v _ _ h hij => f.map_eq_zero_of_eq v h hij }

/-- Coercion of `f.restrictScalars R` to a function agrees with `f`. -/
@[simp]
theorem coe_restrictScalars (f : M [⋀^ι]→ₗ[S] N) : ⇑(f.restrictScalars R) = f :=
  (rfl)

/-- Applying `f.restrictScalars R` to a family of vectors agrees with `f`. -/
theorem restrictScalars_apply (f : M [⋀^ι]→ₗ[S] N) (v : ι → M) :
    f.restrictScalars R v = f v :=
  (rfl)

/-- The underlying multilinear map of `f.restrictScalars R` is
`f.toMultilinearMap.restrictScalars R`. -/
@[simp]
theorem toMultilinearMap_restrictScalars (f : M [⋀^ι]→ₗ[S] N) :
    (f.restrictScalars R : (ι → M) →ₘₗ[R] N) = f.toMultilinearMap.restrictScalars R :=
  (rfl)

/-- Restricting scalars to the base ring `R` is the identity on `R`-alternating maps. -/
@[simp]
theorem restrictScalars_self (f : M [⋀^ι]→ₗ[R] N) : f.restrictScalars R = f :=
  ext fun _ => rfl

/-- `AlternatingMap.restrictScalars R` is injective. -/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M [⋀^ι]→ₗ[S] N) → M [⋀^ι]→ₗ[R] N) :=
  fun _ _ h => ext fun v => by simpa using AlternatingMap.congr_fun h v

/-- Two `S`-alternating maps agree after restricting scalars to `R` iff they are equal. -/
@[simp]
theorem restrictScalars_inj (f g : M [⋀^ι]→ₗ[S] N) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff

end AlternatingMap
