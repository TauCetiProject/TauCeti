/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Restriction of scalars for alternating maps

Given an `A`-alternating map `f : M [⋀^ι]→ₗ[A] N` and a compatible action of `R` on `A`, `M`,
and `N`, `AlternatingMap.restrictScalars R f` reinterprets `f` as an `R`-alternating map
`M [⋀^ι]→ₗ[R] N` with the same underlying function. This is the alternating counterpart of
`MultilinearMap.restrictScalars`.

## Main definitions

* `AlternatingMap.instIsScalarTower`: pointwise `IsScalarTower` instance on `M [⋀^ι]→ₗ[R] N`.
* `AlternatingMap.restrictScalars`: scalar restriction `M [⋀^ι]→ₗ[A] N → M [⋀^ι]→ₗ[R] N`.
* `AlternatingMap.restrictScalarsLM`: `AlternatingMap.restrictScalars` bundled as an `S`-linear
  map for any scalar ring `S` whose action on `N` commutes with those of `R` and `A`.
-/

public section

namespace AlternatingMap

instance instIsScalarTower {R M N ι S T : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Monoid S] [Monoid T] [DistribMulAction S N] [DistribMulAction T N]
    [SMulCommClass R S N] [SMulCommClass R T N] [SMul S T] [IsScalarTower S T N] :
    IsScalarTower S T (M [⋀^ι]→ₗ[R] N) :=
  FunLike.isScalarTower

section Semiring

variable (R : Type*) {A M N ι : Type*} [Semiring R] [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module A N] [IsScalarTower R A N]

/-- Reinterpret an `A`-alternating map as an `R`-alternating map when the actions of `R` and `A`
form scalar towers on the domain and codomain. -/
def restrictScalars (f : M [⋀^ι]→ₗ[A] N) : M [⋀^ι]→ₗ[R] N where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq'

@[simp]
theorem coe_restrictScalars (f : M [⋀^ι]→ₗ[A] N) : ⇑(f.restrictScalars R) = f :=
  (rfl)

@[simp]
theorem restrictScalars_apply (f : M [⋀^ι]→ₗ[A] N) (v : ι → M) : f.restrictScalars R v = f v :=
  (rfl)

@[simp]
theorem toMultilinearMap_restrictScalars (f : M [⋀^ι]→ₗ[A] N) :
    (f.restrictScalars R).toMultilinearMap = f.toMultilinearMap.restrictScalars R :=
  (rfl)

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M [⋀^ι]→ₗ[A] N) → M [⋀^ι]→ₗ[R] N) := fun _ _ h ↦
  ext fun v ↦ congr($h v)

@[simp]
theorem restrictScalars_inj {f g : M [⋀^ι]→ₗ[A] N} :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff

@[simp]
theorem restrictScalars_zero : (0 : M [⋀^ι]→ₗ[A] N).restrictScalars R = 0 :=
  ext fun _ ↦ rfl

@[simp]
theorem restrictScalars_add (f g : M [⋀^ι]→ₗ[A] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  ext fun _ ↦ rfl

@[simp]
theorem restrictScalars_smul {S : Type*} [Monoid S] [DistribMulAction S N]
    [SMulCommClass A S N] [SMulCommClass R S N] (c : S) (f : M [⋀^ι]→ₗ[A] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  ext fun _ ↦ rfl

/-- Scalar restriction bundled as an `S`-linear map. -/
def restrictScalarsLM (S : Type*) [Semiring S] [Module S N]
    [SMulCommClass A S N] [SMulCommClass R S N] :
    (M [⋀^ι]→ₗ[A] N) →ₗ[S] M [⋀^ι]→ₗ[R] N where
  toFun := restrictScalars R
  map_add' := restrictScalars_add R
  map_smul' := restrictScalars_smul R

@[simp]
theorem restrictScalarsLM_apply (S : Type*) [Semiring S] [Module S N]
    [SMulCommClass A S N] [SMulCommClass R S N] (f : M [⋀^ι]→ₗ[A] N) :
    restrictScalarsLM R S f = f.restrictScalars R :=
  (rfl)

end Semiring

section Group

variable (R : Type*) {A M N ι : Type*} [Semiring R] [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommGroup N] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module A N] [IsScalarTower R A N]

@[simp]
theorem restrictScalars_neg (f : M [⋀^ι]→ₗ[A] N) :
    (-f).restrictScalars R = -f.restrictScalars R :=
  ext fun _ ↦ rfl

@[simp]
theorem restrictScalars_sub (f g : M [⋀^ι]→ₗ[A] N) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R :=
  ext fun _ ↦ rfl

end Group

section Curry

variable (R : Type*) {A M N : Type*} [CommSemiring R] [CommSemiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module A N] [IsScalarTower R A N]

@[simp]
theorem curryLeft_restrictScalars {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[A] N) (x : M) :
    (f.restrictScalars R).curryLeft x = (f.curryLeft x).restrictScalars R :=
  ext fun _ ↦ rfl

end Curry

end AlternatingMap
