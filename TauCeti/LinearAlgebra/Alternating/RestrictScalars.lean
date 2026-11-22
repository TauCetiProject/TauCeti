/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Scalar restriction and scalar lifting for alternating maps

An `A`-multilinear alternating map `f : M [⋀^ι]→ₗ[A] N` restricts along a scalar tower `(R, A)` to
an `R`-multilinear alternating map `f.restrictScalars R : M [⋀^ι]→ₗ[R] N`, extending
`MultilinearMap.restrictScalars`. Conversely, an `R`-multilinear alternating map lifts to an
`A`-multilinear alternating map if it is `A`-linear in each updated slot
(`AlternatingMap.mkOfUpdateSMul`) or on `Fin (n + 1)` if `curryLeft` is `A`-linear
(`AlternatingMap.mkOfCurryLeftSMul`).

## Main definitions

* `AlternatingMap.restrictScalars`: restrict an `A`-alternating map to `R`-scalars.
* `AlternatingMap.mkOfUpdateSMul`: promote an `R`-alternating map that is `A`-linear in each slot.
* `AlternatingMap.mkOfCurryLeftSMul`: promote an `R`-alternating map on `Fin (n + 1)` whose
  interior product `curryLeft` is `A`-linear.
-/

public section

namespace AlternatingMap

section RestrictScalars

variable (R : Type*) {A M N ι : Type*} [Semiring R] [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

/-- Reinterpret an `A`-multilinear alternating map as an `R`-multilinear alternating map along a
scalar tower. -/
def restrictScalars (f : M [⋀^ι]→ₗ[A] N) : M [⋀^ι]→ₗ[R] N where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq'

@[simp] theorem coe_restrictScalars (f : M [⋀^ι]→ₗ[A] N) : ⇑(f.restrictScalars R) = f := (rfl)

@[simp] theorem restrictScalars_apply (f : M [⋀^ι]→ₗ[A] N) (v : ι → M) :
    f.restrictScalars R v = f v := (rfl)

@[simp] theorem toMultilinearMap_restrictScalars (f : M [⋀^ι]→ₗ[A] N) :
    (f.restrictScalars R).toMultilinearMap = f.toMultilinearMap.restrictScalars R := (rfl)

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M [⋀^ι]→ₗ[A] N) → M [⋀^ι]→ₗ[R] N) :=
  fun _ _ h ↦ ext fun v ↦ congr($h v)

@[simp] theorem restrictScalars_zero : (0 : M [⋀^ι]→ₗ[A] N).restrictScalars R = 0 := (rfl)

@[simp] theorem restrictScalars_add (f g : M [⋀^ι]→ₗ[A] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R := (rfl)

@[simp] theorem restrictScalars_smul {S : Type*} [Monoid S] [DistribMulAction S N]
    [SMulCommClass A S N] [SMulCommClass R S N] (c : S) (f : M [⋀^ι]→ₗ[A] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R := (rfl)

end RestrictScalars

section RestrictScalarsRing

variable (R : Type*) {A M N ι : Type*} [Semiring R] [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommGroup N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

@[simp] theorem restrictScalars_neg (f : M [⋀^ι]→ₗ[A] N) :
    (-f).restrictScalars R = -f.restrictScalars R := (rfl)

@[simp] theorem restrictScalars_sub (f g : M [⋀^ι]→ₗ[A] N) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R := (rfl)

end RestrictScalarsRing

@[simp] theorem curryLeft_restrictScalars (R : Type*) {A M N : Type*}
    [CommSemiring R] [CommSemiring A] [SMul R A] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module A M] [Module R N] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N] {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[A] N) (x : M) :
    (f.restrictScalars R).curryLeft x = (f.curryLeft x).restrictScalars R := (rfl)

section LiftScalars

variable {R A M N ι : Type*} [Semiring R] [Semiring A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N]

section UpdateSMul

variable (f : M [⋀^ι]→ₗ[R] N)
  (hf : ∀ [DecidableEq ι] (v : ι → M) (i : ι) (a : A) (x : M),
    f (Function.update v i (a • x)) = a • f (Function.update v i x))

/-- Promote an `R`-multilinear alternating map that is `A`-linear in each slot to an `A`-multilinear
alternating map. -/
def mkOfUpdateSMul : M [⋀^ι]→ₗ[A] N where
  toFun := f
  map_update_add' := f.map_update_add'
  map_update_smul' v i a x := hf v i a x
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq'

@[simp] theorem coe_mkOfUpdateSMul : ⇑(mkOfUpdateSMul f @hf) = f := (rfl)

@[simp] theorem mkOfUpdateSMul_apply (v : ι → M) : mkOfUpdateSMul f @hf v = f v := (rfl)

@[simp] theorem restrictScalars_mkOfUpdateSMul [SMul R A] [IsScalarTower R A M]
    [IsScalarTower R A N] : (mkOfUpdateSMul f @hf).restrictScalars R = f := (rfl)

end UpdateSMul

end LiftScalars

section LiftScalarsFin

variable {R A M N : Type*} [CommRing R] [Semiring A]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module A M] [Module R N] [Module A N]
  [SMulCommClass R A N] {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
  (hf : ∀ (a : A) (x : M), f.curryLeft (a • x) = a • f.curryLeft x)

/-- Promote an `R`-multilinear alternating map in `n + 1` arguments to an `A`-multilinear
alternating map once its interior product `curryLeft` is `A`-linear. -/
def mkOfCurryLeftSMul : M [⋀^Fin (n + 1)]→ₗ[A] N :=
  mkOfUpdateSMul f fun {I'} v i a x ↦ by
    obtain rfl : I' = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    rw [← Fin.insertNth_removeNth i (a • x) v, ← Fin.insertNth_removeNth i x v,
      f.map_insertNth, f.map_insertNth, ← curryLeft_apply_apply, ← curryLeft_apply_apply,
      hf a x, smul_apply, smul_comm ((-1 : ℤ) ^ (i : ℕ)) a]

@[simp] theorem coe_mkOfCurryLeftSMul : ⇑(mkOfCurryLeftSMul f hf) = f := (rfl)

@[simp] theorem mkOfCurryLeftSMul_apply (v : Fin (n + 1) → M) :
    mkOfCurryLeftSMul f hf v = f v := (rfl)

@[simp] theorem restrictScalars_mkOfCurryLeftSMul [SMul R A] [IsScalarTower R A M]
    [IsScalarTower R A N] : (mkOfCurryLeftSMul f hf).restrictScalars R = f := (rfl)

end LiftScalarsFin

end AlternatingMap
