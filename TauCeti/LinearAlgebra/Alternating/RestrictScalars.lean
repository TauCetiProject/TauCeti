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
`MultilinearMap.restrictScalars`.

Conversely, an `R`-multilinear alternating map lifts to an `A`-multilinear alternating map as soon
as it is `A`-linear in each updated slot (`AlternatingMap.mkOfUpdateSMul`). On `Fin (n + 1)`-tuples,
alternation reduces `A`-linearity in every slot to `A`-linearity of the interior product
`x ↦ f.curryLeft x` in the first slot (`AlternatingMap.mkOfCurryLeftSMul`), while on an empty
index type the condition is vacuous (`AlternatingMap.mkOfIsEmptyScalars`).

## Main definitions

* `AlternatingMap.restrictScalars`: restrict an `A`-alternating map to `R`-scalars.
* `AlternatingMap.restrictScalarsLinearMap`: scalar restriction bundled as a linear map.
* `AlternatingMap.mkOfUpdateSMul`: promote an `R`-alternating map that is `A`-linear in each slot
  to an `A`-alternating map.
* `AlternatingMap.mkOfCurryLeftSMul`: promote an `R`-alternating map on `Fin (n + 1)` whose
  interior product `curryLeft` is `A`-linear to an `A`-alternating map.
* `AlternatingMap.mkOfIsEmptyScalars`: promote an `R`-alternating map on an empty index type to an
  `A`-alternating map.
-/

@[expose] public section

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

@[simp]
theorem coe_restrictScalars (f : M [⋀^ι]→ₗ[A] N) : ⇑(f.restrictScalars R) = f :=
  (rfl)

@[simp]
theorem restrictScalars_apply (f : M [⋀^ι]→ₗ[A] N) (v : ι → M) :
    f.restrictScalars R v = f v :=
  (rfl)

@[simp]
theorem toMultilinearMap_restrictScalars (f : M [⋀^ι]→ₗ[A] N) :
    (f.restrictScalars R).toMultilinearMap = f.toMultilinearMap.restrictScalars R :=
  (rfl)

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M [⋀^ι]→ₗ[A] N) → M [⋀^ι]→ₗ[R] N) :=
  fun _ _ h ↦ ext fun v ↦ congr($h v)

@[simp]
theorem restrictScalars_zero : (0 : M [⋀^ι]→ₗ[A] N).restrictScalars R = 0 :=
  (rfl)

@[simp]
theorem restrictScalars_add (f g : M [⋀^ι]→ₗ[A] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  (rfl)

@[simp]
theorem restrictScalars_smul {S : Type*} [Monoid S] [DistribMulAction S N]
    [SMulCommClass A S N] [SMulCommClass R S N] (c : S) (f : M [⋀^ι]→ₗ[A] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  (rfl)

/-- Scalar restriction of alternating maps bundled as an `S`-linear map. -/
def restrictScalarsLinearMap (S : Type*) [Semiring S] [Module S N]
    [SMulCommClass A S N] [SMulCommClass R S N] :
    (M [⋀^ι]→ₗ[A] N) →ₗ[S] M [⋀^ι]→ₗ[R] N where
  toFun := restrictScalars R
  map_add' := restrictScalars_add R
  map_smul' := restrictScalars_smul R

@[simp]
theorem restrictScalarsLinearMap_apply (S : Type*) [Semiring S] [Module S N]
    [SMulCommClass A S N] [SMulCommClass R S N] (f : M [⋀^ι]→ₗ[A] N) :
    restrictScalarsLinearMap R S f = f.restrictScalars R :=
  (rfl)

end RestrictScalars

section RestrictScalarsRing

variable (R : Type*) {A M N ι : Type*} [Semiring R] [Semiring A] [SMul R A]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

@[simp]
theorem restrictScalars_neg (f : M [⋀^ι]→ₗ[A] N) :
    (-f).restrictScalars R = -f.restrictScalars R :=
  (rfl)

@[simp]
theorem restrictScalars_sub (f g : M [⋀^ι]→ₗ[A] N) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R :=
  (rfl)

end RestrictScalarsRing

section CurryLeft

variable (R : Type*) {A M N : Type*} [CommSemiring R] [CommSemiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

@[simp]
theorem curryLeft_restrictScalars {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[A] N) (x : M) :
    (f.restrictScalars R).curryLeft x = (f.curryLeft x).restrictScalars R :=
  (rfl)

end CurryLeft

section LiftScalars

variable {R A M N ι : Type*} [Semiring R] [Semiring A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N]

/-- Promote an `R`-multilinear alternating map that is `A`-linear in each slot to an `A`-multilinear
alternating map. -/
def mkOfUpdateSMul (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ [DecidableEq ι] (v : ι → M) (i : ι) (a : A) (x : M),
      f (Function.update v i (a • x)) = a • f (Function.update v i x)) :
    M [⋀^ι]→ₗ[A] N where
  toFun := f
  map_update_add' := f.map_update_add'
  map_update_smul' v i a x := hf v i a x
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq'

@[simp]
theorem coe_mkOfUpdateSMul (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ [DecidableEq ι] (v : ι → M) (i : ι) (a : A) (x : M),
      f (Function.update v i (a • x)) = a • f (Function.update v i x)) :
    ⇑(mkOfUpdateSMul f hf) = f :=
  (rfl)

@[simp]
theorem mkOfUpdateSMul_apply (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ [DecidableEq ι] (v : ι → M) (i : ι) (a : A) (x : M),
      f (Function.update v i (a • x)) = a • f (Function.update v i x)) (v : ι → M) :
    mkOfUpdateSMul f hf v = f v :=
  (rfl)

@[simp]
theorem restrictScalars_mkOfUpdateSMul [SMul R A] [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ [DecidableEq ι] (v : ι → M) (i : ι) (a : A) (x : M),
      f (Function.update v i (a • x)) = a • f (Function.update v i x)) :
    (mkOfUpdateSMul f hf).restrictScalars R = f :=
  (rfl)

/-- On an empty index type, any `R`-alternating map is vacuously `A`-multilinear. -/
def mkOfIsEmptyScalars (A : Type*) [Semiring A] [Module A M] [Module A N] [IsEmpty ι]
    (f : M [⋀^ι]→ₗ[R] N) : M [⋀^ι]→ₗ[A] N :=
  mkOfUpdateSMul f fun _ i ↦ isEmptyElim i

@[simp]
theorem coe_mkOfIsEmptyScalars (A : Type*) [Semiring A] [Module A M] [Module A N] [IsEmpty ι]
    (f : M [⋀^ι]→ₗ[R] N) : ⇑(mkOfIsEmptyScalars A f) = f :=
  (rfl)

@[simp]
theorem mkOfIsEmptyScalars_apply (A : Type*) [Semiring A] [Module A M] [Module A N] [IsEmpty ι]
    (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) : mkOfIsEmptyScalars A f v = f v :=
  (rfl)

@[simp]
theorem restrictScalars_mkOfIsEmptyScalars [SMul R A] [IsScalarTower R A M] [IsScalarTower R A N]
    [IsEmpty ι] (f : M [⋀^ι]→ₗ[R] N) :
    (mkOfIsEmptyScalars A f).restrictScalars R = f :=
  (rfl)

end LiftScalars

section LiftScalarsFin

variable {R A M N : Type*} [CommRing R] [Semiring A]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module A M] [Module R N] [Module A N]
  [SMulCommClass R A N]

/-- Promote an `R`-multilinear alternating map in `n + 1` arguments to an `A`-multilinear
alternating map once its interior product `curryLeft` is `A`-linear. -/
def mkOfCurryLeftSMul {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (x : M), f.curryLeft (a • x) = a • f.curryLeft x) :
    M [⋀^Fin (n + 1)]→ₗ[A] N :=
  mkOfUpdateSMul f fun {I'} v i a x ↦ by
    -- Alternation moves the `i`-th slot to the front via `Fin.insertNth_removeNth`.
    obtain rfl : I' = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    rw [← Fin.insertNth_removeNth i (a • x) v, ← Fin.insertNth_removeNth i x v,
      f.map_insertNth, f.map_insertNth, ← curryLeft_apply_apply, ← curryLeft_apply_apply,
      hf a x, smul_apply, smul_comm ((-1 : ℤ) ^ (i : ℕ)) a]

@[simp]
theorem coe_mkOfCurryLeftSMul {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (x : M), f.curryLeft (a • x) = a • f.curryLeft x) :
    ⇑(mkOfCurryLeftSMul f hf) = f :=
  (rfl)

@[simp]
theorem mkOfCurryLeftSMul_apply {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (x : M), f.curryLeft (a • x) = a • f.curryLeft x) (v : Fin (n + 1) → M) :
    mkOfCurryLeftSMul f hf v = f v :=
  (rfl)

@[simp]
theorem restrictScalars_mkOfCurryLeftSMul [SMul R A] [IsScalarTower R A M] [IsScalarTower R A N]
    {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (x : M), f.curryLeft (a • x) = a • f.curryLeft x) :
    (mkOfCurryLeftSMul f hf).restrictScalars R = f :=
  (rfl)

end LiftScalarsFin

end AlternatingMap
