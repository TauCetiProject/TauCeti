/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Scalar restriction and scalar towers for alternating maps

This file supplies scalar-action utilities for `AlternatingMap` complementing
`Mathlib.LinearAlgebra.Alternating.Basic` and `Mathlib.LinearAlgebra.Alternating.Curry`:

* `AlternatingMap.instIsScalarTower`: alternating maps inherit scalar towers from their codomain.
* `AlternatingMap.restrictScalars`: scalar restriction of an `A`-multilinear alternating map to an
  `R`-multilinear alternating map along compatible scalar towers, together with injectivity and
  compatibility with algebraic operations and `curryLeft`.
* `AlternatingMap.ofCurryLeftSMul`: lifting an `R`-multilinear alternating map
  `M [⋀^Fin (n + 1)]→ₗ[R] N` that is `A`-homogeneous in its first argument (`curryLeft`) to an
  `A`-multilinear alternating map.
-/

public section

namespace AlternatingMap

/-- Alternating maps inherit scalar towers from their codomain. -/
instance instIsScalarTower {R S T M N ι : Type*}
    [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Monoid S] [Monoid T] [SMul S T]
    [DistribMulAction S N] [DistribMulAction T N]
    [SMulCommClass R S N] [SMulCommClass R T N] [IsScalarTower S T N] :
    IsScalarTower S T (M [⋀^ι]→ₗ[R] N) :=
  FunLike.isScalarTower

section RestrictScalars

variable (R : Type*) [Semiring R] {A M N ι : Type*} [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

/-- Reinterpret an `A`-multilinear alternating map as an `R`-multilinear alternating map along a
compatible scalar action of `R` on `A`. -/
def restrictScalars (f : M [⋀^ι]→ₗ[A] N) : M [⋀^ι]→ₗ[R] N where
  __ := f.toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq

@[simp] theorem coe_restrictScalars (f : M [⋀^ι]→ₗ[A] N) : ⇑(f.restrictScalars R) = f := (rfl)
@[simp] theorem restrictScalars_apply (f : M [⋀^ι]→ₗ[A] N) (v : ι → M) :
    f.restrictScalars R v = f v := (rfl)

/-- Scalar restriction on alternating maps is injective. -/
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

section RestrictScalarsAddCommGroup
variable (R : Type*) [Semiring R] {A M N : Type*} [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommGroup N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

@[simp] theorem restrictScalars_neg {ι : Type*} (f : M [⋀^ι]→ₗ[A] N) :
    (-f).restrictScalars R = -f.restrictScalars R := (rfl)
@[simp] theorem restrictScalars_sub {ι : Type*} (f g : M [⋀^ι]→ₗ[A] N) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R := (rfl)
end RestrictScalarsAddCommGroup

section RestrictScalarsCommSemiring
variable (R : Type*) [CommSemiring R] {A M N : Type*} [CommSemiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

@[simp] theorem restrictScalars_curryLeft {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[A] N) (m : M) :
    (f.curryLeft m).restrictScalars R = (f.restrictScalars R).curryLeft m := (rfl)
end RestrictScalarsCommSemiring

section OfCurryLeftSMul
variable {R A M N : Type*} [CommSemiring R] [Semiring A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N] {n : ℕ}

/-- Build an `A`-multilinear alternating map from an `R`-multilinear alternating map that is
`A`-homogeneous in its first argument. -/
def ofCurryLeftSMul (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (m : M) (w : Fin n → M), f.curryLeft (a • m) w = a • f.curryLeft m w) :
    M [⋀^Fin (n + 1)]→ₗ[A] N where
  toFun := f
  map_update_add' := by intro _ m i x y; exact f.map_update_add m i x y
  map_update_smul' := by
    intro inst v i a m
    obtain rfl : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    by_cases hi : i = 0
    · subst hi
      have h₁ : Function.update v 0 (a • m) = Matrix.vecCons (a • m) (Fin.tail v) := by
        ext j; refine Fin.cases (by simp) (fun _ ↦ by simp [Fin.tail]) j
      have h₂ : Function.update v 0 m = Matrix.vecCons m (Fin.tail v) := by
        ext j; refine Fin.cases (by simp) (fun _ ↦ by simp [Fin.tail]) j
      rw [h₁, h₂]; exact hf a m (Fin.tail v)
    · let u₁ : Fin (n + 1) → M := Function.update v i (a • m)
      let u₂ : Fin (n + 1) → M := Function.update v i m
      have hswap : f (u₁ ∘ Equiv.swap 0 i) = a • f (u₂ ∘ Equiv.swap 0 i) := by
        have hu₁ : u₁ ∘ Equiv.swap 0 i =
            Matrix.vecCons (a • m) (Fin.tail (u₂ ∘ Equiv.swap 0 i)) := by
          ext j; refine Fin.cases (by simp [u₁]) (fun j ↦ ?_) j
          have hne : Equiv.swap 0 i j.succ ≠ i := fun h ↦
            Fin.succ_ne_zero j <| (Equiv.swap 0 i).injective <|
              h.trans (Equiv.swap_apply_left 0 i).symm
          simp [u₁, u₂, Fin.tail, hne]
        have hu₂ : u₂ ∘ Equiv.swap 0 i =
            Matrix.vecCons m (Fin.tail (u₂ ∘ Equiv.swap 0 i)) := by
          ext j; refine Fin.cases (by simp [u₂]) (fun _ ↦ by simp [Fin.tail]) j
        rw [hu₁, hu₂]; exact hf a m (Fin.tail (u₂ ∘ Equiv.swap 0 i))
      have h₁ : f (u₁ ∘ Equiv.swap 0 i) + f u₁ = 0 := f.map_swap_add u₁ (Ne.symm hi)
      have h₂ : f (u₁ ∘ Equiv.swap 0 i) + a • f u₂ = 0 := by
        rw [hswap, ← smul_add, f.map_swap_add u₂ (Ne.symm hi), smul_zero]
      rw [← zero_add (f u₁), ← h₂, add_right_comm _ (a • f u₂), h₁, zero_add]; rfl
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq

@[simp] theorem coe_ofCurryLeftSMul (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (m : M) (w : Fin n → M), f.curryLeft (a • m) w = a • f.curryLeft m w) :
    ⇑(ofCurryLeftSMul f hf) = f := (rfl)
@[simp] theorem ofCurryLeftSMul_apply (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (m : M) (w : Fin n → M), f.curryLeft (a • m) w = a • f.curryLeft m w)
    (v : Fin (n + 1) → M) : ofCurryLeftSMul f hf v = f v := (rfl)
@[simp] theorem restrictScalars_ofCurryLeftSMul [SMul R A] [IsScalarTower R A M]
    [IsScalarTower R A N] (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (m : M) (w : Fin n → M), f.curryLeft (a • m) w = a • f.curryLeft m w) :
    (ofCurryLeftSMul f hf).restrictScalars R = f := by ext v; simp
end OfCurryLeftSMul

end AlternatingMap
