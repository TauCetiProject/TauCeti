/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Currying the first argument of a multilinear map into its values

A multilinear map `f` in `n + 1` arguments determines the multilinear map in the last `n`
arguments whose value at `(m₁, …, mₙ)` is the linear map `m₀ ↦ f (m₀, m₁, …, mₙ)`. This gives a
linear equivalence `TauCeti.multilinearCurryFirstEquiv`. It differs from Mathlib's
`multilinearCurryLeftEquiv`, which curries the first argument outside, into linear maps valued in
multilinear maps, and is the first-argument counterpart of `multilinearCurryRightEquiv`.

Cochains with values in linear maps out of an algebra arise in this way from cochains with one
more argument, which is how scalar Hochschild cochains are compared with cochains valued in the
dual bimodule.

Fixing a single argument `p : Fin (n + 1)` of a multilinear map `f` to `x : M p` produces a
multilinear map `MultilinearMap.compInsertNth f p x` in the remaining `n` arguments over any scalar
semiring, without the commutativity hypothesis required by `MultilinearMap.curryMid` to vary `x`
linearly. When the target carries a commuting `S`-module structure, this operation is `S`-linear in
`f` (`MultilinearMap.compInsertNthLinearMap`).

## Main definitions

* `TauCeti.multilinearCurryFirstEquiv`: `f ↦ ((m₁, …, mₙ) ↦ (m₀ ↦ f (m₀, m₁, …, mₙ)))`.
* `MultilinearMap.compInsertNth`, `MultilinearMap.compInsertNthLinearMap`: fixing argument `p` of a
  multilinear map to `x` via `Fin.insertNth`, bundled as a linear map in the multilinear map.
-/

public section

namespace TauCeti

variable (R : Type*) {n : ℕ} (M : Fin (n + 1) → Type*) (N : Type*) [CommSemiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]

/-- Currying the first argument of a multilinear map into its values:
`f ↦ ((m₁, …, mₙ) ↦ (m₀ ↦ f (m₀, m₁, …, mₙ)))`. -/
def multilinearCurryFirstEquiv :
    MultilinearMap (RingHom.id R) M N ≃ₗ[R] MultilinearMap (RingHom.id R) (fun i : Fin n ↦ M
        i.succ) (M 0 →ₗ[R] N) where
  toFun f := MultilinearMap.mk'
    (fun m ↦
      { toFun x := f (Fin.cons x m)
        map_add' x y := f.cons_add m x y
        map_smul' r x := f.cons_smul m r x })
    (fun m i x y ↦ LinearMap.ext fun z ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Fin.cons_update,
        MultilinearMap.map_update_add])
    (fun m i r x ↦ LinearMap.ext fun z ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Fin.cons_update,
        MultilinearMap.map_update_smul])
  map_add' f g := rfl
  map_smul' r f := rfl
  invFun g := MultilinearMap.mk' (fun m ↦ g (Fin.tail m) (m 0))
    (fun m i x y ↦ by cases i using Fin.cases <;> simp [Ne.symm])
    (fun m i r x ↦ by cases i using Fin.cases <;> simp [Ne.symm])
  left_inv f := by ext m; exact congrArg f (Fin.cons_self_tail m)
  right_inv g := by ext m x; simp

variable {R M N}

/-- The curried map evaluates `f` on the tuple with `x` prepended. -/
@[simp]
theorem multilinearCurryFirstEquiv_apply_apply (f : MultilinearMap (RingHom.id R) M N)
    (m : ∀ i : Fin n, M i.succ) (x : M 0) :
    multilinearCurryFirstEquiv R M N f m x = f (Fin.cons x m) :=
  (rfl)

/-- The uncurried map evaluates on the last `n` entries and then on the first one. -/
@[simp]
theorem multilinearCurryFirstEquiv_symm_apply
    (g : MultilinearMap (RingHom.id R) (fun i : Fin n ↦ M i.succ) (M 0 →ₗ[R] N)) (m : ∀ i, M i) :
    (multilinearCurryFirstEquiv R M N).symm g m = g (Fin.tail m) (m 0) :=
  (rfl)

end TauCeti

namespace MultilinearMap

variable {R R₂ : Type*} [Semiring R] [Semiring R₂] {σ : R →+* R₂}
  {n : ℕ} {M : Fin (n + 1) → Type*} {N : Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R₂ N]

/-- Fix argument `p` of a multilinear map `f` in `n + 1` variables to `x : M p`, yielding a
multilinear map in the remaining `n` variables. Unlike `MultilinearMap.curryMid`, which bundles
linearity in `x` as well and therefore requires a commutative scalar semiring on the target, fixing
`x` first requires no commutativity assumption on the scalars. -/
def compInsertNth (f : (Π i, M i) →ₘₛₗ[σ] N) (p : Fin (n + 1)) (x : M p) :
    (Π i, M (p.succAbove i)) →ₘₛₗ[σ] N :=
  MultilinearMap.mk' (fun m ↦ f (p.insertNth x m))
    (fun m i u v ↦ by simp_rw [Fin.insertNth_update, f.map_update_add])
    (fun m i c u ↦ by simp_rw [Fin.insertNth_update, f.map_update_smul])

/-- Evaluating `f.compInsertNth p x` on `m` inserts `x` at index `p` of `m`. -/
@[simp]
theorem compInsertNth_apply (f : (Π i, M i) →ₘₛₗ[σ] N) (p : Fin (n + 1)) (x : M p)
    (m : Π i, M (p.succAbove i)) :
    f.compInsertNth p x m = f (p.insertNth x m) :=
  (rfl)

/-- `MultilinearMap.compInsertNth` as an `S`-linear map in the multilinear map `f`. -/
def compInsertNthLinearMap (S : Type*) [Semiring S] [Module S N] [SMulCommClass R₂ S N]
    (p : Fin (n + 1)) (x : M p) :
    ((Π i, M i) →ₘₛₗ[σ] N) →ₗ[S] (Π i, M (p.succAbove i)) →ₘₛₗ[σ] N where
  toFun f := f.compInsertNth p x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `MultilinearMap.compInsertNthLinearMap` acts by `MultilinearMap.compInsertNth`. -/
@[simp]
theorem compInsertNthLinearMap_apply (S : Type*) [Semiring S] [Module S N] [SMulCommClass R₂ S N]
    (p : Fin (n + 1)) (x : M p) (f : (Π i, M i) →ₘₛₗ[σ] N) :
    compInsertNthLinearMap S p x f = f.compInsertNth p x :=
  (rfl)

end MultilinearMap
