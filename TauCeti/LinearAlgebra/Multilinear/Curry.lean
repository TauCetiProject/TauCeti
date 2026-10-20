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

## Main definitions

* `TauCeti.multilinearCurryFirstEquiv`: `f ↦ ((m₁, …, mₙ) ↦ (m₀ ↦ f (m₀, m₁, …, mₙ)))`.
-/

public section

namespace TauCeti

variable (R : Type*) {n : ℕ} (M : Fin (n + 1) → Type*) (N : Type*) [CommSemiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]

/-- Currying the first argument of a multilinear map into its values:
`f ↦ ((m₁, …, mₙ) ↦ (m₀ ↦ f (m₀, m₁, …, mₙ)))`. -/
def multilinearCurryFirstEquiv :
    MultilinearMap R M N ≃ₗ[R] MultilinearMap R (fun i : Fin n ↦ M i.succ) (M 0 →ₗ[R] N) where
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
theorem multilinearCurryFirstEquiv_apply_apply (f : MultilinearMap R M N)
    (m : ∀ i : Fin n, M i.succ) (x : M 0) :
    multilinearCurryFirstEquiv R M N f m x = f (Fin.cons x m) :=
  (rfl)

/-- The uncurried map evaluates on the last `n` entries and then on the first one. -/
@[simp]
theorem multilinearCurryFirstEquiv_symm_apply
    (g : MultilinearMap R (fun i : Fin n ↦ M i.succ) (M 0 →ₗ[R] N)) (m : ∀ i, M i) :
    (multilinearCurryFirstEquiv R M N).symm g m = g (Fin.tail m) (m 0) :=
  (rfl)

end TauCeti
