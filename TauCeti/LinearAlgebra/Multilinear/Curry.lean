/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Currying the first argument of a multilinear map into its values

A multilinear map `f` in `n + 1` arguments, semilinear along `σ : R →+* S` with `S` commutative,
determines the multilinear map in the last `n` arguments whose value at `(m₁, …, mₙ)` is the
semilinear map `m₀ ↦ f (m₀, m₁, …, mₙ)`. This gives an `S`-linear equivalence
`TauCeti.multilinearCurryFirstEquiv`. It differs from Mathlib's
`multilinearCurryLeftEquiv`, which curries the first argument outside, into linear maps valued in
multilinear maps, and is the first-argument counterpart of `multilinearCurryRightEquiv`.

Cochains with values in linear maps out of an algebra arise in this way from cochains with one
more argument, which is how scalar Hochschild cochains are compared with cochains valued in the
dual bimodule.

`MultilinearMap.compInsertNth f p x` fixes argument `p : Fin (n + 1)` of `f` to `x : M p` over any
scalar semiring (without the commutativity hypothesis of `MultilinearMap.curryMid`), bundled as an
`S`-linear map in `f` by `MultilinearMap.compInsertNthLinearMap`.

## Main definitions

* `TauCeti.multilinearCurryFirstEquiv`: `f ↦ ((m₁, …, mₙ) ↦ (m₀ ↦ f (m₀, m₁, …, mₙ)))`.
* `MultilinearMap.compInsertNth`, `MultilinearMap.compInsertNthLinearMap`: fixing argument `p` to
  `x` via `Fin.insertNth`.
-/

public section

namespace TauCeti

variable {R S : Type*} [Semiring R] [CommSemiring S] (σ : R →+* S) {n : ℕ}
  (M : Fin (n + 1) → Type*) (N : Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid N] [Module S N]

/-- Currying the first argument of a multilinear map into its values:
`f ↦ ((m₁, …, mₙ) ↦ (m₀ ↦ f (m₀, m₁, …, mₙ)))`. -/
def multilinearCurryFirstEquiv :
    ((Π i, M i) →ₘₛₗ[σ] N) ≃ₗ[S] (Π i : Fin n, M i.succ) →ₘₛₗ[σ] M 0 →ₛₗ[σ] N where
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
  left_inv f := by ext m; simp
  right_inv g := by ext m x; simp

variable {σ M N}

/-- The curried map evaluates `f` on the tuple with `x` prepended. -/
@[simp]
theorem multilinearCurryFirstEquiv_apply_apply (f : (Π i, M i) →ₘₛₗ[σ] N)
    (m : ∀ i : Fin n, M i.succ) (x : M 0) :
    multilinearCurryFirstEquiv σ M N f m x = f (Fin.cons x m) :=
  (rfl)

/-- The uncurried map evaluates on the last `n` entries and then on the first one. -/
@[simp]
theorem multilinearCurryFirstEquiv_symm_apply
    (g : (Π i : Fin n, M i.succ) →ₘₛₗ[σ] M 0 →ₛₗ[σ] N) (m : ∀ i, M i) :
    (multilinearCurryFirstEquiv σ M N).symm g m = g (Fin.tail m) (m 0) :=
  (rfl)

end TauCeti

namespace MultilinearMap
variable {R R₂ : Type*} [Semiring R] [Semiring R₂] {σ : R →+* R₂}
  {n : ℕ} {M : Fin (n + 1) → Type*} {N : Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R₂ N]

/-- Fix argument `p` of a multilinear map `f` in `n + 1` variables to `x : M p`. -/
def compInsertNth (f : (Π i, M i) →ₘₛₗ[σ] N) (p : Fin (n + 1)) (x : M p) :
    (Π i, M (p.succAbove i)) →ₘₛₗ[σ] N :=
  MultilinearMap.mk' (fun m ↦ f (p.insertNth x m))
    (fun m i u v ↦ by simp_rw [Fin.insertNth_update, f.map_update_add])
    (fun m i c u ↦ by simp_rw [Fin.insertNth_update, f.map_update_smul])
/-- Evaluating `f.compInsertNth p x` on `m` inserts `x` at index `p` of `m`. -/
@[simp] theorem compInsertNth_apply (f : (Π i, M i) →ₘₛₗ[σ] N) (p : Fin (n + 1)) (x : M p)
    (m : Π i, M (p.succAbove i)) : f.compInsertNth p x m = f (p.insertNth x m) := (rfl)
/-- Fixing argument `p` to `0` yields the zero multilinear map. -/
@[simp] theorem compInsertNth_zero (f : (Π i, M i) →ₘₛₗ[σ] N) (p : Fin (n + 1)) :
    f.compInsertNth p 0 = 0 := by ext m; exact f.map_coord_zero p (by simp)
/-- `compInsertNth` is additive in the inserted entry. -/
@[simp] theorem compInsertNth_add (f : (Π i, M i) →ₘₛₗ[σ] N) (p : Fin (n + 1)) (x y : M p) :
    f.compInsertNth p (x + y) = f.compInsertNth p x + f.compInsertNth p y := by
  ext m; exact f.map_insertNth_add p m x y
/-- `compInsertNth` is `σ`-homogeneous in the inserted entry. -/
@[simp] theorem compInsertNth_smul [SMulCommClass R₂ R₂ N] (f : (Π i, M i) →ₘₛₗ[σ] N)
    (p : Fin (n + 1)) (c : R) (x : M p) : f.compInsertNth p (c • x) = σ c • f.compInsertNth p x :=
  by ext m; exact f.map_insertNth_smul p m c x
/-- Fixing an argument of the zero multilinear map yields zero. -/
@[simp] theorem zero_compInsertNth (p : Fin (n + 1)) (x : M p) :
    (0 : (Π i, M i) →ₘₛₗ[σ] N).compInsertNth p x = 0 := (rfl)
/-- `compInsertNth` is additive in the multilinear map. -/
@[simp] theorem add_compInsertNth (f g : (Π i, M i) →ₘₛₗ[σ] N) (p : Fin (n + 1)) (x : M p) :
    (f + g).compInsertNth p x = f.compInsertNth p x + g.compInsertNth p x := (rfl)
/-- `compInsertNth` commutes with scalar multiplication of the multilinear map. -/
@[simp] theorem smul_compInsertNth {S : Type*} [DistribSMul S N] [SMulCommClass R₂ S N] (c : S)
    (f : (Π i, M i) →ₘₛₗ[σ] N) (p : Fin (n + 1)) (x : M p) :
    (c • f).compInsertNth p x = c • f.compInsertNth p x := (rfl)

section Linear
variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R₂ S N] (p : Fin (n + 1))

/-- `MultilinearMap.compInsertNth` as an `S`-linear map in the multilinear map `f`. -/
def compInsertNthLinearMap (x : M p) :
    ((Π i, M i) →ₘₛₗ[σ] N) →ₗ[S] (Π i, M (p.succAbove i)) →ₘₛₗ[σ] N :=
  { toFun := (·.compInsertNth p x), map_add' _ _ := rfl, map_smul' _ _ := rfl }
/-- `MultilinearMap.compInsertNthLinearMap` acts by `MultilinearMap.compInsertNth`. -/
@[simp] theorem compInsertNthLinearMap_apply (x : M p) (f : (Π i, M i) →ₘₛₗ[σ] N) :
    compInsertNthLinearMap S p x f = f.compInsertNth p x := (rfl)
/-- Fixing argument `p` to `0` yields the zero linear map on multilinear maps. -/
@[simp] theorem compInsertNthLinearMap_zero :
    compInsertNthLinearMap (R := R) (R₂ := R₂) (σ := σ) (M := M) (N := N) S p 0 = 0 := by
  ext f; simp
/-- `compInsertNthLinearMap` is additive in the inserted entry. -/
@[simp] theorem compInsertNthLinearMap_add (x y : M p) :
    compInsertNthLinearMap (R := R) (R₂ := R₂) (σ := σ) (M := M) (N := N) S p (x + y) =
      compInsertNthLinearMap S p x + compInsertNthLinearMap S p y := by ext f; simp
end Linear
end MultilinearMap
