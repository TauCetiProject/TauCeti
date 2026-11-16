/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension along algebra maps

For an algebra map `f : A →ₐ[R] B` and an `R`-module `M`, the induced map
`A ⊗[R] M → B ⊗[R] M` is semilinear over `f`.

For a tower `R → A → B` and an `R`-module `M`, the structure map `A → B` induces a map
`A ⊗[R] M → B ⊗[R] M` in two ways: as the `A`-linear map
`TensorProduct.AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)`, and as the `R`-linear
base change of the `R`-algebra map `IsScalarTower.toAlgHom R A B`. This file records that the two
agree as functions, so the `A`-linearity of the first applies to the second.

For a subring `B` of a commutative ring `R` and an `R`-module `M`, an element of `B` can be moved
across the tensor sign of `R ⊗[B] M`.

## Main results

* `AlgHom.rTensor_toLinearMap_apply_smul`: the scalar-extension comparison induced by an algebra
  map is semilinear over that map.
* `TensorProduct.AlgebraTensorModule.rTensor_linearMap_apply`: the `A`-linear base change of the
  structure map `A → B` is the base change of the `R`-algebra map `A →ₐ[R] B`.
* `TensorProduct.AlgebraTensorModule.lTensor_eq_baseChange`: over the coefficient algebra itself,
  `TensorProduct.AlgebraTensorModule.lTensor` is `LinearMap.baseChange`.

* `TensorProduct.tmul_eq_one_tmul_smul_of_mem`: in `R ⊗[B] M`, for a subring `B` of `R` and
  `r ∈ B`, `r ⊗ m = 1 ⊗ r • m`.
* `Submodule.one_tmul_mem_baseChange_of_smul_mem`: if `a • x ∈ N` and `a` becomes a unit in `A`,
  then `1 ⊗ₜ x` lies in the base change of `N` to `A`.
* `LinearMap.liftBaseChangeSemilinear`, `AddMonoidHom.liftBaseChangeSemilinear`,
  `LinearMap.ext_one_tmul`, `LinearMap.eq_liftBaseChangeSemilinear_iff`,
  `AddMonoidHom.eq_liftBaseChangeSemilinear_iff`, `LinearMap.apply_liftBaseChangeSemilinear`, and
  `AddMonoidHom.apply_liftBaseChangeSemilinear`: semilinear extensions out of `S ⊗[R] M`, their
  universal property, and compatibility with linear forms.
-/

public section

open TensorProduct

/-- The comparison `A ⊗[R] M → B ⊗[R] M` of scalar extensions induced by an algebra map `f`
is semilinear over `f`. -/
@[simp]
theorem AlgHom.rTensor_toLinearMap_apply_smul {R A B M : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring B] [Algebra R B] [AddCommMonoid M] [Module R M]
    (f : A →ₐ[R] B) (a : A) (z : A ⊗[R] M) :
    LinearMap.rTensor M f.toLinearMap (a • z) =
      f a • LinearMap.rTensor M f.toLinearMap z := by
  induction z using TensorProduct.inductionOn with
  | tmul x m => simp [TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- The `A`-linear base change of the structure map `A → B` is, as a function, the base change
of the `R`-algebra map `A →ₐ[R] B`. -/
@[simp]
theorem TensorProduct.AlgebraTensorModule.rTensor_linearMap_apply {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [AddCommMonoid M] [Module R M] (x : A ⊗[R] M) :
    AlgebraTensorModule.rTensor R M (Algebra.linearMap A B) x =
      (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x := by
  rw [AlgebraTensorModule.coe_rTensor]
  exact congrArg (LinearMap.rTensor M · x) (LinearMap.ext fun a ↦ by simp)

/-- Over the coefficient algebra itself, `TensorProduct.AlgebraTensorModule.lTensor` is
`LinearMap.baseChange`: both extend scalars along `A`. -/
theorem TensorProduct.AlgebraTensorModule.lTensor_eq_baseChange {R : Type*} (A : Type*)
    {M N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    AlgebraTensorModule.lTensor A A f = f.baseChange A :=
  AlgebraTensorModule.ext fun a x => by simp

/-- In `R ⊗[B] M`, for a subring `B` of `R`, an element `r ∈ B` can be moved across the tensor
sign: `r ⊗ m = 1 ⊗ r • m`. -/
theorem TensorProduct.tmul_eq_one_tmul_smul_of_mem {R M : Type*} [CommRing R] [AddCommMonoid M]
    [Module R M] {B : Subring R} {r : R} (hr : r ∈ B) (m : M) :
    r ⊗ₜ[B] m = (1 : R) ⊗ₜ (r • m) := by
  simpa [Subring.smul_def] using smul_tmul (⟨r, hr⟩ : B) (1 : R) m

/-- If `a • x` lies in a submodule `N` and `a` becomes a unit in the algebra `A`, then `1 ⊗ₜ x`
lies in the base change of `N` to `A`. -/
theorem Submodule.one_tmul_mem_baseChange_of_smul_mem {R A M : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M] (N : Submodule R M) {a : R}
    (ha : IsUnit (algebraMap R A a)) {x : M} (hx : a • x ∈ N) :
    (1 : A) ⊗ₜ x ∈ N.baseChange A := by
  obtain ⟨u, hu⟩ := ha
  have h := (N.baseChange A).smul_mem (↑u⁻¹ : A) (tmul_mem_baseChange_of_mem 1 hx)
  rwa [← smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← hu, smul_tmul', smul_eq_mul,
    Units.inv_mul] at h

/-- Base change preserves left inverses: if `f ∘ₗ g = id`, then `f.baseChange A` is a left
inverse of `g.baseChange A`. -/
theorem LinearMap.baseChange_leftInverse {R A M N : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {f : N →ₗ[R] M} {g : M →ₗ[R] N} (h : f ∘ₗ g = .id) :
    Function.LeftInverse (f.baseChange A) (g.baseChange A) := fun z ↦ by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h, LinearMap.baseChange_id,
    LinearMap.id_apply]

section Semilinear

variable {R S T M V : Type*} [CommSemiring R] [Semiring S] [Algebra R S] [Semiring T]
  {σ : S →+* T} [AddCommMonoid M] [Module R M] [AddCommMonoid V] [Module T V]

/-- Lift `f : M →ₛₗ[σ.comp (algebraMap R S)] V` to `(S ⊗[R] M) →ₛₗ[σ] V` via `s ⊗ₜ m ↦ σ s • f m`.
-/
def LinearMap.liftBaseChangeSemilinear (f : M →ₛₗ[σ.comp (algebraMap R S)] V) :
    (S ⊗[R] M) →ₛₗ[σ] V :=
  let g : (S ⊗[R] M) →+ V :=
    TensorProduct.liftAddHom
      { toFun s :=
          { toFun m := σ s • f m, map_zero' := by simp, map_add' _ _ := by simp [smul_add] }
        map_zero' := by ext m; simp
        map_add' _ _ := by ext m; simp [add_smul] }
      (fun r s m ↦ by
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Algebra.smul_def, Algebra.commutes,
          map_mul, map_smulₛₗ, RingHom.comp_apply, mul_smul])
  { toFun := g, map_add' := g.map_add
    map_smul' c z := TensorProduct.inductionOn z
      (fun _ _ ↦ by simp [g, TensorProduct.smul_tmul', mul_smul])
      (fun _ _ hx hy ↦ by simp [smul_add, hx, hy]) }

@[simp]
theorem LinearMap.liftBaseChangeSemilinear_tmul (f : M →ₛₗ[σ.comp (algebraMap R S)] V) (s : S)
    (m : M) : f.liftBaseChangeSemilinear (s ⊗ₜ[R] m) = σ s • f m := (rfl)

/-- Two `σ`-semilinear maps out of `S ⊗[R] M` are equal if they agree on every `1 ⊗ₜ[R] m`. -/
theorem LinearMap.ext_one_tmul {g₁ g₂ : (S ⊗[R] M) →ₛₗ[σ] V}
    (h : ∀ m : M, g₁ (1 ⊗ₜ[R] m) = g₂ (1 ⊗ₜ[R] m)) : g₁ = g₂ :=
  LinearMap.ext fun z ↦ TensorProduct.inductionOn z
    (fun s m ↦ by
      rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smulₛₗ, map_smulₛₗ, h])
    (fun _ _ hu hv ↦ by simp [hu, hv])

/-- Universal property of `LinearMap.liftBaseChangeSemilinear`. -/
theorem LinearMap.eq_liftBaseChangeSemilinear_iff {f : M →ₛₗ[σ.comp (algebraMap R S)] V}
    {g : (S ⊗[R] M) →ₛₗ[σ] V} :
    g = f.liftBaseChangeSemilinear ↔ ∀ m : M, g (1 ⊗ₜ[R] m) = f m :=
  ⟨fun hg m ↦ by simp [hg], fun h ↦ LinearMap.ext_one_tmul fun m ↦ by simp [h]⟩

/-- Evaluating `F : V →ₗ[T] T` on `f.liftBaseChangeSemilinear z` agrees with `σ (φ z)` whenever
they agree on every `1 ⊗ₜ[R] m`. -/
theorem LinearMap.apply_liftBaseChangeSemilinear (f : M →ₛₗ[σ.comp (algebraMap R S)] V)
    (F : V →ₗ[T] T) (φ : (S ⊗[R] M) →ₗ[S] S)
    (hF : ∀ m : M, F (f m) = σ (φ (1 ⊗ₜ[R] m))) (z : S ⊗[R] M) :
    F (f.liftBaseChangeSemilinear z) = σ (φ z) :=
  TensorProduct.inductionOn z
    (fun s m ↦ by
      rw [liftBaseChangeSemilinear_tmul, map_smul, hF, smul_eq_mul, ← map_mul, ← smul_eq_mul,
        ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    (fun _ _ hu hv ↦ by simp [hu, hv])

end Semilinear

section AddMonoidHomSemilinear

variable {S T X V : Type*} [Ring S] [Ring T] [AddCommGroup X] [AddCommGroup V] [Module T V]

/-- Lift `f : X →+ V` across `S ⊗[ℤ] X` along `σ : S →+* T` via `s ⊗ₜ x ↦ σ s • f x`. -/
def AddMonoidHom.liftBaseChangeSemilinear (f : X →+ V) (σ : S →+* T) : (S ⊗[ℤ] X) →ₛₗ[σ] V :=
  LinearMap.liftBaseChangeSemilinear (R := ℤ) (σ := σ)
    { toFun := f, map_add' := f.map_add
      map_smul' n x := by simp only [eq_intCast, Int.cast_smul_eq_zsmul, map_zsmul] }

@[simp]
theorem AddMonoidHom.liftBaseChangeSemilinear_tmul (f : X →+ V) (σ : S →+* T) (s : S) (x : X) :
    f.liftBaseChangeSemilinear σ (s ⊗ₜ[ℤ] x) = σ s • f x := (rfl)

/-- Universal property of `AddMonoidHom.liftBaseChangeSemilinear`. -/
theorem AddMonoidHom.eq_liftBaseChangeSemilinear_iff {f : X →+ V} {σ : S →+* T}
    {g : (S ⊗[ℤ] X) →ₛₗ[σ] V} :
    g = f.liftBaseChangeSemilinear σ ↔ ∀ x : X, g (1 ⊗ₜ[ℤ] x) = f x :=
  LinearMap.eq_liftBaseChangeSemilinear_iff

/-- Evaluating `F : V →ₗ[T] T` on `f.liftBaseChangeSemilinear σ z` agrees with `σ (φ z)` whenever
they agree on every `1 ⊗ₜ[ℤ] x`. -/
theorem AddMonoidHom.apply_liftBaseChangeSemilinear (f : X →+ V) (σ : S →+* T)
    (F : V →ₗ[T] T) (φ : (S ⊗[ℤ] X) →ₗ[S] S)
    (hF : ∀ x : X, F (f x) = σ (φ (1 ⊗ₜ[ℤ] x))) (z : S ⊗[ℤ] X) :
    F (f.liftBaseChangeSemilinear σ z) = σ (φ z) :=
  LinearMap.apply_liftBaseChangeSemilinear _ F φ hF z

end AddMonoidHomSemilinear
