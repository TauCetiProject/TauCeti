/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Base change of quadratic forms on free modules

Mathlib's `QuadraticForm.baseChange` extends a quadratic form `Q` on an `R`-module `M` to
`A ⊗[R] M` through the symmetric bilinear form `QuadraticMap.associated Q`, so it requires `2` to
be invertible in `R`. On a free module no such hypothesis is needed. There `Q` is
`B.toQuadraticMap` for a (generally nonsymmetric) bilinear form `B`
(`LinearMap.BilinMap.toQuadraticMap_surjective`), and the quadratic form of `B.baseChange A`
extends `Q`. It does not depend on the choice of `B`, because a quadratic map on `A ⊗[R] M` is
determined by its values on the pure tensors `1 ⊗ₜ m` (`QuadraticForm.baseChange_ext`).

This is the scalar extension of quadratic forms available in characteristic two and over rings
such as the `2`-adic integers, where a quadratic form carries more information than its polar
form: over `ZMod 2` the planes `x * y` and `x ^ 2 + x * y + y ^ 2` have the same polar form but
are not isometric.

## Main definitions

* `QuadraticForm.freeBaseChange A Q`: the extension of a quadratic form `Q` on a free `R`-module
  `M` to the quadratic form on `A ⊗[R] M` with `Q.freeBaseChange A (a ⊗ₜ m) = Q m • (a * a)`.
* `QuadraticMap.IsometryEquiv.freeBaseChange`: the extension of an isometric equivalence.

## Main results

* `QuadraticForm.eq_freeBaseChange_iff`: `Q.freeBaseChange A` is the unique quadratic form on
  `A ⊗[R] M` taking the value `algebraMap R A (Q m)` at `1 ⊗ₜ m` for every `m`.
* `LinearMap.BilinForm.toQuadraticMap_baseChange`: the quadratic form of the base change of a
  bilinear form `B` is the base change of `B.toQuadraticMap`.
* `QuadraticForm.freeBaseChange_eq_baseChange`: when `2` is invertible, `Q.freeBaseChange A` is
  Mathlib's `Q.baseChange A`.
* `QuadraticForm.polarBilin_freeBaseChange`: the polar form of `Q.freeBaseChange A` is the base
  change of the polar form of `Q`.
* `QuadraticForm.nondegenerate_polarBilin_freeBaseChange_iff`: on a finite free module, along an
  injective map of integral domains, base change preserves and reflects nondegeneracy of the
  polar form.
-/

public section

noncomputable section

open TensorProduct

namespace QuadraticForm

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section Free

variable [Module.Free R M]

variable (A) in
/-- The **base change** of a quadratic form `Q` on a free `R`-module `M` to an `R`-algebra `A`:
the quadratic form on `A ⊗[R] M` with `Q.freeBaseChange A (a ⊗ₜ m) = Q m • (a * a)`
(`QuadraticForm.freeBaseChange_tmul`). It is the quadratic form of the base change of any
bilinear form `B` with `B.toQuadraticMap = Q` (`LinearMap.BilinForm.toQuadraticMap_baseChange`).

Unlike `QuadraticForm.baseChange`, this does not need `2` to be invertible in `R`; the two agree
when it is (`QuadraticForm.freeBaseChange_eq_baseChange`). -/
def freeBaseChange (Q : QuadraticForm R M) : QuadraticForm A (A ⊗[R] M) :=
  (LinearMap.BilinForm.baseChange A
    (LinearMap.BilinMap.toQuadraticMap_surjective Q).choose).toQuadraticMap

/-- The base change of `Q` evaluated on a pure tensor `a ⊗ₜ m` is `Q m • (a * a)`. -/
@[simp]
theorem freeBaseChange_tmul (Q : QuadraticForm R M) (a : A) (m : M) :
    Q.freeBaseChange A (a ⊗ₜ m) = Q m • (a * a) := by
  rw [freeBaseChange, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinForm.baseChange_tmul, ← LinearMap.BilinMap.toQuadraticMap_apply,
    (LinearMap.BilinMap.toQuadraticMap_surjective Q).choose_spec]

/-- The base change of `Q` takes the value `algebraMap R A (Q m)` at `1 ⊗ₜ m`. -/
theorem freeBaseChange_one_tmul (Q : QuadraticForm R M) (m : M) :
    Q.freeBaseChange A (1 ⊗ₜ m) = algebraMap R A (Q m) := by
  rw [freeBaseChange_tmul, mul_one, Algebra.smul_def, mul_one]

/-- The base change of `Q` takes the value `algebraMap R A (Q (b i))` on the base change of a
basis vector `b i`. -/
theorem freeBaseChange_basis_baseChange (Q : QuadraticForm R M) {ι : Type*}
    (b : Module.Basis ι R M) (i : ι) :
    Q.freeBaseChange A (b.baseChange A i) = algebraMap R A (Q (b i)) := by
  rw [Module.Basis.baseChange_apply, freeBaseChange_one_tmul]

/-- **Uniqueness of base change.** A quadratic form on `A ⊗[R] M` is the base change of `Q` if
and only if it takes the value `algebraMap R A (Q m)` at `1 ⊗ₜ m` for every `m`. -/
theorem eq_freeBaseChange_iff {Q : QuadraticForm R M} {Q' : QuadraticForm A (A ⊗[R] M)} :
    Q' = Q.freeBaseChange A ↔ ∀ m, Q' (1 ⊗ₜ m) = algebraMap R A (Q m) := by
  refine ⟨fun h m ↦ h ▸ freeBaseChange_one_tmul Q m, fun h ↦ baseChange_ext fun m ↦ ?_⟩
  rw [h, freeBaseChange_one_tmul]

end Free

/-- The quadratic form of the base change of a bilinear form `B` on a free module is the base
change of the quadratic form of `B`. -/
theorem _root_.LinearMap.BilinForm.toQuadraticMap_baseChange [Module.Free R M]
    (B : LinearMap.BilinForm R M) :
    (B.baseChange A).toQuadraticMap = freeBaseChange A B.toQuadraticMap :=
  eq_freeBaseChange_iff.mpr fun m ↦ by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinForm.baseChange_tmul, mul_one,
      Algebra.smul_def, mul_one, LinearMap.BilinMap.toQuadraticMap_apply]

/-- When `2` is invertible, `QuadraticForm.freeBaseChange` agrees with Mathlib's
`QuadraticForm.baseChange`. -/
theorem freeBaseChange_eq_baseChange [Module.Free R M] [Invertible (2 : R)]
    (Q : QuadraticForm R M) : Q.freeBaseChange A = Q.baseChange A :=
  (eq_freeBaseChange_iff.mpr fun m ↦ by
    rw [baseChange_tmul, mul_one, Algebra.smul_def, mul_one]).symm

section Free

variable [Module.Free R M]

variable (A) in
/-- The base change of the zero form is zero. -/
@[simp]
theorem freeBaseChange_zero : (0 : QuadraticForm R M).freeBaseChange A = 0 :=
  (eq_freeBaseChange_iff.mpr fun m ↦ by simp).symm

/-- Base change is additive in the quadratic form. -/
@[simp]
theorem freeBaseChange_add (Q₁ Q₂ : QuadraticForm R M) :
    (Q₁ + Q₂).freeBaseChange A = Q₁.freeBaseChange A + Q₂.freeBaseChange A :=
  (eq_freeBaseChange_iff.mpr fun m ↦ by
    simp only [add_apply, freeBaseChange_one_tmul, map_add]).symm

/-- Base change carries the scalar multiple `r • Q` to `algebraMap R A r • Q.freeBaseChange A`. -/
@[simp]
theorem freeBaseChange_smul (r : R) (Q : QuadraticForm R M) :
    (r • Q).freeBaseChange A = algebraMap R A r • Q.freeBaseChange A :=
  (eq_freeBaseChange_iff.mpr fun m ↦ by
    simp only [smul_apply, freeBaseChange_one_tmul, smul_eq_mul, map_mul]).symm

/-- Polarization after base change, evaluated on pure tensors. -/
@[simp]
theorem polar_freeBaseChange_tmul (Q : QuadraticForm R M) (a a' : A) (m m' : M) :
    QuadraticMap.polar (Q.freeBaseChange A) (a ⊗ₜ m) (a' ⊗ₜ m') =
      QuadraticMap.polar Q m m' • (a * a') := by
  obtain ⟨B, rfl⟩ := LinearMap.BilinMap.toQuadraticMap_surjective Q
  rw [← LinearMap.BilinForm.toQuadraticMap_baseChange, LinearMap.BilinMap.polar_toQuadraticMap,
    LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.BilinForm.baseChange_tmul,
    LinearMap.BilinForm.baseChange_tmul, mul_comm a' a, add_smul]

/-- The polar form of the base change of `Q` is the base change of the polar form of `Q`. -/
@[simp]
theorem polarBilin_freeBaseChange (Q : QuadraticForm R M) :
    (Q.freeBaseChange A).polarBilin = LinearMap.BilinForm.baseChange A Q.polarBilin := by
  ext m m'
  simp

/-- On a finite free module, along an injective map of integral domains, base change preserves
and reflects nondegeneracy of the polar form. In particular, it preserves and reflects the
perfectness of the polar form over any field extension. -/
theorem nondegenerate_polarBilin_freeBaseChange_iff [Module.Finite R M] [IsDomain A]
    [FaithfulSMul R A] (Q : QuadraticForm R M) :
    (Q.freeBaseChange A).polarBilin.Nondegenerate ↔ Q.polarBilin.Nondegenerate := by
  rw [polarBilin_freeBaseChange]
  exact LinearMap.BilinForm.nondegenerate_baseChange_iff _ (Module.Free.chooseBasis R M)

/-- Base change commutes with precomposition by a linear map. -/
theorem freeBaseChange_comp [Module.Free R N] (Q : QuadraticForm R N) (f : M →ₗ[R] N) :
    freeBaseChange A (Q.comp f) = (Q.freeBaseChange A).comp (f.baseChange A) :=
  (eq_freeBaseChange_iff.mpr fun m ↦ by
    rw [QuadraticMap.comp_apply, LinearMap.baseChange_tmul, freeBaseChange_one_tmul,
      QuadraticMap.comp_apply]).symm

end Free

end QuadraticForm

namespace QuadraticMap

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module.Free R M] [AddCommGroup N] [Module R N] [Module.Free R N]
  {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N}

variable (A) in
/-- An isometric equivalence of quadratic forms on free modules extends to an isometric
equivalence of their base changes, given by the base change of the underlying linear
equivalence. -/
def IsometryEquiv.freeBaseChange (e : Q₁.IsometryEquiv Q₂) :
    (Q₁.freeBaseChange A).IsometryEquiv (Q₂.freeBaseChange A) where
  toLinearEquiv := e.toLinearEquiv.baseChange R A M N
  map_app' x := by
    have h : Q₂.comp e.toLinearEquiv.toLinearMap = Q₁ := QuadraticMap.ext e.map_app
    conv_rhs => rw [← h, QuadraticForm.freeBaseChange_comp, QuadraticMap.comp_apply,
      ← LinearEquiv.coe_baseChange]
    -- The goal applies `Q₂.freeBaseChange A` to `toFun x` of the same coerced linear map.
    rfl

/-- On pure tensors, the base change of an isometric equivalence applies the original
equivalence to the vector. -/
@[simp]
theorem IsometryEquiv.freeBaseChange_tmul (e : Q₁.IsometryEquiv Q₂) (a : A) (m : M) :
    e.freeBaseChange A (a ⊗ₜ m) = a ⊗ₜ e m :=
  LinearEquiv.baseChange_tmul R A M N (e := e.toLinearEquiv) a m

variable (A) in
/-- Isometric quadratic forms on free modules remain isometric after base change. -/
theorem Equivalent.freeBaseChange (h : Q₁.Equivalent Q₂) :
    (Q₁.freeBaseChange A).Equivalent (Q₂.freeBaseChange A) :=
  h.elim fun e ↦ ⟨e.freeBaseChange A⟩

end QuadraticMap
