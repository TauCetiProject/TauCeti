/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Basic identities for Lie algebra base change and scalar restriction

The additive identification between a scalar-restricted Lie ring and its original carrier
preserves brackets (`RestrictScalars.addEquiv_lie`). Any `A`-linear Lie equivalence between two
`A`-Lie algebras restricts along `Algebra R A` to an `R`-linear Lie equivalence
`LieEquiv.restrictScalars` between their `RestrictScalars R A` type aliases. Iterating the action
of a pure tensor `a ⊗ₜ[R] u` on `A ⊗[R] M` multiplies the scalar factor by `a ^ m` while
iterating the action of `u` on `M`.

## Main definitions and results

* `RestrictScalars.addEquiv_lie` and `RestrictScalars.addEquiv_symm_lie`: `RestrictScalars.addEquiv`
  and its inverse preserve Lie brackets.
* `LieEquiv.restrictScalars`: scalar restriction of a Lie algebra equivalence across
  `RestrictScalars`, together with `LieEquiv.restrictScalars_apply` and
  `LieEquiv.restrictScalars_symm_apply`.
* `LieAlgebra.ExtendScalars.toEnd_pow_tmul` and `LieAlgebra.ExtendScalars.ad_pow_tmul`: iterated
  action and adjoint powers of a pure tensor `a ⊗ₜ[R] u` on `b ⊗ₜ[R] v`.

## References

* `Mathlib.Algebra.Lie.BaseChange`, for the inherited Lie-ring and Lie-algebra structures on
  `RestrictScalars` and `LieAlgebra.ExtendScalars.bracket_tmul`.
-/

public section

/-- The additive identification for scalar restriction preserves the Lie bracket. -/
@[simp]
theorem RestrictScalars.addEquiv_lie {R A L : Type*} [LieRing L]
    (x y : RestrictScalars R A L) :
    RestrictScalars.addEquiv R A L ⁅x, y⁆ =
      ⁅RestrictScalars.addEquiv R A L x, RestrictScalars.addEquiv R A L y⁆ := rfl

/-- The inverse additive identification for scalar restriction preserves the Lie bracket. -/
@[simp]
theorem RestrictScalars.addEquiv_symm_lie {R A L : Type*} [LieRing L] (x y : L) :
    (RestrictScalars.addEquiv R A L).symm ⁅x, y⁆ =
      ⁅(RestrictScalars.addEquiv R A L).symm x, (RestrictScalars.addEquiv R A L).symm y⁆ := rfl

namespace LieEquiv

variable (R : Type*) {A L₁ L₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L₁] [LieAlgebra A L₁] [LieRing L₂] [LieAlgebra A L₂]

/-- Restrict the scalars of an `A`-linear Lie equivalence along `Algebra R A`, yielding an
`R`-linear Lie equivalence between the `RestrictScalars R A` type aliases. -/
def restrictScalars (e : L₁ ≃ₗ⁅A⁆ L₂) :
    RestrictScalars R A L₁ ≃ₗ⁅R⁆ RestrictScalars R A L₂ where
  toFun x := (RestrictScalars.addEquiv R A L₂).symm (e (RestrictScalars.addEquiv R A L₁ x))
  invFun y := (RestrictScalars.addEquiv R A L₁).symm (e.symm (RestrictScalars.addEquiv R A L₂ y))
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp
  map_smul' r x := by
    rw [RestrictScalars.addEquiv_map_smul, map_smul,
      RestrictScalars.addEquiv_symm_map_algebraMap_smul, RingHom.id_apply]
  map_lie' {x y} := by
    simp only [RestrictScalars.addEquiv_lie, map_lie, RestrictScalars.addEquiv_symm_lie]

/-- Evaluating a scalar-restricted Lie equivalence transports through `RestrictScalars.addEquiv`. -/
@[simp]
theorem restrictScalars_apply (e : L₁ ≃ₗ⁅A⁆ L₂) (x : RestrictScalars R A L₁) :
    e.restrictScalars R x =
      (RestrictScalars.addEquiv R A L₂).symm (e (RestrictScalars.addEquiv R A L₁ x)) := by
  rfl

/-- Evaluating the inverse of a scalar-restricted Lie equivalence transports `e.symm` through
`RestrictScalars.addEquiv`. -/
@[simp]
theorem restrictScalars_symm_apply (e : L₁ ≃ₗ⁅A⁆ L₂) (y : RestrictScalars R A L₂) :
    (e.restrictScalars R).symm y =
      (RestrictScalars.addEquiv R A L₁).symm (e.symm (RestrictScalars.addEquiv R A L₂ y)) := by
  rfl

end LieEquiv

namespace LieAlgebra.ExtendScalars

open scoped TensorProduct

/-- Iterating the `S`-linear action of a pure tensor `a ⊗ₜ[R] u` on `b ⊗ₜ[R] v` in the extended
Lie module `A ⊗[R] M` raises `a` to the `m`-th power and iterates the action of `u` on `v`.

Quantifying over `S` lets the same identity serve both the `A`-linear action on `A ⊗[R] M` and,
when `M = L`, the `R`-linear adjoint action on `A ⊗[R] L`. -/
theorem toEnd_pow_tmul {S R A L M : Type*} [CommRing S] [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] [LieAlgebra S (A ⊗[R] L)] [Module S (A ⊗[R] M)]
    [LieModule S (A ⊗[R] L) (A ⊗[R] M)] (a b : A) (u : L) (v : M) (m : ℕ) :
    (LieModule.toEnd S (A ⊗[R] L) (A ⊗[R] M) (a ⊗ₜ[R] u) ^ m) (b ⊗ₜ[R] v) =
      (a ^ m * b) ⊗ₜ[R] ((LieModule.toEnd R L M u ^ m) v) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp, LieModule.toEnd_apply_apply, ih,
      LieAlgebra.ExtendScalars.bracket_tmul, pow_succ', mul_assoc,
      pow_succ', mul_apply_eq_comp, LieModule.toEnd_apply_apply]

/-- Iterating the `S`-linear adjoint action of a pure tensor `a ⊗ₜ[R] u` on `b ⊗ₜ[R] v` in the
extended Lie algebra `A ⊗[R] L` raises `a` to the `m`-th power and iterates `ad R L u` on `v`. -/
theorem ad_pow_tmul {S R A L : Type*} [CommRing S] [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L] [LieAlgebra R L] [LieAlgebra S (A ⊗[R] L)] (a b : A) (u v : L) (m : ℕ) :
    (LieAlgebra.ad S (A ⊗[R] L) (a ⊗ₜ[R] u) ^ m) (b ⊗ₜ[R] v) =
      (a ^ m * b) ⊗ₜ[R] ((LieAlgebra.ad R L u ^ m) v) :=
  toEnd_pow_tmul a b u v m

end LieAlgebra.ExtendScalars
