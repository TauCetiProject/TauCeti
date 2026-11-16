/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Bialgebra equivalences

Bialgebra equivalences `A₁ ≃ₐc[R] A₁'` and `A₂ ≃ₐc[R] A₂'` identify the bialgebra homomorphisms
`A₁ →ₐc[R] A₂` with the bialgebra homomorphisms `A₁' →ₐc[R] A₂'`, by conjugation. This is the
bialgebra analogue of Mathlib's `AlgEquiv.arrowCongr`. It is used to compare functors of bialgebra
homomorphisms whose values are only identified up to canonical bialgebra isomorphisms, such as
iterated base changes.

A bialgebra whose structure map is surjective is trivial: its counit is a bialgebra equivalence
with the base ring. The structure map of a bialgebra is always injective, so surjectivity is the
whole condition. This is the common form of the statement that an affine group is trivial.

## Main definitions

* `BialgEquiv.arrowCongr`: the bijection `(A₁ →ₐc[R] A₂) ≃ (A₁' →ₐc[R] A₂')` induced by two
  bialgebra equivalences.
* `Bialgebra.counitBialgEquivOfSurjective`: the counit as a bialgebra equivalence with the base
  ring, when the structure map is surjective.

## Main results

* `BialgEquiv.arrowCongr_apply` and `BialgEquiv.arrowCongr_symm_apply`: it and its inverse are
  conjugation by the two equivalences.
* `Bialgebra.counitBialgEquivOfSurjective_apply` and
  `Bialgebra.counitBialgEquivOfSurjective_symm_apply`: the counit equivalence is the counit, and
  its inverse is the structure map.
-/

public section

namespace BialgEquiv

variable {R A₁ A₂ A₁' A₂' : Type*} [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₁']
  [Semiring A₂'] [Algebra R A₁] [Algebra R A₂] [Algebra R A₁'] [Algebra R A₂']
  [CoalgebraStruct R A₁] [CoalgebraStruct R A₂] [CoalgebraStruct R A₁'] [CoalgebraStruct R A₂']

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as bialgebras, then the type of
bialgebra homomorphisms `A₁ →ₐc[R] A₂` is equivalent to the type of bialgebra homomorphisms
`A₁' →ₐc[R] A₂'`. -/
def arrowCongr (e₁ : A₁ ≃ₐc[R] A₁') (e₂ : A₂ ≃ₐc[R] A₂') : (A₁ →ₐc[R] A₂) ≃ (A₁' →ₐc[R] A₂') where
  toFun f := (e₂ : A₂ →ₐc[R] A₂').comp (f.comp (e₁.symm : A₁' →ₐc[R] A₁))
  invFun f := (e₂.symm : A₂' →ₐc[R] A₂).comp (f.comp (e₁ : A₁ →ₐc[R] A₁'))
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/-- `BialgEquiv.arrowCongr e₁ e₂` sends `f` to `e₂ ∘ f ∘ e₁⁻¹`. -/
@[simp]
theorem arrowCongr_apply (e₁ : A₁ ≃ₐc[R] A₁') (e₂ : A₂ ≃ₐc[R] A₂') (f : A₁ →ₐc[R] A₂) :
    arrowCongr e₁ e₂ f = (e₂ : A₂ →ₐc[R] A₂').comp (f.comp (e₁.symm : A₁' →ₐc[R] A₁)) :=
  (rfl)

/-- The inverse of `BialgEquiv.arrowCongr e₁ e₂` sends `f` to `e₂⁻¹ ∘ f ∘ e₁`. -/
@[simp]
theorem arrowCongr_symm_apply (e₁ : A₁ ≃ₐc[R] A₁') (e₂ : A₂ ≃ₐc[R] A₂') (f : A₁' →ₐc[R] A₂') :
    (arrowCongr e₁ e₂).symm f = (e₂.symm : A₂' →ₐc[R] A₂).comp (f.comp (e₁ : A₁ →ₐc[R] A₁')) :=
  (rfl)

end BialgEquiv

namespace Bialgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- A bialgebra whose structure map is surjective is bialgebra-equivalent to its base ring via
the counit. -/
noncomputable def counitBialgEquivOfSurjective (h : Function.Surjective (algebraMap R A)) :
    A ≃ₐc[R] R :=
  BialgEquiv.ofBijective (counitBialgHom R A)
    ⟨fun x y hxy ↦ by
      obtain ⟨r, rfl⟩ := h x
      obtain ⟨s, rfl⟩ := h y
      simp only [counitBialgHom_apply, counit_algebraMap] at hxy
      rw [hxy],
    counit_surjective⟩

/-- The counit equivalence of a bialgebra with surjective structure map is the counit. -/
@[simp]
theorem counitBialgEquivOfSurjective_apply (h : Function.Surjective (algebraMap R A)) (x : A) :
    counitBialgEquivOfSurjective h x = Coalgebra.counit (R := R) x := by
  rw [counitBialgEquivOfSurjective]
  exact congrFun (BialgEquiv.coe_ofBijective (counitBialgHom R A) _) x

/-- The inverse of the counit equivalence of a bialgebra with surjective structure map is the
structure map. -/
@[simp]
theorem counitBialgEquivOfSurjective_symm_apply (h : Function.Surjective (algebraMap R A))
    (r : R) : (counitBialgEquivOfSurjective h).symm r = algebraMap R A r := by
  let e := counitBialgEquivOfSurjective h
  refine e.toMulEquiv.symm_apply_eq.mpr ?_
  calc
    r = Coalgebra.counit (R := R) (algebraMap R A r) := (counit_algebraMap r).symm
    _ = e (algebraMap R A r) := (counitBialgEquivOfSurjective_apply h _).symm

end Bialgebra
