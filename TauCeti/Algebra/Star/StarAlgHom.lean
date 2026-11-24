/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary

/-!
# Functoriality of `StarAlgHom.toNonUnitalStarAlgHom` and `StarAlgEquiv.arrowCongr`

This file supplements `Mathlib.Algebra.Star.StarAlgHom` with basic functoriality and injectivity
lemmas for forgetting unitality on `StarAlgHom`, together with injectivity and unitary-conjugacy
transport along `StarAlgEquiv.arrowCongr` and `StarAlgEquiv.arrowCongr'`:

* `StarAlgHom.toNonUnitalStarAlgHom_id`: forgetting unitality sends `StarAlgHom.id` to
  `NonUnitalStarAlgHom.id`.
* `StarAlgHom.toNonUnitalStarAlgHom_comp`: forgetting unitality preserves composition.
* `StarAlgHom.toNonUnitalStarAlgHom_injective`: forgetting unitality is injective.
* `StarAlgEquiv.arrowCongr'_injective_iff`, `StarAlgEquiv.arrowCongr_injective_iff`: conjugating
  by `⋆`-algebra equivalences preserves injectivity.
* `StarAlgEquiv.exists_unitary_conj_arrowCongr'_iff`,
  `StarAlgEquiv.exists_unitary_conj_arrowCongr_iff`: conjugating by `⋆`-algebra equivalences
  preserves unitary conjugacy in the target.
-/

public section

namespace StarAlgHom

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]

/-- Forgetting unitality sends the identity `StarAlgHom` to the identity `NonUnitalStarAlgHom`. -/
@[simp]
theorem toNonUnitalStarAlgHom_id :
    (StarAlgHom.id R A).toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id R A :=
  NonUnitalStarAlgHom.ext fun _ ↦ rfl

/-- Forgetting unitality preserves composition of `StarAlgHom`s. -/
@[simp]
theorem toNonUnitalStarAlgHom_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) :
    (f.comp g).toNonUnitalStarAlgHom = f.toNonUnitalStarAlgHom.comp g.toNonUnitalStarAlgHom :=
  NonUnitalStarAlgHom.ext fun _ ↦ rfl

/-- Forgetting unitality on `StarAlgHom` is injective. -/
theorem toNonUnitalStarAlgHom_injective :
    Function.Injective (toNonUnitalStarAlgHom (R := R) (A := A) (B := B)) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

end StarAlgHom

namespace StarAlgEquiv

section NonUnitalArrowCongr

variable {R A₁ A₂ A₁' A₂' : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A₁] [DistribMulAction R A₁] [Star A₁]
  [NonUnitalNonAssocSemiring A₁'] [DistribMulAction R A₁'] [Star A₁']

/-- Conjugating a non-unital `⋆`-algebra homomorphism by `⋆`-algebra equivalences preserves
injectivity. -/
theorem arrowCongr'_injective_iff
    [NonUnitalNonAssocSemiring A₂] [DistribMulAction R A₂] [Star A₂]
    [NonUnitalNonAssocSemiring A₂'] [DistribMulAction R A₂'] [Star A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (f : A₁ →⋆ₙₐ[R] A₂) :
    Function.Injective (e₁.arrowCongr' e₂ f) ↔ Function.Injective f := by
  refine ⟨fun h x y hxy ↦ ?_, fun h ↦ e₂.injective.comp (h.comp e₁.symm.injective)⟩
  have h' := congrArg e₁.symm (h (a₁ := e₁ x) (a₂ := e₁ y) (by simp [hxy]))
  simpa using h'

/-- Conjugating non-unital `⋆`-algebra homomorphisms by `⋆`-algebra equivalences preserves unitary
conjugacy in the target. -/
theorem exists_unitary_conj_arrowCongr'_iff
    [Semiring A₂] [DistribMulAction R A₂] [StarMul A₂]
    [Semiring A₂'] [DistribMulAction R A₂'] [StarMul A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (φ ψ : A₁ →⋆ₙₐ[R] A₂) :
    (∃ u : unitary A₂', ∀ x, (u : A₂') * e₁.arrowCongr' e₂ φ x * star (u : A₂') =
        e₁.arrowCongr' e₂ ψ x) ↔
      ∃ u : unitary A₂, ∀ x, (u : A₂) * φ x * star (u : A₂) = ψ x := by
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨⟨e₂.symm u, Unitary.map_mem e₂.symm u.prop⟩, fun x ↦ ?_⟩,
    fun ⟨u, hu⟩ ↦ ⟨⟨e₂ u, Unitary.map_mem e₂ u.prop⟩, fun x ↦ ?_⟩⟩
  · simpa only [arrowCongr'_apply, NonUnitalStarAlgHom.comp_apply, toNonUnitalStarAlgHom_apply,
      map_mul, map_star, symm_apply_apply] using congrArg e₂.symm (hu (e₁ x))
  · simpa only [arrowCongr'_apply, NonUnitalStarAlgHom.comp_apply, toNonUnitalStarAlgHom_apply,
      map_mul, map_star] using congrArg e₂ (hu (e₁.symm x))

end NonUnitalArrowCongr

section UnitalArrowCongr

variable {R A₁ A₂ A₁' A₂' : Type*} [CommSemiring R]
  [Semiring A₁] [Algebra R A₁] [Star A₁]
  [Semiring A₁'] [Algebra R A₁'] [Star A₁']

/-- Forgetting unitality intertwines `StarAlgEquiv.arrowCongr` with `StarAlgEquiv.arrowCongr'`. -/
theorem toNonUnitalStarAlgHom_arrowCongr
    [Semiring A₂] [Algebra R A₂] [Star A₂]
    [Semiring A₂'] [Algebra R A₂'] [Star A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (f : A₁ →⋆ₐ[R] A₂) :
    (e₁.arrowCongr e₂ f).toNonUnitalStarAlgHom = e₁.arrowCongr' e₂ f.toNonUnitalStarAlgHom :=
  rfl

/-- Conjugating a unital `⋆`-algebra homomorphism by `⋆`-algebra equivalences preserves
injectivity. -/
theorem arrowCongr_injective_iff
    [Semiring A₂] [Algebra R A₂] [Star A₂]
    [Semiring A₂'] [Algebra R A₂'] [Star A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (f : A₁ →⋆ₐ[R] A₂) :
    Function.Injective (e₁.arrowCongr e₂ f) ↔ Function.Injective f :=
  arrowCongr'_injective_iff e₁ e₂ f.toNonUnitalStarAlgHom

/-- Conjugating unital `⋆`-algebra homomorphisms by `⋆`-algebra equivalences preserves unitary
conjugacy in the target. -/
theorem exists_unitary_conj_arrowCongr_iff
    [Semiring A₂] [Algebra R A₂] [StarMul A₂]
    [Semiring A₂'] [Algebra R A₂'] [StarMul A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (φ ψ : A₁ →⋆ₐ[R] A₂) :
    (∃ u : unitary A₂', ∀ x, (u : A₂') * e₁.arrowCongr e₂ φ x * star (u : A₂') =
        e₁.arrowCongr e₂ ψ x) ↔
      ∃ u : unitary A₂, ∀ x, (u : A₂) * φ x * star (u : A₂) = ψ x :=
  exists_unitary_conj_arrowCongr'_iff e₁ e₂ φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom

end UnitalArrowCongr

end StarAlgEquiv
