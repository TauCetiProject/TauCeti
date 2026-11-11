/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Cointegrals of monoid algebras

For the group-like coproduct on a monoid algebra, the left and right cointegrals
are exactly the scalar multiples of the coefficient functional at the identity.
In particular there is a nonzero cointegral over every nontrivial coefficient
semiring, even for an infinite monoid. Over a nontrivial coefficient semiring, the
counit is not a cointegral when the monoid has a nonidentity element. These results
only require a distinguished element `1` on the indexing type, not multiplication.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k M : Type*} [CommSemiring k] [One M]

/-- On a monoid algebra, the right-cointegral equation can be checked on the
canonical monoid basis. -/
theorem isRightCointegral_monoidAlgebra_iff (φ : Module.Dual k (MonoidAlgebra k M)) :
    IsRightCointegral φ ↔ ∀ m : M,
      φ (MonoidAlgebra.single m 1) • MonoidAlgebra.single m 1 =
        φ (MonoidAlgebra.single m 1) • (1 : MonoidAlgebra k M) := by
  rw [isRightCointegral_def]
  constructor
  · intro hφ m
    simpa using hφ (MonoidAlgebra.single m 1)
  · intro hφ
    have heq : (TensorProduct.lid k (MonoidAlgebra k M)).toLinearMap ∘ₗ
        φ.rTensor (MonoidAlgebra k M) ∘ₗ Coalgebra.comul =
        LinearMap.toSpanSingleton k (MonoidAlgebra k M) 1 ∘ₗ φ := by
      apply (MonoidAlgebra.basis M k).ext
      intro m
      simpa using hφ m
    intro h
    exact congrArg (fun f : MonoidAlgebra k M →ₗ[k] MonoidAlgebra k M => f h) heq

/-- The right-cointegral line is spanned by the coefficient functional at the identity. -/
theorem isRightCointegral_monoidAlgebra_iff_eq_smul
    (φ : Module.Dual k (MonoidAlgebra k M)) :
    IsRightCointegral φ ↔ φ = φ 1 • (MonoidAlgebra.basis M k).coord 1 := by
  classical
  rw [isRightCointegral_monoidAlgebra_iff]
  constructor
  · intro hφ
    apply (MonoidAlgebra.basis M k).ext
    intro m
    by_cases hm : m = 1
    · subst m
      simp [MonoidAlgebra.one_def, ← MonoidAlgebra.basis_apply]
    · have heq := congrArg (fun x : MonoidAlgebra k M => x.coeff m) (hφ m)
      have hzero : φ (MonoidAlgebra.single m 1) = 0 := by
        simpa [MonoidAlgebra.one_def, hm] using heq
      simpa [← MonoidAlgebra.basis_apply, Ne.symm hm] using hzero
  · intro hφ m
    rw [hφ]
    by_cases hm : m = 1
    · subst m
      simp [MonoidAlgebra.one_def]
    · simp [← MonoidAlgebra.basis_apply, Ne.symm hm]

/-- The coefficient at the identity is a right cointegral, with no finiteness assumption. -/
theorem isRightCointegral_monoidAlgebra_coord_one :
    IsRightCointegral ((MonoidAlgebra.basis M k).coord 1) := by
  rw [isRightCointegral_monoidAlgebra_iff_eq_smul]
  simp [MonoidAlgebra.one_def, ← MonoidAlgebra.basis_apply]

/-- The left-cointegral line is spanned by the coefficient functional at the identity. -/
theorem isLeftCointegral_monoidAlgebra_iff_eq_smul
    (φ : Module.Dual k (MonoidAlgebra k M)) :
    IsLeftCointegral φ ↔ φ = φ 1 • (MonoidAlgebra.basis M k).coord 1 := by
  rw [isLeftCointegral_iff_isRightCointegral, isRightCointegral_monoidAlgebra_iff_eq_smul]

/-- The coefficient at the identity is a left cointegral, with no finiteness assumption. -/
theorem isLeftCointegral_monoidAlgebra_coord_one :
    IsLeftCointegral ((MonoidAlgebra.basis M k).coord 1) := by
  rw [isLeftCointegral_iff_isRightCointegral]
  exact isRightCointegral_monoidAlgebra_coord_one

/-- Over a nontrivial coefficient semiring, the counit is not a right cointegral when the
indexing type has an element distinct from `1`. -/
theorem not_isRightCointegral_monoidAlgebra_counit [Nontrivial k]
    {m : M} (hm : m ≠ 1) :
    ¬ IsRightCointegral (Coalgebra.counit (R := k) (A := MonoidAlgebra k M)) := by
  intro hφ
  have heq := (isRightCointegral_monoidAlgebra_iff _).mp hφ m
  have hcoeff := congrArg (fun x : MonoidAlgebra k M => x.coeff m) heq
  simp [MonoidAlgebra.one_def, hm] at hcoeff

/-- Over a nontrivial coefficient semiring, the counit is not a left cointegral when the
indexing type has an element distinct from `1`. -/
theorem not_isLeftCointegral_monoidAlgebra_counit [Nontrivial k]
    {m : M} (hm : m ≠ 1) :
    ¬ IsLeftCointegral (Coalgebra.counit (R := k) (A := MonoidAlgebra k M)) := by
  rw [isLeftCointegral_iff_isRightCointegral]
  exact not_isRightCointegral_monoidAlgebra_counit hm

end TauCeti
