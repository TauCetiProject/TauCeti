/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses
public import TauCeti.Algebra.MvPolynomial.Division

/-!
# Renaming variables, and discarding the ones outside the range

Renaming the variables of a multivariable polynomial along an equivalence `e : σ ≃ τ` is a
ring equivalence. Mathlib's `RingHomInvPair.of_ringEquiv` and
`RingHomInvPair.of_ringEquiv_symm` are deliberately not instances, so this file registers them
for `MvPolynomial.renameEquiv`. This lets semilinear equivalences over variable renaming be used
and inverted without requiring downstream local instances.

Along an injective renaming `f : σ → τ`, Mathlib's `MvPolynomial.killCompl` sets the variables
outside the range of `f` to zero. When exactly one variable `X a` is discarded, the polynomials
it kills are exactly the multiples of `X a`.

## Main definitions

* `TauCeti.renameRingHomInvPair`: variable renaming and its inverse form a `RingHomInvPair`.
* `TauCeti.renameRingHomInvPairSymm`: the same inverse pair in the reverse direction.

## Main results

* `MvPolynomial.killCompl_eq_zero_iff_X_dvd`: when the range of the renaming is the complement of
  a single variable `X a`, discarding that variable kills exactly the multiples of `X a`.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R] {f : σ → τ} (hf : Function.Injective f) {a : τ}

/-- Discarding the variables outside the range of an injective renaming kills a variable in the
complement of that range. -/
theorem killCompl_X_of_notMem_range (ha : a ∉ Set.range f) :
    killCompl (R := R) hf (X a) = 0 := by
  simp [killCompl, ha]

/-- When the range of an injective renaming is the complement of a single variable `X a`,
discarding the variables outside the range kills exactly the multiples of `X a`. -/
theorem killCompl_eq_zero_iff_X_dvd (ha : Set.range f = {a}ᶜ) (p : MvPolynomial τ R) :
    killCompl hf p = 0 ↔ X a ∣ p := by
  have hna : a ∉ Set.range f := by simp [ha]
  constructor
  · intro h
    rw [X_dvd_iff_modMonomial_eq_zero]
    refine MvPolynomial.ext _ _ fun m => ?_
    rcases Nat.eq_zero_or_pos (m a) with hm | hm
    · -- A monomial avoiding `a` is renamed from a monomial in the source variables.
      have hsub : ↑m.support ⊆ Set.range f := by
        intro x hx
        rw [ha]
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl
        exact (Finsupp.mem_support_iff.mp hx) hm
      have hmd : Finsupp.mapDomain f (Finsupp.comapDomain f m hf.injOn) = m :=
        m.mapDomain_comapDomain f hf hsub
      rw [coeff_modMonomial_of_not_le _ (by rw [Finsupp.single_le_iff]; omega), ← hmd,
        ← coeff_killCompl hf, h]
      simp
    · rw [coeff_modMonomial_of_le _ (by rw [Finsupp.single_le_iff]; omega)]
      simp
  · rintro ⟨q, rfl⟩
    rw [map_mul, killCompl_X_of_notMem_range hf hna, zero_mul]

end MvPolynomial

namespace TauCeti

variable {σ τ : Type*} (R : Type*) [CommSemiring R]

/-- A polynomial variable-renaming ring equivalence and its inverse form a
`RingHomInvPair`. -/
noncomputable instance renameRingHomInvPair (e : σ ≃ τ) :
    RingHomInvPair
      ((MvPolynomial.renameEquiv R e).toRingEquiv :
        MvPolynomial σ R →+* MvPolynomial τ R)
      ((MvPolynomial.renameEquiv R e).toRingEquiv.symm :
        MvPolynomial τ R →+* MvPolynomial σ R) :=
  RingHomInvPair.of_ringEquiv (MvPolynomial.renameEquiv R e).toRingEquiv

/-- The inverse polynomial variable-renaming ring equivalence and the forward equivalence form a
`RingHomInvPair`. -/
noncomputable instance renameRingHomInvPairSymm (e : σ ≃ τ) :
    RingHomInvPair
      ((MvPolynomial.renameEquiv R e).toRingEquiv.symm :
        MvPolynomial τ R →+* MvPolynomial σ R)
      ((MvPolynomial.renameEquiv R e).toRingEquiv :
        MvPolynomial σ R →+* MvPolynomial τ R) :=
  RingHomInvPair.of_ringEquiv_symm (MvPolynomial.renameEquiv R e).toRingEquiv

end TauCeti
