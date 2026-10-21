/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic

/-!
# Frobenius functionals on division algebras

Every nonzero `K`-linear functional on a division semiring `L` over a commutative semiring
`K` is a Frobenius functional. For a finite-dimensional division algebra over a field,
the multiplication pairing identifies `L` with its `K`-dual, and two nonzero functionals
differ by multiplication by a unique unit of `L`. For a field extension, this unique
scalar is the change of functional in Scharlau transfer.

The functional choice follows Scharlau, *Quadratic and Hermitian Forms*, Chapter 2,
§5, and Lam, *Introduction to Quadratic Forms over Fields*, Chapter VII, §1.
-/

public section

noncomputable section

namespace LinearMap

section DivisionSemiring

variable {K L : Type*} [CommSemiring K] [DivisionSemiring L] [Algebra K L]

/-- On a division semiring `L` over a commutative semiring `K`, a `K`-linear functional is
Frobenius exactly when it is nonzero. No finite-dimensionality assumption is needed. -/
@[simp]
theorem isFrobeniusFunctional_iff_ne_zero (s : L →ₗ[K] K) :
    s.IsFrobeniusFunctional ↔ s ≠ 0 := by
  rw [isFrobeniusFunctional_iff]
  constructor
  · intro hs hzero
    exact one_ne_zero (hs.1 1 (by simp [hzero]))
  · intro hs
    obtain ⟨x, hx⟩ : ∃ x : L, s x ≠ 0 := by simpa [Ne, LinearMap.ext_iff] using hs
    constructor
    · intro a ha
      by_contra hne
      exact hx (by simpa [mul_assoc, hne] using ha (a⁻¹ * x))
    · intro b hb
      by_contra hne
      exact hx (by simpa [← mul_assoc, hne] using hb (x * b⁻¹))

end DivisionSemiring

variable {K L : Type*} [Field K] [DivisionRing L] [Algebra K L]

/-- Two nonzero `K`-linear functionals on a finite-dimensional division algebra differ by
multiplication by a unique unit of the algebra. -/
theorem existsUnique_unit_apply_eq_apply_mul (s t : L →ₗ[K] K)
    [FiniteDimensional K L] (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃! u : Lˣ, ∀ x : L, t x = s ((u : L) * x) := by
  have hsFrob : s.IsFrobeniusFunctional := s.isFrobeniusFunctional_iff_ne_zero.mpr hs
  let e := hsFrob.toDualEquiv
  let a := e.symm t
  have hta : e a = t := e.apply_symm_apply t
  have happly (b x : L) : e b x = s (b * x) := hsFrob.toDualEquiv_apply_apply b x
  have ha : a ≠ 0 := e.symm.map_ne_zero_iff.mpr ht
  refine ⟨Units.mk0 a ha, ?_, ?_⟩
  · intro x
    rw [← hta, happly]
    simp
  · intro u hu
    apply Units.ext
    apply e.injective
    calc
      e (u : L) = t := by
        ext x
        rw [happly]
        exact (hu x).symm
      _ = e a := hta.symm

end LinearMap
