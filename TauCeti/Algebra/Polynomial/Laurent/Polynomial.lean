/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Extending Laurent-valued algebra homomorphisms over the origin

A Laurent polynomial comes from a polynomial exactly when all its negative coefficients
vanish. The same criterion applies to an algebra homomorphism with Laurent-polynomial values:
its extension over the origin is unique because `Polynomial.toLaurent` is injective.

The range criterion specializes `Finsupp.mem_range_mapDomain_iff` along the natural-number
inclusion into the integers. The algebra-homomorphism extension uses `AlgEquiv.ofInjective`
and `AlgHom.codRestrict` to factor through the polynomial subalgebra.
-/

public section

namespace TauCeti

variable {R A H : Type*}

/-- A Laurent polynomial comes from a polynomial exactly when its negative coefficients vanish. -/
@[simp]
theorem exists_toLaurent_eq_iff [Semiring A] {p : LaurentPolynomial A} :
    (∃ q : Polynomial A, q.toLaurent = p) ↔ ∀ n : ℤ, n < 0 → p.coeff n = 0 := by
  rw [← Set.mem_range]
  have hcast (n : ℤ) : n ∉ Set.range (Nat.cast : ℕ → ℤ) ↔ n < 0 := by
    constructor
    · intro hn
      by_contra h
      exact hn ⟨n.toNat, Int.toNat_of_nonneg (by omega)⟩
    · rintro hn ⟨m, hm⟩
      omega
  have hrange : p ∈ Set.range Polynomial.toLaurent ↔
      p.coeff ∈ Set.range (Finsupp.mapDomain (Nat.cast : ℕ → ℤ)) := by
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.toFinsupp.coeff, rfl⟩
    · rintro ⟨q, hq⟩
      refine ⟨Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff q), ?_⟩
      exact AddMonoidAlgebra.coeff_injective hq
  rw [hrange, Finsupp.mem_range_mapDomain_iff (Nat.cast : ℕ → ℤ) Nat.cast_injective]
  exact forall_congr' fun n ↦ imp_congr_left (hcast n)

variable [CommSemiring R] [CommSemiring A] [Semiring H]
variable [Algebra R A] [Algebra R H]

/-- A Laurent-valued algebra homomorphism extends to polynomial values exactly when all its
negative coefficients vanish. -/
theorem exists_algHom_toLaurent_comp_eq_iff {f : H →ₐ[R] LaurentPolynomial A} :
    (∃ F : H →ₐ[R] Polynomial A,
      (Polynomial.toLaurentAlg.restrictScalars R).comp F = f) ↔
      ∀ h : H, ∀ n : ℤ, n < 0 → (f h).coeff n = 0 := by
  constructor
  · rintro ⟨F, rfl⟩ h
    exact exists_toLaurent_eq_iff.mp ⟨F h, rfl⟩
  · intro hf
    let i : Polynomial A →ₐ[R] LaurentPolynomial A :=
      Polynomial.toLaurentAlg.restrictScalars R
    let e := AlgEquiv.ofInjective i Polynomial.toLaurent_injective
    let F := e.symm.toAlgHom.comp (f.codRestrict i.range fun h ↦
      exists_toLaurent_eq_iff.mpr (hf h))
    refine ⟨F, AlgHom.ext fun h ↦ ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply (f.codRestrict i.range _ h))

end TauCeti
