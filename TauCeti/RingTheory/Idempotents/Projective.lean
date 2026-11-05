/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Projectivity of principal ideals of idempotents

For an idempotent `e` in a semiring `R`, right multiplication by `e` retracts the regular
module onto its principal left ideal `Re`. Thus `Re` is projective. This is the projectivity
input for constructing projective covers from primitive idempotents.
If `R` is projective over a coefficient semiring `k` acting compatibly with multiplication
(`IsScalarTower k R R`), the same retraction makes `Re` projective over those coefficients.

For an idempotent `e` of an `R`-algebra `S` that is projective over a commutative semiring `R`, with
`e S = R e`, the surjection `R → R e` splits, so some `c : R` acts as the identity on `e` and
kills the annihilator of `e` (`IsIdempotentElem.exists_smul_eq_self_and_mul_eq_zero`).

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., §21.
-/

public section

namespace IsIdempotentElem

variable {R : Type*} [Semiring R] {e : R}

/-- A principal idempotent ideal of a semiring that is projective over a compatible coefficient
semiring is projective over those coefficients. The retraction is right multiplication by the
idempotent. -/
theorem projective_span_singleton_restrictScalars {k : Type*} [Semiring k] [Module k R]
    [IsScalarTower k R R] [Module.Projective k R] (he : IsIdempotentElem e) :
    Module.Projective k (Ideal.span {e} : Ideal R) := by
  apply Module.Projective.of_split ((Ideal.span {e} : Ideal R).subtype.restrictScalars k)
    ((LinearMap.toSpanSingleton R _ (TauCeti.spanSingletonGenerator e)).restrictScalars k)
  exact LinearMap.ext (TauCeti.smul_spanSingletonGenerator he)

/-- The principal left ideal of an idempotent is projective: right multiplication by the
idempotent retracts the regular module onto that ideal. -/
theorem projective_span_singleton (he : IsIdempotentElem e) :
    Module.Projective R (Ideal.span {e} : Ideal R) :=
  he.projective_span_singleton_restrictScalars (k := R)

/-- Let `e` be an idempotent of an `R`-algebra `S` that is projective as an `R`-module, with
`e S = R e`. Then the surjection `R → R e` splits: some `c : R` has `c e = e` and kills the
annihilator of `e`. -/
theorem exists_smul_eq_self_and_mul_eq_zero {R S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S]
    [Module.Projective R S] {e : S} (he : IsIdempotentElem e)
    (hσ : ∀ y : S, ∃ σ : R, σ • e = e * y) :
    ∃ c : R, c • e = e ∧ ∀ r : R, r • e = 0 → r * c = 0 := by
  -- The summand `e S` of `S` is projective, so `R → e S`, `r ↦ r e` has a section `τ`.
  let L := LinearMap.mulLeft R e
  have hL (y : S) : L y ∈ LinearMap.range L := LinearMap.mem_range_self L y
  have : Module.Projective R (LinearMap.range L) :=
    Module.Projective.of_split (LinearMap.range L).subtype (L.codRestrict _ hL) (by
      ext ⟨_, y, rfl⟩
      simp [L, ← mul_assoc, he.eq])
  let e' : LinearMap.range L := ⟨e, by simpa [L] using hL 1⟩
  have hρ : Function.Surjective (LinearMap.toSpanSingleton R (LinearMap.range L) e') := by
    rintro ⟨_, y, rfl⟩
    obtain ⟨σ, hσ⟩ := hσ y
    exact ⟨σ, Subtype.ext hσ⟩
  obtain ⟨τ, hτ⟩ := Module.projective_lifting_property _ LinearMap.id hρ
  refine ⟨τ e', congrArg Subtype.val (LinearMap.congr_fun hτ e'), fun r hr ↦ ?_⟩
  have hre : r • e' = 0 := Subtype.ext hr
  rw [← smul_eq_mul, ← map_smul, hre, map_zero]

end IsIdempotentElem
