/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Laurent.Basic
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Int.Cast.Basic

/-!
# Positive Laurent polynomials with integral monoid-algebra coefficients

For a commutative monoid `P`, the natural-coefficient Laurent polynomials form a
subsemiring of `LaurentRing (MonoidAlgebra ℤ P) K`. Its elements have nonnegative integer
coefficients at every pair consisting of a Laurent exponent and a coefficient monomial.
This is a condition on the unique finite expansion, rather than on an ambient field order.

The positive subsemiring is the image of the actual coefficient map from
`LaurentRing (MonoidAlgebra ℕ P) K`. Its coefficient criterion uses the generic
`MonoidAlgebra.mem_rangeS_mapRingHom_iff`, which reuses `MonoidAlgebra.range_map`.
Variable maps may identify variables and still preserve
positivity. Reflection requires injectivity.

This constructs the positive carrier and its transport; it asserts no positivity theorem
for mutation-generated cluster variables.

## References

* K. Lee and R. Schiffler, *Positivity for cluster algebras*, Annals of Mathematics 182
  (2015), §2, Conjecture 2.6, for the coefficientwise meaning of positivity.
-/

public section

namespace TauCeti.LaurentRing

variable (P K : Type*) [CommMonoid P]

/-- Include natural-coefficient Laurent polynomials in those with integral monoid-algebra
coefficients. -/
noncomputable def natCoeffMap :
    LaurentRing (MonoidAlgebra ℕ P) K →+* LaurentRing (MonoidAlgebra ℤ P) K :=
  AddMonoidAlgebra.mapRingHom (K →₀ ℤ)
    (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ))

/-- The positive Laurent subsemiring over the integral monoid algebra is the image of
the corresponding natural-coefficient Laurent semiring. -/
noncomputable def positive : Subsemiring (LaurentRing (MonoidAlgebra ℤ P) K) :=
  (natCoeffMap P K).rangeS

/-- The positive subsemiring is the image of the natural-coefficient inclusion. -/
theorem positive_def : positive P K = (natCoeffMap P K).rangeS := by rfl

variable {P K}

/-- The inclusion is the usual natural-to-integer cast on every coefficient. -/
@[simp]
theorem coeff_natCoeffMap (p : LaurentRing (MonoidAlgebra ℕ P) K) (m : K →₀ ℤ) (a : P) :
    ((natCoeffMap P K p).coeff m).coeff a = ((p.coeff m).coeff a : ℤ) := by
  simp [natCoeffMap]

/-- The natural-coefficient representative of a positive Laurent polynomial is unique. -/
theorem natCoeffMap_injective : Function.Injective (natCoeffMap P K) := by
  intro p q h
  ext m a
  have hc := congrArg (fun r : LaurentRing (MonoidAlgebra ℤ P) K ↦ (r.coeff m).coeff a) h
  simpa only [coeff_natCoeffMap, Nat.cast_inj] using hc

/-- A Laurent polynomial is positive exactly when it has a unique natural-coefficient
representative. -/
theorem mem_positive_iff_existsUnique (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    p ∈ positive P K ↔ ∃! q, natCoeffMap P K q = p := by
  rw [positive_def, RingHom.mem_rangeS]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq, fun y hy ↦ natCoeffMap_injective (hy.trans hq.symm)⟩
  · rintro ⟨q, hq, _⟩
    exact ⟨q, hq⟩

/-- Positivity is exactly nonnegativity at every Laurent and coefficient-monoid exponent. -/
theorem mem_positive_iff (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    p ∈ positive P K ↔ ∀ m a, 0 ≤ (p.coeff m).coeff a := by
  rw [positive, natCoeffMap, AddMonoidAlgebra.mem_rangeS_mapRingHom_iff]
  simp_rw [MonoidAlgebra.mem_rangeS_mapRingHom_iff, RingHom.mem_rangeS]
  simp only [Nat.coe_castRingHom]
  constructor
  · intro h m a
    obtain ⟨n, hn⟩ := h m a
    simpa only [← hn] using Int.natCast_nonneg n
  · intro h m a
    exact ⟨((p.coeff m).coeff a).toNat, Int.toNat_of_nonneg (h m a)⟩

/-- Every natural-coefficient representative defines a positive Laurent polynomial. -/
theorem natCoeffMap_mem_positive (p : LaurentRing (MonoidAlgebra ℕ P) K) :
    natCoeffMap P K p ∈ positive P K := (natCoeffMap P K).mem_rangeS_self p

/-- Renaming Laurent variables preserves positivity, including maps that identify variables. -/
theorem rename_mem_positive {K' : Type*} (f : K → K')
    {p : LaurentRing (MonoidAlgebra ℤ P) K} (hp : p ∈ positive P K) :
    rename f p ∈ positive P K' := by
  obtain ⟨q, rfl⟩ := hp
  refine ⟨rename f q, ?_⟩
  simpa only [natCoeffMap] using
    mapRingHom_rename (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) f q

/-- An injective variable map also reflects positivity. -/
theorem rename_mem_positive_iff {K' : Type*} {f : K → K'} (hf : Function.Injective f)
    (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    rename f p ∈ positive P K' ↔ p ∈ positive P K := by
  refine ⟨?_, rename_mem_positive f⟩
  intro h
  rw [mem_positive_iff] at h ⊢
  intro m a
  have hc : (rename f p).coeff (Finsupp.mapDomain f m) = p.coeff m := by
    rw [rename_apply, AddMonoidAlgebra.coeff_mapDomain]
    exact Finsupp.mapDomain_apply_of_injective (Finsupp.mapDomain_injective hf) _ m
  simpa only [hc] using h (Finsupp.mapDomain f m) a

/-- Relabelling variables preserves and reflects the positive subsemiring. -/
@[simp↓]
theorem renameEquiv_mem_positive_iff {K' : Type*} (e : K ≃ K')
    (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    renameEquiv (MonoidAlgebra ℤ P) e p ∈ positive P K' ↔ p ∈ positive P K := by
  rw [renameEquiv_apply]
  exact rename_mem_positive_iff e.injective p

/-- Mapping the coefficient monoid preserves positivity even when its monomials collide. -/
theorem mapDomain_coeff_mem_positive {Q : Type*} [CommMonoid Q] (f : P →* Q)
    {p : LaurentRing (MonoidAlgebra ℤ P) K} (hp : p ∈ positive P K) :
    AddMonoidAlgebra.mapRingHom (K →₀ ℤ) (MonoidAlgebra.mapDomainRingHom ℤ f) p ∈
      positive Q K := by
  obtain ⟨q, rfl⟩ := hp
  refine ⟨AddMonoidAlgebra.mapRingHom (K →₀ ℤ) (MonoidAlgebra.mapDomainRingHom ℕ f) q, ?_⟩
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  simp only [natCoeffMap, AddMonoidAlgebra.coeff_mapRingHom]
  exact DFunLike.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom (Nat.castRingHom ℤ) f) (q.coeff m)

/-- An injective coefficient-monoid map also reflects positivity. -/
theorem mapDomain_coeff_mem_positive_iff {Q : Type*} [CommMonoid Q] (f : P →* Q)
    (hf : Function.Injective f) (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    AddMonoidAlgebra.mapRingHom (K →₀ ℤ) (MonoidAlgebra.mapDomainRingHom ℤ f) p ∈
        positive Q K ↔ p ∈ positive P K := by
  refine ⟨?_, mapDomain_coeff_mem_positive f⟩
  intro h
  rw [mem_positive_iff] at h ⊢
  intro m a
  have hc :
      (MonoidAlgebra.mapDomainRingHom ℤ f (p.coeff m)).coeff (f a) = (p.coeff m).coeff a := by
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
    exact Finsupp.mapDomain_apply_of_injective hf _ a
  simpa only [AddMonoidAlgebra.coeff_mapRingHom, hc] using h m (f a)

/-- A Laurent polynomial and its negative can both be positive only when it is zero. -/
theorem neg_mem_positive_iff {p : LaurentRing (MonoidAlgebra ℤ P) K}
    (hp : p ∈ positive P K) : -p ∈ positive P K ↔ p = 0 := by
  constructor
  · intro hn
    apply AddMonoidAlgebra.ext
    ext m a
    apply le_antisymm
    · have h := (mem_positive_iff (-p)).mp hn m a
      simpa using h
    · exact (mem_positive_iff p).mp hp m a
  · rintro rfl
    simp

end TauCeti.LaurentRing
