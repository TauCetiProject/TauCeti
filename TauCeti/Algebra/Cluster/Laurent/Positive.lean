/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Laurent.Basic
public import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Positive Laurent polynomials with integral monoid-algebra coefficients

For a monoid `P`, the natural-coefficient Laurent polynomials form a
subsemiring of `LaurentRing (MonoidAlgebra ℤ P) K`. Its elements have nonnegative integer
coefficients at every pair consisting of a Laurent exponent and a coefficient monomial.
This is a condition on the unique finite expansion, rather than on an ambient field order.

`TauCeti.LaurentRing.natCoeffMap` includes natural-coefficient Laurent polynomials,
`TauCeti.LaurentRing.positive` is its image subsemiring, and
`TauCeti.LaurentRing.mem_positive_iff` characterizes membership by coefficient nonnegativity.
Coefficient-monoid homomorphisms preserve positivity for arbitrary monoids and reflect it
when injective. Variable renaming preserves positivity for commutative coefficient monoids,
even when variables collide, and reflects it when the variable map is injective.

This constructs the positive carrier and its transport; it asserts no positivity theorem
for mutation-generated cluster variables.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15
  (2002), Introduction, for the group-ring Laurent setting and positivity conjecture.
* K. Lee and R. Schiffler, *Positivity for cluster algebras*, Annals of Mathematics 182
  (2015), §2, Conjecture 2.6, for a later coefficientwise formulation.
-/

public section

namespace TauCeti.LaurentRing

section Monoid

variable (P K : Type*) [Monoid P]

/-- Include natural-coefficient Laurent polynomials in those with integral monoid-algebra
coefficients. -/
noncomputable def natCoeffMap :
    LaurentRing (MonoidAlgebra ℕ P) K →+* LaurentRing (MonoidAlgebra ℤ P) K :=
  AddMonoidAlgebra.mapRingHom (K →₀ ℤ)
    (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ))

/-- The natural-coefficient inclusion is the iterated coefficient homomorphism. -/
theorem natCoeffMap_def : natCoeffMap P K =
    AddMonoidAlgebra.mapRingHom (K →₀ ℤ)
      (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) := by rfl

/-- The positive Laurent subsemiring over the integral monoid algebra is the image of
the corresponding natural-coefficient Laurent semiring. -/
noncomputable def positive : Subsemiring (LaurentRing (MonoidAlgebra ℤ P) K) :=
  (natCoeffMap P K).rangeS

/-- The positive subsemiring is the image of the natural-coefficient inclusion. -/
theorem positive_def : positive P K = (natCoeffMap P K).rangeS := by rfl

variable {P K}

/-- The inclusion applies the natural-to-integer map to a Laurent monomial's coefficient. -/
@[simp]
theorem natCoeffMap_single (m : K →₀ ℤ) (c : MonoidAlgebra ℕ P) :
    natCoeffMap P K (AddMonoidAlgebra.single m c) =
      AddMonoidAlgebra.single m (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ) c) := by
  simp [natCoeffMap_def]

/-- The inclusion fixes every Laurent variable. -/
@[simp]
theorem natCoeffMap_X (i : K) : natCoeffMap P K (X i) = X i := by
  simp [natCoeffMap_def]

/-- Each Laurent coefficient is mapped by the natural-to-integer monoid-algebra map. -/
@[simp]
theorem coeff_natCoeffMap (p : LaurentRing (MonoidAlgebra ℕ P) K) (m : K →₀ ℤ) :
    (natCoeffMap P K p).coeff m =
      MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ) (p.coeff m) := by
  simp [natCoeffMap_def]

/-- The natural-coefficient representative of a positive Laurent polynomial is unique. -/
theorem natCoeffMap_injective : Function.Injective (natCoeffMap P K) := by
  rw [natCoeffMap_def, AddMonoidAlgebra.coe_mapRingHom]
  apply AddMonoidAlgebra.map_injective
  rw [AddMonoidHom.coe_ofClass, MonoidAlgebra.coe_mapRingHom]
  exact MonoidAlgebra.map_injective _ Nat.cast_injective

/-- Equality of included natural-coefficient polynomials reflects equality of representatives. -/
@[simp]
theorem natCoeffMap_inj (p q : LaurentRing (MonoidAlgebra ℕ P) K) :
    natCoeffMap P K p = natCoeffMap P K q ↔ p = q := natCoeffMap_injective.eq_iff

/-- The inclusion kills only the zero polynomial. -/
@[simp]
theorem natCoeffMap_eq_zero (p : LaurentRing (MonoidAlgebra ℕ P) K) :
    natCoeffMap P K p = 0 ↔ p = 0 := map_eq_zero_iff _ natCoeffMap_injective

/-- The natural-to-integer inclusion preserves the finite Laurent support exactly. -/
@[simp]
theorem support_coeff_natCoeffMap (p : LaurentRing (MonoidAlgebra ℕ P) K) :
    (natCoeffMap P K p).coeff.support = p.coeff.support := by
  rw [natCoeffMap_def, AddMonoidAlgebra.coe_mapRingHom, AddMonoidAlgebra.coeff_map]
  apply Finsupp.support_mapRange_of_injective
  rw [AddMonoidHom.coe_ofClass, MonoidAlgebra.coe_mapRingHom]
  exact MonoidAlgebra.map_injective _ Nat.cast_injective

/-- A Laurent polynomial is positive exactly when it has a unique natural-coefficient
representative. -/
theorem mem_positive_iff_existsUnique (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    p ∈ positive P K ↔ ∃! q, natCoeffMap P K q = p := by
  rw [positive_def]
  exact RingHom.mem_rangeS.trans natCoeffMap_injective.existsUnique_iff_exists.symm

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
@[simp]
theorem natCoeffMap_mem_positive (p : LaurentRing (MonoidAlgebra ℕ P) K) :
    natCoeffMap P K p ∈ positive P K := (natCoeffMap P K).mem_rangeS_self p

/-- A Laurent monomial is positive exactly when its coefficient has nonnegative entries. -/
theorem single_mem_positive_iff (m : K →₀ ℤ) (c : MonoidAlgebra ℤ P) :
    AddMonoidAlgebra.single m c ∈ positive P K ↔ ∀ a, 0 ≤ c.coeff a := by
  classical
  rw [mem_positive_iff]
  constructor
  · intro h a
    simpa using h m a
  · intro h n a
    by_cases hm : m = n <;> simp [AddMonoidAlgebra.coeff_single, hm, h]

/-- A monomial with one integral coefficient is positive exactly when that integer is
nonnegative. -/
@[simp]
theorem single_single_mem_positive_iff (m : K →₀ ℤ) (a : P) (r : ℤ) :
    AddMonoidAlgebra.single m (MonoidAlgebra.single a r) ∈ positive P K ↔ 0 ≤ r := by
  classical
  rw [single_mem_positive_iff]
  constructor
  · intro h
    simpa using h a
  · intro h b
    by_cases hab : a = b <;> simp [MonoidAlgebra.coeff_single, hab, h]

/-- Every Laurent monomial with coefficient one belongs to the positive subsemiring. -/
@[simp]
theorem single_one_mem_positive (m : K →₀ ℤ) :
    AddMonoidAlgebra.single m (1 : MonoidAlgebra ℤ P) ∈ positive P K := by
  rw [MonoidAlgebra.one_def]
  simp

/-- The Laurent variables belong to the positive subsemiring. -/
@[simp]
theorem X_mem_positive (i : K) : (X i : LaurentRing (MonoidAlgebra ℤ P) K) ∈ positive P K := by
  rw [X_def]
  exact single_one_mem_positive _

/-- Inclusion of natural coefficients commutes with mapping the coefficient monoid. -/
theorem natCoeffMap_mapRingHom_mapDomainRingHom {Q : Type*} [Monoid Q] (f : P →* Q)
    (p : LaurentRing (MonoidAlgebra ℕ P) K) :
    natCoeffMap Q K (AddMonoidAlgebra.mapRingHom (K →₀ ℤ)
        (MonoidAlgebra.mapDomainRingHom ℕ f) p) =
      AddMonoidAlgebra.mapRingHom (K →₀ ℤ) (MonoidAlgebra.mapDomainRingHom ℤ f)
        (natCoeffMap P K p) := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  simp only [natCoeffMap_def, AddMonoidAlgebra.coeff_mapRingHom]
  exact DFunLike.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom (Nat.castRingHom ℤ) f) (p.coeff m)

/-- Mapping the coefficient monoid preserves positivity even when its monomials collide. -/
theorem mapRingHom_mapDomainRingHom_mem_positive {Q : Type*} [Monoid Q] (f : P →* Q)
    {p : LaurentRing (MonoidAlgebra ℤ P) K} (hp : p ∈ positive P K) :
    AddMonoidAlgebra.mapRingHom (K →₀ ℤ) (MonoidAlgebra.mapDomainRingHom ℤ f) p ∈
      positive Q K := by
  rw [positive_def, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨q, rfl⟩ := hp
  exact ⟨AddMonoidAlgebra.mapRingHom (K →₀ ℤ) (MonoidAlgebra.mapDomainRingHom ℕ f) q,
    natCoeffMap_mapRingHom_mapDomainRingHom f q⟩

/-- An injective coefficient-monoid map also reflects positivity. -/
theorem mapRingHom_mapDomainRingHom_mem_positive_iff {Q : Type*} [Monoid Q] (f : P →* Q)
    (hf : Function.Injective f) (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    AddMonoidAlgebra.mapRingHom (K →₀ ℤ) (MonoidAlgebra.mapDomainRingHom ℤ f) p ∈
        positive Q K ↔ p ∈ positive P K := by
  refine ⟨?_, mapRingHom_mapDomainRingHom_mem_positive f⟩
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

end Monoid

section CommMonoid

variable {P K : Type*} [CommMonoid P]

/-- Inclusion of natural coefficients commutes with variable renaming. -/
theorem natCoeffMap_rename {K' : Type*} (f : K → K')
    (p : LaurentRing (MonoidAlgebra ℕ P) K) :
    natCoeffMap P K' (rename f p) = rename f (natCoeffMap P K p) := by
  simpa only [natCoeffMap_def] using
    mapRingHom_rename (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) f p

/-- Renaming Laurent variables preserves positivity, including maps that identify variables. -/
theorem rename_mem_positive {K' : Type*} (f : K → K')
    {p : LaurentRing (MonoidAlgebra ℤ P) K} (hp : p ∈ positive P K) :
    rename f p ∈ positive P K' := by
  rw [positive_def, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨q, rfl⟩ := hp
  exact ⟨rename f q, natCoeffMap_rename f q⟩

/-- An injective variable map also reflects positivity. -/
theorem rename_mem_positive_iff {K' : Type*} {f : K → K'} (hf : Function.Injective f)
    (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    rename f p ∈ positive P K' ↔ p ∈ positive P K := by
  refine ⟨?_, rename_mem_positive f⟩
  intro h
  rw [mem_positive_iff] at h ⊢
  intro m a
  simpa only [coeff_rename_mapDomain hf] using h (Finsupp.mapDomain f m) a

/-- An equivalence of variable indices preserves and reflects coefficient positivity. -/
@[simp]
theorem rename_equiv_mem_positive_iff {K' : Type*} (e : K ≃ K')
    (p : LaurentRing (MonoidAlgebra ℤ P) K) :
    rename e p ∈ positive P K' ↔ p ∈ positive P K :=
  rename_mem_positive_iff e.injective p


end CommMonoid

end TauCeti.LaurentRing
