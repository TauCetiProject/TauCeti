/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.BigOperators.Associated

/-!
# Units of a localization away from a prime or product of primes

Let `R` be a commutative domain and `S` a localization of `R` away from a prime element `p`. An
element of `R` becomes a unit in `S` if and only if it divides a power of `p`, hence (by
`dvd_prime_pow`) if and only if it is associated to `p ^ n` for some `n : ℕ`. In particular, an
element not divisible by `p` that becomes a unit in `S` was already a unit in `R`, and every unit
of `S` factors uniquely as `u * p ^ m` with `u : Rˣ` and `m : ℤ`, giving a multiplicative
equivalence `Rˣ × Multiplicative ℤ ≃* Sˣ`.

More generally, when `S` is a localization away from a finite product `∏ i ∈ s, p i` of primes in
`R`, every unit of `S` is a unit of `R` times integer powers of the factors `p i`, and when the
primes `p i` are pairwise non-associated this gives `Rˣ × (s → Multiplicative ℤ) ≃* Sˣ`.

## Main definitions

* `TauCeti.Localization.awayUnit S x`: the image of `x` as a unit of an away localization `S` at
  `x`, with inverse `IsLocalization.Away.invSelf x`.
* `TauCeti.Localization.awayUnitOfDvd S h`: the image of a divisor `y` of `x` as a unit of an away
  localization `S` at `x`.
* `Prime.awayUnitsMulEquiv hp S`: the unit group isomorphism `Rˣ × Multiplicative ℤ ≃* Sˣ` for a
  localization `S` of a domain `R` away from a prime `p`.
* `TauCeti.Localization.awayUnitsMulEquivProdPrimes S s hp hs`: the unit group isomorphism
  `Rˣ × (s → Multiplicative ℤ) ≃* Sˣ` for a localization away from a product of pairwise
  non-associated primes.

## Main results

* `Prime.isUnit_of_isUnit_away_of_not_dvd`: an element not divisible by `p` that is a unit away
  from `p` is already a unit.
* `Prime.isUnit_algebraMap_away_iff` and `Prime.isUnit_away_iff`: characterizations of units in a
  localization away from a prime `p`.
* `Finset.isUnit_algebraMap_away_prod_primes_iff` and `Finset.isUnit_away_prod_primes_iff`:
  characterizations of units in a localization away from a product of primes.
-/

public section

namespace TauCeti.Localization

section Semiring

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- In a localization `S` of `R` away from `x`, the image `algebraMap R S x` paired with
`IsLocalization.Away.invSelf x` as a unit of `S`. -/
noncomputable def awayUnit (x : R) [IsLocalization.Away x S] : Sˣ where
  val := algebraMap R S x
  inv := IsLocalization.Away.invSelf x
  val_inv := IsLocalization.Away.mul_invSelf x
  inv_val := by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf x

@[simp]
theorem val_awayUnit (x : R) [IsLocalization.Away x S] :
    (awayUnit S x : S) = algebraMap R S x :=
  (rfl)

@[simp]
theorem val_inv_awayUnit (x : R) [IsLocalization.Away x S] :
    (((awayUnit S x)⁻¹ : Sˣ) : S) = IsLocalization.Away.invSelf x :=
  (rfl)

/-- Any divisor `y` of `x` maps to a unit in a localization `S` away from `x`. -/
noncomputable def awayUnitOfDvd {x y : R} (h : y ∣ x) [IsLocalization.Away x S] : Sˣ where
  val := algebraMap R S y
  inv := algebraMap R S h.choose * IsLocalization.Away.invSelf x
  val_inv := by
    rw [← mul_assoc, ← map_mul, ← h.choose_spec]
    exact IsLocalization.Away.mul_invSelf x
  inv_val := by
    rw [mul_comm, ← mul_assoc, ← map_mul, ← h.choose_spec]
    exact IsLocalization.Away.mul_invSelf x

@[simp]
theorem val_awayUnitOfDvd {x y : R} (h : y ∣ x) [IsLocalization.Away x S] :
    (awayUnitOfDvd S h : S) = algebraMap R S y :=
  (rfl)

/-- Over a domain (including a commutative semiring without subtraction), localizing away from a
nonzero element `x` yields an injective `algebraMap R S`. -/
theorem algebraMap_away_injective [IsDomain R] {x : R} [IsLocalization.Away x S] (hx : x ≠ 0) :
    Function.Injective (algebraMap R S) := fun _ _ hab ↦ by
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers x) S).mp hab
  exact mul_left_cancel₀ (pow_ne_zero k hx) hc

end Semiring

end TauCeti.Localization

namespace Prime

variable {R S : Type*} [CommSemiring R] [IsDomain R] [CommSemiring S] [Algebra R S]
  {p x : R} [IsLocalization.Away p S]

/-- Inverting a prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_away_of_not_dvd (hp : Prime p)
    (hx : IsUnit (algebraMap R S x)) (hpx : ¬p ∣ x) : IsUnit x := by
  obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := S) p).mp hx
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow hp n).mp hn
  by_cases hi0 : i = 0
  · exact associated_one_iff_isUnit.mp (by simpa [hi0] using hi)
  · exact (hpx ((dvd_pow_self p hi0).trans hi.dvd')).elim

/-- In a domain, the image of `x` in a localization away from a prime `p` is a unit if and only if
`x` is associated to `p ^ n` for some `n : ℕ`. -/
theorem isUnit_algebraMap_away_iff (hp : Prime p) :
    IsUnit (algebraMap R S x) ↔ ∃ n : ℕ, Associated x (p ^ n) := by
  rw [IsLocalization.Away.algebraMap_isUnit_iff (S := S) p]
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ⟨n, hn.dvd⟩⟩
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp n).mp hn
  exact ⟨i, hi⟩

/-- Every element of a localization `S` of a domain `R` away from a prime `p` is a unit if and only
if it has the form `u * p ^ m` with `u : Rˣ` and `m : ℤ`. -/
theorem isUnit_away_iff (hp : Prime p) {y : S} :
    IsUnit y ↔
      ∃ (u : Rˣ) (m : ℤ),
        algebraMap R S (u : R) * ((TauCeti.Localization.awayUnit S p ^ m : Sˣ) : S) = y := by
  refine ⟨fun hy ↦ ?_, fun ⟨u, m, h⟩ ↦ h ▸
    ((u.isUnit.map (algebraMap R S)).mul (TauCeti.Localization.awayUnit S p ^ m).isUnit)⟩
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hay⟩ := IsLocalization.surj (Submonoid.powers p) y
  dsimp only at hay
  have ha_unit : IsUnit (algebraMap R S a) := by
    rw [← hay, map_pow]
    exact hy.mul ((TauCeti.Localization.awayUnit S p).isUnit.pow n)
  obtain ⟨i, u, hu⟩ := (hp.isUnit_algebraMap_away_iff (S := S)).mp ha_unit |>.imp fun _ h ↦ h.symm
  refine ⟨u, (i : ℤ) - (n : ℤ), ?_⟩
  have hmul :
      algebraMap R S (u : R) *
          ((TauCeti.Localization.awayUnit S p ^ ((i : ℤ) - (n : ℤ)) : Sˣ) : S) *
          ((TauCeti.Localization.awayUnit S p ^ (n : ℤ) : Sˣ) : S) =
        y * ((TauCeti.Localization.awayUnit S p ^ (n : ℤ) : Sˣ) : S) := by
    rw [mul_assoc, ← Units.val_mul, ← zpow_add, sub_add_cancel, zpow_natCast,
      Units.val_pow_eq_pow_val, TauCeti.Localization.val_awayUnit, ← map_pow, ← map_mul,
      mul_comm (u : R), hu, ← hay]
    simp [zpow_natCast, map_pow]
  exact (TauCeti.Localization.awayUnit S p ^ (n : ℤ)).isUnit.mul_right_cancel hmul

/-- In a domain `R`, the units of a localization `S` away from a prime `p` are canonically
isomorphic to `Rˣ × Multiplicative ℤ`, sending `(u, m)` to `u * p ^ m`. -/
noncomputable def awayUnitsMulEquiv (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] : Rˣ × Multiplicative ℤ ≃* Sˣ := by
  let f : Rˣ × Multiplicative ℤ →* Sˣ :=
    { toFun um :=
        Units.map (algebraMap R S : R →* S) um.1 *
          TauCeti.Localization.awayUnit S p ^ um.2.toAdd
      map_one' := by simp
      map_mul' a b := by simp [zpow_add, mul_mul_mul_comm] }
  refine MulEquiv.ofBijective f ⟨?_, fun y ↦ ?_⟩
  · rw [← f.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨u, m⟩ hm
    rw [MonoidHom.mem_ker] at hm
    have hinj : Function.Injective (algebraMap R S) :=
      TauCeti.Localization.algebraMap_away_injective S hp.ne_zero
    -- Clear any negative power of `p` and inject back into `R`, where `p` cannot divide a unit.
    obtain ⟨n, hn | hn⟩ := m.toAdd.eq_nat_or_neg
    · have hS : algebraMap R S ((u : R) * p ^ n) = algebraMap R S 1 := by
        have hval := congrArg Units.val hm
        simpa [f, hn, zpow_natCast, map_mul, map_pow] using hval
      have hR : (u : R) * p ^ n = 1 := hinj hS
      have hn0 : n = 0 := by
        by_contra hn0
        exact hp.not_isUnit (isUnit_iff_dvd_one.mpr
          ((dvd_pow_self p hn0).trans ⟨u, ((mul_comm _ _).trans hR).symm⟩))
      subst hn0
      have hu1 : u = 1 := Units.ext (by simpa using hR)
      have hm1 : m = 1 := Multiplicative.toAdd.injective (by simpa using hn)
      simp [hu1, hm1]
    · have hm' : Units.map (algebraMap R S : R →* S) u =
          TauCeti.Localization.awayUnit S p ^ (n : ℤ) := by
        have hmul := congrArg (· * TauCeti.Localization.awayUnit S p ^ (n : ℤ)) hm
        simpa [f, hn, mul_assoc, ← zpow_add] using hmul
      have hR : (u : R) = p ^ n := hinj <| by
        have hval := congrArg Units.val hm'
        simpa [zpow_natCast, map_pow] using hval
      have hn0 : n = 0 := by
        by_contra hn0
        exact hp.not_isUnit (isUnit_of_dvd_unit (hR ▸ dvd_pow_self p hn0) u.isUnit)
      subst hn0
      have hu1 : u = 1 := Units.ext (by simpa using hR)
      have hm1 : m = 1 := Multiplicative.toAdd.injective (by simpa using hn)
      simp [hu1, hm1]
  · obtain ⟨u, m, hy⟩ := (hp.isUnit_away_iff (S := S)).mp y.isUnit
    exact ⟨(u, Multiplicative.ofAdd m), Units.ext (by simpa [f] using hy)⟩

@[simp]
theorem awayUnitsMulEquiv_apply (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] (u : Rˣ) (m : Multiplicative ℤ) :
    hp.awayUnitsMulEquiv S (u, m) =
      Units.map (algebraMap R S : R →* S) u *
        TauCeti.Localization.awayUnit S p ^ m.toAdd :=
  (rfl)

theorem coe_awayUnitsMulEquiv_apply (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] (u : Rˣ) (m : Multiplicative ℤ) :
    ((hp.awayUnitsMulEquiv S (u, m) : Sˣ) : S) =
      algebraMap R S (u : R) * ((TauCeti.Localization.awayUnit S p ^ m.toAdd : Sˣ) : S) :=
  (rfl)

@[simp]
theorem awayUnitsMulEquiv_symm_map (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] (u : Rˣ) :
    (hp.awayUnitsMulEquiv S).symm (Units.map (algebraMap R S : R →* S) u) = (u, 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

@[simp]
theorem awayUnitsMulEquiv_symm_awayUnit (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] :
    (hp.awayUnitsMulEquiv S).symm (TauCeti.Localization.awayUnit S p) =
      (1, Multiplicative.ofAdd 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

end Prime

namespace Finset

variable {ι R S : Type*} [CommSemiring R] [IsDomain R] [CommSemiring S] [Algebra R S]

/-- In a domain `R`, the image of `x` in a localization `S` away from `∏ i ∈ s, p i` (with each
`p i` prime) is a unit if and only if `x` is associated to `∏ i ∈ s, p i ^ m i` for some
`m : ι → ℕ`. -/
theorem isUnit_algebraMap_away_prod_primes_iff (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) [IsLocalization.Away (∏ i ∈ s, p i) S] {x : R} :
    IsUnit (algebraMap R S x) ↔ ∃ m : ι → ℕ, Associated x (∏ i ∈ s, p i ^ m i) := by
  rw [IsLocalization.Away.algebraMap_isUnit_iff (S := S) (∏ i ∈ s, p i)]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨m, -, hxm⟩ := (s.dvd_prod_primes_pow_iff hp k).mp hk
    exact ⟨m, hxm⟩
  · rintro ⟨m, hxm⟩
    classical
    refine ⟨s.sup m, ?_⟩
    rw [← prod_pow]
    exact hxm.dvd.trans (prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (le_sup hi))

/-- Every element of a localization `S` of a domain `R` away from a product `∏ i ∈ s, p i` of
primes is a unit if and only if it is `u * ∏ i : s, p i ^ m i` for some `u : Rˣ` and `m : s → ℤ`. -/
theorem isUnit_away_prod_primes_iff (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) [IsLocalization.Away (∏ i ∈ s, p i) S] {y : S} :
    IsUnit y ↔
      ∃ (u : Rˣ) (m : s → ℤ),
        algebraMap R S (u : R) *
            ((∏ i : s,
              TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.2) ^ m i : Sˣ) : S) =
          y := by
  refine ⟨fun hy ↦ ?_, fun ⟨u, m, h⟩ ↦ h ▸
    ((u.isUnit.map (algebraMap R S)).mul (Units.isUnit _))⟩
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hay⟩ := IsLocalization.surj (Submonoid.powers (∏ i ∈ s, p i)) y
  dsimp only at hay
  have hprod_unit :
      ((∏ i : s,
          TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.2) ^ (n : ℤ) : Sˣ) : S) =
        algebraMap R S ((∏ i ∈ s, p i) ^ n) := by
    rw [← Units.coeHom_apply, map_prod, prod_coe_sort_eq_attach, ← prod_pow, map_prod]
    refine (prod_congr rfl fun i _ ↦ ?_).trans (prod_attach s _)
    simp [zpow_natCast, map_pow]
  have ha_unit : IsUnit (algebraMap R S a) := by
    rw [← hay, ← hprod_unit]
    exact hy.mul (Units.isUnit _)
  obtain ⟨k, u, hu⟩ :=
    (s.isUnit_algebraMap_away_prod_primes_iff (S := S) hp).mp ha_unit |>.imp fun _ h ↦ h.symm
  refine ⟨u, fun i ↦ (k i.1 : ℤ) - (n : ℤ), ?_⟩
  let P : Sˣ := ∏ i : s, TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.2) ^ (n : ℤ)
  have hmul :
      algebraMap R S (u : R) *
          ((∏ i : s,
            TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.2) ^
              ((k i.1 : ℤ) - (n : ℤ)) : Sˣ) : S) *
          (P : S) =
        y * (P : S) := by
    rw [mul_assoc, ← Units.val_mul, ← prod_mul_distrib]
    have hpow :
        ((∏ x : s,
            TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p x.2) ^
                ((k x.1 : ℤ) - (n : ℤ)) *
              TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p x.2) ^ (n : ℤ) : Sˣ) : S) =
          algebraMap R S (∏ i ∈ s, p i ^ k i) := by
      rw [← Units.coeHom_apply, map_prod, prod_coe_sort_eq_attach, map_prod]
      refine (prod_congr rfl fun x _ ↦ ?_).trans (prod_attach s _)
      rw [Units.coeHom_apply, ← zpow_add, sub_add_cancel, zpow_natCast, Units.val_pow_eq_pow_val,
        TauCeti.Localization.val_awayUnitOfDvd, map_pow]
    rw [hpow, ← map_mul, mul_comm (u : R), hu, ← hay, hprod_unit]
  exact P.isUnit.mul_right_cancel hmul

end Finset

namespace TauCeti.Localization

/-- Auxiliary multiplicative homomorphism for `awayUnitsMulEquivProdPrimes`. -/
private noncomputable def awayUnitsProdPrimesHom {ι R : Type*} (S : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S] (s : Finset ι) (p : ι → R)
    [IsLocalization.Away (∏ i ∈ s, p i) S] :
    Rˣ × (s → Multiplicative ℤ) →* Sˣ where
  toFun um :=
    Units.map (algebraMap R S : R →* S) um.1 *
      ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.2) ^ (um.2 i).toAdd
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib, zpow_add, mul_mul_mul_comm]

private theorem awayUnitsProdPrimesHom_injective {ι R : Type*} (S : Type*) [CommSemiring R]
    [IsDomain R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] :
    Function.Injective (awayUnitsProdPrimesHom S s p) := by
  rw [← (awayUnitsProdPrimesHom S s p).ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨u, m⟩ hm
  rw [MonoidHom.mem_ker] at hm
  have hprod_ne : ∏ i ∈ s, p i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi ↦ (hp i hi).ne_zero
  have hinj : Function.Injective (algebraMap R S) := algebraMap_away_injective S hprod_ne
  classical
  -- Separate positive and negative exponents to clear denominators into `R`, then apply
  -- exponent uniqueness for pairwise non-associated primes.
  let a : ι → ℕ := fun i ↦ if hi : i ∈ s then (m ⟨i, hi⟩).toAdd.toNat else 0
  let b : ι → ℕ := fun i ↦ if hi : i ∈ s then (-(m ⟨i, hi⟩).toAdd).toNat else 0
  let B : Sˣ := ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.2) ^ (b i.1 : ℤ)
  have hf_apply : awayUnitsProdPrimesHom S s p (u, m) =
      Units.map (algebraMap R S : R →* S) u *
        ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.2) ^ (m i).toAdd := rfl
  have hmul : ((awayUnitsProdPrimesHom S s p (u, m) * B : Sˣ) : S) = (B : S) := by
    rw [hm, one_mul]
  rw [hf_apply, mul_assoc, ← Finset.prod_mul_distrib, Units.val_mul] at hmul
  have hadd (i : s) : (m i).toAdd + (b i.1 : ℤ) = (a i.1 : ℤ) := by
    simp only [a, b, i.2, ↓reduceDIte, Subtype.eta]
    omega
  have hLHS :
      ((∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.2) ^ (m i).toAdd *
          awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.2) ^ (b i.1 : ℤ) : Sˣ) : S) =
        algebraMap R S (∏ i ∈ s, p i ^ a i) := by
    rw [← Units.coeHom_apply, map_prod, Finset.prod_coe_sort_eq_attach, map_prod]
    refine (Finset.prod_congr rfl fun i _ ↦ ?_).trans (Finset.prod_attach s _)
    rw [Units.coeHom_apply, ← zpow_add, hadd i, zpow_natCast, Units.val_pow_eq_pow_val,
      val_awayUnitOfDvd, map_pow]
  have hRHS : (B : S) = algebraMap R S (∏ i ∈ s, p i ^ b i) := by
    rw [← Units.coeHom_apply, map_prod, Finset.prod_coe_sort_eq_attach, map_prod]
    refine (Finset.prod_congr rfl fun i _ ↦ ?_).trans (Finset.prod_attach s _)
    rw [Units.coeHom_apply, zpow_natCast, Units.val_pow_eq_pow_val, val_awayUnitOfDvd, map_pow]
  have hR : (u : R) * ∏ i ∈ s, p i ^ a i = ∏ i ∈ s, p i ^ b i := hinj <| by
    rw [map_mul, ← hLHS, ← hRHS]
    simpa using hmul
  have hassoc : Associated (∏ i ∈ s, p i ^ a i) (∏ i ∈ s, p i ^ b i) :=
    ⟨u, by rw [mul_comm, hR]⟩
  have hm0 : ∀ i : s, (m i).toAdd = 0 := fun i ↦ by
    have hab := s.eq_of_associated_prod_pow_primes hp hs hassoc i.2
    simp only [a, b, i.2, ↓reduceDIte, Subtype.eta] at hab
    omega
  have hm1 : m = 1 := funext fun i ↦ Multiplicative.toAdd.injective (hm0 i)
  have hu1 : u = 1 := Units.ext <| by
    rw [Finset.prod_eq_one fun i hi ↦ by simp [a, hi, hm0 ⟨i, hi⟩],
      Finset.prod_eq_one fun i hi ↦ by simp [b, hi, hm0 ⟨i, hi⟩], mul_one] at hR
    exact hR
  simp [hu1, hm1]

/-- For a finite family of pairwise non-associated primes `p i` (`i ∈ s`) in a domain `R`, the
units of a localization `S` away from `∏ i ∈ s, p i` are canonically isomorphic to
`Rˣ × (s → Multiplicative ℤ)`. -/
noncomputable def awayUnitsMulEquivProdPrimes {ι R : Type*} (S : Type*) [CommSemiring R]
    [IsDomain R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] :
    Rˣ × (s → Multiplicative ℤ) ≃* Sˣ :=
  MulEquiv.ofBijective (awayUnitsProdPrimesHom S s p)
    ⟨awayUnitsProdPrimesHom_injective S s hp hs, fun y ↦ by
      obtain ⟨u, m, hy⟩ := (s.isUnit_away_prod_primes_iff (S := S) hp).mp y.isUnit
      exact ⟨(u, fun i ↦ Multiplicative.ofAdd (m i)),
        Units.ext (by simpa [awayUnitsProdPrimesHom] using hy)⟩⟩

@[simp]
theorem awayUnitsMulEquivProdPrimes_apply {ι R : Type*} (S : Type*) [CommSemiring R] [IsDomain R]
    [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R} (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] (u : Rˣ) (m : s → Multiplicative ℤ) :
    awayUnitsMulEquivProdPrimes S s hp hs (u, m) =
      Units.map (algebraMap R S : R →* S) u *
        ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.2) ^ (m i).toAdd :=
  (rfl)

end TauCeti.Localization
