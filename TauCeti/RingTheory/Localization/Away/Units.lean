/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.BigOperators.Associated
public import TauCeti.RingTheory.Localization.Defs
import TauCeti.RingTheory.Localization.Away.Basic

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
* `TauCeti.Localization.awayProdPrimesUnitsMulEquiv S s hp hs`: the unit group isomorphism
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
    (awayUnit S x : S) = algebraMap R S x := by
  simp [awayUnit]

@[simp]
theorem val_inv_awayUnit (x : R) [IsLocalization.Away x S] :
    (((awayUnit S x)⁻¹ : Sˣ) : S) = IsLocalization.Away.invSelf x := by
  simp [awayUnit]

/-- Any divisor `y` of `x` maps to a unit in a localization `S` away from `x`. -/
noncomputable def awayUnitOfDvd {x y : R} (h : y ∣ x) [IsLocalization.Away x S] : Sˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := S) x h).unit

@[simp]
theorem val_awayUnitOfDvd {x y : R} (h : y ∣ x) [IsLocalization.Away x S] :
    (awayUnitOfDvd S h : S) = algebraMap R S y :=
  (IsLocalization.Away.isUnit_of_dvd (S := S) x h).unit_spec

end Semiring

end TauCeti.Localization

private theorem coe_prod_awayUnitOfDvd_zpow_natCast {ι R : Type*} (S : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S] (s : Finset ι) (p : ι → R) (k : ι → ℕ)
    [IsLocalization.Away (∏ i ∈ s, p i) S] :
    ((∏ i : s,
        TauCeti.Localization.awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (k i.val : ℤ) :
        Sˣ) : S) =
      algebraMap R S (∏ i ∈ s, p i ^ k i) := by
  simp only [Units.coe_prod, zpow_natCast, Units.val_pow_eq_pow_val,
    TauCeti.Localization.val_awayUnitOfDvd, map_prod, map_pow]
  exact Finset.prod_coe_sort s fun i ↦ algebraMap R S (p i) ^ k i

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
              TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.property) ^ m i : Sˣ) : S) =
          y := by
  refine ⟨fun hy ↦ ?_, fun ⟨u, m, h⟩ ↦ h ▸
    ((u.isUnit.map (algebraMap R S)).mul (Units.isUnit _))⟩
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hay⟩ := IsLocalization.surj (Submonoid.powers (∏ i ∈ s, p i)) y
  dsimp only at hay
  have hprod_unit :
      ((∏ i : s,
          TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.property) ^ (n : ℤ) : Sˣ) : S) =
        algebraMap R S ((∏ i ∈ s, p i) ^ n) := by
    rw [coe_prod_awayUnitOfDvd_zpow_natCast S s p (fun _ ↦ n), prod_pow]
  have ha_unit : IsUnit (algebraMap R S a) := by
    rw [← hay, ← hprod_unit]
    exact hy.mul (Units.isUnit _)
  obtain ⟨k, u, hu⟩ :=
    (s.isUnit_algebraMap_away_prod_primes_iff (S := S) hp).mp ha_unit |>.imp fun _ h ↦ h.symm
  refine ⟨u, fun i ↦ (k i.val : ℤ) - (n : ℤ), ?_⟩
  let P : Sˣ :=
    ∏ i : s, TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.property) ^ (n : ℤ)
  have hmul :
      algebraMap R S (u : R) *
          ((∏ i : s,
            TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p i.property) ^
              ((k i.val : ℤ) - (n : ℤ)) : Sˣ) : S) *
          (P : S) =
        y * (P : S) := by
    rw [mul_assoc, ← Units.val_mul, ← prod_mul_distrib]
    have hpow :
        ((∏ x : s,
            TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p x.property) ^
                ((k x.val : ℤ) - (n : ℤ)) *
              TauCeti.Localization.awayUnitOfDvd S (dvd_prod_of_mem p x.property) ^ (n : ℤ) :
              Sˣ) : S) =
          algebraMap R S (∏ i ∈ s, p i ^ k i) := by
      simp_rw [← zpow_add, sub_add_cancel]
      exact coe_prod_awayUnitOfDvd_zpow_natCast S s p k
    rw [hpow, ← map_mul, mul_comm (u : R), hu, ← hay, hprod_unit]
  exact P.isUnit.mul_right_cancel hmul

end Finset

namespace TauCeti.Localization

/-- Auxiliary multiplicative homomorphism for `awayProdPrimesUnitsMulEquiv`. -/
private noncomputable def awayUnitsProdPrimesHom {ι R : Type*} (S : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S] (s : Finset ι) (p : ι → R)
    [IsLocalization.Away (∏ i ∈ s, p i) S] :
    Rˣ × (s → Multiplicative ℤ) →* Sˣ where
  toFun um :=
    Units.map (algebraMap R S : R →* S) um.1 *
      ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (um.2 i).toAdd
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib, zpow_add, mul_mul_mul_comm]

@[simp]
private theorem awayUnitsProdPrimesHom_apply {ι R : Type*} (S : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S] (s : Finset ι) (p : ι → R)
    [IsLocalization.Away (∏ i ∈ s, p i) S] (u : Rˣ) (m : s → Multiplicative ℤ) :
    awayUnitsProdPrimesHom S s p (u, m) =
      Units.map (algebraMap R S : R →* S) u *
        ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (m i).toAdd := by
  simp [awayUnitsProdPrimesHom]

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
  let B : Sˣ := ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (b i.val : ℤ)
  have hmul : ((awayUnitsProdPrimesHom S s p (u, m) * B : Sˣ) : S) = (B : S) := by
    rw [hm, one_mul]
  rw [awayUnitsProdPrimesHom_apply, mul_assoc, ← Finset.prod_mul_distrib, Units.val_mul] at hmul
  have hadd (i : s) : (m i).toAdd + (b i.val : ℤ) = (a i.val : ℤ) := by
    simp only [a, b, i.property, ↓reduceDIte, Subtype.eta]
    omega
  have hLHS :
      ((∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (m i).toAdd *
          awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (b i.val : ℤ) : Sˣ) : S) =
        algebraMap R S (∏ i ∈ s, p i ^ a i) := by
    simp_rw [← zpow_add, hadd]
    exact coe_prod_awayUnitOfDvd_zpow_natCast S s p a
  have hR : (u : R) * ∏ i ∈ s, p i ^ a i = ∏ i ∈ s, p i ^ b i := hinj <| by
    rw [map_mul, ← hLHS, ← coe_prod_awayUnitOfDvd_zpow_natCast S s p b]
    simpa only [Units.coe_map, MonoidHom.coe_ofClass] using hmul
  have hassoc : Associated (∏ i ∈ s, p i ^ a i) (∏ i ∈ s, p i ^ b i) :=
    ⟨u, by rw [mul_comm, hR]⟩
  have hm0 : ∀ i : s, (m i).toAdd = 0 := fun i ↦ by
    have hab := s.eq_of_associated_prod_pow_primes hp hs hassoc i.property
    simp only [a, b, i.property, ↓reduceDIte, Subtype.eta] at hab
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
noncomputable def awayProdPrimesUnitsMulEquiv {ι R : Type*} (S : Type*) [CommSemiring R]
    [IsDomain R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] :
    Rˣ × (s → Multiplicative ℤ) ≃* Sˣ :=
  MulEquiv.ofBijective (awayUnitsProdPrimesHom S s p)
    ⟨awayUnitsProdPrimesHom_injective S s hp hs, fun y ↦ by
      obtain ⟨u, m, hy⟩ := (s.isUnit_away_prod_primes_iff (S := S) hp).mp y.isUnit
      exact ⟨(u, fun i ↦ Multiplicative.ofAdd (m i)), Units.ext (by simpa using hy)⟩⟩

@[simp]
theorem awayProdPrimesUnitsMulEquiv_apply {ι R : Type*} (S : Type*) [CommSemiring R] [IsDomain R]
    [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R} (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] (u : Rˣ) (m : s → Multiplicative ℤ) :
    awayProdPrimesUnitsMulEquiv S s hp hs (u, m) =
      Units.map (algebraMap R S : R →* S) u *
        ∏ i : s, awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (m i).toAdd :=
  (rfl)

theorem coe_awayProdPrimesUnitsMulEquiv_apply {ι R : Type*} (S : Type*) [CommSemiring R]
    [IsDomain R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] (u : Rˣ) (m : s → Multiplicative ℤ) :
    ((awayProdPrimesUnitsMulEquiv S s hp hs (u, m) : Sˣ) : S) =
      algebraMap R S (u : R) *
        ((∏ i : s,
          awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property) ^ (m i).toAdd : Sˣ) : S) := by
  simp

@[simp]
theorem awayProdPrimesUnitsMulEquiv_symm_map {ι R : Type*} (S : Type*) [CommSemiring R]
    [IsDomain R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] (u : Rˣ) :
    (awayProdPrimesUnitsMulEquiv S s hp hs).symm (Units.map (algebraMap R S : R →* S) u) =
      (u, 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

@[simp]
theorem awayProdPrimesUnitsMulEquiv_symm_awayUnitOfDvd {ι R : Type*} [DecidableEq ι] (S : Type*)
    [CommSemiring R] [IsDomain R] [CommSemiring S] [Algebra R S] (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    [IsLocalization.Away (∏ i ∈ s, p i) S] (i : s) :
    (awayProdPrimesUnitsMulEquiv S s hp hs).symm
        (awayUnitOfDvd S (Finset.dvd_prod_of_mem p i.property)) =
      (1, Pi.mulSingle i (Multiplicative.ofAdd 1)) := by
  rw [MulEquiv.symm_apply_eq, awayProdPrimesUnitsMulEquiv_apply, map_one, one_mul,
    Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end TauCeti.Localization

namespace Prime

variable {R S : Type*} [CommSemiring R] [IsDomain R] [CommSemiring S] [Algebra R S]
  {p x : R} [IsLocalization.Away p S]

/-- In a domain, the image of `x` in a localization away from a prime `p` is a unit if and only if
`x` is associated to `p ^ n` for some `n : ℕ`. -/
theorem isUnit_algebraMap_away_iff (hp : Prime p) :
    IsUnit (algebraMap R S x) ↔ ∃ n : ℕ, Associated x (p ^ n) := by
  have : IsLocalization.Away (∏ _ ∈ ({()} : Finset Unit), p) S := by
    rwa [Finset.prod_singleton]
  rw [({()} : Finset Unit).isUnit_algebraMap_away_prod_primes_iff (S := S)
    (p := fun _ ↦ p) (fun _ _ ↦ hp)]
  exact ⟨fun ⟨m, hm⟩ ↦ ⟨m (), by simpa using hm⟩, fun ⟨n, hn⟩ ↦ ⟨fun _ ↦ n, by simpa using hn⟩⟩

/-- Inverting a prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_away_of_not_dvd (hp : Prime p)
    (hx : IsUnit (algebraMap R S x)) (hpx : ¬p ∣ x) : IsUnit x := by
  obtain ⟨i, hi⟩ := (hp.isUnit_algebraMap_away_iff (S := S)).mp hx
  by_cases hi0 : i = 0
  · exact associated_one_iff_isUnit.mp (by simpa [hi0] using hi)
  · exact (hpx ((dvd_pow_self p hi0).trans hi.dvd')).elim

/-- Every element of a localization `S` of a domain `R` away from a prime `p` is a unit if and only
if it has the form `u * p ^ m` with `u : Rˣ` and `m : ℤ`. -/
theorem isUnit_away_iff (hp : Prime p) {y : S} :
    IsUnit y ↔
      ∃ (u : Rˣ) (m : ℤ),
        algebraMap R S (u : R) * ((TauCeti.Localization.awayUnit S p ^ m : Sˣ) : S) = y := by
  have : IsLocalization.Away (∏ _ ∈ ({()} : Finset Unit), p) S := by
    rwa [Finset.prod_singleton]
  have hunit {q : R} [IsLocalization.Away q S] (hq : p ∣ q) :
      TauCeti.Localization.awayUnitOfDvd S hq = TauCeti.Localization.awayUnit S p :=
    Units.ext (by simp)
  rw [({()} : Finset Unit).isUnit_away_prod_primes_iff (S := S) (p := fun _ ↦ p) (fun _ _ ↦ hp)]
  refine ⟨fun ⟨u, m, hy⟩ ↦ ⟨u, m default, ?_⟩, fun ⟨u, m, hy⟩ ↦ ⟨u, fun _ ↦ m, ?_⟩⟩
  · simpa [Fintype.prod_unique, hunit] using hy
  · simpa [Fintype.prod_unique, hunit] using hy

/-- In a domain `R`, the units of a localization `S` away from a prime `p` are canonically
isomorphic to `Rˣ × Multiplicative ℤ`, sending `(u, m)` to `u * p ^ m`. -/
noncomputable def awayUnitsMulEquiv (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] : Rˣ × Multiplicative ℤ ≃* Sˣ :=
  letI : IsLocalization.Away (∏ _ ∈ ({()} : Finset Unit), p) S := by
    rwa [Finset.prod_singleton]
  ((MulEquiv.refl Rˣ).prodCongr
    (MulEquiv.piUnique fun _ : ({()} : Finset Unit) ↦ Multiplicative ℤ).symm).trans
    (TauCeti.Localization.awayProdPrimesUnitsMulEquiv S ({()} : Finset Unit)
      (p := fun _ ↦ p) (fun _ _ ↦ hp) (by simp))

@[simp]
theorem awayUnitsMulEquiv_apply (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] (u : Rˣ) (m : Multiplicative ℤ) :
    hp.awayUnitsMulEquiv S (u, m) =
      Units.map (algebraMap R S : R →* S) u *
        TauCeti.Localization.awayUnit S p ^ m.toAdd := by
  have hunit {q : R} [IsLocalization.Away q S] (hq : p ∣ q) :
      TauCeti.Localization.awayUnitOfDvd S hq = TauCeti.Localization.awayUnit S p :=
    Units.ext (by simp)
  simp [awayUnitsMulEquiv, MulEquiv.prodCongr, hunit]

theorem coe_awayUnitsMulEquiv_apply (hp : Prime p) (S : Type*) [CommSemiring S] [Algebra R S]
    [IsLocalization.Away p S] (u : Rˣ) (m : Multiplicative ℤ) :
    ((hp.awayUnitsMulEquiv S (u, m) : Sˣ) : S) =
      algebraMap R S (u : R) * ((TauCeti.Localization.awayUnit S p ^ m.toAdd : Sˣ) : S) := by
  simp

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
