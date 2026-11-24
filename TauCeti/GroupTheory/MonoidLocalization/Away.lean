/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.GroupTheory.MonoidLocalization.Divisibility
public import TauCeti.Algebra.BigOperators.Associated
import Mathlib.Algebra.Regular.Pow
import Mathlib.GroupTheory.NoncommPiCoprod
import TauCeti.Algebra.Group.Prod

/-!
# Units of localizations of commutative monoids away from an element

For a commutative monoid localization `F : Submonoid.LocalizationMap.AwayMap x S` away from `x`,
every divisor `y` of `x` maps to a unit `F.unitOfDvd h : Sˣ`, with `1` mapping to `1` and products
splitting as products of units.

When `R` is a cancellative commutative monoid with zero
(`[CommMonoidWithZero R] [IsCancelMulZero R]`)
and `x = ∏ i ∈ s, p i` is a finite product of pairwise non-associated primes `p i`, every unit of
`S` factors uniquely as a unit of `R` times integer powers of the primes `p i`, giving
`Rˣ × (s → Multiplicative ℤ) ≃* Sˣ` (`Submonoid.LocalizationMap.AwayMap.prodPrimesUnitsMulEquiv`),
and for a single prime `p` this specializes to `Rˣ × Multiplicative ℤ ≃* Sˣ`
(`Prime.awayMapUnitsMulEquiv`).

## Main definitions

* `Submonoid.LocalizationMap.AwayMap.unitOfDvd`: the unit `Sˣ` attached to a divisor `y ∣ x`.
* `Submonoid.LocalizationMap.AwayMap.prodPrimesUnitsMulEquiv`: the unit group equivalence
  `Rˣ × (s → Multiplicative ℤ) ≃* Sˣ` for a localization away from a product of pairwise
  non-associated primes.
* `Prime.awayMapUnitsMulEquiv`: the unit group equivalence `Rˣ × Multiplicative ℤ ≃* Sˣ` for a
  localization away from a prime `p`.

## Main results

* `Submonoid.LocalizationMap.AwayMap.isUnit_of_dvd` and `isUnit_apply_iff`: units among images
  of elements of `R`.
* `Submonoid.LocalizationMap.AwayMap.unitOfDvd_one` and `unitOfDvd_mul`: unit-level identities for
  `1` and products dividing `x`.
* `Submonoid.LocalizationMap.AwayMap.isUnit_map_prod_primes_iff` and `isUnit_prod_primes_iff`:
  characterizations of units in a localization away from a product of primes.
* `Prime.isUnit_map_awayMap_iff`, `Prime.isUnit_of_isUnit_awayMap_of_not_dvd`, and
  `Prime.isUnit_awayMap_iff`: characterizations of units in a localization away from a prime `p`.
-/

public section

assert_not_exists Field

namespace Submonoid.LocalizationMap.AwayMap

section CommMonoid

variable {R S : Type*} [CommMonoid R] [CommMonoid S]

/-- Any divisor `y` of `x` maps to a unit under an away localization map `F : AwayMap x S`. -/
theorem isUnit_of_dvd {x : R} (F : AwayMap x S) {y : R} (h : y ∣ x) : IsUnit (F y) :=
  isUnit_of_dvd_unit (map_dvd F h) (F.map_units ⟨x, Submonoid.mem_powers x⟩)

/-- An element `y : R` maps to a unit under `F : AwayMap x S` if and only if `y` divides some
power of `x`. -/
theorem isUnit_apply_iff {x : R} (F : AwayMap x S) {y : R} :
    IsUnit (F y) ↔ ∃ n : ℕ, y ∣ x ^ n := by
  rw [F.map_isUnit_iff]
  simp [Submonoid.mem_powers_iff]

/-- Any divisor `y` of `x` maps to a unit in `Sˣ` under an away localization map `F`. -/
noncomputable def unitOfDvd {x : R} (F : AwayMap x S) {y : R} (h : y ∣ x) : Sˣ :=
  (F.isUnit_of_dvd h).unit

@[simp]
theorem val_unitOfDvd {x : R} (F : AwayMap x S) {y : R} (h : y ∣ x) :
    (F.unitOfDvd h : S) = F y :=
  (F.isUnit_of_dvd h).unit_spec

/-- If `x = y * z`, the inverse of `F.unitOfDvd h` in `S` is `F z * F.invSelf x`. -/
theorem val_inv_unitOfDvd_of_eq_mul {x y z : R} (F : AwayMap x S) (h : y ∣ x) (hx : x = y * z) :
    (((F.unitOfDvd h)⁻¹ : Sˣ) : S) = F z * F.invSelf x := by
  apply (F.unitOfDvd h).isUnit.mul_left_cancel
  rw [Units.mul_inv, val_unitOfDvd, ← mul_assoc, ← map_mul, ← hx, AwayMap.invSelf]
  exact ((F.mk'_spec' 1 ⟨x, Submonoid.mem_powers x⟩).trans (map_one F)).symm

@[simp]
theorem val_inv_unitOfDvd_self {x : R} (F : AwayMap x S) (h : x ∣ x) :
    (((F.unitOfDvd h)⁻¹ : Sˣ) : S) = F.invSelf x := by
  simpa using F.val_inv_unitOfDvd_of_eq_mul h (mul_one x).symm

/-- The unit associated to `1 ∣ x` is `1`. -/
@[simp]
theorem unitOfDvd_one {x : R} (F : AwayMap x S) (h : (1 : R) ∣ x) :
    F.unitOfDvd h = 1 :=
  Units.ext (by simp)

/-- The unit associated to a product `a * b ∣ x` is the product of the units associated to `a ∣ x`
and `b ∣ x`. -/
theorem unitOfDvd_mul {x a b : R} (F : AwayMap x S) (ha : a ∣ x) (hb : b ∣ x) (hab : a * b ∣ x) :
    F.unitOfDvd hab = F.unitOfDvd ha * F.unitOfDvd hb :=
  Units.ext (by simp)

/-- Two `unitOfDvd` constructions for the same divisor agree whenever the underlying localization
maps agree on that divisor. -/
theorem unitOfDvd_eq_of_eq {x₁ x₂ y : R} (F₁ : AwayMap x₁ S) (F₂ : AwayMap x₂ S)
    (hF : F₁ y = F₂ y) (h₁ : y ∣ x₁) (h₂ : y ∣ x₂) :
    F₁.unitOfDvd h₁ = F₂.unitOfDvd h₂ :=
  Units.ext (by simp [hF])

private noncomputable def primeUnit {ι : Type*} {x : R} {s : Finset ι} {p : ι → R}
    (F : AwayMap x S) (hx : x = ∏ i ∈ s, p i) (i : s) : Sˣ :=
  F.unitOfDvd ((Finset.dvd_prod_of_mem p i.property).trans hx.symm.dvd)

@[simp]
private theorem val_primeUnit {ι : Type*} {x : R} {s : Finset ι} {p : ι → R}
    (F : AwayMap x S) (hx : x = ∏ i ∈ s, p i) (i : s) :
    ((F.primeUnit hx i : Sˣ) : S) = F (p i.val) := by
  simp [primeUnit]

private theorem coe_prod_unitOfDvd_zpow_natCast_of_eq {ι : Type*} {x : R} (s : Finset ι)
    (p : ι → R) (hx : x = ∏ i ∈ s, p i) (F : AwayMap x S) (k : ι → ℕ) :
    ((∏ i : s, F.primeUnit hx i ^ (k i.val : ℤ) : Sˣ) : S) =
      F (∏ i ∈ s, p i ^ k i) := by
  simp only [Units.coe_prod, zpow_natCast, Units.val_pow_eq_pow_val, val_primeUnit, map_prod,
    map_pow]
  exact Finset.prod_coe_sort s fun i ↦ F (p i) ^ k i

/-- A product of natural powers of `F.unitOfDvd` over `s` evaluates in `S` to
`F (∏ i ∈ s, p i ^ k i)`. -/
theorem coe_prod_unitOfDvd_zpow_natCast {ι : Type*} (s : Finset ι) (p : ι → R)
    (F : AwayMap (∏ i ∈ s, p i) S) (k : ι → ℕ) :
    ((∏ i : s, F.unitOfDvd (Finset.dvd_prod_of_mem p i.property) ^ (k i.val : ℤ) : Sˣ) : S) =
      F (∏ i ∈ s, p i ^ k i) :=
  F.coe_prod_unitOfDvd_zpow_natCast_of_eq s p rfl k

private theorem mul_prod_primeUnit_zpow_eq_iff_of_eq {ι : Type*} {x : R} (s : Finset ι)
    {p : ι → R} (hx : x = ∏ i ∈ s, p i) (F : AwayMap x S) (u : Rˣ) (y : S)
    (m : s → ℤ) (a b : ι → ℕ) (hmk : ∀ i : s, m i + (b i.val : ℤ) = (a i.val : ℤ)) :
    F (u : R) * ((∏ i : s, F.primeUnit hx i ^ m i : Sˣ) : S) = y ↔
      F ((u : R) * ∏ i ∈ s, p i ^ a i) = y * F (∏ i ∈ s, p i ^ b i) := by
  let B : Sˣ := ∏ i : s, F.primeUnit hx i ^ (b i.val : ℤ)
  have hB : (B : S) = F (∏ i ∈ s, p i ^ b i) :=
    F.coe_prod_unitOfDvd_zpow_natCast_of_eq s p hx b
  have hAB : ((∏ i : s, F.primeUnit hx i ^ m i : Sˣ) : S) * (B : S) =
      F (∏ i ∈ s, p i ^ a i) := by
    rw [← Units.val_mul, ← Finset.prod_mul_distrib]
    simp_rw [← zpow_add, hmk]
    exact F.coe_prod_unitOfDvd_zpow_natCast_of_eq s p hx a
  rw [← B.isUnit.mul_left_inj, mul_assoc, hAB, ← map_mul, hB]

private theorem prodPrimesUnitsHom_of_eq_comm {ι : Type*} {x : R} (s : Finset ι) (p : ι → R)
    (hx : x = ∏ i ∈ s, p i) (F : AwayMap x S) :
    Pairwise (fun i j : s ↦ ∀ a b,
      Commute (zpowersHom Sˣ (F.primeUnit hx i) a) (zpowersHom Sˣ (F.primeUnit hx j) b)) :=
  fun _ _ _ _ _ ↦ Commute.all _ _

/-- Auxiliary multiplicative homomorphism for `prodPrimesUnitsMulEquiv`. -/
private noncomputable def prodPrimesUnitsHom_of_eq {ι : Type*} {x : R} (s : Finset ι) (p : ι → R)
    (hx : x = ∏ i ∈ s, p i) (F : AwayMap x S) :
    Rˣ × (s → Multiplicative ℤ) →* Sˣ :=
  (Units.map F.toMonoidHom).coprod
    (MonoidHom.noncommPiCoprod (fun i : s ↦ zpowersHom Sˣ (F.primeUnit hx i))
      (F.prodPrimesUnitsHom_of_eq_comm s p hx))

@[simp]
private theorem prodPrimesUnitsHom_of_eq_apply {ι : Type*} {x : R} (s : Finset ι) (p : ι → R)
    (hx : x = ∏ i ∈ s, p i) (F : AwayMap x S) (u : Rˣ) (m : s → Multiplicative ℤ) :
    F.prodPrimesUnitsHom_of_eq s p hx (u, m) =
      Units.map F.toMonoidHom u * ∏ i : s, F.primeUnit hx i ^ (m i).toAdd := by
  dsimp only [prodPrimesUnitsHom_of_eq]
  rw [MonoidHom.coprod_apply]
  dsimp only
  rw [MonoidHom.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  simp only [zpowersHom_apply]

private theorem prodPrimesUnitsHom_of_eq_mulSingle {ι : Type*} {x : R} (s : Finset ι)
    [DecidableEq ↥s] (p : ι → R) (hx : x = ∏ i ∈ s, p i) (F : AwayMap x S) (i : s) :
    F.prodPrimesUnitsHom_of_eq s p hx (1, Pi.mulSingle i (Multiplicative.ofAdd (1 : ℤ))) =
      F.primeUnit hx i := by
  dsimp only [prodPrimesUnitsHom_of_eq]
  rw [MonoidHom.coprod_apply]
  dsimp only
  rw [map_one, one_mul, MonoidHom.noncommPiCoprod_mulSingle]
  simp

end CommMonoid

section CancelMulZero

variable {ι R S : Type*} [CommMonoidWithZero R] [IsCancelMulZero R] [CommMonoid S]

private theorem isUnit_map_prod_primes_iff_of_eq {x : R} (s : Finset ι) {p : ι → R}
    (hx : x = ∏ i ∈ s, p i) (hp : ∀ i ∈ s, Prime (p i)) (F : AwayMap x S) {y : R} :
    IsUnit (F y) ↔ ∃ m : ι → ℕ, Associated y (∏ i ∈ s, p i ^ m i) := by
  rw [F.isUnit_apply_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [hx] at hk
    obtain ⟨m, -, hym⟩ := (s.dvd_prod_primes_pow_iff hp k).mp hk
    exact ⟨m, hym⟩
  · rintro ⟨m, hym⟩
    classical
    refine ⟨s.sup m, ?_⟩
    rw [hx, ← Finset.prod_pow]
    exact hym.dvd.trans
      (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (Finset.le_sup hi))

/-- In a cancellative commutative monoid with zero `R`, the image of `x` under an away
localization map `F` at `∏ i ∈ s, p i` (with each `p i` prime) is a unit if and only if `x` is
associated to `∏ i ∈ s, p i ^ m i` for some `m : ι → ℕ`. -/
theorem isUnit_map_prod_primes_iff (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (F : AwayMap (∏ i ∈ s, p i) S) {x : R} :
    IsUnit (F x) ↔ ∃ m : ι → ℕ, Associated x (∏ i ∈ s, p i ^ m i) :=
  F.isUnit_map_prod_primes_iff_of_eq s rfl hp

private theorem isUnit_prod_primes_iff_of_eq {x : R} (s : Finset ι) {p : ι → R}
    (hx : x = ∏ i ∈ s, p i) (hp : ∀ i ∈ s, Prime (p i)) (F : AwayMap x S) {y : S} :
    IsUnit y ↔
      ∃ (u : Rˣ) (m : s → ℤ),
        F (u : R) * ((∏ i : s, F.primeUnit hx i ^ m i : Sˣ) : S) = y := by
  refine ⟨fun hy ↦ ?_, fun ⟨u, m, h⟩ ↦ h ▸ ((u.isUnit.map F).mul (Units.isUnit _))⟩
  obtain ⟨⟨a, m⟩, hay⟩ := F.surj y
  obtain ⟨n, hn⟩ := m.property
  rw [← hn, map_pow] at hay
  let P : Sˣ := ∏ i : s, F.primeUnit hx i ^ (n : ℤ)
  have hP : (P : S) = F x ^ n := by
    rw [F.coe_prod_unitOfDvd_zpow_natCast_of_eq s p hx (fun _ ↦ n), Finset.prod_pow, ← hx,
      map_pow]
  have ha_unit : IsUnit (F a) := by
    rw [← hay, ← hP]
    exact hy.mul P.isUnit
  obtain ⟨k, u, hu⟩ :=
    (F.isUnit_map_prod_primes_iff_of_eq s hx hp).mp ha_unit |>.imp fun _ h ↦ h.symm
  refine ⟨u, fun i ↦ (k i.val : ℤ) - (n : ℤ),
    (F.mul_prod_primeUnit_zpow_eq_iff_of_eq s hx u y _ k (fun _ ↦ n)
      (fun _ ↦ sub_add_cancel _ _)).mpr ?_⟩
  rw [mul_comm (u : R), hu, ← hay, Finset.prod_pow, ← hx, map_pow]

/-- Every element of a localization `S` of a cancellative commutative monoid with zero `R` away
from a product `∏ i ∈ s, p i` of primes is a unit if and only if it is `u * ∏ i : s, p i ^ m i`
for some `u : Rˣ` and `m : s → ℤ`. -/
theorem isUnit_prod_primes_iff (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (F : AwayMap (∏ i ∈ s, p i) S) {y : S} :
    IsUnit y ↔
      ∃ (u : Rˣ) (m : s → ℤ),
        F (u : R) *
            ((∏ i : s, F.unitOfDvd (Finset.dvd_prod_of_mem p i.property) ^ m i : Sˣ) : S) =
          y :=
  F.isUnit_prod_primes_iff_of_eq s rfl hp

private theorem prodPrimesUnitsHom_of_eq_injective {x : R} (s : Finset ι) {p : ι → R}
    (hx : x = ∏ i ∈ s, p i) (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    (F : AwayMap x S) :
    Function.Injective (F.prodPrimesUnitsHom_of_eq s p hx) := by
  rw [← (F.prodPrimesUnitsHom_of_eq s p hx).ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨u, m⟩ hm
  rw [MonoidHom.mem_ker] at hm
  have hreg : IsRegular x := by
    rw [hx]
    exact IsRegular.prod fun i hi ↦ IsRegular.of_ne_zero (hp i hi).ne_zero
  have hinj : Function.Injective F :=
    F.injective_iff.mpr fun _ ⟨k, hk⟩ ↦ hk ▸ hreg.pow k
  classical
  -- Separate positive and negative exponents to clear denominators into `R`, then apply
  -- exponent uniqueness for pairwise non-associated primes.
  let a : ι → ℕ := fun i ↦ if hi : i ∈ s then (m ⟨i, hi⟩).toAdd.toNat else 0
  let b : ι → ℕ := fun i ↦ if hi : i ∈ s then (-(m ⟨i, hi⟩).toAdd).toNat else 0
  have hadd (i : s) : (m i).toAdd + (b i.val : ℤ) = (a i.val : ℤ) := by
    simp only [a, b, i.property, ↓reduceDIte, Subtype.eta]
    omega
  have hm' : F (u : R) * ((∏ i : s, F.primeUnit hx i ^ (m i).toAdd : Sˣ) : S) = 1 := by
    simpa [prodPrimesUnitsHom_of_eq_apply] using congrArg Units.val hm
  have hR : (u : R) * ∏ i ∈ s, p i ^ a i = ∏ i ∈ s, p i ^ b i := hinj <| by
    simpa using (F.mul_prod_primeUnit_zpow_eq_iff_of_eq s hx u 1 _ a b hadd).mp hm'
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

private theorem prodPrimesUnitsHom_of_eq_bijective {x : R} (s : Finset ι) {p : ι → R}
    (hx : x = ∏ i ∈ s, p i) (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    (F : AwayMap x S) :
    Function.Bijective (F.prodPrimesUnitsHom_of_eq s p hx) :=
  ⟨F.prodPrimesUnitsHom_of_eq_injective s hx hp hs, fun y ↦ by
    obtain ⟨u, m, hy⟩ := (F.isUnit_prod_primes_iff_of_eq s hx hp).mp y.isUnit
    exact ⟨(u, fun i ↦ Multiplicative.ofAdd (m i)), Units.ext (by simpa using hy)⟩⟩

private noncomputable def prodPrimesUnitsMulEquiv_of_eq {x : R} (s : Finset ι) {p : ι → R}
    (hx : x = ∏ i ∈ s, p i) (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    (F : AwayMap x S) :
    Rˣ × (s → Multiplicative ℤ) ≃* Sˣ :=
  MulEquiv.ofBijective (F.prodPrimesUnitsHom_of_eq s p hx)
    (F.prodPrimesUnitsHom_of_eq_bijective s hx hp hs)

@[simp]
private theorem prodPrimesUnitsMulEquiv_of_eq_apply {x : R} (s : Finset ι) {p : ι → R}
    (hx : x = ∏ i ∈ s, p i) (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    (F : AwayMap x S) (u : Rˣ) (m : s → Multiplicative ℤ) :
    F.prodPrimesUnitsMulEquiv_of_eq s hx hp hs (u, m) =
      Units.map F.toMonoidHom u * ∏ i : s, F.primeUnit hx i ^ (m i).toAdd := by
  simp [prodPrimesUnitsMulEquiv_of_eq]

/-- For a finite family of pairwise non-associated primes `p i` (`i ∈ s`) in a cancellative
commutative monoid with zero `R`, the units of an away localization `S` at `∏ i ∈ s, p i` are
canonically isomorphic to `Rˣ × (s → Multiplicative ℤ)`. -/
noncomputable def prodPrimesUnitsMulEquiv (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    (F : AwayMap (∏ i ∈ s, p i) S) :
    Rˣ × (s → Multiplicative ℤ) ≃* Sˣ :=
  F.prodPrimesUnitsMulEquiv_of_eq s rfl hp hs

@[simp]
theorem prodPrimesUnitsMulEquiv_apply (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    (F : AwayMap (∏ i ∈ s, p i) S) (u : Rˣ) (m : s → Multiplicative ℤ) :
    F.prodPrimesUnitsMulEquiv s hp hs (u, m) =
      Units.map F.toMonoidHom u *
        ∏ i : s, F.unitOfDvd (Finset.dvd_prod_of_mem p i.property) ^ (m i).toAdd := by
  simp [prodPrimesUnitsMulEquiv, primeUnit]

@[simp]
theorem prodPrimesUnitsMulEquiv_symm_map (s : Finset ι) {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    (F : AwayMap (∏ i ∈ s, p i) S) (u : Rˣ) :
    (F.prodPrimesUnitsMulEquiv s hp hs).symm (Units.map F.toMonoidHom u) = (u, 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

@[simp]
theorem prodPrimesUnitsMulEquiv_symm_unitOfDvd (s : Finset ι) [DecidableEq ↥s] {p : ι → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j))
    (F : AwayMap (∏ i ∈ s, p i) S) (i : s) :
    (F.prodPrimesUnitsMulEquiv s hp hs).symm
        (F.unitOfDvd (Finset.dvd_prod_of_mem p i.property)) =
      (1, Pi.mulSingle i (Multiplicative.ofAdd (1 : ℤ))) := by
  rw [MulEquiv.symm_apply_eq, eq_comm, prodPrimesUnitsMulEquiv, prodPrimesUnitsMulEquiv_of_eq,
    MulEquiv.ofBijective_apply]
  exact F.prodPrimesUnitsHom_of_eq_mulSingle s p rfl i

end CancelMulZero

end Submonoid.LocalizationMap.AwayMap

namespace Prime

variable {R S : Type*} [CommMonoidWithZero R] [IsCancelMulZero R] [CommMonoid S] {p x : R}

/-- In a cancellative commutative monoid with zero, the image of `x` under an away localization
map `F` at a prime `p` is a unit if and only if `x` is associated to `p ^ n` for some `n : ℕ`. -/
theorem isUnit_map_awayMap_iff (hp : Prime p) (F : Submonoid.LocalizationMap.AwayMap p S) :
    IsUnit (F x) ↔ ∃ n : ℕ, Associated x (p ^ n) := by
  rw [F.isUnit_map_prod_primes_iff_of_eq ({()} : Finset Unit)
    (Finset.prod_singleton (fun _ : Unit ↦ p) ()).symm (fun _ _ ↦ hp)]
  exact ⟨fun ⟨m, hm⟩ ↦ ⟨m (), by simpa using hm⟩, fun ⟨n, hn⟩ ↦ ⟨fun _ ↦ n, by simpa using hn⟩⟩

/-- Inverting a prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_awayMap_of_not_dvd (hp : Prime p)
    (F : Submonoid.LocalizationMap.AwayMap p S) (hx : IsUnit (F x)) (hpx : ¬p ∣ x) : IsUnit x := by
  obtain ⟨i, hi⟩ := (hp.isUnit_map_awayMap_iff F).mp hx
  by_cases hi0 : i = 0
  · exact associated_one_iff_isUnit.mp (by simpa [hi0] using hi)
  · exact (hpx ((dvd_pow_self p hi0).trans hi.dvd')).elim

/-- Every element of a localization `S` of a cancellative commutative monoid with zero `R` away
from a prime `p` is a unit if and only if it has the form `u * p ^ m` with `u : Rˣ` and
`m : ℤ`. -/
theorem isUnit_awayMap_iff (hp : Prime p) (F : Submonoid.LocalizationMap.AwayMap p S) {y : S} :
    IsUnit y ↔
      ∃ (u : Rˣ) (m : ℤ),
        F (u : R) * ((F.unitOfDvd (dvd_rfl : p ∣ p) ^ m : Sˣ) : S) = y := by
  rw [F.isUnit_prod_primes_iff_of_eq ({()} : Finset Unit) (p := fun _ ↦ p)
    (Finset.prod_singleton (fun _ : Unit ↦ p) ()).symm (fun _ _ ↦ hp)]
  exact ⟨fun ⟨u, m, hy⟩ ↦ ⟨u, m default,
      by simpa only [Fintype.prod_unique, Submonoid.LocalizationMap.AwayMap.primeUnit] using hy⟩,
    fun ⟨u, m, hy⟩ ↦ ⟨u, fun _ ↦ m,
      by simpa only [Fintype.prod_unique, Submonoid.LocalizationMap.AwayMap.primeUnit] using hy⟩⟩

/-- In a cancellative commutative monoid with zero `R`, the units of an away localization `S` at a
prime `p` are canonically isomorphic to `Rˣ × Multiplicative ℤ`, sending `(u, m)` to
`u * p ^ m`. -/
noncomputable def awayMapUnitsMulEquiv (hp : Prime p)
    (F : Submonoid.LocalizationMap.AwayMap p S) : Rˣ × Multiplicative ℤ ≃* Sˣ :=
  ((MulEquiv.refl Rˣ).prodCongr
    (MulEquiv.piUnique fun _ : ({()} : Finset Unit) ↦ Multiplicative ℤ).symm).trans
    (F.prodPrimesUnitsMulEquiv_of_eq ({()} : Finset Unit) (p := fun _ ↦ p)
      (Finset.prod_singleton (fun _ : Unit ↦ p) ()).symm (fun _ _ ↦ hp) (by simp))

@[simp]
theorem awayMapUnitsMulEquiv_apply (hp : Prime p) (F : Submonoid.LocalizationMap.AwayMap p S)
    (u : Rˣ) (m : Multiplicative ℤ) :
    hp.awayMapUnitsMulEquiv F (u, m) =
      Units.map F.toMonoidHom u * F.unitOfDvd (dvd_rfl : p ∣ p) ^ m.toAdd := by
  simp [awayMapUnitsMulEquiv, MulEquiv.prodCongr_apply,
    Submonoid.LocalizationMap.AwayMap.primeUnit]

@[simp]
theorem awayMapUnitsMulEquiv_symm_map (hp : Prime p) (F : Submonoid.LocalizationMap.AwayMap p S)
    (u : Rˣ) :
    (hp.awayMapUnitsMulEquiv F).symm (Units.map F.toMonoidHom u) = (u, 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

@[simp]
theorem awayMapUnitsMulEquiv_symm_unitOfDvd (hp : Prime p)
    (F : Submonoid.LocalizationMap.AwayMap p S) :
    (hp.awayMapUnitsMulEquiv F).symm (F.unitOfDvd (dvd_rfl : p ∣ p)) =
      (1, Multiplicative.ofAdd (1 : ℤ)) := by
  rw [MulEquiv.symm_apply_eq]
  simp

end Prime
