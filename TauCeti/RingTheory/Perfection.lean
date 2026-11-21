/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfection

/-!
# Coordinates of the perfection of a monoid

For a commutative monoid `M`, Mathlib's `Perfection M p` is the monoid of compatible systems
`(xₙ)ₙ` with `xₙ₊₁ ^ p = xₙ`. If every element of `M` has a `p`-th root, every element of `M`
starts such a system, and more generally every coordinate map `Perfection M p → M` is surjective.
Mathlib proves this for rings of characteristic `p` with surjective Frobenius
(`Perfection.coeff_surjective`); the statement here needs no ring structure, and applies for
instance to the multiplicative monoid of an algebraically closed field of any characteristic.
Each coordinate map also detects units: a compatible system is invertible as soon as one of its
terms is, since the inverses of its terms are again compatible.

## Main definitions

* `PreTilt.equivPerfection`: the ring isomorphism `PreTilt O p ≃+* Perfection (ModP O p) p`.

## Main results

* `Perfection.coeffMonoidHom_surjective`: if `x ↦ x ^ p` is surjective on `M`, so is every
  coordinate map `Perfection.coeffMonoidHom M p n`.
* `Perfection.isLocalHom_coeffMonoidHom`, `Perfection.isLocalHom_coeff`,
  `PreTilt.isLocalHom_coeff`: an element of a perfection, or of a tilt, is a unit as soon as one
  of its coordinates is.
* `Perfection.coeff_lift_apply`: the coordinates of `Perfection.lift p k R φ x` are the values of
  `φ` at the `p ^ n`-th roots of `x`.
* `Perfection.coeff_eq_zero_iff`: in the perfection of a reduced ring of characteristic `p`, an
  element vanishes as soon as one of its coordinates does.
* `PreTilt.ext`, `PreTilt.coeff_equivPerfection`, `PreTilt.coeff_equivPerfection_symm`: coordinate
  extensionality and coordinate formulas for `PreTilt.equivPerfection`.
* `PreTilt.coeff_eq_zero_iff`: in `PreTilt O p`, each coordinate detects zero when `O ⧸ p` is
  reduced.
* `TauCeti.dvd_of_compatible_roots`: in a compatible root sequence, later roots divide earlier ones.
-/

public section

namespace Perfection

variable {M : Type*} [CommMonoid M] {p : ℕ}

/-- **If every element of `M` has a `p`-th root, every coordinate of `Perfection M p` is
surjective.** -/
theorem coeffMonoidHom_surjective (h : Function.Surjective fun x : M ↦ x ^ p) (n : ℕ) :
    Function.Surjective (coeffMonoidHom M p n) := by
  intro x
  -- iterating a choice of `p`-th roots starting at `x` gives a compatible system `f` with zeroth
  -- term `x`, and raising `f` to the `p ^ n`-th power moves `x` to the `n`-th term
  choose r hr using h
  let f : Perfection M p := ⟨fun k ↦ r^[k] x, fun k ↦ by
    simp only [Function.iterate_succ_apply', hr]⟩
  refine ⟨f ^ p ^ n, ?_⟩
  have hf := coeffMonoidHom_pow_p_pow f 0 n
  rw [zero_add] at hf
  exact hf.trans (coeffMonoidHom_mk _ _ 0)

/-- **An element of the perfection is a unit as soon as one of its coordinates is.** Every
coordinate of `x` is a `p`-power root of its zeroth coordinate, hence a unit, and the inverses of
the coordinates form a compatible system, which is the inverse of `x`. -/
instance isLocalHom_coeffMonoidHom (n : ℕ) : IsLocalHom (coeffMonoidHom M p n) := by
  refine ⟨fun x hx ↦ ?_⟩
  have h0 : IsUnit (coeffMonoidHom M p 0 x) := by
    rw [← coeffMonoidHom_pow_p_pow_self x n]
    exact hx.pow _
  have hu (m : ℕ) : IsUnit (coeffMonoidHom M p m x) := by
    rcases eq_or_ne p 0 with rfl | hp
    · -- for `p = 0` every coordinate is a `0`-th power, hence `1`
      rw [← coeffMonoidHom_pow_p' x m, pow_zero]
      exact isUnit_one
    · rw [← coeffMonoidHom_pow_p_pow_self x m] at h0
      exact (isUnit_pow_iff (pow_ne_zero m hp)).mp h0
  let u (m : ℕ) : Mˣ := (hu m).unit
  have hpow (m : ℕ) : u (m + 1) ^ p = u m := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, u, IsUnit.unit_spec] using coeffMonoidHom_pow_p' x m
  let y : Perfection M p := ⟨fun m ↦ ↑((u m)⁻¹), fun m ↦ by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hpow]⟩
  refine isUnit_iff_exists_inv.mpr ⟨y, extMonoid fun m ↦ ?_⟩
  rw [map_mul, coeffMonoidHom_mk, map_one]
  exact (hu m).mul_val_inv

/-- The `n`-th coordinate of `Perfection.lift p k R φ x` is `φ` applied to the `p ^ n`-th root of
`x` in the perfect ring `k`. -/
theorem coeff_lift_apply [Fact p.Prime] {k R : Type*} [CommSemiring k] [CharP k p]
    [PerfectRing k p] [CommSemiring R] [CharP R p] (φ : k →+* R) (n : ℕ) (x : k) :
    coeff R p n (lift p k R φ x) = φ ((iterateFrobeniusEquiv k p n).symm x) := by
  rw [iterateFrobeniusEquiv_symm, RingAut.coe_pow]
  rfl

section Reduced

variable {R : Type*} [CommSemiring R] [Fact p.Prime] [CharP R p] [IsReduced R]

/-- **In the perfection of a reduced ring, each coordinate detects zero.** For `f` in the
perfection of a reduced ring of characteristic `p`, `coeff n f = 0` if and only if `f = 0`. -/
@[simp]
theorem coeff_eq_zero_iff (n : ℕ) {f : Perfection R p} : coeff R p n f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  have hlater (m : ℕ) : coeff R p (n + m) f = 0 := by
    induction m with
    | zero => exact h
    | succ m ih => exact IsNilpotent.eq_zero ⟨p, by rw [← add_assoc, coeff_pow_p', ih]⟩
  ext k
  rw [map_zero]
  exact not_not.mp fun hk ↦ coeff_ne_zero_of_le hk (Nat.le_add_left k n) (hlater k)

end Reduced

/-- **An element of the perfection of a ring is a unit as soon as one of its coordinates is.** -/
instance isLocalHom_coeff {R : Type*} [CommSemiring R] [Fact p.Prime] [CharP R p] (n : ℕ) :
    IsLocalHom (coeff R p n) :=
  ⟨fun x hx ↦ isUnit_of_map_unit (coeffMonoidHom R p n) x hx⟩

end Perfection

namespace PreTilt

variable {O : Type*} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]

/-- Two elements of `PreTilt O p` are equal if all of their `ModP O p` coordinates agree. -/
@[ext]
theorem ext {f g : PreTilt O p} (h : ∀ n, coeff n f = coeff n g) : f = g :=
  Perfection.ext h

/-- The ring isomorphism `PreTilt O p ≃+* Perfection (ModP O p) p`. -/
def equivPerfection : PreTilt O p ≃+* Perfection (ModP O p) p :=
  RingEquiv.refl (Perfection (ModP O p) p)

/-- `PreTilt.equivPerfection` preserves coordinates in `ModP O p`. -/
@[simp]
theorem coeff_equivPerfection (x : PreTilt O p) (n : ℕ) :
    Perfection.coeff (ModP O p) p n (equivPerfection x) = coeff n x := by
  rw [equivPerfection, coeff_def]
  rfl

/-- `PreTilt.equivPerfection.symm` preserves coordinates in `ModP O p`. -/
@[simp]
theorem coeff_equivPerfection_symm (x : Perfection (ModP O p) p) (n : ℕ) :
    coeff n (equivPerfection.symm x) = Perfection.coeff (ModP O p) p n x := by
  rw [equivPerfection, coeff_def]
  rfl

/-- **If `O ⧸ p` is reduced, each coordinate of the tilt detects zero.** For `f` in
`PreTilt O p`, `coeff n f = 0` if and only if `f = 0`. -/
@[simp]
theorem coeff_eq_zero_iff [IsReduced (ModP O p)] (n : ℕ) {f : PreTilt O p} :
    coeff n f = 0 ↔ f = 0 :=
  -- `PreTilt O p` is by definition `Perfection (ModP O p) p`, with `coeff` its coordinate maps
  Perfection.coeff_eq_zero_iff (R := ModP O p) n

/-- **An element of the tilt is a unit as soon as one of its coordinates in `O ⧸ p` is.** -/
instance isLocalHom_coeff (n : ℕ) : IsLocalHom (coeff (O := O) (p := p) n) :=
  ⟨fun x hx ↦ (isUnit_map_iff equivPerfection x).mp <|
    isUnit_of_map_unit (Perfection.coeff (ModP O p) p n) _ (by rwa [coeff_equivPerfection])⟩

end PreTilt

namespace TauCeti

section CommMonoid

variable {R : Type*} [CommMonoid R] {p : ℕ} {r : ℕ → R}

/-- In a compatible root sequence, every later root divides every earlier root. -/
theorem dvd_of_compatible_roots (hr : ∀ n, r (n + 1) ^ p = r n)
    {m n : ℕ} (hmn : m ≤ n) : r n ∣ r m := by
  by_cases hp : p = 0
  · have hone (n : ℕ) : r n = 1 := by
      simpa only [hp, pow_zero] using (hr n).symm
    simp only [hone, dvd_refl]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hpow : r (m + k) ^ p ^ k = r m := by
    simpa only [Perfection.coeffMonoidHom_mk] using
      Perfection.coeffMonoidHom_pow_p_pow' (⟨r, hr⟩ : Perfection R p) m k
  rw [← hpow]
  exact dvd_pow_self _ (pow_ne_zero k hp)

end CommMonoid

end TauCeti
