/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.ZMod.Basic
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Multisections of power series

For `m : ℕ` and a residue class `r : ZMod m`, the *multisection* of a power series
`f = ∑ aₙ Xⁿ` is its part `f_[r] = ∑_{n ≡ r (mod m)} aₙ Xⁿ` in the degrees congruent to `r`
modulo `m` (`PowerSeries.multisection m r`); for `m = 2` these are the even and odd parts of `f`.
The multisections of `f` add up to `f`, and multisection is a projection, compatible with the
grading by `ZMod m`: the product of a series supported in the degrees `≡ r` and one supported in
the degrees `≡ s` is supported in the degrees `≡ r + s`.

Multisection commutes with rescaling the variable, `f_[r](a X) = (f(a X))_[r]`, and with
substitution of a series `T` supported in the degrees `≡ 1`: `(F(T))_[r] = F_[r](T)`, because
`T ^ k` is then supported in the degrees `≡ k`. Over a field
containing a primitive `m`-th root of unity `ζ`, the multisection is the average of the rotations
of `f` by the `m`-th roots of unity `ξ = ζ ^ a` (the roots of unity filter):

  `m · f_[r] = ∑_{a < m} ξ ^ (-r) f(ξ X)`, `ξ = ζ ^ a`,

by the orthogonality of the characters of `ZMod m` (`IsPrimitiveRoot.sum_zpow_pow_eq`).

For `r = 1` this expresses the part of a series `y` in the degrees `≡ 1 (mod m)` as the mean of
the series `ξ⁻¹ y(ξ X)`; for a parameter `y` of a formal group with complex multiplication by the
`m`-th roots of unity, these are the transforms of `y` by the automorphisms `[ξ]`.

## Main definitions

* `PowerSeries.multisection m r`: the part of a power series in the degrees congruent to `r`
  modulo `m`, as a linear map.

## Main results

* `PowerSeries.sum_multisection`: a power series is the sum of its `m` multisections.
* `PowerSeries.multisection_mul_of_eq`, `PowerSeries.multisection_pow_of_eq`: products and powers
  of series supported in single residue classes.
* `PowerSeries.rescale_multisection`: multisection commutes with rescaling.
* `PowerSeries.multisection_subst`: `(F(T))_[r] = F_[r](T)` when `T` is supported in the degrees
  `≡ 1 (mod m)`.
* `PowerSeries.natCast_smul_multisection`: the roots of unity filter
  `m · f_[r] = ∑_{a < m} ξ ^ (-r) f(ξ X)`, `ξ = ζ ^ a`.

## References

* J. Riordan, *Combinatorial Identities*, Wiley (1968) (series multisection).
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/CM/FormalGroup/IntegralParameter.lean` (declarations `New.congruencePart`,
  `New.congruencePart_rescale`, `New.congruencePart_eq_sum`, `New.congruencePart_subst`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. The results here correspond to these declarations,
  which are stated over `ℂ_p`; the proofs follow the outline of that formal proof.
-/

public section

namespace PowerSeries

section Semiring

variable {R : Type*} [Semiring R] {m : ℕ}

/-- The *multisection* of a power series `f = ∑ aₙ Xⁿ` for the residue class `r` modulo `m`: the
part `∑_{n ≡ r (mod m)} aₙ Xⁿ` of `f` in the degrees congruent to `r` modulo `m`. -/
noncomputable def multisection (m : ℕ) (r : ZMod m) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n ↦ if (n : ZMod m) = r then coeff n f else 0
  map_add' f g := by
    ext n
    simp only [coeff_mk, map_add]
    split_ifs <;> simp
  map_smul' a f := by
    ext n
    simp only [coeff_mk, map_smul, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

@[simp]
theorem coeff_multisection (r : ZMod m) (f : R⟦X⟧) (n : ℕ) :
    coeff n (multisection m r f) = if (n : ZMod m) = r then coeff n f else 0 := by
  simp [multisection]

/-- A power series is its own multisection for `r` exactly when it is supported in the degrees
congruent to `r` modulo `m`. -/
theorem multisection_eq_self_iff {r : ZMod m} {f : R⟦X⟧} :
    multisection m r f = f ↔ ∀ n : ℕ, (n : ZMod m) ≠ r → coeff n f = 0 := by
  refine ⟨fun h n hn ↦ by rw [← h, coeff_multisection, ite_eq_right hn], fun h ↦ ?_⟩
  ext n
  rw [coeff_multisection]
  split_ifs with hn
  · rfl
  · exact (h n hn).symm

/-- Taking a multisection twice: the multisections for distinct residue classes are orthogonal
projections. -/
theorem multisection_multisection (r s : ZMod m) (f : R⟦X⟧) :
    multisection m r (multisection m s f) = if s = r then multisection m r f else 0 := by
  ext n
  split_ifs with h
  · subst h
    simp only [coeff_multisection]
    split_ifs <;> rfl
  · simp only [coeff_multisection, map_zero]
    split_ifs with h₁ h₂ <;> simp_all

/-- A power series is the sum of its `m` multisections. -/
theorem sum_multisection [NeZero m] (f : R⟦X⟧) : ∑ r : ZMod m, multisection m r f = f := by
  ext n
  simp [map_sum, Finset.sum_ite_eq]

/-- The product of a series supported in the degrees `≡ r` and a series supported in the degrees
`≡ s` modulo `m` is supported in the degrees `≡ r + s`. -/
theorem multisection_mul_of_eq {r s : ZMod m} {f g : R⟦X⟧} (hf : multisection m r f = f)
    (hg : multisection m s g = g) : multisection m (r + s) (f * g) = f * g := by
  rw [multisection_eq_self_iff] at hf hg ⊢
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases hx₁ : (x.1 : ZMod m) = r
  · rw [hg x.2 fun hx₂ ↦ hn (by rw [← hx, Nat.cast_add, hx₁, hx₂]), mul_zero]
  · rw [hf x.1 hx₁, zero_mul]

/-- The `k`-th power of a series supported in the degrees `≡ r` modulo `m` is supported in the
degrees `≡ k r`. -/
theorem multisection_pow_of_eq {r : ZMod m} {f : R⟦X⟧} (hf : multisection m r f = f) (k : ℕ) :
    multisection m (k • r) (f ^ k) = f ^ k := by
  induction k with
  | zero =>
    rw [zero_smul, pow_zero, multisection_eq_self_iff]
    intro n hn
    rw [coeff_one, ite_eq_right fun h ↦ hn (by rw [h, Nat.cast_zero])]
  | succ k ih => rw [succ_nsmul, pow_succ, multisection_mul_of_eq ih hf]

/-- Multisection commutes with applying a ring homomorphism to the coefficients. -/
theorem map_multisection {S : Type*} [Semiring S] (φ : R →+* S) (r : ZMod m) (f : R⟦X⟧) :
    map φ (multisection m r f) = multisection m r (map φ f) := by
  ext n
  simp only [coeff_map, coeff_multisection]
  split_ifs <;> simp

end Semiring

/-- Multisection commutes with rescaling the variable: `f_[r](a X)` is the part of `f(a X)` in
the degrees congruent to `r` modulo `m`. -/
theorem rescale_multisection {R : Type*} [CommSemiring R] {m : ℕ} (a : R) (r : ZMod m)
    (f : R⟦X⟧) : rescale a (multisection m r f) = multisection m r (rescale a f) := by
  ext n
  simp only [coeff_rescale, coeff_multisection]
  split_ifs <;> simp

section CommRing

variable {R : Type*} [CommRing R] {m : ℕ}

/-- **Multisection of a substitution.** If `T` is supported in the degrees `≡ 1 (mod m)`, then
`(F(T))_[r] = F_[r](T)`: the powers `T ^ k` are supported in the degrees `≡ k`. (For `m ≠ 1`
such a `T` has no constant term; for `m = 1` every multisection is the identity.) -/
theorem multisection_subst {S : Type*} [CommRing S] [Algebra R S] {T : S⟦X⟧}
    (hT : multisection m 1 T = T) (r : ZMod m) (F : R⟦X⟧) :
    multisection m r (F.subst T) = (multisection m r F).subst T := by
  rcases eq_or_ne m 1 with rfl | hm
  · simp only [multisection_eq_self_iff.mpr fun _ hn ↦ absurd (Subsingleton.elim _ _) hn]
  have hT₀ : constantCoeff T = 0 := by
    have := (ZMod.nontrivial_iff.mpr hm)
    rw [← coeff_zero_eq_constantCoeff_apply, ← hT, coeff_multisection, Nat.cast_zero,
      ite_eq_right zero_ne_one]
  -- the coefficient of `Xⁿ` in `T ^ k` vanishes unless `n ≡ k`
  have hpow (k n : ℕ) (h : (n : ZMod m) ≠ k) : coeff n (T ^ k) = 0 := by
    have := multisection_pow_of_eq hT k
    rw [nsmul_one, multisection_eq_self_iff] at this
    exact this n h
  ext n
  rw [coeff_multisection, coeff_subst_eq_sum_range _ hT₀, coeff_subst_eq_sum_range _ hT₀]
  simp only [coeff_multisection, ite_smul, zero_smul]
  split_ifs with hn
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    split_ifs with hk
    · rfl
    · rw [hpow k n (by rw [hn]; exact Ne.symm hk), smul_zero]
  · refine (Finset.sum_eq_zero fun k _ ↦ ?_).symm
    split_ifs with hk
    · rw [hpow k n (by rwa [hk]), smul_zero]
    · rfl

end CommRing

section Field

/-- **The roots of unity filter.** In a field with a primitive `m`-th root of unity `ζ`, `m` times
the multisection `f_[r]` is the sum of the rotations `ξ ^ (-r) f(ξ X)` over the `m`-th roots of
unity `ξ = ζ ^ a`, `a < m`. -/
theorem natCast_smul_multisection {K : Type*} [Field K] {m : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (r : ℕ) (f : K⟦X⟧) :
    (m : K) • multisection m r f = ∑ a : Fin m, (ζ ^ (a : ℕ))⁻¹ ^ r • rescale (ζ ^ (a : ℕ)) f := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  ext n
  rw [coeff_smul, coeff_multisection, map_sum]
  simp only [coeff_smul, coeff_rescale, smul_eq_mul, ← mul_assoc]
  -- the coefficient of `Xⁿ` is `fₙ` times the sum of the powers of `ζ ^ (n - r)`
  have hterm (a : ℕ) : (ζ ^ a)⁻¹ ^ r * (ζ ^ a) ^ n = (ζ ^ ((n : ℤ) - r)) ^ a := by
    rw [zpow_sub₀ (hζ.ne_zero hm.ne'), zpow_natCast, zpow_natCast, div_eq_mul_inv, mul_pow,
      inv_pow, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm a r, mul_comm a n,
      mul_comm]
  simp_rw [hterm]
  have hc : (m : ℤ) ∣ (n : ℤ) - r ↔ (n : ZMod m) = r := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_natCast, Int.cast_natCast, eq_comm]
  rw [← Finset.sum_mul, hζ.sum_zpow_pow_eq]
  by_cases h : (n : ZMod m) = r <;> simp [h, hc]

end Field

end PowerSeries
