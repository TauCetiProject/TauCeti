/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import TauCeti.RingTheory.HahnSeries.Map

/-!
# Bounded denominators of Hahn and Laurent series

Let `A` be an algebra over a commutative ring `R`. A Hahn series `x : A⟦Γ⟧`, for instance a
Laurent series in `A⸨X⸩ = A⟦ℤ⟧`, has *bounded denominators* over `R`
(`HahnSeries.HasBoundedDenominators R x`) when a single non-zero-divisor `d` of `R` clears the
denominators of all its coefficients at once: every `d • x.coeff g` lies in the image of `R`
(`IsLocalization.IsInteger R`). Over `ℤ`, for coefficients in `ℚ` or `ℂ`, this asks for one
positive integer `D` with `D aₙ ∈ ℤ` for every `n`, including the finitely many negative `n` of a
Laurent series (`HahnSeries.hasBoundedDenominators_int_iff`). It is stronger than every
coefficient having some denominator: `∑ Xⁿ / 2ⁿ` has all its coefficients in `ℤ[1/2]` and
unbounded denominators.

This is the arithmetic condition of the unbounded denominators theorem of Calegari, Dimitrov and
Tang: a modular form on a finite-index subgroup of `SL₂(ℤ)` whose `q`-expansion has rational
coefficients has bounded denominators exactly when it is modular for a congruence subgroup.

The series with bounded denominators are closed under the ring operations, and an order embedding
of the exponents, such as substituting `Xᵈ` for `X`, preserves and reflects the condition
(`HahnSeries.hasBoundedDenominators_embDomain_iff`; see
`LaurentSeries.hasBoundedDenominators_expand_iff` in
`TauCeti.RingTheory.LaurentSeries.BoundedDenominators`), so the condition does not depend on the
choice of a root of the expansion variable.

The main result is the *root property*: over a unique factorization domain `R`, a series `x`
with bounded denominators some power `xⁿ`, `n ≠ 0`, of which has integral coefficients has
integral coefficients itself
(`HahnSeries.HasBoundedDenominators.isInteger_coeff_of_isInteger_coeff_pow`). So a series whose
`n`-th power is integral and which has a non-integral coefficient has unbounded denominators: for
instance the branch `(1 - 16X)^(1/16)` of the sixteenth root, whose `X²`-coefficient is `-15/2`.
The proof clears one prime factor `p` of the denominator at a time: reducing an integral series
modulo `p` lands in the Hahn series over the domain `R ⧸ (p)`, which have no nonzero nilpotent
elements (`HahnSeries.coeff_mem_of_coeff_pow_mem`).

## Main definitions

* `HahnSeries.HasBoundedDenominators R x`: some non-zero-divisor of `R` makes every coefficient of
  `x` integral.

## Main results

* `HahnSeries.HasBoundedDenominators.add`, `.neg`, `.sub`, `.smul`, `.mul`, `.pow`: closure under
  the ring operations.
* `HahnSeries.hasBoundedDenominators_embDomain_iff`: invariance under an order embedding of the
  exponents.
* `HahnSeries.hasBoundedDenominators_int_iff`: over `ℤ`, one positive integer clears every
  denominator.
* `HahnSeries.HasBoundedDenominators.isInteger_coeff_of_isInteger_coeff_pow`: the root property.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), 627–702, Theorem 1.0.1 and the discussion of (1.0.4).
-/

public section

open IsLocalization

namespace HahnSeries

variable {Γ Γ' R A : Type*}

section CommSemiring

variable [PartialOrder Γ] [CommSemiring R] [CommSemiring A] [Algebra R A]

variable (R) in
/-- A Hahn series `x` over an `R`-algebra `A` has *bounded denominators* over `R` when a single
non-zero-divisor `d` of `R` makes every coefficient `d • x.coeff g` lie in the image of `R`. -/
def HasBoundedDenominators (x : A⟦Γ⟧) : Prop :=
  ∃ d ∈ nonZeroDivisors R, ∀ g, IsInteger R (d • x.coeff g)

theorem hasBoundedDenominators_iff {x : A⟦Γ⟧} :
    x.HasBoundedDenominators R ↔ ∃ d ∈ nonZeroDivisors R, ∀ g, IsInteger R (d • x.coeff g) :=
  Iff.rfl

/-- A series with integral coefficients has bounded denominators. -/
theorem HasBoundedDenominators.of_isInteger {x : A⟦Γ⟧} (hx : ∀ g, IsInteger R (x.coeff g)) :
    x.HasBoundedDenominators R :=
  ⟨1, one_mem _, fun g ↦ by simpa using hx g⟩

@[simp]
theorem hasBoundedDenominators_zero : (0 : A⟦Γ⟧).HasBoundedDenominators R :=
  .of_isInteger fun _ ↦ by simpa using isInteger_zero

theorem HasBoundedDenominators.add {x y : A⟦Γ⟧} (hx : x.HasBoundedDenominators R)
    (hy : y.HasBoundedDenominators R) : (x + y).HasBoundedDenominators R := by
  obtain ⟨d, hd, hdx⟩ := hx
  obtain ⟨e, he, hey⟩ := hy
  refine ⟨d * e, mul_mem hd he, fun g ↦ ?_⟩
  rw [coeff_add, smul_add]
  refine isInteger_add ?_ ?_
  · rw [mul_comm, mul_smul]
    exact isInteger_smul (hdx g)
  · rw [mul_smul]
    exact isInteger_smul (hey g)

theorem HasBoundedDenominators.smul {x : A⟦Γ⟧} (hx : x.HasBoundedDenominators R) (r : R) :
    (r • x).HasBoundedDenominators R := by
  obtain ⟨d, hd, hdx⟩ := hx
  refine ⟨d, hd, fun g ↦ ?_⟩
  rw [coeff_smul, smul_comm]
  exact isInteger_smul (hdx g)

/-- The image of a series under an order embedding of the exponents has bounded denominators
exactly when the series does: the new coefficients are the old ones, together with zeros. -/
@[simp]
theorem hasBoundedDenominators_embDomain_iff [PartialOrder Γ'] (f : Γ ↪o Γ') {x : A⟦Γ⟧} :
    (embDomain f x).HasBoundedDenominators R ↔ x.HasBoundedDenominators R := by
  simp only [hasBoundedDenominators_iff]
  refine exists_congr fun d ↦ and_congr_right fun _ ↦ ⟨fun h g ↦ ?_, fun h b ↦ ?_⟩
  · simpa using h (f g)
  · by_cases hb : b ∈ Set.range f
    · obtain ⟨g, rfl⟩ := hb
      simpa using h g
    · rw [embDomain_of_notMem_range hb, smul_zero]
      exact isInteger_zero

end CommSemiring

section Ring

variable [PartialOrder Γ] [CommRing R] [CommRing A] [Algebra R A]

theorem HasBoundedDenominators.neg {x : A⟦Γ⟧} (hx : x.HasBoundedDenominators R) :
    (-x).HasBoundedDenominators R := by
  obtain ⟨d, hd, hdx⟩ := hx
  refine ⟨d, hd, fun g ↦ ?_⟩
  obtain ⟨r, hr⟩ := hdx g
  exact ⟨-r, by rw [coeff_neg, smul_neg, map_neg, hr]⟩

theorem HasBoundedDenominators.sub {x y : A⟦Γ⟧} (hx : x.HasBoundedDenominators R)
    (hy : y.HasBoundedDenominators R) : (x - y).HasBoundedDenominators R := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- Over `ℤ`, a series has bounded denominators exactly when one positive integer `D` makes all
its coefficients `D aₙ` integers. -/
theorem hasBoundedDenominators_int_iff {x : A⟦Γ⟧} :
    x.HasBoundedDenominators ℤ ↔ ∃ D : ℕ, 0 < D ∧ ∀ g, ∃ z : ℤ, (D : A) * x.coeff g = z := by
  simp only [hasBoundedDenominators_iff, IsInteger, RingHom.mem_rangeS, algebraMap_int_eq,
    eq_intCast, zsmul_eq_mul, mem_nonZeroDivisors_iff_ne_zero]
  refine ⟨fun ⟨d, hd, h⟩ ↦ ⟨d.natAbs, Int.natAbs_pos.mpr hd, fun g ↦ ?_⟩,
    fun ⟨D, hD, h⟩ ↦ ⟨D, by exact_mod_cast hD.ne', fun g ↦ ?_⟩⟩
  · obtain ⟨z, hz⟩ := h g
    refine ⟨d.sign * z, ?_⟩
    rw [← Int.cast_natCast, ← Int.sign_mul_self_eq_natAbs]
    push_cast [hz]
    ring
  · obtain ⟨z, hz⟩ := h g
    exact ⟨z, by rw [Int.cast_natCast, hz]⟩

end Ring

section OrderedCancel

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommSemiring R]
  [CommSemiring A] [Algebra R A]

omit [IsOrderedCancelAddMonoid Γ] in
@[simp]
theorem hasBoundedDenominators_one : (1 : A⟦Γ⟧).HasBoundedDenominators R :=
  .of_isInteger fun g ↦ by
    rw [coeff_one]
    split_ifs
    exacts [isInteger_one, isInteger_zero]

theorem HasBoundedDenominators.mul {x y : A⟦Γ⟧} (hx : x.HasBoundedDenominators R)
    (hy : y.HasBoundedDenominators R) : (x * y).HasBoundedDenominators R := by
  obtain ⟨d, hd, hdx⟩ := hx
  obtain ⟨e, he, hey⟩ := hy
  refine ⟨d * e, mul_mem hd he, fun g ↦ ?_⟩
  rw [coeff_mul, Finset.smul_sum]
  refine Subsemiring.sum_mem _ fun ij _ ↦ ?_
  rw [← smul_mul_smul_comm]
  exact isInteger_mul (hdx _) (hey _)

theorem HasBoundedDenominators.pow {x : A⟦Γ⟧} (hx : x.HasBoundedDenominators R) (n : ℕ) :
    (x ^ n).HasBoundedDenominators R := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul hx

end OrderedCancel

section Domain

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] [IsDomain R]
  [UniqueFactorizationMonoid R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

/-- **The root property of bounded denominators.** Over a unique factorization domain `R`, if
`x` has bounded denominators and `x ^ n` has integral coefficients for some `n ≠ 0`, then `x` has
integral coefficients. -/
theorem HasBoundedDenominators.isInteger_coeff_of_isInteger_coeff_pow {x : A⟦Γ⟧}
    (hx : x.HasBoundedDenominators R) {n : ℕ} (hn : n ≠ 0)
    (hxn : ∀ g, IsInteger R ((x ^ n).coeff g)) (g : Γ) : IsInteger R (x.coeff g) := by
  obtain ⟨w, hw⟩ := mem_map_rangeS.mpr hxn
  obtain ⟨d, hd, hdx⟩ := hx
  -- remove the prime factors of the common denominator `d` one at a time
  induction d using UniqueFactorizationMonoid.induction_on_prime generalizing g with
  | h₁ => exact absurd hd zero_notMem_nonZeroDivisors
  | h₂ u hu =>
    simpa [smul_smul, hu.val_inv_mul] using isInteger_smul (a := ↑hu.unit⁻¹) (hdx g)
  | h₃ a p ha hp ih =>
    refine ih g (mem_nonZeroDivisors_of_ne_zero ha) fun g ↦ ?_
    obtain ⟨y, hy⟩ := mem_map_rangeS (x := (p * a) • x).mpr fun g ↦ by
      rw [coeff_smul]
      exact hdx g
    have hinj := FaithfulSMul.algebraMap_injective R A
    -- `y` lifts `(p * a) • x` to `R⟦Γ⟧`, so `y ^ n` lifts `(p * a) ^ n • x ^ n`
    have hyn : y ^ n = (p * a) ^ n • w := by
      refine mapRingHom_injective hinj ?_
      rw [map_pow, hy, smul_pow, ← hw]
      ext g
      simp only [coeff_smul, coeff_mapRingHom]
      rw [smul_eq_mul, map_mul, Algebra.smul_def]
    obtain ⟨r, hr⟩ : p ∣ y.coeff g := by
      have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      rw [← Ideal.mem_span_singleton]
      refine coeff_mem_of_coeff_pow_mem (n := n) (fun g ↦ ?_) g
      rw [hyn, coeff_smul, smul_eq_mul, Ideal.mem_span_singleton]
      exact (dvd_pow (dvd_mul_right p a) hn).mul_right _
    refine ⟨r, mul_left_cancel₀ ((map_ne_zero_iff _ hinj).mpr hp.ne_zero) ?_⟩
    have := congr(($hy).coeff g)
    rw [coeff_mapRingHom, hr, coeff_smul, mul_smul, Algebra.smul_def p] at this
    rw [← map_mul, this]

end Domain

end HahnSeries
