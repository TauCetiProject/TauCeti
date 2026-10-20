/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import TauCeti.RingTheory.LaurentSeries.Ramified

import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.Polynomial.ScaleRoots

/-!
# Slope normalization of monic polynomials over Laurent series

Let `P = Y ^ m + a₁ Y ^ (m - 1) + ⋯ + a_m` be a monic polynomial over `R⸨t⸩` other than `Y ^ m`.
Among its nonzero lower coefficients `a_i`, `i ≥ 1`, choose one minimizing the slope
`ord(a_i) / i`, and write that slope as `p / q` with `q = i > 0`. After the ramified substitution
`t = s ^ q`, the rescaling `Y = s ^ p Z` and division by `s ^ (p m)`, the polynomial becomes
```
Z ^ m + a₁(s ^ q) s ^ (-p) Z ^ (m - 1) + ⋯ + a_m(s ^ q) s ^ (-p m),
```
whose coefficients have order `q ord(a_i) - p i ≥ 0`, with equality at the chosen index. So it is
a monic polynomial `Q` over `R⟦s⟧` whose reduction modulo `s` has a nonzero coefficient below the
leading one, that is, the reduction is not `Z ^ m`. Division by `s ^ (p m)` after `Y = s ^ p Z` is
root scaling by `s ^ p`, so `P(s ^ q, Y)` is `Polynomial.scaleRoots Q (s ^ p)`; a root `z` of `Q`
gives the root `s ^ p z` of `P(s ^ q, Y)`, and factorizations of `Q` transport to factorizations of
`P(s ^ q, Y)` (`Polynomial.scaleRoots_eval₂_mul`, `Polynomial.mul_scaleRoots'`). Root scaling
multiplies the subleading coefficient by a unit, so `Q` is depressed when `P` is.

This is the normalization step of the formal Newton–Puiseux theorem: when the reduction of `Q` also
splits and its degree is invertible, the reduction factors into coprime monic factors, and
Hensel's lemma lifts this to a factorization of `Q` into monic factors of lower degree.

## Main results

* `Polynomial.Monic.exists_map_expand_eq_scaleRoots`: a monic polynomial `P` over `R⸨X⸩` other
  than `X ^ P.natDegree` becomes, after a substitution `X ↦ X ^ q` in its coefficients, the root
  scaling by `X ^ p` of a monic polynomial over `R⟦X⟧` of the same degree whose reduction is not a
  power of `X`.
* `Polynomial.Monic.exists_map_expand_eq_scaleRoots_of_nextCoeff_eq_zero`: if moreover `P` has
  vanishing subleading coefficient, then so does the reduction of the normalized polynomial.

## References

* H. Mannaa and T. Coquand, *Dynamic Newton–Puiseux Theorem*, arXiv:1304.6770, §1, for the
  ramification and rescaling step of the Newton–Puiseux algorithm.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- **Slope normalization.** A monic polynomial `P` over `R⸨X⸩` other than `X ^ P.natDegree`
becomes, after the ramified substitution `X ↦ X ^ q` in its coefficients, the root scaling by
`X ^ p` of a monic polynomial `Q` over `R⟦X⟧` of the same degree whose reduction modulo `X` is not
`X ^ Q.natDegree`. -/
theorem Monic.exists_map_expand_eq_scaleRoots {P : R⸨X⸩[X]} (hP : P.Monic)
    (hX : P ≠ X ^ P.natDegree) :
    ∃ (q : ℕ+) (p : ℤ) (Q : R⟦X⟧[X]), Q.Monic ∧ Q.natDegree = P.natDegree ∧
      P.map (LaurentSeries.expand R q : R⸨X⸩ →+* R⸨X⸩) =
        (Q.map (ofPowerSeries ℤ R)).scaleRoots (single p 1) ∧
      Q.map PowerSeries.constantCoeff ≠ X ^ Q.natDegree := by
  classical
  have : Nontrivial R := not_subsingleton_iff_nontrivial.1 fun _ ↦ hX (Subsingleton.elim _ _)
  set m := P.natDegree
  -- The trailing coefficient lies below the leading one, since `P ≠ X ^ m`.
  have hS : ({j ∈ Finset.range m | P.coeff j ≠ 0} : Finset ℕ).Nonempty :=
    ⟨P.natTrailingDegree, Finset.mem_filter.2 ⟨Finset.mem_range.2
      (not_le.1 (hX ∘ hP.eq_X_pow_iff_natDegree_le_natTrailingDegree.2)),
      coeff_natTrailingDegree_ne_zero.2 hP.ne_zero⟩⟩
  -- Choose a coefficient of least slope `ord(a_i) / i`, where `i = m - j`.
  obtain ⟨j₀, hj₀, hmin⟩ :=
    Finset.exists_min_image _ (fun j ↦ ((P.coeff j).order : ℚ) / (m - j : ℕ)) hS
  rw [Finset.mem_filter, Finset.mem_range] at hj₀
  set q : ℕ+ := ⟨m - j₀, by omega⟩ with hq
  set p := (P.coeff j₀).order
  -- Every nonzero coefficient lies on or above the line of slope `p / q`.
  have hslope : ∀ j, P.coeff j ≠ 0 → ((m - j : ℕ) : ℤ) * p ≤ (q : ℤ) * (P.coeff j).order := by
    intro j hj
    rcases (le_natDegree_of_ne_zero hj).lt_or_eq with hjm | rfl
    · have h := hmin j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hjm, hj⟩)
      rw [div_le_div_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt hj₀.1)
        (by exact_mod_cast Nat.sub_pos_of_lt hjm)] at h
      have h' : p * ((m - j : ℕ) : ℤ) ≤ (P.coeff j).order * ((m - j₀ : ℕ) : ℤ) := by
        exact_mod_cast h
      rw [hq, PNat.mk_coe]
      linarith
    · rw [Nat.sub_self, Nat.cast_zero, zero_mul, hP.coeff_natDegree, order_one, mul_zero]
  set P' := P.map (LaurentSeries.expand R q : R⸨X⸩ →+* R⸨X⸩)
  have hdeg : P'.natDegree = m := hP.natDegree_map _
  -- The coefficients of the rescaled polynomial `P'(X ^ p Y) / X ^ (p m)`.
  have hcoeff : ∀ j, (P'.scaleRoots (single (-p) 1)).coeff j =
      LaurentSeries.expand R q (P.coeff j) * single (-(((m - j : ℕ) : ℤ) * p)) 1 := by
    intro j
    rw [coeff_scaleRoots, hdeg, coeff_map, single_pow, one_pow, nsmul_eq_mul, mul_neg,
      RingHom.coe_coe]
  -- They are power series, because every coefficient lies on or above the line of slope `p / q`.
  have hlifts : P'.scaleRoots (single (-p) 1) ∈ lifts (ofPowerSeries ℤ R) := by
    refine (lifts_iff_coeff_lifts _).2 fun j ↦ ?_
    rw [hcoeff, TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff]
    intro n hn
    rw [coeff_mul_single, mul_one]
    by_cases hj : P.coeff j = 0
    · rw [hj, map_zero, HahnSeries.coeff_zero]
    exact LaurentSeries.coeff_expand_of_lt_mul_order q (by linarith [hslope j hj])
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := lifts_and_natDegree_eq_and_monic hlifts
    ((monic_scaleRoots_iff _).2 (hP.map _))
  rw [natDegree_scaleRoots, hdeg] at hQdeg
  refine ⟨q, p, Q, hQm, hQdeg, ?_, fun h ↦ ?_⟩
  · rw [hQ, ← scaleRoots_mul, single_mul_single, neg_add_cancel, one_mul, single_zero_one,
      scaleRoots_one]
  -- The coefficient of the chosen index has order zero, so its constant coefficient is nonzero.
  have h₀ := congrArg (fun F ↦ F.coeff j₀) h
  simp only [coeff_map, coeff_X_pow, hQdeg, hj₀.1.ne, ite_false] at h₀
  have hj : ofPowerSeries ℤ R (Q.coeff j₀) =
      LaurentSeries.expand R q (P.coeff j₀) * single (-((q : ℤ) * p)) 1 := by
    rw [← coeff_map, hQ, hcoeff, PNat.mk_coe]
  have hc : PowerSeries.constantCoeff (Q.coeff j₀) = (P.coeff j₀).coeff p := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← ofPowerSeries_apply_coeff (Γ := ℤ),
      Nat.cast_zero, hj, coeff_mul_single, zero_sub, neg_neg, mul_one,
      LaurentSeries.coeff_expand_mul]
  exact coeff_order_eq_zero.not.2 hj₀.2 (hc ▸ h₀)

/-- **Slope normalization of a depressed polynomial.** If the monic polynomial `P` over `R⸨X⸩`
has vanishing subleading coefficient and is not `X ^ P.natDegree`, then it has a normalization
`Q` as in `Polynomial.Monic.exists_map_expand_eq_scaleRoots` whose reduction modulo `X` also has
vanishing subleading coefficient. -/
theorem Monic.exists_map_expand_eq_scaleRoots_of_nextCoeff_eq_zero {P : R⸨X⸩[X]} (hP : P.Monic)
    (hnext : P.nextCoeff = 0) (hX : P ≠ X ^ P.natDegree) :
    ∃ (q : ℕ+) (p : ℤ) (Q : R⟦X⟧[X]), Q.Monic ∧ Q.natDegree = P.natDegree ∧
      P.map (LaurentSeries.expand R q : R⸨X⸩ →+* R⸨X⸩) =
        (Q.map (ofPowerSeries ℤ R)).scaleRoots (single p 1) ∧
      (Q.map PowerSeries.constantCoeff).nextCoeff = 0 ∧
      Q.map PowerSeries.constantCoeff ≠ X ^ Q.natDegree := by
  have : Nontrivial R := not_subsingleton_iff_nontrivial.1 fun _ ↦ hX (Subsingleton.elim _ _)
  obtain ⟨q, p, Q, hQm, hQdeg, hQ, hred⟩ := hP.exists_map_expand_eq_scaleRoots hX
  refine ⟨q, p, Q, hQm, hQdeg, hQ, ?_, hred⟩
  have h := congrArg nextCoeff hQ
  rw [nextCoeff_map (f := (LaurentSeries.expand R q : R⸨X⸩ →+* R⸨X⸩))
    (LaurentSeries.expand_injective q), hnext, map_zero, nextCoeff_scaleRoots,
    nextCoeff_map (ofPowerSeries_injective (Γ := ℤ))] at h
  -- The monomial `X ^ p` is a unit, so the subleading coefficient of `Q` vanishes.
  have hQ0 : Q.nextCoeff = 0 := by
    refine ofPowerSeries_injective (Γ := ℤ) ?_
    rw [map_zero, ← mul_one (ofPowerSeries ℤ R Q.nextCoeff), ← single_zero_one,
      ← add_neg_cancel p, ← one_mul (1 : R), ← single_mul_single, ← mul_assoc, ← h, zero_mul]
  rw [nextCoeff_map_eq_of_isUnit_leadingCoeff _ (by simp [hQm.leadingCoeff]), hQ0, map_zero]

end Polynomial
