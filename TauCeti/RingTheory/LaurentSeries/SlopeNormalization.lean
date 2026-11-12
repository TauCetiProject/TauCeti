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

This is the normalization step of the formal Newton–Puiseux theorem. When `P` is depressed, so is
the reduction of `Q`; if that reduction moreover splits and its degree `m` is invertible, then it
is not `(Z - c) ^ m`: its subleading coefficient `-m c` vanishes, forcing `c = 0`, and the
reduction is not `Z ^ m`. So it has two distinct roots and factors into coprime monic factors, and
Hensel's lemma lifts this to a factorization of `Q` into monic factors of lower degree.

## Main results

* `Polynomial.Monic.exists_map_expand_eq_scaleRoots`: a monic polynomial `P` over `R⸨X⸩` other
  than `X ^ P.natDegree` becomes, after a substitution `X ↦ X ^ q` in its coefficients, the root
  scaling by `X ^ p` of a monic polynomial over `R⟦X⟧` of the same degree whose reduction is not a
  power of `X`.
* `Polynomial.Monic.exists_map_expand_eq_scaleRoots_of_nextCoeff_eq_zero`: if moreover `P` has
  vanishing subleading coefficient, then so does the reduction of the normalized polynomial.
* `Polynomial.Monic.exists_coeff_ne_zero_slope_le`: the choice of a nonzero lower coefficient of
  least slope, and `Polynomial.coeff_scaleRoots_map_expand`: the coefficients of the ramified and
  rescaled polynomial.

## References

* H. Mannaa and T. Coquand, *Dynamic Newton–Puiseux Theorem*, arXiv:1304.6770, §1, for the
  ramification and rescaling step of the Newton–Puiseux algorithm.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace Polynomial

variable {R : Type*}

/-- **Least slope.** A monic polynomial `P` over `R⸨X⸩` other than `X ^ P.natDegree` has a
nonzero coefficient `a_{j₀}`, `j₀ < P.natDegree`, of least slope: for every nonzero lower
coefficient `a_j`, the inequality
`ord(a_{j₀}) / (P.natDegree - j₀) ≤ ord(a_j) / (P.natDegree - j)` holds, stated with the
denominators cleared. -/
theorem Monic.exists_coeff_ne_zero_slope_le [Semiring R] {P : R⸨X⸩[X]} (hP : P.Monic)
    (hX : P ≠ X ^ P.natDegree) :
    ∃ j₀ < P.natDegree, P.coeff j₀ ≠ 0 ∧ ∀ j, P.coeff j ≠ 0 →
      ((P.natDegree - j : ℕ) : ℤ) * (P.coeff j₀).order ≤
        ((P.natDegree - j₀ : ℕ) : ℤ) * (P.coeff j).order := by
  classical
  have : Nontrivial R := not_subsingleton_iff_nontrivial.1 fun _ ↦ hX (Subsingleton.elim _ _)
  set m := P.natDegree
  -- The trailing coefficient lies below the leading one, since `P ≠ X ^ m`.
  have hS : ({j ∈ Finset.range m | P.coeff j ≠ 0} : Finset ℕ).Nonempty :=
    ⟨P.natTrailingDegree, Finset.mem_filter.2 ⟨Finset.mem_range.2
      (not_le.1 (hX ∘ hP.eq_X_pow_iff_natDegree_le_natTrailingDegree.2)),
      coeff_natTrailingDegree_ne_zero.2 hP.ne_zero⟩⟩
  obtain ⟨j₀, hj₀, hmin⟩ :=
    Finset.exists_min_image _ (fun j ↦ ((P.coeff j).order : ℚ) / (m - j : ℕ)) hS
  rw [Finset.mem_filter, Finset.mem_range] at hj₀
  refine ⟨j₀, hj₀.1, hj₀.2, fun j hj ↦ ?_⟩
  rcases (le_natDegree_of_ne_zero hj).lt_or_eq with hjm | rfl
  · have h := hmin j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hjm, hj⟩)
    rw [div_le_div_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt hj₀.1)
      (by exact_mod_cast Nat.sub_pos_of_lt hjm)] at h
    have h' : (P.coeff j₀).order * ((m - j : ℕ) : ℤ) ≤ (P.coeff j).order * ((m - j₀ : ℕ) : ℤ) := by
      exact_mod_cast h
    linarith
  · rw [Nat.sub_self, Nat.cast_zero, zero_mul, hP.coeff_natDegree, order_one, mul_zero]

variable [CommSemiring R]

/-- The coefficients of `P(X ^ q, X ^ p Y) / X ^ (p m)`, where `m = P.natDegree`: the root scaling
by `X ^ (-p)` of `P` with the substitution `X ↦ X ^ q` applied to its coefficients. -/
theorem coeff_scaleRoots_map_expand (P : R⸨X⸩[X]) (q : ℕ+) (p : ℤ) (j : ℕ) :
    ((P.map (LaurentSeries.expand R q : R⸨X⸩ →+* R⸨X⸩)).scaleRoots (single (-p) 1)).coeff j =
      LaurentSeries.expand R q (P.coeff j) * single (-(((P.natDegree - j : ℕ) : ℤ) * p)) 1 := by
  rw [coeff_scaleRoots, natDegree_map_eq_of_injective
    (f := (LaurentSeries.expand R q : R⸨X⸩ →+* R⸨X⸩)) (LaurentSeries.expand_injective q),
    coeff_map, single_pow, one_pow, nsmul_eq_mul, mul_neg, RingHom.coe_coe]

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
  have : Nontrivial R := not_subsingleton_iff_nontrivial.1 fun _ ↦ hX (Subsingleton.elim _ _)
  -- Choose a coefficient of least slope `p / q`.
  obtain ⟨j₀, hj₀m, hj₀, hslope⟩ := hP.exists_coeff_ne_zero_slope_le hX
  set q : ℕ+ := ⟨P.natDegree - j₀, by omega⟩ with hq
  set p := (P.coeff j₀).order
  set P' := P.map (LaurentSeries.expand R q : R⸨X⸩ →+* R⸨X⸩)
  -- The rescaled polynomial has power series coefficients, since every nonzero coefficient lies on
  -- or above the line of slope `p / q`.
  have hlifts : P'.scaleRoots (single (-p) 1) ∈ lifts (ofPowerSeries ℤ R) := by
    refine (lifts_iff_coeff_lifts _).2 fun j ↦ ?_
    rw [coeff_scaleRoots_map_expand, TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff]
    intro n hn
    rw [coeff_mul_single, mul_one]
    by_cases hj : P.coeff j = 0
    · rw [hj, map_zero, HahnSeries.coeff_zero]
    refine LaurentSeries.coeff_expand_of_lt_mul_order q ?_
    rw [hq, PNat.mk_coe]
    linarith [hslope j hj]
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := lifts_and_natDegree_eq_and_monic hlifts
    ((monic_scaleRoots_iff _).2 (hP.map _))
  rw [natDegree_scaleRoots, hP.natDegree_map] at hQdeg
  refine ⟨q, p, Q, hQm, hQdeg, ?_, fun h ↦ ?_⟩
  · rw [hQ, ← scaleRoots_mul, single_mul_single, neg_add_cancel, one_mul, single_zero_one,
      scaleRoots_one]
  -- The coefficient of the chosen index has order zero, so its constant coefficient is nonzero.
  have h₀ := congrArg (fun F ↦ F.coeff j₀) h
  simp only [coeff_map, coeff_X_pow, hQdeg, hj₀m.ne, ite_false] at h₀
  have hj : ofPowerSeries ℤ R (Q.coeff j₀) =
      LaurentSeries.expand R q (P.coeff j₀) * single (-((q : ℤ) * p)) 1 := by
    rw [← coeff_map, hQ, coeff_scaleRoots_map_expand, PNat.mk_coe]
  have hc : PowerSeries.constantCoeff (Q.coeff j₀) = (P.coeff j₀).coeff p := by
    have h0 := ofPowerSeries_apply_coeff (Γ := ℤ) (Q.coeff j₀) 0
    rw [Nat.cast_zero, hj] at h0
    simpa [coeff_mul_single, LaurentSeries.coeff_expand_mul] using h0.symm
  exact coeff_order_eq_zero.not.2 hj₀ (hc ▸ h₀)

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
    have hu : single p (1 : R) * single (-p) 1 = 1 := by
      rw [single_mul_single, add_neg_cancel, mul_one, single_zero_one]
    refine ofPowerSeries_injective (Γ := ℤ) ?_
    rw [map_zero, ← (IsUnit.of_mul_eq_one _ hu).mul_left_eq_zero, ← h]
  rw [nextCoeff_map_eq_of_isUnit_leadingCoeff _ (by simp [hQm.leadingCoeff]), hQ0, map_zero]

end Polynomial
