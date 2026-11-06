/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.RootBound
public import TauCeti.RingTheory.PowerSeries.GaussNorm
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Root bounds and root counts for distinguished polynomials

A monic polynomial distinguished in its full degree at a positive radius has all its roots
in the corresponding closed disc. This uses only the Gauss-norm coefficient bounds, without
Weierstrass division or preparation, and applies over ultrametric normed commutative rings
with multiplicative norm, without completeness. It supplies the outer root bound for quotients
of preparation polynomials at nested radii.

The polynomial root estimate is
`Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`.

Over an ultrametric normed field the two dominant degrees of a nonzero polynomial `P` at a
radius `c > 0` count its roots, with multiplicity: the distinguished degree (the last index
attaining the Gauss norm) bounds the number of roots in the closed disc `‖x‖ ≤ c`, and the
lowest dominant degree (the first such index) bounds the number in the open disc `‖x‖ < c`.
When `P` splits both bounds are equalities, so their difference counts the roots on the sphere
`‖x‖ = c`. The linear factor `X - b` has distinguished degree `1` or `0` according as `‖b‖ ≤ c`
or not, and lowest dominant degree `1` or `0` according as `‖b‖ < c` or not; both degrees add
under products, and the factor of `P` without roots contributes nonnegative degrees. No
valuation, Newton polygon or completeness is involved; the counts in terms of the endpoints of a
finite Newton face for a real additive valuation are
`Polynomial.card_filter_roots_lt_addValuation` and `Polynomial.card_filter_roots_le_addValuation`.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.norm_le_of_eval_eq_zero`: the roots of a monic polynomial
  distinguished in its full degree lie in the closed disc.
* `TauCeti.PowerSeries.IsDistinguished.card_filter_roots_norm_le_le` and
  `TauCeti.PowerSeries.IsDistinguished.card_filter_roots_norm_le_eq`: the distinguished degree
  bounds, and for a split polynomial equals, the number of roots in the closed disc.
* `TauCeti.PowerSeries.IsLowestDominant.card_filter_roots_norm_lt_le` and
  `TauCeti.PowerSeries.IsLowestDominant.card_filter_roots_norm_lt_eq`: the same for the lowest
  dominant degree and the open disc.
* `TauCeti.PowerSeries.card_filter_roots_norm_eq`: for a split polynomial the difference of the
  two degrees is the number of roots on the sphere.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {c : ℝ} {s : ℕ}

/-- Every root of a monic polynomial distinguished in its full degree lies in its closed
disc. The coefficient ring need not be complete or a field. -/
theorem IsDistinguished.norm_le_of_eval_eq_zero {P : Polynomial R}
    (hP : IsDistinguished c s (P : PowerSeries R)) (hc : 0 < c)
    (hm : P.IsMonicOfDegree s) {x : R} (hx : P.eval x = 0) : ‖x‖ ≤ c := by
  have : Nontrivial R := nontrivial_of_ne _ _ hP.coeff_ne_zero
  have : NormOneClass R := NormMulClass.toNormOneClass
  obtain ⟨i, hi, hxi⟩ := hm.monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero
    (f := normRingNorm R) (fun a n _ => norm_pow a n)
    IsUltrametricDist.isNonarchimedean_norm hx
  rw [hm.natDegree_eq] at hi hxi
  have hxi' : ‖x‖ ^ (s - i) ≤ ‖P.coeff i‖ := by
    simpa only [← RingNorm.toFun_eq_coe, normRingNorm_toFun] using hxi
  have hcoeff : ‖P.coeff i‖ * c ^ i ≤ c ^ s := by
    simpa [← hP.norm_coeff_mul_pow_eq, hm.coeff_coe_self] using
      _root_.PowerSeries.le_gaussNorm norm c (P : PowerSeries R) hP.hasGaussNorm i
  have hpow : ‖x‖ ^ (s - i) ≤ c ^ (s - i) := by
    apply (mul_le_mul_iff_left₀ (pow_pos hc i)).mp
    calc ‖x‖ ^ (s - i) * c ^ i ≤ ‖P.coeff i‖ * c ^ i :=
           mul_le_mul_of_nonneg_right hxi' (pow_nonneg hc.le i)
      _ ≤ c ^ (s - i) * c ^ i := by
           simpa only [← pow_add, Nat.sub_add_cancel hi.le] using hcoeff
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc.le (Nat.sub_ne_zero_of_lt hi)).mp hpow

section LinearFactor

variable {R : Type*} [NormedRing R] [NormOneClass R] {c : ℝ}

/-- The Gauss norm at `c` of a linear polynomial `X - b` with `c ≤ ‖b‖` is `‖b‖`, attained by the
constant term. -/
private theorem gaussNorm_X_sub_C_of_le {b : R} (hb : c ≤ ‖b‖) :
    (PowerSeries.X - PowerSeries.C b : PowerSeries R).gaussNorm norm c = ‖b‖ := by
  have : Nontrivial R := NormOneClass.nontrivial
  rw [gaussNorm_eq_of_forall_le (s := 0)]
  · simp
  · intro m
    rcases m with _ | _ | m
    · simp
    · simpa using hb
    · simp [PowerSeries.coeff_X]

/-- A linear polynomial `X - b` whose root lies outside the closed disc of radius `c > 0` is
distinguished of degree `0` at `c`: its Gauss norm `‖b‖` is attained only by the constant term. -/
theorem isDistinguished_zero_X_sub_C (hc : 0 < c) {b : R} (hb : c < ‖b‖) :
    IsDistinguished c 0 (PowerSeries.X - PowerSeries.C b) := by
  have : Nontrivial R := NormOneClass.nontrivial
  refine ⟨by simp [gaussNorm_X_sub_C_of_le hb.le], fun m hm ↦ ?_⟩
  rw [gaussNorm_X_sub_C_of_le hb.le]
  rcases m with _ | _ | m
  · omega
  · simpa using hb
  · simpa [PowerSeries.coeff_X, PowerSeries.coeff_C] using hc.trans hb

/-- A linear polynomial `X - b` whose root lies outside the open disc of radius `c > 0` has
lowest dominant degree `0` at `c`: its Gauss norm `‖b‖` is attained by the constant term. -/
theorem isLowestDominant_zero_X_sub_C (hc : 0 < c) {b : R} (hb : c ≤ ‖b‖) :
    IsLowestDominant c 0 (PowerSeries.X - PowerSeries.C b) := by
  refine ⟨?_, by simp [gaussNorm_X_sub_C_of_le hb], fun m hm ↦ absurd hm m.not_lt_zero⟩
  rw [gaussNorm_X_sub_C_of_le hb]
  exact hc.trans_le hb

end LinearFactor

section Field

variable {K : Type*} [NormedField K] {c : ℝ} {d l : ℕ} {P : Polynomial K}

/-- A nonzero constant is distinguished of degree `0` at a positive radius. -/
private theorem isDistinguished_C (hc : 0 < c) {a : K} (ha : a ≠ 0) :
    IsDistinguished c 0 (PowerSeries.C a) := by
  simpa using isDistinguished_monomial hc ha 0

/-- A nonzero constant has lowest dominant degree `0` at a positive radius. -/
private theorem isLowestDominant_C (hc : 0 < c) {a : K} (ha : a ≠ 0) :
    IsLowestDominant c 0 (PowerSeries.C a) := by
  have h := isDistinguished_C hc ha
  exact ⟨h.gaussNorm_pos, h.norm_coeff_mul_pow_eq, fun m hm ↦ absurd hm m.not_lt_zero⟩

variable [IsUltrametricDist K]

/-- A product of linear factors `∏ (X - a)` is distinguished at the radius `c > 0` of degree the
number of its roots in the closed disc of radius `c`, counted with multiplicity. -/
theorem isDistinguished_multiset_prod_X_sub_C (hc : 0 < c) (s : Multiset K) :
    IsDistinguished c (s.filter (‖·‖ ≤ c)).card
      ((s.map fun a ↦ (Polynomial.X - Polynomial.C a : Polynomial K)).prod : PowerSeries K) := by
  induction s using Multiset.induction_on with
  | empty => simpa [map_one] using isDistinguished_C hc (one_ne_zero (α := K))
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.coe_mul, Polynomial.coe_sub,
      Polynomial.coe_X, Polynomial.coe_C, Multiset.filter_cons]
    by_cases ha : ‖a‖ ≤ c
    · simpa [ha, add_comm] using (isDistinguished_X_sub_C hc ha).mul ih hc (norm_mul _ _)
    · simpa [ha] using
        (isDistinguished_zero_X_sub_C hc (not_le.mp ha)).mul ih hc (norm_mul _ _)

/-- A product of linear factors `∏ (X - a)` has lowest dominant degree at the radius `c > 0` the
number of its roots in the open disc of radius `c`, counted with multiplicity. -/
theorem isLowestDominant_multiset_prod_X_sub_C (hc : 0 < c) (s : Multiset K) :
    IsLowestDominant c (s.filter (‖·‖ < c)).card
      ((s.map fun a ↦ (Polynomial.X - Polynomial.C a : Polynomial K)).prod : PowerSeries K) := by
  induction s using Multiset.induction_on with
  | empty => simpa [map_one] using isLowestDominant_C hc (one_ne_zero (α := K))
  | cons a s ih =>
    have hs := hasGaussNorm_of_isRestricted (isRestricted_polynomial (c := c)
      (s.map fun a ↦ (Polynomial.X - Polynomial.C a : Polynomial K)).prod)
    have ha' := hasGaussNorm_of_isRestricted
      (isRestricted_polynomial (c := c) (Polynomial.X - Polynomial.C a))
    rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C] at ha'
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.coe_mul, Polynomial.coe_sub,
      Polynomial.coe_X, Polynomial.coe_C, Multiset.filter_cons]
    by_cases ha : ‖a‖ < c
    · simpa [ha, add_comm] using
        (isLowestDominant_X_sub_C hc ha).mul ih hc ha' hs (norm_mul _ _)
    · simpa [ha] using
        (isLowestDominant_zero_X_sub_C hc (not_lt.mp ha)).mul ih hc ha' hs (norm_mul _ _)

/-- **Roots in the closed disc.** A polynomial over an ultrametric normed field distinguished of
degree `d` at the radius `c > 0` has at most `d` roots `x` with `‖x‖ ≤ c`, counted with
multiplicity. -/
theorem IsDistinguished.card_filter_roots_norm_le_le (hP : IsDistinguished c d (P : PowerSeries K))
    (hc : 0 < c) : (P.roots.filter (‖·‖ ≤ c)).card ≤ d := by
  obtain ⟨q, hq, -, -⟩ := P.exists_prod_multiset_X_sub_C_mul
  have hq0 : (q : PowerSeries K) ≠ 0 := by
    rintro h
    rw [Polynomial.coe_eq_zero_iff.mp h, mul_zero] at hq
    exact hP.ne_zero (by rw [← hq, Polynomial.coe_zero])
  obtain ⟨e, he⟩ := exists_isDistinguished hc (isRestricted_polynomial q) hq0
  have h := (isDistinguished_multiset_prod_X_sub_C hc P.roots).mul he hc (norm_mul _ _)
  rw [← Polynomial.coe_mul, hq] at h
  exact (hP.unique h).symm ▸ Nat.le_add_right _ _

/-- **Roots in the closed disc of a split polynomial.** A split polynomial over an ultrametric
normed field distinguished of degree `d` at the radius `c > 0` has exactly `d` roots `x` with
`‖x‖ ≤ c`, counted with multiplicity. -/
theorem IsDistinguished.card_filter_roots_norm_le_eq (hP : IsDistinguished c d (P : PowerSeries K))
    (hc : 0 < c) (hs : P.Splits) : (P.roots.filter (‖·‖ ≤ c)).card = d := by
  have hlc : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr fun h ↦ hP.ne_zero (by rw [h, Polynomial.coe_zero])
  have h := (isDistinguished_C hc hlc).mul (isDistinguished_multiset_prod_X_sub_C hc P.roots) hc
    (norm_mul _ _)
  rw [← Polynomial.coe_C, ← Polynomial.coe_mul, ← hs.eq_prod_roots, zero_add] at h
  exact hP.unique h |>.symm

/-- **Roots in the open disc.** A polynomial over an ultrametric normed field with lowest dominant
degree `l` at the radius `c > 0` has at most `l` roots `x` with `‖x‖ < c`, counted with
multiplicity. -/
theorem IsLowestDominant.card_filter_roots_norm_lt_le
    (hP : IsLowestDominant c l (P : PowerSeries K)) (hc : 0 < c) :
    (P.roots.filter (‖·‖ < c)).card ≤ l := by
  obtain ⟨q, hq, -, -⟩ := P.exists_prod_multiset_X_sub_C_mul
  have hq0 : (q : PowerSeries K) ≠ 0 := by
    rintro h
    rw [Polynomial.coe_eq_zero_iff.mp h, mul_zero] at hq
    exact hP.ne_zero (by rw [← hq, Polynomial.coe_zero])
  obtain ⟨e, he⟩ := exists_isLowestDominant hc (isRestricted_polynomial q) hq0
  have h := (isLowestDominant_multiset_prod_X_sub_C hc P.roots).mul he hc
    (hasGaussNorm_of_isRestricted (isRestricted_polynomial _))
    (hasGaussNorm_of_isRestricted (isRestricted_polynomial _)) (norm_mul _ _)
  rw [← Polynomial.coe_mul, hq] at h
  exact (hP.unique h).symm ▸ Nat.le_add_right _ _

/-- **Roots in the open disc of a split polynomial.** A split polynomial over an ultrametric normed
field with lowest dominant degree `l` at the radius `c > 0` has exactly `l` roots `x` with
`‖x‖ < c`, counted with multiplicity. -/
theorem IsLowestDominant.card_filter_roots_norm_lt_eq
    (hP : IsLowestDominant c l (P : PowerSeries K)) (hc : 0 < c) (hs : P.Splits) :
    (P.roots.filter (‖·‖ < c)).card = l := by
  have hlc : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr fun h ↦ hP.ne_zero (by rw [h, Polynomial.coe_zero])
  have h := (isLowestDominant_C hc hlc).mul (isLowestDominant_multiset_prod_X_sub_C hc P.roots) hc
    (isLowestDominant_C hc hlc).hasGaussNorm
    (hasGaussNorm_of_isRestricted (isRestricted_polynomial _)) (norm_mul _ _)
  rw [← Polynomial.coe_C, ← Polynomial.coe_mul, ← hs.eq_prod_roots, zero_add] at h
  exact hP.unique h |>.symm

/-- **Roots on the sphere of a split polynomial.** A split polynomial over an ultrametric normed
field distinguished of degree `d` and with lowest dominant degree `l` at the radius `c > 0` has
exactly `d - l` roots `x` with `‖x‖ = c`, counted with multiplicity. -/
theorem card_filter_roots_norm_eq (hd : IsDistinguished c d (P : PowerSeries K))
    (hl : IsLowestDominant c l (P : PowerSeries K)) (hc : 0 < c) (hs : P.Splits) :
    (P.roots.filter (‖·‖ = c)).card = d - l := by
  have h : P.roots.filter (‖·‖ < c) + P.roots.filter (‖·‖ = c) = P.roots.filter (‖·‖ ≤ c) := by
    rw [Multiset.filter_add_filter,
      (Multiset.filter_eq_nil (p := fun x ↦ ‖x‖ < c ∧ ‖x‖ = c)).mpr fun x _ h ↦ h.1.ne h.2,
      add_zero]
    exact Multiset.filter_congr fun x _ ↦ le_iff_lt_or_eq.symm
  have hcard := congrArg Multiset.card h
  rw [Multiset.card_add, hd.card_filter_roots_norm_le_eq hc hs,
    hl.card_filter_roots_norm_lt_eq hc hs] at hcard
  omega

end Field

end TauCeti.PowerSeries
