/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Factorization
public import TauCeti.NumberTheory.Padics.LogGauge
import TauCeti.NumberTheory.NewtonPolygon.Irreducible
import Mathlib.Algebra.Polynomial.UnitTrinomial

/-!
# Explicit Newton slope factorisations over `ℚ_[p]`

Concrete instances of the Newton slope factorisation and irreducibility theorems on `ℚ_[p]`,
with respect to the real `p`-adic additive valuation `TauCeti.padicRealValuation p` normalised by
`v(p) = 1`:

* The quadratic polynomial `1 + p X + p ^ 3 X ^ 2` has Newton polygon heights `0, 1, 3` at
  `0, 1, 2`, so its finite Newton slopes are `1` and `2`. Since these slopes have multiplicity
  one, `1 + p X + p ^ 3 X ^ 2` splits into linear factors over `ℚ_[p]` and factors uniquely into
  coprime constant-one linear polynomials of slopes `1` and `2`, whose roots in `ℚ_[p]` have
  norms `p` and `p ^ 2`.
* By contrast, `1 - p⁻¹ X ^ 2` is pure of slope `-1 / 2` with multiplicity `2`. Since `-1` is
  coprime to `2`, it is irreducible over `ℚ_[p]` (so it does not split over `ℚ_[p]`), while it
  splits into linear factors in any field extension of `ℚ_[p]` containing a square root of `p`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
-/

public section

open Polynomial TauCeti

namespace TauCeti.NewtonPolygonFactorizationExample

section DistinctSlopes

variable {p : ℕ} [Fact p.Prime]

/-- The polynomial `1 + p X + p ^ 3 X ^ 2` is the trinomial with exponents `0, 1, 2` and
coefficients `1, p, p ^ 3`. -/
private theorem one_add_p_X_add_p_cube_X_sq_eq_trinomial :
    (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2 : ℚ_[p][X]) =
      trinomial 0 1 2 1 (p : ℚ_[p]) ((p : ℚ_[p]) ^ 3) := by
  simp [trinomial]

/-- The constant coefficient of `1 + p X + p ^ 3 X ^ 2` is `1`. -/
private theorem coeff_zero_one_add_p_X_add_p_cube_X_sq :
    (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2 : ℚ_[p][X]).coeff 0 = 1 := by
  rw [one_add_p_X_add_p_cube_X_sq_eq_trinomial]
  exact trinomial_trailing_coeff' (by decide) (by decide)

/-- The linear coefficient of `1 + p X + p ^ 3 X ^ 2` is `p`. -/
private theorem coeff_one_one_add_p_X_add_p_cube_X_sq :
    (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2 : ℚ_[p][X]).coeff 1 = (p : ℚ_[p]) := by
  rw [one_add_p_X_add_p_cube_X_sq_eq_trinomial]
  exact trinomial_middle_coeff (by decide) (by decide)

/-- The quadratic coefficient of `1 + p X + p ^ 3 X ^ 2` is `p ^ 3`. -/
private theorem coeff_two_one_add_p_X_add_p_cube_X_sq :
    (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2 : ℚ_[p][X]).coeff 2 =
      (p : ℚ_[p]) ^ 3 := by
  rw [one_add_p_X_add_p_cube_X_sq_eq_trinomial]
  exact trinomial_leading_coeff' (by decide) (by decide)

/-- The coefficients of `1 + p X + p ^ 3 X ^ 2` vanish above degree `2`. -/
private theorem coeff_eq_zero_one_add_p_X_add_p_cube_X_sq {n : ℕ} (hn : 2 < n) :
    (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2 : ℚ_[p][X]).coeff n = 0 := by
  simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
  have h0 : n ≠ 0 := by omega
  have h1 : 1 ≠ n := by omega
  have h2 : n ≠ 2 := by omega
  simp [h0, h1, h2]

/-- Over `ℚ_[p]`, the quadratic polynomial `1 + p X + p ^ 3 X ^ 2` has finite Newton slopes
`{1, 2}`. -/
theorem newtonSlopes_one_add_p_X_add_p_cube_X_sq :
    (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2 : ℚ_[p][X]).newtonSlopes
      (padicRealValuation p) = {1, 2} := by
  set v := padicRealValuation p
  set f : ℚ_[p][X] := 1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp3_ne : ((p : ℚ_[p]) ^ 3) ≠ 0 := pow_ne_zero 3 hp_ne
  have hc0 : f.coeff 0 = 1 := coeff_zero_one_add_p_X_add_p_cube_X_sq
  have hc1 : f.coeff 1 = (p : ℚ_[p]) := coeff_one_one_add_p_X_add_p_cube_X_sq
  have hc2 : f.coeff 2 = (p : ℚ_[p]) ^ 3 := coeff_two_one_add_p_X_add_p_cube_X_sq
  have hc_gt {n : ℕ} (hn : 2 < n) : f.coeff n = 0 := coeff_eq_zero_one_add_p_X_add_p_cube_X_sq hn
  have hdeg : f.natDegree = 2 := natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun n hn => hc_gt hn) (hc2 ▸ hp3_ne)
  have htr_deg : f.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simp [hc0])
  have hnp0 : f.newtonPolygon v 0 = 0 := by simp [hc0]
  have hnp2 : f.newtonPolygon v 2 = (3 : ℝ) := by
    rw [newtonPolygon_eq_of_natDegree_le f v hdeg.le, hc2, v.map_pow, padicRealValuation_p]
    norm_num
  have hnp1 : f.newtonPolygon v 1 = 1 := by
    refine le_antisymm ?_ ?_
    · simpa [hc1, v] using f.newtonPolygon_le v 1
    · have hminor : (fun n : ℕ => ((0 + 1 * (n : ℝ) : ℝ) : WithTop ℝ)) ≤ f.newtonPolygon v := by
        refine le_newtonPolygon (isConvexSeq_affine 0 1) fun n => ?_
        match n with
        | 0 => simp [hc0]
        | 1 => simp [hc1, v]
        | 2 =>
          rw [hc2, v.map_pow, padicRealValuation_p]
          exact WithTop.coe_le_coe.mpr (by norm_num)
        | n + 3 =>
          rw [hc_gt (by omega), v.map_zero]
          exact le_top
      simpa using hminor 1
  have hedges : (f.finite_finiteEdges_newtonPolygon v).toFinset = {0, 1} := by
    ext i
    simp only [Set.Finite.mem_toFinset,
      finiteEdges_newtonPolygon f v (fun _ => v.top_iff.mp), htr_deg, hdeg, Set.mem_Ico,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [newtonSlopes_def, hedges]
  have h01 : (0 : ℕ) ∉ ({1} : Finset ℕ) := by decide
  rw [Finset.insert_val_of_notMem h01, Finset.singleton_val, Multiset.map_cons,
    Multiset.map_singleton]
  have hs0 : unitSlope (f.newtonPolygon v) 0 = 1 := by
    rw [unitSlope_def, zero_add, hnp1, hnp0, WithTop.untop₀_one, WithTop.untop₀_zero, sub_zero]
  have hs1 : unitSlope (f.newtonPolygon v) 1 = 2 := by
    rw [unitSlope_def, hnp2, hnp1, WithTop.untop₀_coe, WithTop.untop₀_one]
    norm_num
  rw [hs0, hs1]
  rfl

/-- Over `ℚ_[p]`, `1 + p X + p ^ 3 X ^ 2` splits into linear factors, because its finite Newton
slopes `1` and `2` are distinct. -/
theorem splits_one_add_p_X_add_p_cube_X_sq :
    (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2 : ℚ_[p][X]).Splits := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  refine splits_of_nodup_newtonSlopes (padicRealValuation p) hp1
    (fun _ hx => norm_eq_rpow_neg_padicRealValuation hx) ?_
  rw [newtonSlopes_one_add_p_X_add_p_cube_X_sq]
  simp

/-- Over `ℚ_[p]`, `1 + p X + p ^ 3 X ^ 2` factors as a product `g₁ * g₂` of coprime constant-one
linear factors pure of slopes `1` and `2`, whose roots in `ℚ_[p]` have norms `p` and `p ^ 2`. -/
theorem exists_coprime_linear_factors_one_add_p_X_add_p_cube_X_sq :
    ∃ g₁ g₂ : ℚ_[p][X], g₁.coeff 0 = 1 ∧ g₂.coeff 0 = 1 ∧
      g₁.natDegree = 1 ∧ g₂.natDegree = 1 ∧ IsCoprime g₁ g₂ ∧
      g₁ * g₂ = 1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2 ∧
      (∀ x : ℚ_[p], g₁.eval x = 0 → ‖x‖ = (p : ℝ)) ∧
      (∀ x : ℚ_[p], g₂.eval x = 0 → ‖x‖ = (p : ℝ) ^ 2) := by
  set v := padicRealValuation p
  set f : ℚ_[p][X] := 1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hv0 : ∀ x : ℚ_[p], v x = ⊤ → x = 0 := fun _ => v.top_iff.mp
  have hf0 : f.coeff 0 = 1 := coeff_zero_one_add_p_X_add_p_cube_X_sq
  obtain ⟨g, hg⟩ := exists_isPureSlopeFactorization v hp1
    (fun _ hx => norm_eq_rpow_neg_padicRealValuation hx) hf0
  have hdeg1 : (g 1).natDegree = 1 := by
    rw [hg.natDegree_apply hv0 1, newtonSlopes_one_add_p_X_add_p_cube_X_sq]
    simp
  have hdeg2 : (g 2).natDegree = 1 := by
    rw [hg.natDegree_apply hv0 2, newtonSlopes_one_add_p_X_add_p_cube_X_sq]
    simp
  have htoFinset : (f.newtonSlopes v).toFinset = {1, 2} := by
    rw [newtonSlopes_one_add_p_X_add_p_cube_X_sq]
    ext m
    simp
  have hprod : g 1 * g 2 = f := by
    have hp := hg.prod_toFinset_eq hv0
    rwa [htoFinset, Finset.prod_pair (by norm_num)] at hp
  refine ⟨g 1, g 2, hg.coeff_zero 1, hg.coeff_zero 2, hdeg1, hdeg2,
    hg.pairwise_isCoprime (by norm_num), hprod, fun x hx => ?_, fun x hx => ?_⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      rw [eval_eq_sum_range, Finset.sum_eq_single 0
        (fun i _ hi => by simp [zero_pow hi]) (by simp)] at hx
      simp [hg.coeff_zero 1] at hx
    have hnorm := norm_eq_rpow_of_forall_mem_newtonSlopes_eq (L := ℚ_[p]) v hp1
      (fun _ hy => norm_eq_rpow_neg_padicRealValuation hy) (hg.apply_ne_zero 1)
      (hg.newtonSlopes_eq 1) hx0 (by simpa using hx)
    rwa [Real.rpow_one] at hnorm
  · have hx0 : x ≠ 0 := by
      rintro rfl
      rw [eval_eq_sum_range, Finset.sum_eq_single 0
        (fun i _ hi => by simp [zero_pow hi]) (by simp)] at hx
      simp [hg.coeff_zero 2] at hx
    have hnorm := norm_eq_rpow_of_forall_mem_newtonSlopes_eq (L := ℚ_[p]) v hp1
      (fun _ hy => norm_eq_rpow_neg_padicRealValuation hy) (hg.apply_ne_zero 2)
      (hg.newtonSlopes_eq 2) hx0 (by simpa using hx)
    norm_num at hnorm
    exact hnorm

end DistinctSlopes

section PureIrreducible

variable {p : ℕ} [Fact p.Prime]

/-- Over `ℚ_[p]`, `1 - p⁻¹ X ^ 2` is pure of slope `-1 / 2` with multiplicity `2`. -/
theorem newtonSlopes_one_sub_inv_p_X_sq :
    (1 - C (p : ℚ_[p])⁻¹ * X ^ 2 : ℚ_[p][X]).newtonSlopes (padicRealValuation p) =
      {-1 / 2, -1 / 2} := by
  set v := padicRealValuation p
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hscale : C (-(p : ℚ_[p])) * (1 - C (p : ℚ_[p])⁻¹ * X ^ 2) = X ^ 2 - C (p : ℚ_[p]) := by
    calc C (-(p : ℚ_[p])) * (1 - C (p : ℚ_[p])⁻¹ * X ^ 2)
        = C ((p : ℚ_[p]) * (p : ℚ_[p])⁻¹) * X ^ 2 - C (p : ℚ_[p]) := by
          simp only [map_neg, map_mul]
          ring
      _ = X ^ 2 - C (p : ℚ_[p]) := by rw [mul_inv_cancel₀ hp_ne, map_one, one_mul]
  have hmonic : (X ^ 2 - C (p : ℚ_[p]) : ℚ_[p][X]).Monic :=
    monic_X_pow_sub_C (p : ℚ_[p]) (by decide)
  have hdeg : (X ^ 2 - C (p : ℚ_[p]) : ℚ_[p][X]).natDegree = 2 :=
    natDegree_X_pow_sub_C (n := 2) (a := (p : ℚ_[p]))
  have heis := newtonSlopes_eq_replicate_of_eisenstein
    (f := (X ^ 2 - C (p : ℚ_[p]) : ℚ_[p][X])) (v := v)
    (by rw [hmonic.leadingCoeff, v.map_one]) (by simp [v]) fun n hn0 hnd => by
      rw [hdeg] at hnd
      have hn1 : n = 1 := by omega
      subst hn1
      simp
  rw [hdeg] at heis
  rw [← newtonSlopes_C_mul _ v (v.ne_top_iff.mpr (neg_ne_zero.mpr hp_ne)), hscale, heis]
  norm_num [Multiset.replicate_succ]

private theorem natDegree_one_sub_inv_p_X_sq :
    (1 - C (p : ℚ_[p])⁻¹ * X ^ 2 : ℚ_[p][X]).natDegree = 2 := by
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hdeg : (C (p : ℚ_[p])⁻¹ * X ^ 2 : ℚ_[p][X]).natDegree = 2 :=
    natDegree_C_mul_X_pow 2 (p : ℚ_[p])⁻¹ (inv_ne_zero hp_ne)
  rw [natDegree_sub_eq_right_of_natDegree_lt (by simp [hdeg]), hdeg]

/-- Over `ℚ_[p]`, `1 - p⁻¹ X ^ 2` is irreducible, by the Newton polygon irreducibility criterion. -/
theorem irreducible_one_sub_inv_p_X_sq :
    Irreducible (1 - C (p : ℚ_[p])⁻¹ * X ^ 2 : ℚ_[p][X]) := by
  refine irreducible_of_forall_mem_newtonSlopes_eq_div (v := padicRealValuation p)
    (fun _ hx => exists_int_padicRealValuation hx)
    (by simp only [coeff_sub, coeff_one, coeff_C_mul, coeff_X_pow]; norm_num)
    (by rw [natDegree_one_sub_inv_p_X_sq]; decide) (a := -1)
    (by rw [natDegree_one_sub_inv_p_X_sq]; decide) fun m hm => ?_
  rw [newtonSlopes_one_sub_inv_p_X_sq] at hm
  rw [natDegree_one_sub_inv_p_X_sq]
  rcases Multiset.mem_cons.mp hm with rfl | hm'
  · norm_num
  · rw [Multiset.mem_singleton.mp hm']
    norm_num

/-- Over `ℚ_[p]`, `1 - p⁻¹ X ^ 2` does not split into linear factors. -/
theorem not_splits_one_sub_inv_p_X_sq :
    ¬ (1 - C (p : ℚ_[p])⁻¹ * X ^ 2 : ℚ_[p][X]).Splits := by
  intro hsp
  have h1 := hsp.natDegree_eq_one_of_irreducible irreducible_one_sub_inv_p_X_sq
  rw [natDegree_one_sub_inv_p_X_sq] at h1
  omega

/-- In any field extension `L` of `ℚ_[p]` containing a square root `π` of `p`, the polynomial
`1 - p⁻¹ X ^ 2` splits into linear factors `(1 - π⁻¹ X) * (1 + π⁻¹ X)`. -/
theorem splits_map_one_sub_inv_p_X_sq_of_sq_eq {L : Type*} [Field L] [Algebra ℚ_[p] L]
    {π : L} (hπ : π ^ 2 = algebraMap ℚ_[p] L p) :
    ((1 - C (p : ℚ_[p])⁻¹ * X ^ 2 : ℚ_[p][X]).map (algebraMap ℚ_[p] L)).Splits := by
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hπ_ne : π ≠ 0 := by
    rintro rfl
    have h0 : algebraMap ℚ_[p] L p = 0 := by simpa using hπ.symm
    exact hp_ne ((injective_iff_map_eq_zero _).mp (algebraMap ℚ_[p] L).injective _ h0)
  have hinv : C (algebraMap ℚ_[p] L p)⁻¹ = (C π⁻¹ : L[X]) * C π⁻¹ := by
    rw [← map_mul, ← mul_inv, ← sq, hπ]
  have hfact : (1 - C (p : ℚ_[p])⁻¹ * X ^ 2 : ℚ_[p][X]).map (algebraMap ℚ_[p] L) =
      (1 - C π⁻¹ * X) * (1 + C π⁻¹ * X) := by
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_pow,
      map_C, map_X, map_inv₀, hinv]
    ring
  rw [hfact]
  refine (Splits.of_natDegree_le_one ?_).mul (Splits.of_natDegree_le_one ?_)
  · compute_degree!
  · compute_degree!

end PureIrreducible

end TauCeti.NewtonPolygonFactorizationExample
