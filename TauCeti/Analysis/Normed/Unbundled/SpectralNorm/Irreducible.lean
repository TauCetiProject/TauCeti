/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The spectral value of an irreducible polynomial

The spectral value of a monic polynomial `p = X ^ d + ∑_{i < d} aᵢ X ^ i` over a seminormed ring
is `spectralValue p = max_{i < d} ‖aᵢ‖ ^ (1 / (d - i))`. By definition every coefficient then
satisfies `‖aᵢ‖ ≤ spectralValue p ^ (d - i)`.

Over a complete ultrametric normed field (including trivially normed fields), the spectral value of
a monic irreducible polynomial of degree `d` is attained at the constant coefficient:
`spectralValue p = ‖a₀‖ ^ (1 / d)`. When the field is nontrivially normed, `p` is the minimal
polynomial of the root of `p` in `AdjoinRoot p`, whose spectral norm is by definition
`spectralValue p`, and Mathlib's `spectralNorm_eq_norm_coeff_zero_rpow` computes that spectral norm
as `‖a₀‖ ^ (1 / d)`; when the norm on `K` is trivial, every nonzero element has norm `1` and a
monic irreducible polynomial with vanishing constant term is `X`. Combining the two,
`‖aᵢ‖ ≤ ‖a₀‖ ^ ((d - i) / d)` for every coefficient. Without normalising, an irreducible `f` of
degree `d` satisfies `‖aᵢ‖ ρ ^ i ≤ ‖a₀‖` whenever `‖a_d‖ ρ ^ d = ‖a₀‖`: in the language of Newton
polygons, an irreducible polynomial over a complete field is pure.

## Main results

* `Polynomial.Monic.norm_coeff_le_spectralValue_pow`: `‖aᵢ‖ ≤ spectralValue p ^ (d - i)` for a
  monic polynomial `p`.
* `Polynomial.spectralValue_eq_norm_coeff_zero_rpow_of_irreducible`: over a complete
  ultrametric normed field, a monic irreducible polynomial has spectral value `‖a₀‖ ^ (1 / d)`.
* `Polynomial.norm_coeff_mul_pow_le_norm_coeff_zero_of_irreducible`: over a complete
  ultrametric normed field, an irreducible polynomial satisfies `‖aᵢ‖ ρ ^ i ≤ ‖a₀‖` for the radius
  `ρ` with `‖a_d‖ ρ ^ d = ‖a₀‖`.
* `Polynomial.Monic.norm_inv_coeff_zero_mul_coeff_le_inv_spectralValue_pow_of_irreducible`: over a
  complete ultrametric normed field, a monic irreducible polynomial satisfies
  `‖(p.coeff 0)⁻¹ * p.coeff k‖ ≤ (spectralValue p)⁻¹ ^ k`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.1.2 and §3.2.1.
-/

public section

namespace Polynomial

/-- Every coefficient of a monic polynomial `p` of degree `d` is bounded by a power of its
spectral value: `‖p.coeff i‖ ≤ spectralValue p ^ (d - i)`. -/
theorem Monic.norm_coeff_le_spectralValue_pow {R : Type*} [SeminormedRing R] [NormOneClass R]
    {p : R[X]} (hp : p.Monic) (i : ℕ) : ‖p.coeff i‖ ≤ spectralValue p ^ (p.natDegree - i) := by
  rcases lt_trichotomy i p.natDegree with hi | rfl | hi
  · have h : spectralValueTerms p i ≤ spectralValue p := le_ciSup (spectralValueTerms_bddAbove p) i
    rw [spectralValueTerms_of_lt_natDegree _ hi] at h
    have hdi : (p.natDegree - i : ℝ) = ((p.natDegree - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hi.le]
    rw [one_div, hdi, Real.rpow_inv_le_iff_of_pos (norm_nonneg _) (spectralValue_nonneg p)
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hi)), Real.rpow_natCast] at h
    exact h
  · simp [hp.coeff_natDegree]
  · simpa [coeff_eq_zero_of_natDegree_lt hi] using pow_nonneg (spectralValue_nonneg p) _

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Over a complete ultrametric normed field (possibly trivially normed), the spectral value of a
monic irreducible polynomial `p` of degree `d` is `‖p.coeff 0‖ ^ (1 / d)`. -/
theorem spectralValue_eq_norm_coeff_zero_rpow_of_irreducible {p : K[X]} (hm : p.Monic)
    (hp : Irreducible p) : spectralValue p = ‖p.coeff 0‖ ^ (1 / p.natDegree : ℝ) := by
  by_cases hK : ∃ c : K, c ≠ 0 ∧ ‖c‖ ≠ 1
  · let := NontriviallyNormedField.ofNormNeOne hK
    have : Fact (Irreducible p) := ⟨hp⟩
    have : Module.Finite K (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite
    have hmin : minpoly K (AdjoinRoot.root p) = p := by
      rw [AdjoinRoot.minpoly_root hp.ne_zero, hm.leadingCoeff, inv_one, C_1, mul_one]
    have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K (AdjoinRoot p) (AdjoinRoot.root p)
    unfold spectralNorm at h
    rwa [hmin] at h
  · push Not at hK
    by_cases ha0 : p.coeff 0 = 0
    · -- A monic irreducible polynomial divisible by `X` is equal to `X`.
      obtain ⟨q, hq⟩ := X_dvd_iff.mpr ha0
      have hqu : IsUnit q := (hp.isUnit_or_isUnit hq).resolve_left irreducible_X.not_isUnit
      have hqm : q.Monic := monic_X.of_mul_monic_left (hq ▸ hm)
      have hq1 : q = 1 := hqm.natDegree_eq_zero.mp (natDegree_eq_zero_of_isUnit hqu)
      have hpX : p = X := by rw [hq, hq1, mul_one]
      have hspecX : spectralValue (X : K[X]) = 0 := by simpa using spectralValue_X_pow (R := K) 1
      rw [hpX, hspecX, coeff_X_zero, norm_zero, natDegree_X, Nat.cast_one, div_one, Real.rpow_one]
    · rw [hK _ ha0, Real.one_rpow]
      refine le_antisymm (ciSup_le fun i ↦ ?_) ?_
      · by_cases hi : i < p.natDegree
        · rw [spectralValueTerms_of_lt_natDegree p hi]
          have hle : ‖p.coeff i‖ ≤ 1 := by
            by_cases hci : p.coeff i = 0
            · simp [hci]
            · exact (hK _ hci).le
          exact Real.rpow_le_one (norm_nonneg _) hle
            (one_div_nonneg.mpr (sub_nonneg.mpr (Nat.cast_le.mpr hi.le)))
        · rw [spectralValueTerms_of_natDegree_le p (not_lt.mp hi)]
          exact zero_le_one
      · refine le_ciSup_of_le (spectralValueTerms_bddAbove p) 0 ?_
        rw [spectralValueTerms_of_lt_natDegree p hp.natDegree_pos, hK _ ha0, Real.one_rpow]

/-- Over a complete ultrametric normed field (possibly trivially normed), let `f` be irreducible of
degree `d` and let `ρ` balance its leading and constant terms, `‖a_d‖ ρ ^ d = ‖a₀‖`. Then
every term satisfies `‖aᵢ‖ ρ ^ i ≤ ‖a₀‖`. -/
theorem norm_coeff_mul_pow_le_norm_coeff_zero_of_irreducible {f : K[X]} (hf : Irreducible f)
    {ρ : ℝ} (hconst : ‖f.leadingCoeff‖ * ρ ^ f.natDegree = ‖f.coeff 0‖) (i : ℕ) :
    ‖f.coeff i‖ * ρ ^ i ≤ ‖f.coeff 0‖ := by
  have hf0 := hf.ne_zero
  have hl0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  -- A negative radius is replaced by its absolute value.
  have hρn : 0 ≤ ρ ^ f.natDegree :=
    (mul_nonneg_iff_of_pos_left (norm_pos_iff.mpr hl0)).1 (hconst ▸ norm_nonneg _)
  obtain ⟨ρ, hρ, hconst, hρi⟩ : ∃ r : ℝ, 0 ≤ r ∧
      ‖f.leadingCoeff‖ * r ^ f.natDegree = ‖f.coeff 0‖ ∧ ρ ^ i ≤ r ^ i :=
    ⟨|ρ|, abs_nonneg ρ, by rwa [pow_abs, abs_of_nonneg hρn],
      (le_abs_self _).trans_eq (pow_abs ρ i).symm⟩
  refine le_trans (mul_le_mul_of_nonneg_left hρi (norm_nonneg _)) ?_
  -- The monic normalisation `g` of `f` has spectral value `ρ`.
  set g := f * C f.leadingCoeff⁻¹
  have hg : g.Monic := monic_mul_leadingCoeff_inv hf0
  have hgd : g.natDegree = f.natDegree := natDegree_mul_leadingCoeff_inv f hf0
  have hgcoeff (n : ℕ) : ‖g.coeff n‖ * ‖f.leadingCoeff‖ = ‖f.coeff n‖ := by
    rw [coeff_mul_C, norm_mul, norm_inv, inv_mul_cancel_right₀ (norm_ne_zero_iff.mpr hl0)]
  have hg0 : ‖g.coeff 0‖ = ρ ^ f.natDegree := by
    apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hl0)
    rw [hgcoeff, ← hconst, mul_comm]
  have hspec : spectralValue g = ρ := by
    rw [spectralValue_eq_norm_coeff_zero_rpow_of_irreducible hg
      (irreducible_mul_leadingCoeff_inv.mpr hf), hgd, one_div, hg0]
    exact Real.pow_rpow_inv_natCast hρ hf.natDegree_pos.ne'
  rcases le_or_gt i f.natDegree with hi | hi
  · calc ‖f.coeff i‖ * ρ ^ i
        = ‖g.coeff i‖ * ‖f.leadingCoeff‖ * ρ ^ i := by rw [hgcoeff]
      _ ≤ ρ ^ (f.natDegree - i) * ‖f.leadingCoeff‖ * ρ ^ i := by
        gcongr
        simpa [hspec, hgd] using hg.norm_coeff_le_spectralValue_pow i
      _ = ‖f.coeff 0‖ := by
        rw [← hconst, mul_comm _ ‖_‖, mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  · rw [coeff_eq_zero_of_natDegree_lt hi, norm_zero, zero_mul]
    exact norm_nonneg _

/-- Over a complete ultrametric normed field (possibly trivially normed), every coefficient of a
monic irreducible polynomial `p` satisfies
`‖(p.coeff 0)⁻¹ * p.coeff k‖ ≤ (spectralValue p)⁻¹ ^ k`. -/
theorem Monic.norm_inv_coeff_zero_mul_coeff_le_inv_spectralValue_pow_of_irreducible
    {p : K[X]} (hm : p.Monic) (hp : Irreducible p) (k : ℕ) :
    ‖(p.coeff 0)⁻¹ * p.coeff k‖ ≤ (spectralValue p)⁻¹ ^ k := by
  by_cases ha0 : p.coeff 0 = 0
  · rw [ha0, inv_zero, zero_mul, norm_zero]
    exact pow_nonneg (inv_nonneg.mpr (spectralValue_nonneg p)) k
  · have hdR : (p.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.natDegree_pos.ne'
    have ha0_pos : 0 < ‖p.coeff 0‖ := norm_pos_iff.mpr ha0
    have hspec_pow : spectralValue p ^ p.natDegree = ‖p.coeff 0‖ := by
      rw [spectralValue_eq_norm_coeff_zero_rpow_of_irreducible hm hp,
        ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hdR,
        Real.rpow_one]
    have hspec_pos : 0 < spectralValue p := by
      by_contra h
      have h0 : spectralValue p = 0 := le_antisymm (not_lt.mp h) (spectralValue_nonneg p)
      rw [h0, zero_pow hp.natDegree_pos.ne'] at hspec_pow
      exact ha0_pos.ne hspec_pow
    have hconst : ‖p.leadingCoeff‖ * spectralValue p ^ p.natDegree = ‖p.coeff 0‖ := by
      rw [hm.leadingCoeff, norm_one, one_mul, hspec_pow]
    have hmul : ‖p.coeff k‖ * spectralValue p ^ k ≤ ‖p.coeff 0‖ :=
      norm_coeff_mul_pow_le_norm_coeff_zero_of_irreducible hp hconst k
    rw [norm_mul, norm_inv, inv_pow, ← div_eq_inv_mul, div_le_iff₀ ha0_pos]
    calc
      ‖p.coeff k‖ = ‖p.coeff k‖ * spectralValue p ^ k * (spectralValue p ^ k)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hspec_pos.ne'), mul_one]
      _ ≤ ‖p.coeff 0‖ * (spectralValue p ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = (spectralValue p ^ k)⁻¹ * ‖p.coeff 0‖ := mul_comm _ _

end Polynomial
