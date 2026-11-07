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

Over a complete nontrivially normed field with an ultrametric norm, the spectral value of a
monic irreducible polynomial of degree `d` is attained at the constant coefficient:
`spectralValue p = ‖a₀‖ ^ (1 / d)`. Indeed `p` is the minimal polynomial of the root of `p` in
`AdjoinRoot p`, whose spectral norm is by definition `spectralValue p`, and Mathlib's
`spectralNorm_eq_norm_coeff_zero_rpow` computes that spectral norm as `‖a₀‖ ^ (1 / d)`; the
latter rests on the fact that all roots of `p` have the same spectral norm. Combining the two,
`‖aᵢ‖ ≤ ‖a₀‖ ^ ((d - i) / d)` for every coefficient. Without normalising, an irreducible `f` of
degree `d` satisfies `‖aᵢ‖ ρ ^ i ≤ ‖a₀‖` whenever `‖a_d‖ ρ ^ d = ‖a₀‖`: in the language of Newton
polygons, an irreducible polynomial over a complete field is pure.

## Main results

* `Polynomial.Monic.norm_coeff_le_spectralValue_pow`: `‖aᵢ‖ ≤ spectralValue p ^ (d - i)` for a
  monic polynomial `p`.
* `Polynomial.spectralValue_eq_norm_coeff_zero_rpow_of_irreducible`: over a complete
  ultrametric field, a monic irreducible polynomial has spectral value `‖a₀‖ ^ (1 / d)`.
* `Polynomial.norm_coeff_mul_pow_le_norm_coeff_zero_of_irreducible`: over a complete
  ultrametric field, an irreducible polynomial satisfies `‖aᵢ‖ ρ ^ i ≤ ‖a₀‖` for the radius `ρ`
  with `‖a_d‖ ρ ^ d = ‖a₀‖`.

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

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Over a complete nontrivially normed field with an ultrametric norm, the spectral value of a
monic irreducible polynomial `p` of degree `d` is `‖p.coeff 0‖ ^ (1 / d)`. -/
theorem spectralValue_eq_norm_coeff_zero_rpow_of_irreducible {p : K[X]} (hm : p.Monic)
    (hp : Irreducible p) : spectralValue p = ‖p.coeff 0‖ ^ (1 / p.natDegree : ℝ) := by
  have : Fact (Irreducible p) := ⟨hp⟩
  have : Module.Finite K (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  have hmin : minpoly K (AdjoinRoot.root p) = p := by
    rw [AdjoinRoot.minpoly_root hp.ne_zero, hm.leadingCoeff, inv_one, C_1, mul_one]
  have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K (AdjoinRoot p) (AdjoinRoot.root p)
  unfold spectralNorm at h
  rwa [hmin] at h

/-- Over a complete nontrivially normed field with an ultrametric norm, let `f` be irreducible of
degree `d` and let `ρ ≥ 0` balance its leading and constant terms, `‖a_d‖ ρ ^ d = ‖a₀‖`. Then
every term satisfies `‖aᵢ‖ ρ ^ i ≤ ‖a₀‖`. -/
theorem norm_coeff_mul_pow_le_norm_coeff_zero_of_irreducible {f : K[X]} (hf : Irreducible f)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hconst : ‖f.leadingCoeff‖ * ρ ^ f.natDegree = ‖f.coeff 0‖) (i : ℕ) :
    ‖f.coeff i‖ * ρ ^ i ≤ ‖f.coeff 0‖ := by
  have hf0 := hf.ne_zero
  have hl0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
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

end Polynomial
