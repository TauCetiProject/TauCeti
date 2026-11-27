/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalPairModel
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree

/-!
# Short equations with rational two-torsion are rare

Among the integral pairs `(A, B)` with `max (4|A|³, 27B²) < X`, those for which `x³ + Ax + B`
has a rational root number at most `15 √X` once `X ≥ 1`
(`TauCeti.ncard_shortCurve_rat_root_le`). When `E_{A,B} : y² = x³ + Ax + B` is nonsingular, the
rational roots of the cubic are the `x`-coordinates of its rational points of order two
(`WeierstrassCurve.torsionBy_two_shortCurve_ne_bot_iff`), and in every case a rational point of
order two lies over a rational root, so the same bound holds for the pairs with
`E_{A,B}(ℚ)[2] ≠ 0` (`TauCeti.ncard_shortCurve_torsionBy_two_ne_bot_le`). The pairs of height
below `X` number on the order of `X^(5/6)`, so this bound is the numerator of the statement that
elliptic curves with a rational point of order two have density zero among all curves ordered by
height. That statement is how the contribution of these curves to the average size of the
`2`-Selmer group, and to the average `2`-rank of `E(ℚ)[2]`, is shown to vanish; the lower bound
for the number of pairs in the denominator is a separate count.

The argument is that of Bhargava and Shankar. A rational root of the monic integral cubic is an
integer `r`, and then `B = -r³ - Ar` is determined by `A` and `r`. The height bounds `|A|` by
`X^(1/3)`, and it bounds the root as well: `r⁶ ≤ 16 · max (4|A|³, 27B²)`
(`WeierstrassCurve.natAbs_pow_six_le_mul_shortEquationHeight`), so `|r| ≤ 2 X^(1/6)`. The pairs
`(A, r)` number at most `(2X^(1/3) + 1)(4X^(1/6) + 1) ≤ 15 X^(1/2)`.

## Main results

* `TauCeti.finite_shortCurve_rat_root` and `TauCeti.ncard_shortCurve_rat_root_le`: the pairs
  `(A, B)` of height below `X` for which `x³ + Ax + B` has a rational root form a finite set, of at
  most `15 √X` elements for `X ≥ 1`.
* `TauCeti.ncard_shortCurve_torsionBy_two_ne_bot_le`: the same bound for the pairs with
  `E_{A,B}(ℚ)[2] ≠ 0`.

## References

* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), 191–242, §1.1.
-/

public section

open Polynomial WeierstrassCurve

namespace TauCeti

/-- The pairs of height below `X` whose cubic has a rational root are, for `X = u⁶ ≥ 0`, images
of pairs `(A, r)` with `|A| ≤ u²` and `|r| ≤ 2u` under `(A, r) ↦ (A, -r³ - Ar)`. -/
private theorem setOf_shortCurve_rat_root_subset {u : ℝ} (hu : 0 ≤ u) :
    {ab : ℤ × ℤ | ((shortCurve ab.1 ab.2).shortEquationHeight : ℝ) < u ^ 6 ∧
        ∃ r : ℚ, r ^ 3 + ab.1 * r + ab.2 = 0} ⊆
      ((Finset.Icc (-(⌊u ^ 2⌋₊ : ℤ)) ⌊u ^ 2⌋₊ ×ˢ Finset.Icc (-(⌊2 * u⌋₊ : ℤ)) ⌊2 * u⌋₊).image
        fun p : ℤ × ℤ ↦ (p.1, -p.2 ^ 3 - p.1 * p.2) : Set (ℤ × ℤ)) := by
  rintro ⟨A, B⟩ ⟨hH, r, hr⟩
  -- the rational root is an integer `z`
  have hp : (X ^ 3 + C A * X + C B : ℤ[X]).Monic := by monicity!
  obtain ⟨z, rfl, -⟩ := exists_integer_of_is_root_of_monic hp (r := r) (by simpa using hr)
  have hz : z ^ 3 + A * z + B = 0 := by
    rw [algebraMap_int_eq, eq_intCast] at hr
    exact_mod_cast hr
  set H := (shortCurve A B).shortEquationHeight
  -- `|A|³ ≤ H < u⁶` and `|z|⁶ ≤ 16H < (2u)⁶`
  have hA : 4 * A.natAbs ^ 3 ≤ H := by
    simpa only [shortCurve_a₄] using
      (shortCurve A B).four_mul_natAbs_a₄_pow_three_le_shortEquationHeight
  have hAu : (A.natAbs : ℝ) ≤ u ^ 2 := by
    refine (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) three_ne_zero).mp ?_
    have : (4 * A.natAbs ^ 3 : ℝ) ≤ H := by exact_mod_cast hA
    nlinarith
  have hzu : (z.natAbs : ℝ) ≤ 2 * u := by
    refine (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num : 6 ≠ 0)).mp ?_
    have : (z.natAbs ^ 6 : ℝ) ≤ 16 * H := by
      exact_mod_cast natAbs_pow_six_le_mul_shortEquationHeight hz
    nlinarith [pow_nonneg hu 6]
  have hA' := Nat.le_floor hAu
  have hz' := Nat.le_floor hzu
  refine Finset.mem_image.mpr ⟨(A, z), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [Finset.mem_Icc]
    omega
  · rw [Finset.mem_Icc]
    omega
  · simp only [Prod.mk.injEq, true_and]
    linear_combination -hz

/-- **Finiteness of the short equations with a rational two-torsion root**: for every `X` only
finitely many pairs `(A, B)` of integers have `max (4|A|³, 27B²) < X` and `x³ + Ax + B` with a
rational root. -/
theorem finite_shortCurve_rat_root (X : ℝ) :
    {ab : ℤ × ℤ | ((shortCurve ab.1 ab.2).shortEquationHeight : ℝ) < X ∧
      ∃ r : ℚ, r ^ 3 + ab.1 * r + ab.2 = 0}.Finite := by
  set u := |X| ^ (6⁻¹ : ℝ)
  have hu6 : u ^ 6 = |X| := Real.rpow_inv_natCast_pow (abs_nonneg X) (by norm_num)
  refine (Finset.finite_toSet _).subset (subset_trans ?_
    (setOf_shortCurve_rat_root_subset (u := u) (by positivity)))
  rintro ab ⟨hH, hr⟩
  exact ⟨hH.trans_le (hu6 ▸ le_abs_self X), hr⟩

/-- **Short equations with a rational two-torsion root are rare**: for `X ≥ 1` at most `15 √X`
pairs `(A, B)` of integers have `max (4|A|³, 27B²) < X` and `x³ + Ax + B` with a rational root,
while the pairs of height below `X` number on the order of `X^(5/6)`. -/
theorem ncard_shortCurve_rat_root_le {X : ℝ} (hX : 1 ≤ X) :
    ({ab : ℤ × ℤ | ((shortCurve ab.1 ab.2).shortEquationHeight : ℝ) < X ∧
      ∃ r : ℚ, r ^ 3 + ab.1 * r + ab.2 = 0}.ncard : ℝ) ≤ 15 * √X := by
  set u := X ^ (6⁻¹ : ℝ)
  have hu6 : u ^ 6 = X := Real.rpow_inv_natCast_pow (by linarith) (by norm_num)
  have hu : 1 ≤ u := Real.one_le_rpow hX (by norm_num)
  have hsqrt : √X = u ^ 3 := by
    rw [← hu6, show u ^ 6 = (u ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsub := setOf_shortCurve_rat_root_subset (u := u) (by positivity)
  rw [hu6] at hsub
  refine (Nat.cast_le.mpr ((Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans_eq
    (Set.ncard_coe_finset _))).trans ?_
  refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
  -- the box has `(2⌊u²⌋ + 1)(2⌊2u⌋ + 1) ≤ (2u² + 1)(4u + 1) ≤ 15u³` elements
  have hcard (N : ℕ) : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  rw [Finset.card_product, hcard, hcard, hsqrt]
  have h₁ : (⌊u ^ 2⌋₊ : ℝ) ≤ u ^ 2 := Nat.floor_le (by positivity)
  have h₂ : (⌊2 * u⌋₊ : ℝ) ≤ 2 * u := Nat.floor_le (by positivity)
  push_cast
  calc (2 * (⌊u ^ 2⌋₊ : ℝ) + 1) * (2 * ⌊2 * u⌋₊ + 1) ≤ (2 * u ^ 2 + 1) * (2 * (2 * u) + 1) := by
        gcongr
    _ ≤ 15 * u ^ 3 := by nlinarith [pow_le_pow_left₀ zero_le_one hu 3]

/-- **Elliptic curves with a rational point of order two are rare**: for `X ≥ 1` at most `15 √X`
pairs `(A, B)` of integers have `max (4|A|³, 27B²) < X` and a point of order two on
`y² = x³ + Ax + B` over `ℚ`. -/
theorem ncard_shortCurve_torsionBy_two_ne_bot_le {X : ℝ} (hX : 1 ≤ X) :
    ({ab : ℤ × ℤ | ((shortCurve ab.1 ab.2).shortEquationHeight : ℝ) < X ∧
      AddSubgroup.torsionBy (shortCurve (ab.1 : ℚ) ab.2).toAffine.Point 2 ≠ ⊥}.ncard : ℝ) ≤
        15 * √X := by
  refine (Nat.cast_le.mpr (Set.ncard_le_ncard ?_ (finite_shortCurve_rat_root X))).trans
    (ncard_shortCurve_rat_root_le hX)
  rintro ab ⟨hH, h⟩
  exact ⟨hH, exists_root_of_torsionBy_two_shortCurve_ne_bot h⟩

end TauCeti
