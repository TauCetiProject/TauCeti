/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder.Relations
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection
public import TauCeti.NumberTheory.LcmUpto
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.StageTwo.Product
import TauCeti.Data.Int.Round

/-!
# Stage-1 and stage-2 factor detection from Montgomery ladder derivations

Let `p ∣ n` be prime. Reducing a binary Montgomery-ladder derivation `LadderRel N D S m R T`
over `ZMod n` along `ZMod.castHom` produces a derivation over `ZMod p` (`LadderRel.map`).
When the reduced doubling constants satisfy `4 * N = (A + 2) * D` and `S` represents a native
point `P` of `model A B` over `ZMod p`, the reduced outputs have vanishing cross difference
with `[m]P` and `[m + 1]P` (`LadderRel.cross_coordinates_castHom_eq_zero`), with no
characteristic, ellipticity, or nonvanishing restriction.

This connects polynomial Montgomery-ladder derivations over a composite modulus directly to
both stages of the elliptic-curve factorization method:

* **Stage 1 (`LadderRel.prime_dvd_gcd_of_addOrderOf_dvd`,
  `LadderRel.prime_dvd_gcd_lcmUpto_of_isPrimePow_le`).** Whenever `addOrderOf P ∣ m` — in
  particular when `m = B₁.lcmUpto` and every prime-power divisor of `addOrderOf P` is at most
  `B₁` — `p` divides `Nat.gcd R.z.val n`.
* **Exact stage-1 divisibility criterion
  (`LadderRel.prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint`,
  `LadderRel.prime_dvd_gcd_lcmUpto_iff_isPrimePow_le`).** Under `B ≠ 0`, nonzero reduced `D`,
  and a nonzero reduced seed `S` representing `P`, `p ∣ Nat.gcd R.z.val n` holds if and only if
  `addOrderOf P ∣ m` or `P` is the distinguished two-torsion point `(0, 0)` (where odd-step
  differential addition degenerates to `(0, 0)` even when `[m]P ≠ 0`). No `p ≠ 2` hypothesis is
  needed: for `p = 2`, `B ≠ 0` and `4 * N = (A + 2) * D` with `D ≠ 0` force `B = 1` and `A = 0`,
  where `(1, 0)` is singular and every native point is either infinity or `(0, 0)`.
  When `2 ∣ m` — in particular for `B₁.lcmUpto` with `2 ≤ B₁` — `addOrderOf (0, 0) = 2`
  absorbs the two-torsion disjunct, so stage-1 detection holds if and only if `addOrderOf P`
  is `B₁`-powersmooth.
* **Proper-factor certification (`LadderRel.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd`).**
  For positive `n`, annihilation modulo one prime divisor `p ∣ n` together with survival away
  from `(0, 0)` modulo another prime divisor `q ∣ n` (with `B' ≠ 0`, the reduced doubling
  relation, and nonzero reductions of `D` and `S` modulo `q`) certifies `1 < Nat.gcd R.z.val n`
  and `Nat.gcd R.z.val n < n`.
* **Stage 2 (`LadderRel.prime_dvd_gcd_cross_of_addOrderOf_dvd_mul`,
  `LadderRel.exists_two_mul_le_and_prime_dvd_gcd_cross`,
  `LadderRel.one_lt_gcd_prod_cross_and_lt_of_addOrderOf_dvd_mul`).** Composing a stage-1
  derivation for `M` with giant-step and baby-step derivations for `i * w` and `j` detects `p`
  in the cross-difference gcd (and in any stage-2 batch product gcd) whenever
  `addOrderOf P ∣ M * q` and `q = i * w ± j`.

## References

* H. W. Lenstra Jr., *Factoring integers with elliptic curves*, Ann. of Math. 126 (1987),
  649–673, §2.
* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1, p. 261.
* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1.
-/

public section

namespace TauCeti.Montgomery.LadderRel

section StageOne

variable {n p m : ℕ} [Fact p.Prime] {A B : ZMod p} {N D : ZMod n} {S R T : Pair (ZMod n)}

/-- Reducing a binary ladder derivation over `ZMod n` modulo a prime `p ∣ n` from a seed whose
reduction modulo `p` represents `P` produces raw representatives of `[m]P` and `[m + 1]P`,
assuming only the reduced doubling-constant relation. -/
theorem cross_coordinates_castHom_eq_zero (h : LadderRel N D S m R T) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    (R.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B (m • P)) = 0 ∧
      (T.map (ZMod.castHom hpn (ZMod p))).cross
        (Montgomery.coordinates A B ((m + 1) • P)) = 0 :=
  (h.map (ZMod.castHom hpn (ZMod p))).cross_coordinates_eq_zero hND hSP

/-- **Stage-1 ladder detection from point order.** If `addOrderOf P ∣ m` modulo a prime `p ∣ n`,
any binary ladder derivation for `m` over `ZMod n` satisfying the reduced doubling-constant
relation from a seed representing `P` has denominator gcd divisible by `p`. -/
theorem prime_dvd_gcd_of_addOrderOf_dvd (h : LadderRel N D S m R T) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (hm : addOrderOf P ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  Montgomery.prime_dvd_gcd_of_addOrderOf_dvd hpn P R hm
    (h.cross_coordinates_castHom_eq_zero hpn hND hSP).1

/-- **Stage-1 ladder detection from group cardinality.** If the cardinality of the native point
group modulo `p` divides `m`, any binary ladder derivation for `m` over `ZMod n` satisfying the
reduced doubling-constant relation from a seed representing `P` has denominator gcd divisible
by `p`. -/
theorem prime_dvd_gcd_of_card_dvd (h : LadderRel N D S m R T) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (hm : Nat.card (model A B).toAffine.Point ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  Montgomery.prime_dvd_gcd_of_card_dvd hpn P R hm
    (h.cross_coordinates_castHom_eq_zero hpn hND hSP).1

/-- On an elliptic monic model modulo a prime `p ∣ n`, divisibility of `m` by the projective point
count implies stage-1 ladder detection of `p` for any derivation satisfying the reduced
doubling-constant relation from a seed representing `P`. -/
theorem prime_dvd_gcd_of_pointCount_dvd [(model A B).IsElliptic]
    (h : LadderRel N D S m R T) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (hm : (model A B).pointCount ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  Montgomery.prime_dvd_gcd_of_pointCount_dvd hpn P R hm
    (h.cross_coordinates_castHom_eq_zero hpn hND hSP).1

/-- **Stage-1 ladder detection for `B₁`-powersmooth point orders.** If every prime-power divisor
of `addOrderOf P` is at most `B₁`, any binary ladder derivation over `ZMod n` for `B₁.lcmUpto`
satisfying the reduced doubling-constant relation from a seed representing `P` modulo a prime
`p ∣ n` detects `p` in its denominator gcd. -/
theorem prime_dvd_gcd_lcmUpto_of_isPrimePow_le {B₁ : ℕ}
    (h : LadderRel N D S B₁.lcmUpto R T) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hP : ∀ q, IsPrimePow q → q ∣ addOrderOf P → q ≤ B₁)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  h.prime_dvd_gcd_of_addOrderOf_dvd hpn hND (Nat.dvd_lcmUpto_iff.mpr hP) hSP

/-- If `addOrderOf P ≤ B₁`, any binary ladder derivation over `ZMod n` for `B₁.lcmUpto` satisfying
the reduced doubling-constant relation from a seed representing `P` modulo a prime `p ∣ n` detects
`p` in its denominator gcd. Finiteness of `ZMod p` supplies positivity of `addOrderOf P`. -/
theorem prime_dvd_gcd_lcmUpto_of_addOrderOf_le {B₁ : ℕ}
    (h : LadderRel N D S B₁.lcmUpto R T) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (hP : addOrderOf P ≤ B₁)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  h.prime_dvd_gcd_of_addOrderOf_dvd hpn hND (Nat.dvd_lcmUpto (addOrderOf_pos P) hP) hSP

private theorem eq_zero_or_eq_twoTorsionPoint_of_two_eq_zero
    (h₂ : (2 : ZMod p) = 0) (hB : B ≠ 0) {d : ZMod p} (hd : d ≠ 0)
    (hA : (A + 2) * d = 0) (P : (model A B).toAffine.Point) :
    P = 0 ∨ P = twoTorsionPoint A hB := by
  have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h₂)
  obtain rfl : p = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hp2).resolve_left (Fact.out : p.Prime).ne_one
  have hA0 : A = 0 := by
    have hA2 : A + 2 = 0 := (mul_eq_zero.mp hA).resolve_right hd
    simpa [h₂] using hA2
  subst hA0
  have eq_one_of_ne_zero {z : ZMod 2} (hz : z ≠ 0) : z = 1 :=
    congr_arg Units.val (Subsingleton.elim (Units.mk0 z hz) 1)
  obtain rfl : B = 1 := eq_one_of_ne_zero hB
  rcases P with _ | ⟨x, y, hns⟩
  · exact .inl rfl
  · by_cases hx : x = 0
    · exact .inr ((some_eq_twoTorsionPoint_iff hB hns).mpr hx)
    · exfalso
      obtain rfl : x = 1 := eq_one_of_ne_zero hx
      simp only [WeierstrassCurve.Affine.nonsingular_iff',
        model_a₁, model_a₂, model_a₃, model_a₄] at hns
      rcases hns.2 with hx' | hy'
      · exact hx' (by linear_combination -2 * h₂)
      · exact hy' (by linear_combination y * h₂)

/-- **Exact stage-1 ladder criterion.** For `B ≠ 0`, nonzero reduced `D` satisfying the reduced
doubling-constant relation `4 * N = (A + 2) * D`, and a nonzero reduced seed `S` representing `P`
modulo a prime `p ∣ n`, the denominator gcd of a binary ladder output at index `m` is divisible by
`p` if and only if `addOrderOf P ∣ m` or `P` is the distinguished point of order two `(0, 0)`.
No `p ≠ 2` or `m ≠ 0` hypothesis is needed. -/
theorem prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint
    (h : LadderRel N D S m R T) (hpn : p ∣ n) (hB : B ≠ 0)
    (hD : ZMod.castHom hpn (ZMod p) D ≠ 0)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hS : S.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd R.z.val n ↔ addOrderOf P ∣ m ∨ P = twoTorsionPoint A hB := by
  rw [R.z.dvd_gcd_val_iff_castHom_eq_zero hpn, ← Pair.map_z]
  by_cases h₂ : (2 : ZMod p) = 0
  · have h4 : (4 : ZMod p) = 0 := by linear_combination 2 * h₂
    have hA : (A + 2) * ZMod.castHom hpn (ZMod p) D = 0 := by
      rw [← hND, h4, zero_mul]
    have hP := eq_zero_or_eq_twoTorsionPoint_of_two_eq_zero h₂ hB hD hA P
    refine iff_of_true
      ((h.map (ZMod.castHom hpn (ZMod p))).z_eq_zero_of_eq_zero_or_eq_twoTorsionPoint hB hSP hP) ?_
    rcases hP with rfl | hT
    · simp
    · exact .inr hT
  · rw [(h.map (ZMod.castHom hpn (ZMod p))).z_eq_zero_iff h₂ hB hD hND hS hSP,
      ← addOrderOf_dvd_iff_nsmul_eq_zero]

/-- For an even multiplier `2 ∣ m`, under `B ≠ 0`, nonzero reduced `D` satisfying the reduced
doubling-constant relation `4 * N = (A + 2) * D`, and a nonzero reduced seed `S` representing `P`
modulo a prime `p ∣ n`, the distinguished two-torsion point has order dividing `m`, so the stage-1
binary ladder detects `p` if and only if `addOrderOf P ∣ m`. -/
theorem prime_dvd_gcd_iff_addOrderOf_dvd
    (h : LadderRel N D S m R T) (hpn : p ∣ n) (hm : 2 ∣ m) (hB : B ≠ 0)
    (hD : ZMod.castHom hpn (ZMod p) D ≠ 0)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hS : S.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd R.z.val n ↔ addOrderOf P ∣ m := by
  rw [h.prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint hpn hB hD hND hS hSP]
  refine ⟨?_, Or.inl⟩
  rintro (hdvd | rfl)
  · exact hdvd
  · rwa [addOrderOf_twoTorsionPoint]

/-- **Powersmoothness characterization of stage-1 ladder detection.** For `2 ≤ B₁`, `B ≠ 0`,
nonzero reduced `D` satisfying the reduced doubling-constant relation `4 * N = (A + 2) * D`, and a
nonzero reduced seed `S` representing `P` modulo a prime `p ∣ n`, a binary ladder derivation over
`ZMod n` for `B₁.lcmUpto` detects `p` if and only if every prime-power divisor of `addOrderOf P`
is at most `B₁`. -/
theorem prime_dvd_gcd_lcmUpto_iff_isPrimePow_le {B₁ : ℕ}
    (h : LadderRel N D S B₁.lcmUpto R T) (hpn : p ∣ n) (hB₁ : 2 ≤ B₁) (hB : B ≠ 0)
    (hD : ZMod.castHom hpn (ZMod p) D ≠ 0)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hS : S.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd R.z.val n ↔ ∀ q, IsPrimePow q → q ∣ addOrderOf P → q ≤ B₁ := by
  rw [h.prime_dvd_gcd_iff_addOrderOf_dvd hpn (Nat.dvd_lcmUpto (by decide) hB₁)
    hB hD hND hS hSP, Nat.dvd_lcmUpto_iff]

/-- Stage-1 ladder annihilation modulo a prime `p ∣ n` (under the reduced doubling-constant
relation from a seed representing `P`), together with a denominator nonzero modulo another divisor
`q ∣ n`, certifies a proper factor of a positive modulus `n`. -/
theorem one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd [NeZero n]
    (h : LadderRel N D S m R T) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (hm : addOrderOf P ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    {q : ℕ} (hqn : q ∣ n) (hq : ZMod.castHom hqn (ZMod q) R.z ≠ 0) :
    1 < Nat.gcd R.z.val n ∧ Nat.gcd R.z.val n < n :=
  Montgomery.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd hpn P R hm
    (h.cross_coordinates_castHom_eq_zero hpn hND hSP).1 hqn hq

/-- **Two-prime proper-factor criterion for the binary ladder.** For a positive modulus `n`, if a
binary ladder derivation over `ZMod n` annihilates `P` modulo a prime `p ∣ n` (under the reduced
doubling-constant relation and `S` representing `P`), while modulo another prime `q ∣ n` we have
`B' ≠ 0`, nonzero reduced `D` satisfying the reduced doubling-constant relation, and a nonzero
reduced seed `S` representing a point `Q ≠ (0, 0)` whose order does not divide `m`, then
`Nat.gcd R.z.val n` is a proper factor of `n`. -/
theorem one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd_of_not_dvd [NeZero n]
    (h : LadderRel N D S m R T) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (hm : addOrderOf P ∣ m)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    {q : ℕ} [Fact q.Prime] (hqn : q ∣ n) {A' B' : ZMod q} (hB' : B' ≠ 0)
    (hD' : ZMod.castHom hqn (ZMod q) D ≠ 0)
    (hND' : 4 * ZMod.castHom hqn (ZMod q) N = (A' + 2) * ZMod.castHom hqn (ZMod q) D)
    {Q : (model A' B').toAffine.Point}
    (hS' : S.map (ZMod.castHom hqn (ZMod q)) ≠ 0)
    (hSQ : (S.map (ZMod.castHom hqn (ZMod q))).cross (Montgomery.coordinates A' B' Q) = 0)
    (hQ : ¬ addOrderOf Q ∣ m) (hQT : Q ≠ twoTorsionPoint A' hB') :
    1 < Nat.gcd R.z.val n ∧ Nat.gcd R.z.val n < n := by
  refine h.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd hpn hND hm hSP hqn ?_
  rw [Ne, ← R.z.dvd_gcd_val_iff_castHom_eq_zero hqn,
    h.prime_dvd_gcd_iff_addOrderOf_dvd_or_eq_twoTorsionPoint hqn hB' hD' hND' hS' hSQ]
  exact not_or.mpr ⟨hQ, hQT⟩

end StageOne

section StageTwo

variable {n p : ℕ} [Fact p.Prime] {A B : ZMod p} {N D : ZMod n} {S : Pair (ZMod n)}

/-- **Stage-2 ladder detection from an annihilating scalar.** If `[q]Q = 0` modulo a prime `p ∣ n`
and `q = k ± j`, two binary ladder derivations satisfying the reduced doubling-constant relation
from a seed representing `Q` at indices `k` and `j` have cross-difference gcd divisible by `p`. -/
theorem prime_dvd_gcd_cross_of_zsmul_eq_zero
    {k j : ℕ} {R₁ T₁ R₂ T₂ : Pair (ZMod n)}
    (h₁ : LadderRel N D S k R₁ T₁) (h₂ : LadderRel N D S j R₂ T₂) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {Q : (model A B).toAffine.Point} {q : ℤ} (hq : q • Q = 0)
    (h : q = (k : ℤ) + j ∨ q = (k : ℤ) - j)
    (hSQ : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B Q) = 0) :
    p ∣ Nat.gcd (R₁.cross R₂).val n := by
  refine Montgomery.prime_dvd_gcd_cross_of_zsmul_eq_zero hpn Q R₁ R₂ hq h ?_ ?_
  · simpa only [natCast_zsmul] using (h₁.cross_coordinates_castHom_eq_zero hpn hND hSQ).1
  · simpa only [natCast_zsmul] using (h₂.cross_coordinates_castHom_eq_zero hpn hND hSQ).1

/-- **Two-stage ladder detection.** Composing a stage-1 ladder derivation for `M` (under the
reduced doubling-constant relation from a seed representing `P` modulo a prime `p ∣ n`) with
giant-step and baby-step ladder derivations for `i * w` and `j` detects `p` in the
cross-difference gcd whenever `addOrderOf P ∣ M * q` and `q = i * w ± j`. -/
theorem prime_dvd_gcd_cross_of_addOrderOf_dvd_mul
    {M q i w j : ℕ} {U₁ V₁ R₁ T₁ R₂ T₂ : Pair (ZMod n)}
    (hM : LadderRel N D S M U₁ V₁)
    (hG : LadderRel N D U₁ (i * w) R₁ T₁)
    (hB : LadderRel N D U₁ j R₂ T₂) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (horder : addOrderOf P ∣ M * q)
    (h : (q : ℤ) = (i : ℤ) * w + j ∨ (q : ℤ) = (i : ℤ) * w - j)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd (R₁.cross R₂).val n := by
  have hU := (hM.cross_coordinates_castHom_eq_zero hpn hND hSP).1
  refine Montgomery.prime_dvd_gcd_cross_of_addOrderOf_dvd_mul hpn P R₁ R₂ horder h ?_ ?_
  · simpa only [← Nat.cast_mul, natCast_zsmul] using
      (hG.cross_coordinates_castHom_eq_zero hpn hND hU).1
  · simpa only [natCast_zsmul] using
      (hB.cross_coordinates_castHom_eq_zero hpn hND hU).1

/-- **Existence of detecting giant-step and baby-step ladder indices.** For a nonzero step `w`,
if `addOrderOf P ∣ M * q` modulo a prime `p ∣ n`, there exist natural indices `i` and `j` with
`2 * j ≤ w` and `q = i * w ± j` such that, under the reduced doubling-constant relation from a
seed representing `P`, every giant-step derivation for `i * w` and baby-step derivation for `j`
from the stage-1 output `U₁` detect `p` in their cross-difference gcd. -/
theorem exists_two_mul_le_and_prime_dvd_gcd_cross
    {M q w : ℕ} {U₁ V₁ : Pair (ZMod n)}
    (hM : LadderRel N D S M U₁ V₁) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (horder : addOrderOf P ∣ M * q)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hw : w ≠ 0) :
    ∃ i j : ℕ, 2 * j ≤ w ∧
      ((q : ℤ) = (i : ℤ) * w + j ∨ (q : ℤ) = (i : ℤ) * w - j) ∧
      ∀ R₁ T₁ R₂ T₂ : Pair (ZMod n),
        LadderRel N D U₁ (i * w) R₁ T₁ →
        LadderRel N D U₁ j R₂ T₂ →
        p ∣ Nat.gcd (R₁.cross R₂).val n := by
  obtain ⟨i, j, hj, hdecomp⟩ :=
    Nat.exists_two_mul_le_and_natCast_eq_mul_add_or_mul_sub q hw
  exact ⟨i, j, hj, hdecomp, fun R₁ T₁ R₂ T₂ hG hB ↦
    hM.prime_dvd_gcd_cross_of_addOrderOf_dvd_mul hG hB hpn hND horder hdecomp hSP⟩

/-- **Batched two-stage ladder detection.** If a stage-2 batch `L` contains a giant-step/baby-step
output pair `(R₁, R₂)` from stage-1 output `U₁` for an annihilating `M * q` with `q = i * w ± j`
(under the reduced doubling-constant relation from a seed representing `P` modulo a prime `p ∣ n`),
`p` divides the gcd of the product of cross differences across `L`. -/
theorem prime_dvd_gcd_prod_cross_of_addOrderOf_dvd_mul
    {M q i w j : ℕ} {U₁ V₁ R₁ T₁ R₂ T₂ : Pair (ZMod n)}
    (hM : LadderRel N D S M U₁ V₁)
    (hG : LadderRel N D U₁ (i * w) R₁ T₁)
    (hB : LadderRel N D U₁ j R₂ T₂) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (L : List (Pair (ZMod n) × Pair (ZMod n)))
    (hmem : (R₁, R₂) ∈ L) (horder : addOrderOf P ∣ M * q)
    (h : (q : ℤ) = (i : ℤ) * w + j ∨ (q : ℤ) = (i : ℤ) * w - j)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0) :
    p ∣ Nat.gcd (L.map (Function.uncurry Pair.cross)).prod.val n := by
  have hU := (hM.cross_coordinates_castHom_eq_zero hpn hND hSP).1
  refine Montgomery.prime_dvd_gcd_prod_cross_of_addOrderOf_dvd_mul hpn P L hmem horder h ?_ ?_
  · simpa only [← Nat.cast_mul, natCast_zsmul] using
      (hG.cross_coordinates_castHom_eq_zero hpn hND hU).1
  · simpa only [natCast_zsmul] using
      (hB.cross_coordinates_castHom_eq_zero hpn hND hU).1

/-- **Proper-factor certification from a batched two-stage ladder.** For a positive modulus `n`,
if a giant-step/baby-step ladder entry in `L` detects `p ∣ n` (under the reduced doubling-constant
relation, `S` representing `P`, `addOrderOf P ∣ M * q`, and `q = i * w ± j`), and every cross
difference in `L` is nonzero modulo another prime divisor `r ∣ n`, then the batch product gcd is
strictly between `1` and `n`. -/
theorem one_lt_gcd_prod_cross_and_lt_of_addOrderOf_dvd_mul [NeZero n]
    {M q i w j : ℕ} {U₁ V₁ R₁ T₁ R₂ T₂ : Pair (ZMod n)}
    (hM : LadderRel N D S M U₁ V₁)
    (hG : LadderRel N D U₁ (i * w) R₁ T₁)
    (hB : LadderRel N D U₁ j R₂ T₂) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (L : List (Pair (ZMod n) × Pair (ZMod n)))
    (hmem : (R₁, R₂) ∈ L) (horder : addOrderOf P ∣ M * q)
    (h : (q : ℤ) = (i : ℤ) * w + j ∨ (q : ℤ) = (i : ℤ) * w - j)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    {r : ℕ} (hr : r.Prime) (hrn : r ∣ n)
    (havoid : ∀ W ∈ L, (W.1.map (ZMod.castHom hrn (ZMod r))).cross
      (W.2.map (ZMod.castHom hrn (ZMod r))) ≠ 0) :
    1 < Nat.gcd (L.map (Function.uncurry Pair.cross)).prod.val n ∧
      Nat.gcd (L.map (Function.uncurry Pair.cross)).prod.val n < n := by
  have hU := (hM.cross_coordinates_castHom_eq_zero hpn hND hSP).1
  refine Montgomery.one_lt_gcd_prod_cross_and_lt_of_addOrderOf_dvd_mul
    hpn P L hmem horder h ?_ ?_ hr hrn havoid
  · simpa only [← Nat.cast_mul, natCast_zsmul] using
      (hG.cross_coordinates_castHom_eq_zero hpn hND hU).1
  · simpa only [natCast_zsmul] using
      (hB.cross_coordinates_castHom_eq_zero hpn hND hU).1

end StageTwo

end TauCeti.Montgomery.LadderRel
