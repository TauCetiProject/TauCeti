/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder.Relations
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.Data.ZMod.GCD
public import TauCeti.NumberTheory.LcmUpto
public import Mathlib.Algebra.Field.ZMod
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint

/-!
# Stage-1 detection from Montgomery coordinate pairs and the binary ladder

Let `p ∣ n` be prime. If a raw pair over `ZMod n` reduces to a representative of the
coordinate pair of `[m]P` over `ZMod p`, and `m` annihilates `P`, then `p` divides the gcd
of its denominator with `n`. Annihilation follows either from divisibility by the point
order or, by Lagrange's theorem, from divisibility by the native group's cardinality;
at the stage-1 multiplier `B₁.lcmUpto`, divisibility is `B₁`-powersmoothness.
For an elliptic model the native group cardinality equals the projective point count.

Only a vanishing cross difference with the coordinate pair is needed in the forward
direction: the reduced raw pair may even be zero, since annihilation still forces its
denominator to vanish. Conversely, when `B ≠ 0` and the reduced pair is nonzero, `p`
divides `gcd(Z, n)` if and only if `addOrderOf P ∣ m` (at `m = B₁.lcmUpto`, if and only if
`addOrderOf P` is `B₁`-powersmooth).

Because `LadderRel` commutes with `ZMod.castHom` and preserves vanishing cross differences
unconditionally over fields, every binary Montgomery-ladder derivation over `ZMod n`
inherits both the unconditional forward detection theorems and, away from
`twoTorsionPoint` with nonzero reduced seed and scaling `D`, the exact divisibility
characterizations (characteristic two included, since `(0, 0)` and infinity are the only
nonsingular points of `model A B` over `ZMod 2` when `B ≠ 0`).

Divisibility by `p` alone need not give a proper factor: every prime divisor might divide
the gcd. For positive `n`, non-annihilation at another prime divisor certifies that the gcd
is strictly between `1` and `n`.

## References

* H. W. Lenstra Jr., *Factoring integers with elliptic curves*, Ann. of Math. 126 (1987),
  649–673, §2.
* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1, p. 261.
* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1.1.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

section Multiplier

variable {n p m : ℕ} [Fact p.Prime] {A B : ZMod p}

/-- If the point order divides the multiplier, any raw pair whose reduction has vanishing
cross difference with the multiple's coordinate pair has denominator gcd divisible by `p`.
Nonzeroness of the reduced pair is not required. -/
theorem prime_dvd_gcd_of_addOrderOf_dvd (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n)) (hm : addOrderOf P ∣ m)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0) :
    p ∣ Nat.gcd R.z.val n := by
  have hmP := addOrderOf_dvd_iff_nsmul_eq_zero.mp hm
  rw [hmP, coordinates_zero, Pair.cross_def] at hR
  have hz : ZMod.castHom hpn (ZMod p) R.z = 0 := by
    simpa using hR
  exact (R.z.dvd_gcd_val_iff_castHom_eq_zero hpn).mpr hz

/-- When `B ≠ 0` and the reduced pair modulo `p` is nonzero, `p` divides `gcd(R.z.val, n)` if and
only if `addOrderOf P ∣ m`. -/
theorem prime_dvd_gcd_iff_addOrderOf_dvd (hpn : p ∣ n) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hR₀ : R.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0) :
    p ∣ Nat.gcd R.z.val n ↔ addOrderOf P ∣ m := by
  rw [R.z.dvd_gcd_val_iff_castHom_eq_zero hpn, ← Pair.map_z,
    z_eq_zero_iff_of_cross_coordinates_eq_zero hB hR₀ hR, addOrderOf_dvd_iff_nsmul_eq_zero]

/-- **Stage-1 detection by the native group cardinality.** A multiple of the group order
annihilates every point, so a raw pair representing that multiple modulo `p` has denominator
gcd divisible by `p`. No ellipticity assumption is needed on the monic model. -/
theorem prime_dvd_gcd_of_card_dvd (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hm : Nat.card (model A B).toAffine.Point ∣ m)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_addOrderOf_dvd hpn P R ((addOrderOf_dvd_natCard P).trans hm) hR

/-- On an elliptic monic model the projective point count can replace the cardinality
of the native group in stage-1 detection. -/
theorem prime_dvd_gcd_of_pointCount_dvd [(model A B).IsElliptic] (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hm : (model A B).pointCount ∣ m)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0) :
    p ∣ Nat.gcd R.z.val n := by
  rw [WeierstrassCurve.pointCount_eq_card_point] at hm
  exact prime_dvd_gcd_of_card_dvd hpn P R hm hR

/-- Stage-1 annihilation modulo `p`, together with a denominator nonzero modulo another
divisor `q`, certifies a proper factor of the positive modulus. -/
theorem one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd [NeZero n] (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n)) (hm : addOrderOf P ∣ m)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • P)) = 0)
    {q : ℕ} (hqn : q ∣ n) (hq : ZMod.castHom hqn (ZMod q) R.z ≠ 0) :
    1 < Nat.gcd R.z.val n ∧ Nat.gcd R.z.val n < n := by
  apply R.z.one_lt_gcd_val_and_gcd_val_lt_of_castHom (Fact.out : p.Prime).one_lt hpn hqn
  · exact (R.z.dvd_gcd_val_iff_castHom_eq_zero hpn).mp
      (prime_dvd_gcd_of_addOrderOf_dvd hpn P R hm hR)
  · exact hq

end Multiplier

/-! ### Stage-1 detection at `Nat.lcmUpto B₁` -/

section LcmUpto

variable {n p B₁ : ℕ} [Fact p.Prime] {A B : ZMod p}

/-- **Stage-1 powersmooth detection.** If `addOrderOf P` is `B₁`-powersmooth (every prime-power
divisor of `addOrderOf P` is at most `B₁`), any raw pair representing `[B₁.lcmUpto]P` modulo `p`
has denominator gcd divisible by `p`. -/
theorem prime_dvd_gcd_lcmUpto_of_isPrimePow_le (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hP : ∀ q, IsPrimePow q → q ∣ addOrderOf P → q ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_addOrderOf_dvd hpn P R (Nat.dvd_lcmUpto_iff.mpr hP) hR

/-- If `addOrderOf P ≤ B₁`, any raw pair representing `[B₁.lcmUpto]P` modulo `p` has denominator
gcd divisible by `p`; positivity of `addOrderOf P` is automatic over the finite field `ZMod p`. -/
theorem prime_dvd_gcd_lcmUpto_of_addOrderOf_le (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n)) (hP : addOrderOf P ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_addOrderOf_dvd hpn P R (Nat.dvd_lcmUpto (addOrderOf_pos P) hP) hR

/-- **Stage-1 powersmooth detection by native group cardinality.** If every prime-power divisor of
`Nat.card (model A B).toAffine.Point` is at most `B₁`, any raw pair representing `[B₁.lcmUpto]P`
modulo `p` has denominator gcd divisible by `p`. -/
theorem prime_dvd_gcd_lcmUpto_of_card_isPrimePow_le (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hcard : ∀ q, IsPrimePow q → q ∣ Nat.card (model A B).toAffine.Point → q ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_card_dvd hpn P R (Nat.dvd_lcmUpto_iff.mpr hcard) hR

/-- **Stage-1 powersmooth detection by projective point count** on an elliptic monic model. -/
theorem prime_dvd_gcd_lcmUpto_of_pointCount_isPrimePow_le [(model A B).IsElliptic] (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hcount : ∀ q, IsPrimePow q → q ∣ (model A B).pointCount → q ≤ B₁)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n :=
  prime_dvd_gcd_of_pointCount_dvd hpn P R (Nat.dvd_lcmUpto_iff.mpr hcount) hR

/-- When `B ≠ 0` and the reduced representative of `[B₁.lcmUpto]P` modulo `p` is nonzero, `p`
divides `gcd(R.z.val, n)` if and only if `addOrderOf P` is `B₁`-powersmooth. -/
theorem prime_dvd_gcd_lcmUpto_iff (hpn : p ∣ n) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hR₀ : R.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n ↔ ∀ q, IsPrimePow q → q ∣ addOrderOf P → q ≤ B₁ :=
  (prime_dvd_gcd_iff_addOrderOf_dvd hpn hB P R hR₀ hR).trans Nat.dvd_lcmUpto_iff

/-- Maximal prime-power form of `prime_dvd_gcd_lcmUpto_iff`: nonzeroness of `addOrderOf P` is
discharged automatically by finiteness of the native point group over `ZMod p`. -/
theorem prime_dvd_gcd_lcmUpto_iff_ordProj_le (hpn : p ∣ n) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (R : Pair (ZMod n))
    (hR₀ : R.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (B₁.lcmUpto • P)) = 0) :
    p ∣ Nat.gcd R.z.val n ↔
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ addOrderOf P → ordProj[ℓ] (addOrderOf P) ≤ B₁ := by
  rw [prime_dvd_gcd_iff_addOrderOf_dvd hpn hB P R hR₀ hR, Nat.dvd_lcmUpto_iff_ordProj_le,
    and_iff_right (addOrderOf_pos P).ne']

end LcmUpto

/-! ### Stage-1 detection from binary Montgomery-ladder derivations over `ZMod n` -/

namespace LadderRel

section Multiplier

variable {n p m : ℕ} [Fact p.Prime] {A B : ZMod p}
  {N D : ZMod n} {S U V : Pair (ZMod n)}

/-- **End-to-end binary-ladder stage-1 detection.** Running `LadderRel` over `ZMod n` for an index
`m` divisible by `addOrderOf P` yields `p ∣ gcd(U.z.val, n)` whenever `4 * N ≡ (A + 2) * D` and
`S` represents `P` modulo `p`. No nondegeneracy assumption on `p`, `B`, `D`, `S`, or `P` is
needed: even if `P = twoTorsionPoint A hB` makes the ladder output `(0, 0)` modulo `p`, its
denominator vanishes modulo `p`. -/
theorem prime_dvd_gcd_of_addOrderOf_dvd (hL : LadderRel N D S m U V) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hm : addOrderOf P ∣ m) :
    p ∣ Nat.gcd U.z.val n :=
  Montgomery.prime_dvd_gcd_of_addOrderOf_dvd hpn P U hm
    (((hL.map (ZMod.castHom hpn (ZMod p))).cross_coordinates hND hSP).1)

/-- Binary-ladder stage-1 detection from `Nat.card (model A B).toAffine.Point ∣ m`. -/
theorem prime_dvd_gcd_of_card_dvd (hL : LadderRel N D S m U V) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hm : Nat.card (model A B).toAffine.Point ∣ m) :
    p ∣ Nat.gcd U.z.val n :=
  hL.prime_dvd_gcd_of_addOrderOf_dvd hpn hND hSP ((addOrderOf_dvd_natCard P).trans hm)

/-- Binary-ladder stage-1 detection from `(model A B).pointCount ∣ m` on an elliptic model. -/
theorem prime_dvd_gcd_of_pointCount_dvd [(model A B).IsElliptic]
    (hL : LadderRel N D S m U V) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hm : (model A B).pointCount ∣ m) :
    p ∣ Nat.gcd U.z.val n := by
  rw [WeierstrassCurve.pointCount_eq_card_point] at hm
  exact hL.prime_dvd_gcd_of_card_dvd hpn hND hSP hm

/-- **Exact prime-detection criterion for the binary ladder.** When `B ≠ 0`, `D` and `S` have
nonzero reductions modulo `p`, `4 * N ≡ (A + 2) * D` modulo `p`, and `S` represents
`P ≠ twoTorsionPoint A hB` modulo `p`, the `m`-th binary-ladder output satisfies
`p ∣ gcd(U.z.val, n)` if and only if `addOrderOf P ∣ m`. Both `P = 0` and `p = 2` are included:
over `ZMod 2` with `B ≠ 0`, every affine point `(1, y)` of `model A B` is singular, so
`P ≠ twoTorsionPoint A hB` forces `P = 0`. -/
theorem prime_dvd_gcd_iff_addOrderOf_dvd (hL : LadderRel N D S m U V) (hpn : p ∣ n)
    (hB : B ≠ 0) (hD : ZMod.castHom hpn (ZMod p) D ≠ 0)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (hS : S.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hPT : P ≠ twoTorsionPoint A hB) :
    p ∣ Nat.gcd U.z.val n ↔ addOrderOf P ∣ m := by
  rcases eq_or_ne p 2 with rfl | hp₂
  · rcases P with _ | ⟨x, y, hns⟩
    · rw [← Affine.Point.zero_def] at hSP ⊢
      have hdiv := hL.prime_dvd_gcd_of_addOrderOf_dvd hpn hND hSP
        (by rw [addOrderOf_zero]; exact one_dvd m)
      simp [hdiv, addOrderOf_zero]
    · exfalso
      have hunit : ∀ t : ZMod 2, t ≠ 0 → t = 1 := fun t ht ↦
        congr_arg Units.val (Subsingleton.elim (Units.mk0 t ht) 1)
      have hx : x ≠ 0 := (some_eq_twoTorsionPoint_iff hB hns).not.mp hPT
      obtain rfl := hunit B hB
      obtain rfl := hunit x hx
      rw [Affine.nonsingular_iff'] at hns
      have h₂ : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
      have h₃ : (3 : ZMod 2) + 1 = 0 := by linear_combination 2 * h₂
      simp [h₂, h₃] at hns
  · have h₂ : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
      exact hp₂ ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
    rw [U.z.dvd_gcd_val_iff_castHom_eq_zero hpn, ← Pair.map_z]
    exact (hL.map (ZMod.castHom hpn (ZMod p))).z_eq_zero_iff_addOrderOf_dvd
      h₂ hB hD hND hS hSP hPT

/-- **Proper-factor detection for the binary ladder.** For positive `n`, annihilation at a prime
`p ∣ n` together with non-divisibility `¬ addOrderOf Q ∣ m` at a prime `q ∣ n` where `Q` and the
ladder parameters are non-exceptional certifies `1 < gcd(U.z.val, n) < n`. -/
theorem one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd [NeZero n]
    (hL : LadderRel N D S m U V) (hpn : p ∣ n)
    (hNDp : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hmp : addOrderOf P ∣ m)
    {q : ℕ} [Fact q.Prime] (hqn : q ∣ n) {Aq Bq : ZMod q} (hBq : Bq ≠ 0)
    (hDq : ZMod.castHom hqn (ZMod q) D ≠ 0)
    (hNDq : 4 * ZMod.castHom hqn (ZMod q) N = (Aq + 2) * ZMod.castHom hqn (ZMod q) D)
    {Q : (model Aq Bq).toAffine.Point} (hSq : S.map (ZMod.castHom hqn (ZMod q)) ≠ 0)
    (hSQ : (S.map (ZMod.castHom hqn (ZMod q))).cross (Montgomery.coordinates Aq Bq Q) = 0)
    (hQT : Q ≠ twoTorsionPoint Aq hBq) (hmq : ¬ addOrderOf Q ∣ m) :
    1 < Nat.gcd U.z.val n ∧ Nat.gcd U.z.val n < n := by
  refine Montgomery.one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd hpn P U hmp
    (((hL.map (ZMod.castHom hpn (ZMod p))).cross_coordinates hNDp hSP).1) hqn ?_
  exact (U.z.dvd_gcd_val_iff_castHom_eq_zero hqn).not.mp
    ((hL.prime_dvd_gcd_iff_addOrderOf_dvd hqn hBq hDq hNDq hSq hSQ hQT).not.mpr hmq)

end Multiplier

section LcmUpto

variable {n p B₁ : ℕ} [Fact p.Prime] {A B : ZMod p}
  {N D : ZMod n} {S U V : Pair (ZMod n)}

/-- **Binary-ladder stage-1 powersmooth detection.** At `m = B₁.lcmUpto`, if `addOrderOf P` is
`B₁`-powersmooth, then `p ∣ gcd(U.z.val, n)` unconditionally. -/
theorem prime_dvd_gcd_lcmUpto_of_isPrimePow_le
    (hL : LadderRel N D S B₁.lcmUpto U V) (hpn : p ∣ n)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point}
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hP : ∀ q, IsPrimePow q → q ∣ addOrderOf P → q ≤ B₁) :
    p ∣ Nat.gcd U.z.val n :=
  hL.prime_dvd_gcd_of_addOrderOf_dvd hpn hND hSP (Nat.dvd_lcmUpto_iff.mpr hP)

/-- **Exact stage-1 powersmoothness criterion for the binary ladder.** Under the nondegeneracy
hypotheses of `LadderRel.prime_dvd_gcd_iff_addOrderOf_dvd`, the `B₁.lcmUpto`-th binary-ladder
output satisfies `p ∣ gcd(U.z.val, n)` if and only if `addOrderOf P` is `B₁`-powersmooth. -/
theorem prime_dvd_gcd_lcmUpto_iff (hL : LadderRel N D S B₁.lcmUpto U V) (hpn : p ∣ n)
    (hB : B ≠ 0) (hD : ZMod.castHom hpn (ZMod p) D ≠ 0)
    (hND : 4 * ZMod.castHom hpn (ZMod p) N = (A + 2) * ZMod.castHom hpn (ZMod p) D)
    {P : (model A B).toAffine.Point} (hS : S.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hSP : (S.map (ZMod.castHom hpn (ZMod p))).cross (Montgomery.coordinates A B P) = 0)
    (hPT : P ≠ twoTorsionPoint A hB) :
    p ∣ Nat.gcd U.z.val n ↔ ∀ q, IsPrimePow q → q ∣ addOrderOf P → q ≤ B₁ :=
  (hL.prime_dvd_gcd_iff_addOrderOf_dvd hpn hB hD hND hS hSP hPT).trans Nat.dvd_lcmUpto_iff

end LcmUpto

end LadderRel

end TauCeti.Montgomery
