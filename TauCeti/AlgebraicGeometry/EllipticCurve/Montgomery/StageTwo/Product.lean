/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.StageTwo.Basic
public import TauCeti.Data.ZMod.ProductGCD

/-!
# Batched stage-2 detection

A stage-2 batch multiplies cross differences of giant-step and baby-step coordinate pairs
in `ZMod n` before taking a gcd. If one pair in the batch represents the coordinates of
`[i * w]([M]P)` and `[j]([M]P)` modulo a prime `p ∣ n`, with `q = i * w ± j` and
`addOrderOf P ∣ M * q`, then `p` divides the batch gcd. The other pairs need not represent
curve points. Zero reductions and repeated entries are allowed.

A proper factor needs more: the second theorem assumes that every cross difference in
the batch is nonzero modulo another prime divisor. Without this, different entries can
detect different primes and the product gcd can equal `n`, even when leaf gcds are proper.
The empty batch has product one and cannot contain a detecting entry.

The proofs combine the single-cross-difference detection theorem with
`List.prime_dvd_gcd_val_prod_iff` and `List.one_lt_gcd_val_prod_and_lt`.

## References

* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1:
  the stage-2 product of cross differences and its gcd test.
-/

public section

namespace TauCeti.Montgomery

variable {n p : ℕ} [Fact p.Prime] {A B : ZMod p}

/-- **Batched stage-2 detection.** A batch containing a giant-step/baby-step pair for an
annihilating scalar detects `p` in the gcd of the product of its cross differences.
No nonzero-representative hypothesis is needed, and nothing is required of other entries. -/
theorem prime_dvd_gcd_prod_cross_of_addOrderOf_dvd_mul (hpn : p ∣ n) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (L : List (Pair (ZMod n) × Pair (ZMod n)))
    {R S : Pair (ZMod n)} (hmem : (R, S) ∈ L) {M q : ℕ} {i w j : ℤ}
    (horder : addOrderOf P ∣ M * q) (h : (q : ℤ) = i * w + j ∨ (q : ℤ) = i * w - j)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B ((i * w) • (M • P))) = 0)
    (hS : (S.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B (j • (M • P))) = 0) :
    p ∣ Nat.gcd (L.map (Function.uncurry Pair.cross)).prod.val n := by
  apply (List.prime_dvd_gcd_val_prod_iff _ (Fact.out : p.Prime)).mpr
  refine ⟨R.cross S, List.mem_map.mpr ⟨(R, S), hmem, rfl⟩, ?_⟩
  exact prime_dvd_gcd_cross_of_addOrderOf_dvd_mul hpn hB P R S horder h hR hS

/-- **A proper factor from a stage-2 batch.** If an annihilating scalar detects `p` at one
entry, and every cross difference avoids another prime divisor `r` of the positive modulus,
then the batch gcd is strictly between one and `n`. It need not itself be prime. -/
theorem one_lt_gcd_prod_cross_and_lt_of_addOrderOf_dvd_mul [NeZero n]
    (hpn : p ∣ n) (hB : B ≠ 0) (P : (model A B).toAffine.Point)
    (L : List (Pair (ZMod n) × Pair (ZMod n))) {R S : Pair (ZMod n)} (hmem : (R, S) ∈ L)
    {M q : ℕ} {i w j : ℤ} (horder : addOrderOf P ∣ M * q)
    (h : (q : ℤ) = i * w + j ∨ (q : ℤ) = i * w - j)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B ((i * w) • (M • P))) = 0)
    (hS : (S.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B (j • (M • P))) = 0)
    {r : ℕ} (hr : r.Prime) (hrn : r ∣ n)
    (havoid : ∀ T ∈ L, (T.1.map (ZMod.castHom hrn (ZMod r))).cross
      (T.2.map (ZMod.castHom hrn (ZMod r))) ≠ 0) :
    1 < Nat.gcd (L.map (Function.uncurry Pair.cross)).prod.val n ∧
      Nat.gcd (L.map (Function.uncurry Pair.cross)).prod.val n < n := by
  have hpG := prime_dvd_gcd_prod_cross_of_addOrderOf_dvd_mul hpn hB P L hmem horder h hR hS
  apply List.one_lt_gcd_val_prod_and_lt _ (Fact.out : p.Prime) hr hrn
  · exact (List.prime_dvd_gcd_val_prod_iff _ (Fact.out : p.Prime)).mp hpG
  · intro t ht
    obtain ⟨⟨U, V⟩, hUV, rfl⟩ := List.mem_map.mp ht
    apply ((U.cross V).dvd_gcd_val_iff_castHom_eq_zero hrn).not.mpr
    rw [← Pair.cross_map]
    exact havoid (U, V) hUV

end TauCeti.Montgomery
