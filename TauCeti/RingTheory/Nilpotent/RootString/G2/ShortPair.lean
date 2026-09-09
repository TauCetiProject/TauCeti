/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.G2.ShortPair
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction

/-!
# The exponential relation for the short pair in type `G₂`

For Chevalley root vectors `x`, `y`, `z`, `w`, `s` at the roots `α`, `α + β`,
`2α + β`, `3α + β`, `3α + 2β`, choose signs such that

```text
[x, y] = 2z,  [x, z] = 3w,  [z, y] = 3s.
```

If `x`, `y`, and `z` are nilpotent, then on any additive subgroup stable under all five
families of divided powers the integral exponentials satisfy

```text
E_x(t) E_y(u) = E_y(u) E_z(2tu) E_w(3t²u) E_s(3tu²) E_x(t).
```

The parameter ring is an arbitrary commutative ring: the factors `2` and `3` are multiplied,
never inverted. This supplies the second nontrivial root-pair configuration in type `G₂`,
complementing the relation for its two simple roots. The conjugation form is also recorded.

The proof uses `Associative.dividedPower_mul_dividedPower_of_g2_short_pair`; its finite-sum
argument follows the long-pair construction in
`TauCeti.RingTheory.Nilpotent.RootString.G2.Basic`, with five factors and the short-pair weights.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti

open Finset TensorProduct

universe u v

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type u} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

/-- The short-pair straightening rule on a subgroup stable under divided powers, with the
Chevalley coefficients `2ᵇ 3ᶜ⁺ᵈ` retained as natural-number scalar multiples. -/
theorem integralDividedPower_mul_integralDividedPower_of_g2_short_pair
    {x y z w s : A} (M : S) (hxy : x * y = y * x + 2 • z)
    (hxz : x * z = z * x + 3 • w) (hzy : z * y = y * z + 3 • s)
    (hxw : Commute x w) (hxs : Commute x s) (hys : Commute y s)
    (hzw : Commute z w) (hzs : Commute z s) (hws : Commute w s)
    (hMx : ∀ n, ∀ a ∈ M, Associative.dividedPower n x • a ∈ M)
    (hMy : ∀ n, ∀ a ∈ M, Associative.dividedPower n y • a ∈ M)
    (hMz : ∀ n, ∀ a ∈ M, Associative.dividedPower n z • a ∈ M)
    (hMw : ∀ n, ∀ a ∈ M, Associative.dividedPower n w • a ∈ M)
    (hMs : ∀ n, ∀ a ∈ M, Associative.dividedPower n s • a ∈ M) (m n : ℕ) :
    integralDividedPower x M m (hMx m) * integralDividedPower y M n (hMy n) =
      ∑ p ∈ Associative.g2ShortPairIndex m n,
        ((2 : ℕ) ^ p.1 * 3 ^ (p.2.1 + p.2.2)) •
          (integralDividedPower y M (n - p.1 - p.2.1 - 2 * p.2.2)
              (hMy (n - p.1 - p.2.1 - 2 * p.2.2)) *
            integralDividedPower z M p.1 (hMz p.1) *
            integralDividedPower w M p.2.1 (hMw p.2.1) *
            integralDividedPower s M p.2.2 (hMs p.2.2) *
            integralDividedPower x M (m - p.1 - 2 * p.2.1 - p.2.2)
              (hMx (m - p.1 - 2 * p.2.1 - p.2.2))) := by
  ext a
  simp only [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_nsmul, coe_integralDividedPower_apply,
    ← mul_smul, ← smul_assoc, ← Finset.sum_smul]
  congr 1
  simpa only [mul_assoc] using
    Associative.dividedPower_mul_dividedPower_of_g2_short_pair
      hxy hxz hzy hxw hxs hys hzw hzs hws m n

/-- Reindex the short-pair straightening region by the five ordered root exponents. -/
private theorem sum_g2ShortPairIndex_diag_flip {B : Type*} [AddCommMonoid B]
    (F : ℕ × ℕ × ℕ × ℕ × ℕ → B) (N : ℕ) :
    ∑ p ∈ (range N ×ˢ range N).sigma (fun mn => Associative.g2ShortPairIndex mn.1 mn.2),
        F (p.1.2 - p.2.1 - p.2.2.1 - 2 * p.2.2.2, p.2.1, p.2.2.1, p.2.2.2,
          p.1.1 - p.2.1 - 2 * p.2.2.1 - p.2.2.2) =
      ∑ p ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N with
        p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2.1 < N ∧
          p.2.2.2.2 + p.2.1 + 2 * p.2.2.1 + p.2.2.2.1 < N, F p := by
  refine Finset.sum_nbij'
    (fun p => (p.1.2 - p.2.1 - p.2.2.1 - 2 * p.2.2.2, p.2.1, p.2.2.1, p.2.2.2,
      p.1.1 - p.2.1 - 2 * p.2.2.1 - p.2.2.2))
    (fun p => ⟨(p.2.2.2.2 + p.2.1 + 2 * p.2.2.1 + p.2.2.2.1,
      p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2.1), (p.2.1, p.2.2.1, p.2.2.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨m, n⟩, b, c, d⟩ hp
    simp only [mem_sigma, mem_product, mem_range, Associative.mem_g2ShortPairIndex] at hp
    simp only [mem_filter, mem_product, mem_range]
    omega
  · rintro ⟨a, b, c, d, q⟩ hp
    simp only [mem_filter, mem_product, mem_range] at hp
    simp only [mem_sigma, mem_product, mem_range, Associative.mem_g2ShortPairIndex]
    omega
  · rintro ⟨⟨m, n⟩, b, c, d⟩ hp
    have hp' : b + c + 2 * d ≤ n ∧ b + 2 * c + d ≤ m :=
      Associative.mem_g2ShortPairIndex.mp (mem_sigma.mp hp).2
    have hn : n - b - c - 2 * d + b + c + 2 * d = n := by omega
    have hm : m - b - 2 * c - d + b + 2 * c + d = m := by omega
    simp [hn, hm]
  · rintro ⟨a, b, c, d, q⟩ _
    have hn : a + b + c + 2 * d - b - c - 2 * d = a := by omega
    have hm : q + b + 2 * c + d - b - 2 * c - d = q := by omega
    simp [hn, hm]
  · rintro ⟨⟨m, n⟩, b, c, d⟩ _
    rfl

/-- The finite generating-function identity for the short-pair straightening rule. -/
private theorem sum_smul_mul_sum_smul_of_g2ShortPair {R : Type*} [CommRing R]
    {B : Type*} [Ring B] [Algebra R B] (Dx Dy Dz Dw Ds : ℕ → B) (N : ℕ)
    (hno : ∀ m n, Dx m * Dy n = ∑ p ∈ Associative.g2ShortPairIndex m n,
      ((2 : ℕ) ^ p.1 * 3 ^ (p.2.1 + p.2.2)) •
        (Dy (n - p.1 - p.2.1 - 2 * p.2.2) * Dz p.1 * Dw p.2.1 * Ds p.2.2 *
          Dx (m - p.1 - 2 * p.2.1 - p.2.2)))
    (hzero : ∀ a b c d q : ℕ,
      N ≤ a + b + c + 2 * d ∨ N ≤ q + b + 2 * c + d →
        Dy a * Dz b * Dw c * Ds d * Dx q = 0) (t u : R) :
    (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) =
      (∑ a ∈ range N, u ^ a • Dy a) * (∑ b ∈ range N, (2 * t * u) ^ b • Dz b) *
        (∑ c ∈ range N, (3 * t ^ 2 * u) ^ c • Dw c) *
        (∑ d ∈ range N, (3 * t * u ^ 2) ^ d • Ds d) *
        (∑ q ∈ range N, t ^ q • Dx q) := by
  classical
  let G : ℕ × ℕ × ℕ × ℕ × ℕ → B := fun p =>
    (u ^ p.1 * (2 * t * u) ^ p.2.1 * (3 * t ^ 2 * u) ^ p.2.2.1 *
      (3 * t * u ^ 2) ^ p.2.2.2.1 * t ^ p.2.2.2.2) •
      (Dy p.1 * Dz p.2.1 * Dw p.2.2.1 * Ds p.2.2.2.1 * Dx p.2.2.2.2)
  -- Expand the ordered product over the full box of exponents.
  have hbox : ∑ p ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N, G p =
      (∑ a ∈ range N, u ^ a • Dy a) * (∑ b ∈ range N, (2 * t * u) ^ b • Dz b) *
        (∑ c ∈ range N, (3 * t ^ 2 * u) ^ c • Dw c) *
        (∑ d ∈ range N, (3 * t * u ^ 2) ^ d • Ds d) *
        (∑ q ∈ range N, t ^ q • Dx q) := by
    simp only [mul_assoc]
    simp only [sum_mul_sum]
    simp only [G, sum_product, mul_sum, smul_mul_smul_comm, mul_assoc]
  -- Expand the original product and reindex its straightened terms.
  have hsrc : ∑ p ∈ (range N ×ˢ range N).sigma
        (fun mn => Associative.g2ShortPairIndex mn.1 mn.2),
        (t ^ p.1.1 * u ^ p.1.2) • (((2 : ℕ) ^ p.2.1 * 3 ^ (p.2.2.1 + p.2.2.2)) •
          (Dy (p.1.2 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) * Dz p.2.1 * Dw p.2.2.1 *
            Ds p.2.2.2 * Dx (p.1.1 - p.2.1 - 2 * p.2.2.1 - p.2.2.2))) =
      (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) := by
    rw [sum_sigma, sum_mul_sum]
    simp only [sum_product, smul_mul_smul_comm, hno, smul_sum]
  rw [← hsrc, ← hbox]
  trans ∑ p ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N with
      p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2.1 < N ∧
        p.2.2.2.2 + p.2.1 + 2 * p.2.2.1 + p.2.2.2.1 < N, G p
  · rw [← sum_g2ShortPairIndex_diag_flip G N]
    refine sum_congr rfl ?_
    rintro ⟨⟨m, n⟩, b, c, d⟩ hp
    simp only [mem_sigma, mem_product, mem_range, Associative.mem_g2ShortPairIndex] at hp
    obtain ⟨a, rfl⟩ : ∃ a, n = a + (b + c + 2 * d) := ⟨n - b - c - 2 * d, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, m = q + (b + 2 * c + d) := ⟨m - b - 2 * c - d, by omega⟩
    have hn : a + (b + c + 2 * d) - b - c - 2 * d = a := by omega
    have hm : q + (b + 2 * c + d) - b - 2 * c - d = q := by omega
    simp only [G, hn, hm, ← Nat.cast_smul_eq_nsmul R, smul_smul]
    congr 1
    push_cast
    simp only [mul_pow, pow_add, pow_mul]
    ring
  · -- Outside the reindexed slice one factor is zero by the truncation hypothesis.
    exact sum_filter_of_ne fun p _ hne => by
      by_contra h
      exact hne (by simp [G, hzero p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (by omega)])

section Exponential

variable {R : Type v} [CommRing R] [Algebra ℤ R]

-- Match tensor products to the module structure carried by the explicit `ℤ`-algebra.
attribute [local instance high] Algebra.toModule

/-- The Chevalley exponential relation for `α`, `α + β` in type `G₂`, over any commutative
parameter ring. Only `x`, `y`, and `z` need explicit nilpotency hypotheses: the central
commutator relations force nilpotency of `w` and `s`. -/
theorem baseChangeExp_mul_baseChangeExp_of_g2_short_pair
    {x y z w s : A} (M : S) (hxy : x * y = y * x + 2 • z)
    (hxz : x * z = z * x + 3 • w) (hzy : z * y = y * z + 3 • s)
    (hxw : Commute x w) (hxs : Commute x s) (hys : Commute y s)
    (hzw : Commute z w) (hzs : Commute z s) (hws : Commute w s)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z)
    (hMx : ∀ n, ∀ a ∈ M, Associative.dividedPower n x • a ∈ M)
    (hMy : ∀ n, ∀ a ∈ M, Associative.dividedPower n y • a ∈ M)
    (hMz : ∀ n, ∀ a ∈ M, Associative.dividedPower n z • a ∈ M)
    (hMw : ∀ n, ∀ a ∈ M, Associative.dividedPower n w • a ∈ M)
    (hMs : ∀ n, ∀ a ∈ M, Associative.dividedPower n s • a ∈ M) (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (2 * t * u) *
        baseChangeExp w M hMw (3 * t ^ 2 * u) * baseChangeExp s M hMs (3 * t * u ^ 2) *
        baseChangeExp x M hMx t := by
  classical
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  obtain ⟨kz, hkz⟩ := hz
  obtain ⟨kw, hkw⟩ := Associative.isNilpotent_of_commutator_eq_nsmul (by decide)
    hxz hxw hzw ⟨kx, hkx⟩
  obtain ⟨ks, hks⟩ := Associative.isNilpotent_of_commutator_eq_nsmul (by decide)
    hzy hzs hys ⟨kz, hkz⟩
  let N := kx + ky + kz + 2 * kw + 2 * ks
  have hxN : x ^ N = 0 := pow_eq_zero_of_le (by omega) hkx
  have hyN : y ^ N = 0 := pow_eq_zero_of_le (by omega) hky
  have hzN : z ^ N = 0 := pow_eq_zero_of_le (by omega) hkz
  have hwN : w ^ N = 0 := pow_eq_zero_of_le (by omega) hkw
  have hsN : s ^ N = 0 := pow_eq_zero_of_le (by omega) hks
  rw [baseChangeExp_of_pow_eq_zero x M hMx hxN, baseChangeExp_of_pow_eq_zero y M hMy hyN,
    baseChangeExp_of_pow_eq_zero z M hMz hzN, baseChangeExp_of_pow_eq_zero w M hMw hwN,
    baseChangeExp_of_pow_eq_zero s M hMs hsN]
  refine sum_smul_mul_sum_smul_of_g2ShortPair (R := R)
    (fun n => (integralDividedPower x M n (hMx n)).baseChange R)
    (fun n => (integralDividedPower y M n (hMy n)).baseChange R)
    (fun n => (integralDividedPower z M n (hMz n)).baseChange R)
    (fun n => (integralDividedPower w M n (hMw n)).baseChange R)
    (fun n => (integralDividedPower s M n (hMs n)).baseChange R) N ?_ ?_ t u
  · intro m n
    have h := congrArg (fun f : Module.End ℤ M => (Module.End.baseChangeHom ℤ R M) f)
      (integralDividedPower_mul_integralDividedPower_of_g2_short_pair
        M hxy hxz hzy hxw hxs hys hzw hzs hws hMx hMy hMz hMw hMs m n)
    simp only [map_mul, map_sum, map_nsmul] at h
    exact h
  · intro a b c d q h
    -- If every exponent is below its nilpotency bound, both weights are below `N`.
    have hv : ky ≤ a ∨ kz ≤ b ∨ kw ≤ c ∨ ks ≤ d ∨ kx ≤ q := by omega
    rcases hv with ha | hb | hc | hd | hq
    · simp [baseChange_integralDividedPower_eq_zero_of_le y M (hMy a) hky ha]
    · simp [baseChange_integralDividedPower_eq_zero_of_le z M (hMz b) hkz hb]
    · simp [baseChange_integralDividedPower_eq_zero_of_le w M (hMw c) hkw hc]
    · simp [baseChange_integralDividedPower_eq_zero_of_le s M (hMs d) hks hd]
    · simp [baseChange_integralDividedPower_eq_zero_of_le x M (hMx q) hkx hq]

/-- Conjugating the short-pair root subgroup of `y` by that of `x` produces the three
additional root factors with parameters `2tu`, `3t²u`, and `3tu²`. -/
theorem baseChangeExp_conj_of_g2_short_pair
    {x y z w s : A} (M : S) (hxy : x * y = y * x + 2 • z)
    (hxz : x * z = z * x + 3 • w) (hzy : z * y = y * z + 3 • s)
    (hxw : Commute x w) (hxs : Commute x s) (hys : Commute y s)
    (hzw : Commute z w) (hzs : Commute z s) (hws : Commute w s)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z)
    (hMx : ∀ n, ∀ a ∈ M, Associative.dividedPower n x • a ∈ M)
    (hMy : ∀ n, ∀ a ∈ M, Associative.dividedPower n y • a ∈ M)
    (hMz : ∀ n, ∀ a ∈ M, Associative.dividedPower n z • a ∈ M)
    (hMw : ∀ n, ∀ a ∈ M, Associative.dividedPower n w • a ∈ M)
    (hMs : ∀ n, ∀ a ∈ M, Associative.dividedPower n s • a ∈ M) (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u * baseChangeExp x M hMx (-t) =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (2 * t * u) *
        baseChangeExp w M hMw (3 * t ^ 2 * u) * baseChangeExp s M hMs (3 * t * u ^ 2) := by
  rw [baseChangeExp_mul_baseChangeExp_of_g2_short_pair M hxy hxz hzy hxw hxs hys hzw hzs hws
    hx hy hz hMx hMy hMz hMw hMs t u, mul_assoc, ← baseChangeExp_add x M hMx hx,
    add_neg_cancel, baseChangeExp_zero x M hMx hx, mul_one]

end Exponential

end TauCeti
