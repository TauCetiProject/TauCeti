/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Binomial
public import TauCeti.QuantumGroups.QuantumInteger.Laurent
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.Tactic

/-!
# Quantum factorials

This file defines the quantum factorial `[n]_q! = [1]_q [2]_q ⋯ [n]_q` of the symmetric quantum
integers `[r]_q = (q^r - q^(-r)) / (q - q⁻¹)` in a field, and the corresponding Laurent polynomial
`[n]_v! ∈ ℤ[v, v⁻¹]`.

Quantum factorials are the denominators of the divided powers `x^(n) = x^n / [n]_q!` of the
Chevalley generators of a quantized enveloping algebra. Their nonvanishing is the genericity
hypothesis under which those divided powers exist: `[n]_q! ≠ 0` for every `n` exactly when `q` is
nonzero and not a root of unity. At a root of unity, with `q²` of order `ℓ`, the quantum factorial
`[n]_q!` is nonzero exactly for `n < ℓ`. The field convention makes every quantum integer vanish
when `q - q⁻¹ = 0`, so `[n]_(±1)! = 0` for `n ≥ 1`; the Laurent quantum factorial instead
specializes to `n!` at `v = 1`.

## Main definitions

* `TauCeti.quantumFactorial q n`: the quantum factorial `[n]_q!` in a field.
* `TauCeti.laurentQuantumFactorial n`: the quantum factorial `[n]_v!` in `ℤ[v, v⁻¹]`.

## Main results

* `TauCeti.quantumInteger_eq_zero_iff_dvd`: if `q ≠ 0` and `q²` is a primitive `ℓ`-th root of
  unity, then `[r]_q = 0` iff `ℓ ∣ r`.
* `TauCeti.forall_quantumFactorial_ne_zero_iff`: `[n]_q! ≠ 0` for all `n` iff `q` is a generic
  quantum parameter, that is, nonzero and not a root of unity.
* `TauCeti.quantumFactorial_ne_zero_iff_lt`: if `q²` is a primitive `ℓ`-th root of unity with
  `ℓ > 0`, then `[n]_q! ≠ 0` iff `n < ℓ`.
* `TauCeti.quantumBinomial_mul_quantumFactorial_mul_quantumFactorial`: for `k ≤ n`,
  `[n choose k]_q [k]_q! [n - k]_q! = [n]_q!`, with no hypothesis on `q`.
* `TauCeti.inv_quantumFactorial_smul_add_pow`: the divided-power form of the `q`-binomial
  theorem, `(x + y)^(n) = ∑_k q^(k(n-k)) x^(k) y^(n-k)` when `y x = q² x y` and `[n]_q! ≠ 0`.
* `TauCeti.laurentEval_laurentQuantumFactorial` and
  `TauCeti.laurentEval_one_laurentQuantumFactorial`: `[n]_v!` specializes to `[n]_q!` at `v = q`
  when `q - q⁻¹ ≠ 0`, and to `n!` at `v = 1`.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, Chapter 0, for
  quantum factorials and the symmetric normalization.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Section 1.3, for
  quantum factorials and divided powers.
-/

public section

open Finset LaurentPolynomial

namespace TauCeti

section Field

variable {K : Type*} [Field K]

/-! ### Vanishing of quantum integers at roots of unity -/

/-- If `q ≠ 0` and `q²` is a primitive `ℓ`-th root of unity, then the quantum integer `[r]_q`
vanishes exactly when `ℓ ∣ r`. For `ℓ = 1`, that is `q = ±1`, every quantum integer vanishes by
the field convention. -/
theorem quantumInteger_eq_zero_iff_dvd {q : K} (hq : q ≠ 0) {ℓ : ℕ}
    (h : IsPrimitiveRoot (q ^ 2) ℓ) (r : ℤ) :
    quantumInteger q r = 0 ↔ (ℓ : ℤ) ∣ r := by
  have hu : IsPrimitiveRoot (Units.mk0 (q ^ 2) (pow_ne_zero 2 hq)) ℓ :=
    IsPrimitiveRoot.coe_units_iff.mp h
  rw [← hu.zpow_eq_one_iff_dvd]
  simp only [← Units.val_eq_one, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  simpa [zpow_mul] using quantumInteger_eq_zero_iff hq r

/-! ### Quantum factorials in a field -/

/-- The quantum factorial `[n]_q! = [1]_q [2]_q ⋯ [n]_q` of the symmetric quantum integers. -/
noncomputable def quantumFactorial (q : K) (n : ℕ) : K :=
  ∏ j ∈ range n, quantumInteger q (j + 1)

/-- The defining product formula for the quantum factorial. -/
theorem quantumFactorial_def (q : K) (n : ℕ) :
    quantumFactorial q n = ∏ j ∈ range n, quantumInteger q (j + 1) :=
  (rfl)

/-- `[0]_q! = 1`. -/
@[simp]
theorem quantumFactorial_zero (q : K) : quantumFactorial q 0 = 1 := by
  simp [quantumFactorial_def]

/-- `[n + 1]_q! = [n]_q! [n + 1]_q`. -/
theorem quantumFactorial_succ (q : K) (n : ℕ) :
    quantumFactorial q (n + 1) = quantumFactorial q n * quantumInteger q (n + 1) := by
  simp [quantumFactorial_def, prod_range_succ]

/-- `[1]_q! = [1]_q`, which is `1` when `q - q⁻¹ ≠ 0`. -/
@[simp]
theorem quantumFactorial_one (q : K) : quantumFactorial q 1 = quantumInteger q 1 := by
  simp [quantumFactorial_def]

/-- Replacing the parameter by its inverse leaves every quantum factorial unchanged. -/
@[simp]
theorem quantumFactorial_inv (q : K) (n : ℕ) : quantumFactorial q⁻¹ n = quantumFactorial q n := by
  simp [quantumFactorial_def]

/-- The quantum factorial `[n]_q!` vanishes exactly when one of its factors `[j + 1]_q`,
`j < n`, does. -/
theorem quantumFactorial_eq_zero_iff {q : K} {n : ℕ} :
    quantumFactorial q n = 0 ↔ ∃ j < n, quantumInteger q (j + 1) = 0 := by
  simp [quantumFactorial_def, prod_eq_zero_iff]

/-- Nonvanishing of quantum factorials passes to smaller indices: if `[n]_q! ≠ 0` and `m ≤ n`,
then `[m]_q! ≠ 0`. -/
theorem quantumFactorial_ne_zero_of_le {q : K} {m n : ℕ} (hmn : m ≤ n)
    (hn : quantumFactorial q n ≠ 0) : quantumFactorial q m ≠ 0 := by
  rw [ne_eq, quantumFactorial_eq_zero_iff] at hn ⊢
  rintro ⟨j, hj, h⟩
  exact hn ⟨j, hj.trans_le hmn, h⟩

/-- A nonzero quantum factorial `[n]_q!` with `n ≥ 1` forces the defining denominator
`q - q⁻¹` of the quantum integers to be nonzero. -/
theorem sub_inv_ne_zero_of_quantumFactorial_ne_zero {q : K} {n : ℕ} (hn₀ : n ≠ 0)
    (hn : quantumFactorial q n ≠ 0) : q - q⁻¹ ≠ 0 := by
  intro hd
  refine quantumFactorial_ne_zero_of_le (Nat.one_le_iff_ne_zero.mpr hn₀) hn ?_
  simp [quantumInteger_def, hd]

/-- Quantum factorials do not vanish at a generic quantum parameter. -/
theorem quantumFactorial_ne_zero {q : K} (hq : IsGenericQuantumParameter q) (n : ℕ) :
    quantumFactorial q n ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ _ => quantumInteger_ne_zero hq (by omega)

/-- **Genericity through quantum factorials**: all quantum factorials `[n]_q!` are nonzero exactly
when `q` is a generic quantum parameter, that is, nonzero and not a root of unity. -/
theorem forall_quantumFactorial_ne_zero_iff {q : K} :
    (∀ n, quantumFactorial q n ≠ 0) ↔ IsGenericQuantumParameter q := by
  refine ⟨fun h => ?_, quantumFactorial_ne_zero⟩
  have hq := ne_zero_of_sub_inv_ne_zero
    (sub_inv_ne_zero_of_quantumFactorial_ne_zero one_ne_zero (h 1))
  refine isGenericQuantumParameter_iff.mpr ⟨hq, fun n hn hpow => h n ?_⟩
  -- The factor `[n]_q` of `[n]_q!` vanishes, because `q^(2n) = (q^n)^2 = 1`.
  refine quantumFactorial_eq_zero_iff.mpr ⟨n - 1, by omega, ?_⟩
  rw [Nat.cast_pred (by omega), sub_add_cancel, quantumInteger_eq_zero_iff hq]
  simp [mul_comm, zpow_mul, hpow]

/-- **Quantum factorials at a root of unity**: if `q²` is a primitive `ℓ`-th root of unity with
`ℓ > 0`, then `[n]_q! ≠ 0` exactly when `n < ℓ`. -/
theorem quantumFactorial_ne_zero_iff_lt {q : K} {ℓ : ℕ} (h : IsPrimitiveRoot (q ^ 2) ℓ)
    (hℓ : 0 < ℓ) {n : ℕ} : quantumFactorial q n ≠ 0 ↔ n < ℓ := by
  have hq : q ≠ 0 := fun hq => by simpa [hq, hℓ.ne'] using h.pow_eq_one
  have key (j : ℕ) : quantumInteger q (j + 1) = 0 ↔ ℓ ∣ j + 1 := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_add_one]
    exact quantumInteger_eq_zero_iff_dvd hq h _
  simp only [ne_eq, quantumFactorial_eq_zero_iff, key, not_exists, not_and]
  refine ⟨fun hn => ?_, fun hn j hj hdvd => ?_⟩
  · by_contra! hle
    exact hn (ℓ - 1) (by omega) (by rw [Nat.sub_add_cancel hℓ])
  · exact absurd (Nat.le_of_dvd j.succ_pos hdvd) (by omega)

/-- Ring homomorphisms between fields commute with the quantum factorials. -/
@[simp]
theorem _root_.RingHom.map_quantumFactorial {L : Type*} [Field L] (φ : K →+* L) (q : K) (n : ℕ) :
    φ (quantumFactorial q n) = quantumFactorial (φ q) n := by
  simp [quantumFactorial_def]

-- At `q = 2` over `ℚ`: `[3]_2! = 1 · 5/2 · 21/4 = 105/8`.
example : quantumFactorial (2 : ℚ) 3 = 105 / 8 := by
  norm_num [quantumFactorial_def, prod_range_succ, quantumInteger_def]

-- At `q = 1` the field convention gives `[1]_1 = 0/0 = 0`, so `[1]_1! = 0`.
example : quantumFactorial (1 : ℚ) 1 = 0 := by
  simp [quantumInteger_def]

/-! ### Quantum binomial coefficients as quotients of quantum factorials -/

/-- The quantum binomial coefficient times the two complementary quantum factorials is the
quantum factorial: `[n choose k]_q [k]_q! [n - k]_q! = [n]_q!` for `k ≤ n`. This holds for every
parameter `q`, including those at which quantum factorials vanish. -/
theorem quantumBinomial_mul_quantumFactorial_mul_quantumFactorial (q : K) {n k : ℕ}
    (hk : k ≤ n) :
    quantumBinomial q n k * quantumFactorial q k * quantumFactorial q (n - k) =
      quantumFactorial q n := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- Absorb the factor `[k + 1]_q` into the binomial, and extract `[n - k]_q` from
    -- `[n - k]_q!`.
    have habs := quantumBinomial_succ_right_eq q n k
    have hfac := quantumFactorial_succ q (n - (k + 1))
    rw [show n - (k + 1) + 1 = n - k by omega, Nat.cast_sub (by omega : k + 1 ≤ n),
      show ((n : ℤ) - (k + 1 : ℕ) + 1) = n - k by push_cast; ring] at hfac
    rw [← ih (by omega), quantumFactorial_succ, hfac]
    linear_combination quantumFactorial q k * quantumFactorial q (n - (k + 1)) * habs

/-- When `[n]_q! ≠ 0`, the quantum binomial coefficient is the quotient of quantum factorials
`[n choose k]_q = [n]_q! / ([k]_q! [n - k]_q!)` for `k ≤ n`. -/
theorem quantumBinomial_eq_div {q : K} {n k : ℕ} (hn : quantumFactorial q n ≠ 0) (hk : k ≤ n) :
    quantumBinomial q n k =
      quantumFactorial q n / (quantumFactorial q k * quantumFactorial q (n - k)) := by
  rw [eq_div_iff (mul_ne_zero (quantumFactorial_ne_zero_of_le hk hn)
      (quantumFactorial_ne_zero_of_le (Nat.sub_le n k) hn)), ← mul_assoc,
    quantumBinomial_mul_quantumFactorial_mul_quantumFactorial q hk]

/-- **The divided-power `q`-binomial theorem**: if `y x = q² x y` and `[n]_q! ≠ 0`, then the
divided power `(x + y)^(n) = (x + y)^n / [n]_q!` expands as
`∑_k q^(k(n-k)) x^(k) y^(n-k)`, with `x^(k) = x^k / [k]_q!`. -/
theorem inv_quantumFactorial_smul_add_pow {A : Type*} [Semiring A] [Algebra K A] {q : K}
    {x y : A} (h : y * x = q ^ 2 • (x * y)) {n : ℕ} (hn : quantumFactorial q n ≠ 0) :
    (quantumFactorial q n)⁻¹ • (x + y) ^ n = ∑ k ∈ range (n + 1),
      q ^ (k * (n - k)) •
        ((quantumFactorial q k)⁻¹ • x ^ k * (quantumFactorial q (n - k))⁻¹ • y ^ (n - k)) := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp
  have hq := ne_zero_of_sub_inv_ne_zero (sub_inv_ne_zero_of_quantumFactorial_ne_zero hn₀ hn)
  rw [add_pow_of_mul_eq_smul_mul hq h, smul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [smul_mul_smul_comm, smul_smul, smul_smul, quantumBinomial_eq_div hn hkn]
  congr 1
  have := quantumFactorial_ne_zero_of_le hkn hn
  have := quantumFactorial_ne_zero_of_le (Nat.sub_le n k) hn
  field_simp

end Field

/-! ### The Laurent quantum factorial -/

/-- The quantum factorial `[n]_v! = [1]_v [2]_v ⋯ [n]_v` of the Laurent quantum integers in
`ℤ[v, v⁻¹]`. -/
noncomputable def laurentQuantumFactorial (n : ℕ) : ℤ[T;T⁻¹] :=
  ∏ j ∈ range n, laurentQuantumInteger (j + 1)

/-- The defining product formula for the Laurent quantum factorial. -/
theorem laurentQuantumFactorial_def (n : ℕ) :
    laurentQuantumFactorial n = ∏ j ∈ range n, laurentQuantumInteger (j + 1) :=
  (rfl)

/-- `[0]_v! = 1`. -/
@[simp]
theorem laurentQuantumFactorial_zero : laurentQuantumFactorial 0 = 1 := by
  simp [laurentQuantumFactorial_def]

/-- `[n + 1]_v! = [n]_v! [n + 1]_v`. -/
theorem laurentQuantumFactorial_succ (n : ℕ) :
    laurentQuantumFactorial (n + 1) =
      laurentQuantumFactorial n * laurentQuantumInteger (n + 1) := by
  simp [laurentQuantumFactorial_def, prod_range_succ]

/-- At a unit `q` of a field with `q - q⁻¹ ≠ 0`, the Laurent quantum factorial `[n]_v!` takes the
value `[n]_q!`. -/
theorem laurentEval_laurentQuantumFactorial {K : Type*} [Field K] {u : Kˣ}
    (hu : (u : K) - (u : K)⁻¹ ≠ 0) (n : ℕ) :
    laurentEval u (laurentQuantumFactorial n) = quantumFactorial (u : K) n := by
  simp [laurentQuantumFactorial_def, quantumFactorial_def, laurentEval_laurentQuantumInteger hu]

/-- At `v = 1` the Laurent quantum factorial `[n]_v!` is the factorial `n!`. -/
@[simp]
theorem laurentEval_one_laurentQuantumFactorial {A : Type*} [CommRing A] (n : ℕ) :
    laurentEval (1 : Aˣ) (laurentQuantumFactorial n) = n.factorial := by
  simp [laurentQuantumFactorial_def, ← prod_range_add_one_eq_factorial]

end TauCeti
