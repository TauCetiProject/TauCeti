/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Cyclic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum

/-!
# The dyadic cyclic generators `q_θ^{(2)}(2^k)` and their Gauss sums

For `k ≥ 1` and an integer `θ`, Nikulin's finite quadratic module `q_θ^{(2)}(2^k)` is the cyclic
group `ℤ/2^k` with

```text
q(x) = θx² / 2^{k+1},   b(x, y) = θxy / 2^k.
```

In the half-norm convention it is the discriminant form of the `2`-adic lattice of rank one with
Gram matrix `(θ·2^k)`, and for odd `θ` it is one of the generators of Nikulin's classification of
nondegenerate finite quadratic modules, alongside the odd-primary cyclic forms and the two forms
`u^{(2)}(2^k)`, `v^{(2)}(2^k)` on `(ℤ/2^k)²`.

This file constructs it from the cyclic presentation `TauCeti.FiniteQuadraticModule.cyclic`,
proves it nondegenerate exactly for odd `θ`, and evaluates its Gauss sum for odd `θ` (Nikulin,
Proposition 1.11.2):

```text
∑_{x ∈ ℤ/2^k} e^{2πi θx²/2^{k+1}} = √(2^k) · e^{2πi (θ + 4kω(θ))/8},   ω(θ) = (θ² − 1)/8.
```

The normalized Gauss sum `G(q) / √#A` of `q_θ^{(2)}(2^k)` is therefore the eighth root of unity
`e^{2πi (θ + 4kω(θ))/8}`, which is the value of the Gauss-sum invariant on this generator. Unlike
the odd-primary generators, no sign of a classical quadratic Gauss sum enters: the value follows
from the recursion `G(q_θ^{(2)}(2^{k+2})) = 2·G(q_θ^{(2)}(2^k))`, which holds because translation
by `2^{k+1}` in `ℤ/2^{k+2}` multiplies the summand at `x` by `(-1)^x`, together with the two values
`G(q_θ^{(2)}(2)) = 1 + i^θ` and `G(q_θ^{(2)}(4)) = 2e^{2πiθ/8}`.

## Main declarations

* `TauCeti.FiniteQuadraticModule.dyadicCyclic`: the finite quadratic module `q_θ^{(2)}(2^k)`.
* `TauCeti.FiniteQuadraticModule.isNondegenerate_dyadicCyclic_iff`: it is nondegenerate exactly
  when `θ` is odd.
* `TauCeti.FiniteQuadraticModule.gaussSum_dyadicCyclic_add_two`: the recursion in `k`.
* `TauCeti.FiniteQuadraticModule.gaussSum_dyadicCyclic`: the closed form of its Gauss sum.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8 for the
  generators and Proposition 1.11.2 for their Gauss sums.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

open Complex ComplexConjugate Finset
open scoped Real

namespace TauCeti.FiniteQuadraticModule

/-! ## The generator -/

variable (k : ℕ) [NeZero k] (θ : ℤ)

/-- **Nikulin's dyadic cyclic generator** `q_θ^{(2)}(2^k)`, for `k ≥ 1`: the cyclic group `ℤ/2^k`
with quadratic form `q(x) = θx² / 2^{k+1}` and pairing `b(x, y) = θxy / 2^k`. It is the
discriminant form of the rank-one `2`-adic lattice with Gram matrix `(θ·2^k)`, and it is
nondegenerate exactly when `θ` is odd. -/
@[expose] noncomputable def dyadicCyclic : FiniteQuadraticModule :=
  cyclic (2 ^ k) (((θ / 2 ^ (k + 1) : ℚ)) : AddCircle (1 : ℚ))
    (by
      -- `(2^k)² · θ / 2^{k+1} = 2^{k-1}θ` is an integer because `k ≥ 1`.
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
      refine AddCircle.zsmul_coe_eq_zero (c := 2 ^ j * θ) ?_
      push_cast
      field_simp
      ring)
    (by
      refine AddCircle.zsmul_coe_eq_zero (c := θ) ?_
      push_cast
      field_simp
      ring)

/-- The quadratic form of `q_θ^{(2)}(2^k)` on the reduction of an integer `j` is
`θj² / 2^{k+1}`. -/
@[simp]
theorem dyadicCyclic_quadratic_intCast (j : ℤ) :
    (dyadicCyclic k θ).quadratic (j : ZMod (2 ^ k)) =
      ((θ * j ^ 2 / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) := by
  unfold dyadicCyclic
  rw [cyclic_quadratic, cyclicMap_intCast, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  push_cast
  ring_nf

/-- The pairing of `q_θ^{(2)}(2^k)` on the reductions of integers `i` and `j` is
`θij / 2^k`. -/
@[simp]
theorem dyadicCyclic_pairing_intCast (i j : ℤ) :
    (dyadicCyclic k θ).toFiniteBilinearModule.pairing (i : ZMod (2 ^ k)) (j : ZMod (2 ^ k)) =
      ((θ * i * j / 2 ^ k : ℚ) : AddCircle (1 : ℚ)) := by
  unfold dyadicCyclic
  rw [cyclic_pairing, polar_cyclicMap_intCast, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  congr 1
  push_cast
  field_simp
  ring

/-- **`q_θ^{(2)}(2^k)` is nondegenerate exactly when `θ` is odd.** For even `θ` the nonzero
element `2^{k-1}` lies in the radical. -/
theorem isNondegenerate_dyadicCyclic_iff : (dyadicCyclic k θ).IsNondegenerate ↔ Odd θ := by
  refine ⟨fun h ↦ ?_, fun hθ ↦ ?_⟩
  · by_contra hodd
    obtain ⟨s, rfl⟩ := Int.not_odd_iff_even.1 hodd
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
    have hx : ((2 ^ j : ℤ) : ZMod (2 ^ (j + 1))) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hd
      push_cast at hd
      have hle := Int.le_of_dvd (by positivity) hd
      rw [pow_succ] at hle
      linarith [pow_pos (zero_lt_two : (0 : ℤ) < 2) j]
    have hpair : (dyadicCyclic (j + 1) (s + s)).toFiniteBilinearModule.pairing
        ((2 ^ j : ℤ) : ZMod (2 ^ (j + 1))) = 0 := by
      have hval : ∀ i : ℤ, (dyadicCyclic (j + 1) (s + s)).toFiniteBilinearModule.pairing
          ((2 ^ j : ℤ) : ZMod (2 ^ (j + 1))) (i : ZMod (2 ^ (j + 1))) = 0 := fun i ↦ by
        rw [dyadicCyclic_pairing_intCast]
        exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2 ⟨s * i, by push_cast; field_simp; ring⟩
      refine AddMonoidHom.ext fun y ↦ ?_
      obtain ⟨i, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ (j + 1)) y
      -- The zero character evaluates to `0`; `AddMonoidHom.zero_apply` holds by `rfl`.
      exact hval i
    exact hx (FiniteBilinearModule.IsNondegenerate.injective _ h (hpair.trans (map_zero _).symm))
  · have hcop : IsCoprime ((2 : ℤ) ^ k) θ := by
      obtain ⟨t, rfl⟩ := hθ
      exact IsCoprime.pow_left ⟨-t, 1, by ring⟩
    refine (FiniteBilinearModule.isNondegenerate_iff_injective _).2
      ((injective_iff_map_eq_zero _).2 fun x hx ↦ ?_)
    obtain ⟨j, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) x
    have h : (dyadicCyclic k θ).toFiniteBilinearModule.pairing (j : ZMod (2 ^ k))
        ((1 : ℤ) : ZMod (2 ^ k)) = 0 :=
      -- The zero character evaluates to `0`; `AddMonoidHom.zero_apply` holds by `rfl`.
      DFunLike.congr_fun hx _
    rw [dyadicCyclic_pairing_intCast,
      show (θ * j * (1 : ℤ) / 2 ^ k : ℚ) = ((θ * j : ℤ) : ℚ) / ((2 ^ k : ℕ) : ℚ) by
        push_cast; ring,
      AddCircle.coe_intCast_div_natCast_eq_zero_iff (NeZero.ne _)] at h
    push_cast at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd j (2 ^ k)).2
      (by exact_mod_cast hcop.dvd_of_dvd_mul_left h)

/-! ## The Gauss sum -/

/-- The summand `e^{2πi θn²/2^{k+1}}` of the Gauss sum of `q_θ^{(2)}(2^k)` at a natural
representative `n`. -/
private noncomputable def term (k : ℕ) (θ : ℤ) (n : ℕ) : ℂ :=
  expCircle (((θ * n ^ 2 / 2 ^ (k + 1) : ℚ)) : AddCircle (1 : ℚ))

/-- The Gauss sum of `q_θ^{(2)}(2^k)` as a sum over the representatives `0, …, 2^k - 1`. -/
private theorem gaussSum_dyadicCyclic_eq_sum_range :
    (dyadicCyclic k θ).gaussSum = ∑ n ∈ range (2 ^ k), term k θ n := by
  -- The carrier of `dyadicCyclic k θ` is `ZMod (2 ^ k)`, so its Gauss sum is a sum over residues.
  have hsum : (dyadicCyclic k θ).gaussSum =
      ∑ x : ZMod (2 ^ k), expCircle ((dyadicCyclic k θ).quadratic x) := by
    let : Fintype (dyadicCyclic k θ) := inferInstanceAs (Fintype (ZMod (2 ^ k)))
    exact gaussSum_eq_sum _
  rw [hsum]
  refine Finset.sum_nbij' ZMod.val (fun n ↦ (n : ZMod (2 ^ k)))
    (fun x _ ↦ mem_range.2 (ZMod.val_lt _)) (fun _ _ ↦ mem_univ _)
    (fun x _ ↦ ZMod.natCast_zmod_val _) (fun n hn ↦ ZMod.val_natCast_of_lt (mem_range.1 hn))
    fun x _ ↦ ?_
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Int.cast_natCast, dyadicCyclic_quadratic_intCast]
  rw [term, Int.cast_natCast]

/-- Translating by `2^{k+1}` in `ℤ/2^{k+2}` multiplies the summand at `n` by `(-1)^n`, for odd
`θ` and `k ≥ 1`. -/
private theorem term_add (j : ℕ) {θ : ℤ} (hθ : Odd θ) (n : ℕ) :
    term (j + 3) θ (2 ^ (j + 2) + n) = (-1) ^ n * term (j + 3) θ n := by
  obtain ⟨t, rfl⟩ := hθ
  have h : (((2 * t + 1 : ℤ) : ℚ) * ((2 ^ (j + 2) + n : ℕ) : ℚ) ^ 2 / 2 ^ (j + 3 + 1)) =
      (n • (1 / 2 : ℚ) + ((2 * t + 1 : ℤ) : ℚ) * (n : ℚ) ^ 2 / 2 ^ (j + 3 + 1)) +
        ((2 ^ j * (2 * t + 1) + t * n : ℤ) : ℚ) := by
    rw [nsmul_eq_mul]
    push_cast
    field_simp
    ring
  rw [term, h, QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _),
    AddCircle.coe_add, AddChar.map_add_eq_mul,
    AddCircle.coe_nsmul, AddChar.map_nsmul_eq_pow, expCircle_half, term]

/-- The summand of `q_θ^{(2)}(2^{k+2})` at `2n` is the summand of `q_θ^{(2)}(2^k)` at `n`. -/
private theorem term_two_mul (k : ℕ) (θ : ℤ) (n : ℕ) :
    term (k + 2) θ (2 * n) = term k θ n := by
  rw [term, term]
  congr 2
  push_cast
  field_simp
  ring

/-- The recursion on the representative sums. -/
private theorem sum_range_term_add_two (j : ℕ) {θ : ℤ} (hθ : Odd θ) :
    ∑ n ∈ range (2 ^ (j + 3)), term (j + 3) θ n =
      2 * ∑ n ∈ range (2 ^ (j + 1)), term (j + 1) θ n := by
  -- A sum over `range (2m)` is the sum over `range m` of pairs of consecutive terms.
  have hpairs : ∀ (f : ℕ → ℂ) (m : ℕ),
      ∑ n ∈ range (2 * m), f n = ∑ n ∈ range m, (f (2 * n) + f (2 * n + 1)) := by
    intro f m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
        sum_range_succ]
      ring
  rw [show 2 ^ (j + 3) = 2 ^ (j + 2) + 2 ^ (j + 2) by ring, sum_range_add]
  simp_rw [term_add j hθ]
  rw [← sum_add_distrib, show 2 ^ (j + 2) = 2 * 2 ^ (j + 1) by ring, hpairs,
    mul_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, mul_neg_one, ← term_two_mul (j + 1)]
  ring

/-- **The Gauss sum of `q_θ^{(2)}(2^{k+2})` is twice that of `q_θ^{(2)}(2^k)`**, for odd `θ`. -/
theorem gaussSum_dyadicCyclic_add_two (hθ : Odd θ) :
    (dyadicCyclic (k + 2) θ).gaussSum = 2 * (dyadicCyclic k θ).gaussSum := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
  rw [gaussSum_dyadicCyclic_eq_sum_range, gaussSum_dyadicCyclic_eq_sum_range]
  exact sum_range_term_add_two j hθ

/-- The Gauss sum of `q_θ^{(2)}(2)` is `1 + i^θ`. -/
private theorem gaussSum_dyadicCyclic_one (hθ : Odd θ) :
    (dyadicCyclic 1 θ).gaussSum =
      √(2 ^ 1 : ℝ) * expCircle ((((2 * θ + 1 * (θ ^ 2 - 1)) / 16 : ℚ)) : AddCircle (1 : ℚ)) := by
  have hsum : (dyadicCyclic 1 θ).gaussSum = 1 + expCircle (((θ / 4 : ℚ)) : AddCircle (1 : ℚ)) := by
    rw [gaussSum_dyadicCyclic_eq_sum_range, pow_one, sum_range_succ, sum_range_one, term, term]
    norm_num
  have hsqrt : (√2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 zero_lt_two)
  rw [hsum, pow_one]
  obtain ⟨t, rfl⟩ := hθ
  obtain ⟨u, rfl | rfl⟩ := Int.even_or_odd' t
  · rw [show (((2 * (2 * u) + 1 : ℤ) : ℚ) / 4) = 1 / 4 + ((u : ℤ) : ℚ) by push_cast; ring,
      show ((2 * ((2 * (2 * u) + 1 : ℤ) : ℚ) + 1 * (((2 * (2 * u) + 1 : ℤ) : ℚ) ^ 2 - 1)) / 16) =
        1 / 8 + ((u ^ 2 + u : ℤ) : ℚ) by push_cast; ring,
      QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _),
      QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _),
      expCircle_quarter, expCircle_eighth, mul_div_cancel₀ _ hsqrt]
  · rw [show (((2 * (2 * u + 1) + 1 : ℤ) : ℚ) / 4) = -(1 / 4) + ((u + 1 : ℤ) : ℚ) by
        push_cast; ring,
      show ((2 * ((2 * (2 * u + 1) + 1 : ℤ) : ℚ) + 1 * (((2 * (2 * u + 1) + 1 : ℤ) : ℚ) ^ 2 - 1)) /
        16) = -(1 / 8) + ((u ^ 2 + 2 * u + 1 : ℤ) : ℚ) by push_cast; ring,
      QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _),
      QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _),
      AddCircle.coe_neg, expCircle_neg, AddCircle.coe_neg, expCircle_neg, expCircle_quarter,
      expCircle_eighth, map_div₀, conj_ofReal, mul_div_cancel₀ _ hsqrt, map_add, map_one, conj_I]

/-- The Gauss sum of `q_θ^{(2)}(4)` is `2e^{2πiθ/8}`. -/
private theorem gaussSum_dyadicCyclic_two (hθ : Odd θ) :
    (dyadicCyclic 2 θ).gaussSum =
      √(2 ^ 2 : ℝ) * expCircle ((((2 * θ + 2 * (θ ^ 2 - 1)) / 16 : ℚ)) : AddCircle (1 : ℚ)) := by
  have hsum : (dyadicCyclic 2 θ).gaussSum =
      1 + 2 * expCircle (((θ / 8 : ℚ)) : AddCircle (1 : ℚ)) +
        expCircle (((θ / 2 : ℚ)) : AddCircle (1 : ℚ)) := by
    rw [gaussSum_dyadicCyclic_eq_sum_range]
    simp only [show 2 ^ 2 = 0 + 1 + 1 + 1 + 1 by rfl, sum_range_succ, sum_range_zero, term]
    norm_num [-expCircle_coe]
    rw [show (θ : ℚ) * 4 / 8 = θ / 2 by ring, show (θ : ℚ) * 9 / 8 = θ / 8 + θ by ring,
      QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _)]
    ring
  obtain ⟨m, hm⟩ := Int.eight_dvd_sq_sub_one_of_odd hθ
  replace hm : (θ : ℚ) ^ 2 - 1 = 8 * m := by exact_mod_cast hm
  obtain ⟨t, rfl⟩ := hθ
  rw [hsum, show (((2 * t + 1 : ℤ) : ℚ) / 2) = 1 / 2 + (t : ℚ) by push_cast; ring,
    QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _), expCircle_half,
    show (2 * ((2 * t + 1 : ℤ) : ℚ) + 2 * (((2 * t + 1 : ℤ) : ℚ) ^ 2 - 1)) / 16 =
      ((2 * t + 1 : ℤ) : ℚ) / 8 + (m : ℚ) by linear_combination hm / 8,
    QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _),
    Real.sqrt_sq zero_le_two]
  push_cast
  ring

/-- **The Gauss sum of Nikulin's dyadic generator** `q_θ^{(2)}(2^k)`, for odd `θ` and `k ≥ 1`:

```text
G(q_θ^{(2)}(2^k)) = √(2^k) · e^{2πi (2θ + k(θ² − 1))/16}.
```

In Nikulin's notation the exponent is `(θ + 4kω(θ))/8` with `ω(θ) = (θ² − 1)/8`, so the
Gauss-sum invariant of `q_θ^{(2)}(2^k)` is `θ + 4kω(θ) mod 8`. -/
theorem gaussSum_dyadicCyclic (hθ : Odd θ) :
    (dyadicCyclic k θ).gaussSum =
      √(2 ^ k : ℝ) * expCircle ((((2 * θ + k * (θ ^ 2 - 1)) / 16 : ℚ)) : AddCircle (1 : ℚ)) := by
  obtain ⟨m, hm⟩ := Int.eight_dvd_sq_sub_one_of_odd hθ
  replace hm : (θ : ℚ) ^ 2 - 1 = 8 * m := by exact_mod_cast hm
  -- Induction in steps of two, from the values at `k = 1` and `k = 2`.
  suffices h : ∀ j : ℕ,
      (dyadicCyclic (j + 1) θ).gaussSum = √(2 ^ (j + 1) : ℝ) *
        expCircle ((((2 * θ + ((j + 1 : ℕ) : ℚ) * (θ ^ 2 - 1)) / 16 : ℚ)) : AddCircle (1 : ℚ)) ∧
      (dyadicCyclic (j + 2) θ).gaussSum = √(2 ^ (j + 2) : ℝ) *
        expCircle ((((2 * θ + ((j + 2 : ℕ) : ℚ) * (θ ^ 2 - 1)) / 16 : ℚ)) : AddCircle (1 : ℚ)) by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
    exact (h j).1
  intro j
  induction j with
  | zero => exact ⟨by simpa using gaussSum_dyadicCyclic_one θ hθ,
      by simpa using gaussSum_dyadicCyclic_two θ hθ⟩
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    rw [gaussSum_dyadicCyclic_add_two (j + 1) θ hθ, ih.1,
      show (2 * (θ : ℚ) + ((j + 1 + 2 : ℕ) : ℚ) * ((θ : ℚ) ^ 2 - 1)) / 16 =
        (2 * θ + ((j + 1 : ℕ) : ℚ) * (θ ^ 2 - 1)) / 16 + (m : ℚ) by
        push_cast; linear_combination hm / 8,
      QuotientAddGroup.mk_add_of_mem _ (AddSubgroup.intCast_mem_zmultiples_one _),
      show (2 : ℝ) ^ (j + 1 + 2) = 2 ^ 2 * 2 ^ (j + 1) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq zero_le_two]
    push_cast
    ring

end TauCeti.FiniteQuadraticModule
