/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Minpoly.Field

import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.FieldTheory.AlgebraicClosure

/-!
# Weil numbers

Fix a real number `q > 1` and an integer `n`. An element `α` of a field `K` of characteristic zero
is a *Weil `q`-number of weight `n`* (Deligne: *pure of weight `n` relative to `q`*) if `α` is
algebraic over `ℚ` and every complex root of its minimal polynomial over `ℚ` has absolute value
`q ^ (n / 2)`. By Deligne, the eigenvalues of geometric Frobenius on the `ℓ`-adic cohomology
`H^i` of a smooth projective variety over a finite field with `q` elements are Weil `q`-numbers
of weight `i` (and algebraic integers), and the weight of a Frobenius module is read off from
them.

The predicate only depends on the minimal polynomial of `α`, so it is preserved and reflected by
field homomorphisms and does not depend on the ambient field. It is equivalent to the condition
`‖σ α‖ = q ^ (n / 2)` for every field embedding `σ` into `ℂ` of the algebraic closure of `ℚ`
in `K`. Algebraicity is part of the definition: a transcendental element has minimal polynomial
`0`, whose complex root condition would be vacuous. Integrality over `ℤ` is a separate condition:
`q⁻¹` is a Weil `q`-number of weight `-2` for every integer `q ≥ 2`, but not an algebraic integer.

## Main definitions

* `TauCeti.IsWeilNumber q n α`: `α` is a Weil `q`-number of weight `n`.

## Main results

* `TauCeti.IsWeilNumber.norm_apply_eq`: every field embedding into `ℂ` sends a Weil `q`-number
  of weight `n` to a complex number of absolute value `q ^ (n / 2)`.
* `TauCeti.isWeilNumber_iff_forall_norm_apply_eq`: over a field algebraic over `ℚ`, this
  modulus condition at every complex embedding characterizes Weil numbers.
* `TauCeti.isWeilNumber_map_iff`: field homomorphisms preserve and reflect Weil numbers.
* `TauCeti.IsWeilNumber.of_aeval_eq_zero`: a root of a nonzero rational polynomial all of whose
  complex roots have absolute value `q ^ (n / 2)` is a Weil `q`-number of weight `n`.
* `TauCeti.IsWeilNumber.ne_zero`, `TauCeti.IsWeilNumber.unique`: a Weil number is nonzero and
  its weight is unique.
* `TauCeti.IsWeilNumber.mul`, `TauCeti.IsWeilNumber.inv`, `TauCeti.IsWeilNumber.zpow`: weights
  add under products and are negated by inverses.
* `TauCeti.isWeilNumber_inv_iff`: `α⁻¹` is a Weil `q`-number of weight `n` if and only if `α` is
  one of weight `-n`.
* `TauCeti.IsWeilNumber.conj_apply`: the complex conjugate of `σ α` is `q ^ n / σ α`.
* `TauCeti.isWeilNumber_pow_iff`: `α` is a Weil `q`-number of weight `n` if and only if `α ^ r`
  is a Weil `q ^ r`-number of weight `n`, for `r ≠ 0` and `0 ≤ q`.

The file closes with the basic examples: the roots of `X² - X + 2` are Weil `2`-numbers of
weight `1`, roots of unity have weight `0`, `1 + √2` is a Weil number for no `q` and no weight
although its absolute value at one real embedding is `(1 + √2)²` raised to `1 / 2`, and `q⁻¹`
is a Weil number that is not an algebraic integer.

## References

* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS 52 (1980), §1.2, (1.2.1), (1.2.12)
  and (1.2.14).
* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), §1, (1.5.1) and (1.7).
-/

public section

open Polynomial

namespace TauCeti

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
  {q : ℝ} {n m : ℤ} {α β : K}

/-- An element `α` of a field of characteristic zero is a *Weil `q`-number of weight `n`* if
`1 < q`, `α` is algebraic over `ℚ`, and every complex root of the minimal polynomial of `α`
over `ℚ` has absolute value `q ^ (n / 2)`. -/
structure IsWeilNumber (q : ℝ) (n : ℤ) (α : K) : Prop where
  /-- The base of a Weil number is greater than `1`. -/
  one_lt : 1 < q
  /-- A Weil number is algebraic over `ℚ`. -/
  isIntegral : IsIntegral ℚ α
  /-- Every complex root of the minimal polynomial of `α` over `ℚ` (every Galois conjugate of `α`
  in `ℂ`) has absolute value `q ^ (n / 2)`. -/
  norm_eq_of_mem_aroots ⦃z : ℂ⦄ : z ∈ (minpoly ℚ α).aroots ℂ → ‖z‖ = q ^ ((n : ℝ) / 2)

/-- Unbundled form of the definition of a Weil number. -/
theorem isWeilNumber_iff : IsWeilNumber q n α ↔
    1 < q ∧ IsIntegral ℚ α ∧ ∀ z ∈ (minpoly ℚ α).aroots ℂ, ‖z‖ = q ^ ((n : ℝ) / 2) :=
  ⟨fun h ↦ ⟨h.one_lt, h.isIntegral, h.norm_eq_of_mem_aroots⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

namespace IsWeilNumber

/-- The base of a Weil number is positive. -/
theorem pos (h : IsWeilNumber q n α) : 0 < q :=
  zero_lt_one.trans h.one_lt

/-- Every field embedding into `ℂ` sends a Weil `q`-number of weight `n` to a complex number of
absolute value `q ^ (n / 2)`. -/
theorem norm_apply_eq (h : IsWeilNumber q n α) (σ : K →+* ℂ) :
    ‖σ α‖ = q ^ ((n : ℝ) / 2) := by
  refine h.norm_eq_of_mem_aroots (mem_aroots.mpr ⟨minpoly.ne_zero h.isIntegral, ?_⟩)
  have := aeval_algHom_apply σ.toRatAlgHom α (minpoly ℚ α)
  rwa [minpoly.aeval, map_zero] at this

/-- A root of a nonzero rational polynomial all of whose complex roots have absolute value
`q ^ (n / 2)` is a Weil `q`-number of weight `n`. The polynomial need not be irreducible. -/
theorem of_aeval_eq_zero {P : ℚ[X]} (hq : 1 < q) (hP : P ≠ 0) (hα : aeval α P = 0)
    (hroots : ∀ z ∈ P.aroots ℂ, ‖z‖ = q ^ ((n : ℝ) / 2)) : IsWeilNumber q n α := by
  have hle : (minpoly ℚ α).aroots ℂ ≤ P.aroots ℂ :=
    roots.le_of_dvd (Polynomial.map_ne_zero hP) (Polynomial.map_dvd _ (minpoly.dvd ℚ α hα))
  exact ⟨hq, isAlgebraic_iff_isIntegral.mp ⟨P, hP, hα⟩,
    fun z hz ↦ hroots z (Multiset.mem_of_le hle hz)⟩

/-- A Weil number is nonzero. -/
theorem ne_zero (h : IsWeilNumber q n α) : α ≠ 0 := by
  rintro rfl
  have h0 := h.norm_eq_of_mem_aroots (z := 0) (by simp [minpoly.zero])
  rw [norm_zero] at h0
  exact (Real.rpow_pos_of_pos h.pos _).ne' h0.symm

/-- The weight of a Weil `q`-number is unique. -/
theorem unique (h : IsWeilNumber q n α) (h' : IsWeilNumber q m α) : n = m := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ (minpoly ℚ α)
    (minpoly.degree_pos h.isIntegral).ne'
  have hmem : z ∈ (minpoly ℚ α).aroots ℂ := mem_aroots.mpr ⟨minpoly.ne_zero h.isIntegral, hz⟩
  have := (h.norm_eq_of_mem_aroots hmem).symm.trans (h'.norm_eq_of_mem_aroots hmem)
  rw [Real.rpow_right_inj h.pos h.one_lt.ne',
    div_left_inj₀ two_ne_zero] at this
  exact_mod_cast this

end IsWeilNumber

/-- Zero is a Weil number of no weight. -/
@[simp]
theorem not_isWeilNumber_zero : ¬IsWeilNumber q n (0 : K) :=
  fun h ↦ h.ne_zero rfl

/-- Field homomorphisms preserve and reflect Weil numbers. -/
@[simp]
theorem isWeilNumber_map_iff {F : Type*} [FunLike F K L] [RingHomClass F K L] (f : F) :
    IsWeilNumber q n (f α) ↔ IsWeilNumber q n α := by
  have hmin : minpoly ℚ (f α) = minpoly ℚ α :=
    minpoly.algHom_eq (f : K →+* L).toRatAlgHom (f : K →+* L).injective α
  have hint : IsIntegral ℚ (f α) ↔ IsIntegral ℚ α :=
    isIntegral_algHom_iff (f : K →+* L).toRatAlgHom (f : K →+* L).injective
  rw [isWeilNumber_iff, isWeilNumber_iff, hmin, hint]

/-- Over a field algebraic over `ℚ`, an element is a Weil `q`-number of weight `n` if and only
if `1 < q` and every field embedding into `ℂ` sends it to a complex number of absolute value
`q ^ (n / 2)`. -/
theorem isWeilNumber_iff_forall_norm_apply_eq [Algebra.IsAlgebraic ℚ K] :
    IsWeilNumber q n α ↔ 1 < q ∧ ∀ σ : K →+* ℂ, ‖σ α‖ = q ^ ((n : ℝ) / 2) := by
  refine ⟨fun h ↦ ⟨h.one_lt, h.norm_apply_eq⟩, fun ⟨hq, h⟩ ↦
    ⟨hq, Algebra.IsIntegral.isIntegral α, fun z hz ↦ ?_⟩⟩
  have hz' : z ∈ (minpoly ℚ α).rootSet ℂ := mem_rootSet.mpr (mem_aroots.mp hz)
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hz'
  obtain ⟨ψ, rfl⟩ := hz'
  exact h ψ.toRingHom

/-- An algebraic element of `K` lies in the algebraic closure of `ℚ` in `K`. Weil-number
statements about such elements are transported to that subfield with `isWeilNumber_map_iff`. -/
private theorem exists_algebraicClosure_val_eq (hα : IsIntegral ℚ α) :
    ∃ a : algebraicClosure ℚ K, (algebraicClosure ℚ K).val a = α :=
  ⟨⟨α, mem_algebraicClosure_iff'.mpr hα⟩, IntermediateField.val_mk _ _⟩

/-- An algebraic element `α` is a Weil `q`-number of weight `n` if and only if `1 < q` and every
field embedding into `ℂ` of the algebraic closure of `ℚ` in `K` sends `α` to a complex number of
absolute value `q ^ (n / 2)`. -/
theorem isWeilNumber_iff_forall_algebraicClosure (hα : IsIntegral ℚ α) :
    IsWeilNumber q n α ↔
      1 < q ∧ ∀ σ : algebraicClosure ℚ K →+* ℂ,
        ‖σ ⟨α, mem_algebraicClosure_iff'.mpr hα⟩‖ = q ^ ((n : ℝ) / 2) :=
  (isWeilNumber_map_iff (algebraicClosure ℚ K).val
    (α := ⟨α, mem_algebraicClosure_iff'.mpr hα⟩)).trans
    (isWeilNumber_iff_forall_norm_apply_eq (K := algebraicClosure ℚ K))

/-- A root of unity is a Weil `q`-number of weight `0` for every `q > 1`. -/
theorem isWeilNumber_of_pow_eq_one {k : ℕ} (hq : 1 < q) (hk : k ≠ 0) (hα : α ^ k = 1) :
    IsWeilNumber q 0 α := by
  refine IsWeilNumber.of_aeval_eq_zero (P := X ^ k - 1) hq (X_pow_sub_C_ne_zero
    (Nat.pos_of_ne_zero hk) 1) (by simp [hα]) fun z hz ↦ ?_
  rw [mem_aroots] at hz
  simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at hz
  simpa using Complex.norm_eq_one_of_pow_eq_one hz.2 hk

/-- The element `1` is a Weil `q`-number of weight `0` for every `q > 1`. -/
theorem isWeilNumber_one (hq : 1 < q) : IsWeilNumber q 0 (1 : K) :=
  isWeilNumber_of_pow_eq_one hq one_ne_zero (one_pow 1)

namespace IsWeilNumber

/-- The product of Weil `q`-numbers of weights `n` and `m` is a Weil `q`-number of weight
`n + m`. -/
theorem mul (hα : IsWeilNumber q n α) (hβ : IsWeilNumber q m β) :
    IsWeilNumber q (n + m) (α * β) := by
  have hq : 0 < q := hα.pos
  obtain ⟨a, rfl⟩ := exists_algebraicClosure_val_eq hα.isIntegral
  obtain ⟨b, rfl⟩ := exists_algebraicClosure_val_eq hβ.isIntegral
  rw [isWeilNumber_map_iff, isWeilNumber_iff_forall_norm_apply_eq] at hα hβ
  rw [← map_mul, isWeilNumber_map_iff, isWeilNumber_iff_forall_norm_apply_eq]
  refine ⟨hα.1, fun σ ↦ ?_⟩
  rw [map_mul, norm_mul, hα.2, hβ.2, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

/-- The inverse of a Weil `q`-number of weight `n` is a Weil `q`-number of weight `-n`. -/
theorem inv (h : IsWeilNumber q n α) : IsWeilNumber q (-n) α⁻¹ := by
  obtain ⟨a, rfl⟩ := exists_algebraicClosure_val_eq h.isIntegral
  have hq : 0 < q := h.pos
  rw [isWeilNumber_map_iff, isWeilNumber_iff_forall_norm_apply_eq] at h
  rw [← map_inv₀, isWeilNumber_map_iff, isWeilNumber_iff_forall_norm_apply_eq]
  refine ⟨h.1, fun σ ↦ ?_⟩
  rw [map_inv₀, norm_inv, h.2, ← Real.rpow_neg hq.le]
  congr 1
  push_cast
  ring

/-- A natural power `α ^ k` of a Weil `q`-number `α` of weight `n` is a Weil `q`-number of weight
`k * n`. -/
theorem pow (h : IsWeilNumber q n α) (k : ℕ) : IsWeilNumber q (k * n) (α ^ k) := by
  induction k with
  | zero => simpa using isWeilNumber_one h.one_lt
  | succ k ih => simpa [pow_succ, add_mul] using ih.mul h

/-- An integer power `α ^ k` of a Weil `q`-number `α` of weight `n` is a Weil `q`-number of
weight `k * n`. -/
theorem zpow (h : IsWeilNumber q n α) (k : ℤ) : IsWeilNumber q (k * n) (α ^ k) := by
  cases k with
  | ofNat k => simpa using h.pow k
  | negSucc k =>
    rw [zpow_negSucc, show Int.negSucc k * n = -(((k + 1 : ℕ) : ℤ) * n) by
      rw [Int.negSucc_eq]; push_cast; ring]
    exact (h.pow (k + 1)).inv

/-- The complex conjugate of the image of a Weil `q`-number `α` of weight `n` under a field
embedding `σ` into `ℂ` is `q ^ n / σ α`. -/
theorem conj_apply (h : IsWeilNumber q n α) (σ : K →+* ℂ) :
    starRingEnd ℂ (σ α) = (q : ℂ) ^ n / σ α := by
  have hσ : σ α ≠ 0 := (map_ne_zero σ).mpr h.ne_zero
  have hnorm : (‖σ α‖ : ℂ) ^ 2 = (q : ℂ) ^ n := by
    rw [h.norm_apply_eq, ← Complex.ofReal_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul h.pos.le]
    norm_num [Real.rpow_intCast]
  rw [eq_div_iff hσ, mul_comm, Complex.mul_conj', hnorm]

/-- If `q` is rational and `α` is a Weil `q`-number of weight `n`, then the image of
`α + q ^ n * α⁻¹` under every field embedding of `K` into `ℂ` is fixed by complex
conjugation. -/
theorem conj_apply_add_zpow_mul_inv {q : ℚ} (h : IsWeilNumber (q : ℝ) n α) (σ : K →+* ℂ) :
    starRingEnd ℂ (σ (α + (q : K) ^ n * α⁻¹)) = σ (α + (q : K) ^ n * α⁻¹) := by
  have hσ : σ α ≠ 0 := (map_ne_zero σ).mpr h.ne_zero
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast h.pos.ne'
  have hc := h.conj_apply σ
  simp only [map_add, map_mul, map_zpow₀, map_ratCast, map_inv₀, Complex.ofReal_ratCast] at hc ⊢
  rw [hc]
  field_simp
  ring

end IsWeilNumber

/-- The inverse `α⁻¹` is a Weil `q`-number of weight `n` if and only if `α` is a Weil `q`-number
of weight `-n`. -/
@[simp]
theorem isWeilNumber_inv_iff : IsWeilNumber q n α⁻¹ ↔ IsWeilNumber q (-n) α :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, fun h ↦ by simpa only [neg_neg] using h.inv⟩

/-- A rational number `q > 1` is a Weil `q`-number of weight `2`. -/
theorem isWeilNumber_ratCast {q : ℚ} (hq : 1 < q) : IsWeilNumber (q : ℝ) 2 (q : K) := by
  refine IsWeilNumber.of_aeval_eq_zero (P := X - C q) (by exact_mod_cast hq) (X_sub_C_ne_zero q)
    (by simp) fun z hz ↦ ?_
  rw [aroots_X_sub_C, Multiset.mem_singleton] at hz
  rw [hz, eq_ratCast, Complex.norm_ratCast]
  norm_num [(zero_lt_one.trans hq).le]

/-- If `q > 1` is rational, then `q ^ k` is a Weil `q`-number of weight `2 * k` for every integer
`k`. -/
theorem isWeilNumber_ratCast_zpow {q : ℚ} (hq : 1 < q) (k : ℤ) :
    IsWeilNumber (q : ℝ) (2 * k) ((q : K) ^ k) := by
  simpa [mul_comm] using (isWeilNumber_ratCast (K := K) hq).zpow k

/-- For `r ≠ 0` and `q ≥ 0`, an element `α` is a Weil `q`-number of weight `n` if and only if
`α ^ r` is a Weil `q ^ r`-number of weight `n`. This is the effect on weights of replacing a
finite field with `q` elements by its extension of degree `r`. -/
theorem isWeilNumber_pow_iff {r : ℕ} (hr : r ≠ 0) (hq : 0 ≤ q) :
    IsWeilNumber (q ^ r) n (α ^ r) ↔ IsWeilNumber q n α := by
  by_cases hα : IsIntegral ℚ α
  · obtain ⟨a, rfl⟩ := exists_algebraicClosure_val_eq hα
    rw [← map_pow, isWeilNumber_map_iff, isWeilNumber_map_iff,
      isWeilNumber_iff_forall_norm_apply_eq, isWeilNumber_iff_forall_norm_apply_eq,
      one_lt_pow_iff_of_nonneg hq hr]
    refine and_congr_right fun _ ↦ forall_congr' fun σ ↦ ?_
    rw [map_pow, norm_pow, ← Real.rpow_pow_comm hq,
      pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hq _) hr]
  · exact iff_of_false (fun h ↦ hα (IsIntegral.of_pow (Nat.pos_of_ne_zero hr) h.isIntegral))
      fun h ↦ hα h.isIntegral

/-! ### Examples -/

/-- The roots `(1 ± i√7) / 2` of `X² - X + 2` are Weil `2`-numbers of weight `1`. -/
theorem isWeilNumber_of_sq_sub_add_two (hα : α ^ 2 - α + 2 = 0) : IsWeilNumber 2 1 α := by
  have hmonic : (X ^ 2 - X + 2 : ℚ[X]).Monic := by monicity!
  refine IsWeilNumber.of_aeval_eq_zero (P := X ^ 2 - X + 2) one_lt_two hmonic.ne_zero
    (by simpa [map_ofNat] using hα) fun z hz ↦ ?_
  rw [mem_aroots] at hz
  have hz' : z ^ 2 - z + 2 = 0 := by simpa [map_ofNat] using hz.2
  have hre := congrArg Complex.re hz'
  have him := congrArg Complex.im hz'
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, sq,
    Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.zero_re,
    Complex.zero_im] at hre him
  have hnorm : Complex.normSq z = 2 := by
    rw [Complex.normSq_apply]
    have hx : z.re = 1 / 2 := by
      by_contra hx
      have hy : z.im = 0 := by
        have : z.im * (2 * z.re - 1) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (by linarith) hx
      rw [hy] at hre
      nlinarith [sq_nonneg (z.re - 1 / 2)]
    rw [hx] at hre ⊢
    linarith
  rw [Complex.norm_def, hnorm, Real.sqrt_eq_rpow]
  norm_num

/-- `1 + √2` is a Weil `q`-number for no `q` and no weight `n`: its conjugate `1 - √2` has a
different absolute value. Its absolute value at the real embedding alone is `q ^ (1 / 2)` for
`q = (1 + √2) ^ 2`, so the condition at a single complex embedding does not suffice. -/
theorem not_isWeilNumber_one_add_sqrt_two : ¬IsWeilNumber q n (1 + √2 : ℝ) := by
  intro h
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have hP : (X ^ 2 - 2 * X - 1 : ℚ[X]) = minpoly ℚ (1 + √2 : ℝ) := by
    refine minpoly.eq_of_irreducible_of_monic ?_
      (by simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
          linear_combination hs) (by monicity!)
    have hdeg : (X ^ 2 - 2 * X - 1 : ℚ[X]).natDegree = 2 := by compute_degree!
    refine irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) fun r hr ↦ ?_
    simp only [IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one] at hr
    have hr' : ((r : ℝ) - 1) ^ 2 = 2 := by
      exact_mod_cast (by linear_combination hr : ((r - 1) ^ 2 : ℚ) = 2)
    refine irrational_sqrt_two ⟨|r - 1|, ?_⟩
    push_cast
    rw [← Real.sqrt_sq_eq_abs, hr']
  have hroot (x : ℝ) (hx : x ^ 2 - 2 * x - 1 = 0) : ‖(x : ℂ)‖ = q ^ ((n : ℝ) / 2) := by
    refine h.norm_eq_of_mem_aroots (mem_aroots.mpr ⟨minpoly.ne_zero h.isIntegral, ?_⟩)
    rw [← hP]
    simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
    exact_mod_cast hx
  have h₁ := hroot (1 + √2) (by linear_combination hs)
  have h₂ := hroot (1 - √2) (by linear_combination hs)
  rw [Complex.norm_real, Real.norm_eq_abs] at h₁ h₂
  have hlt := Real.one_lt_sqrt_two
  rw [abs_of_pos (by linarith), ← h₂, abs_of_neg (by linarith)] at h₁
  linarith

/-- For a natural number `q ≥ 2`, the rational number `q⁻¹` is a Weil `q`-number of weight
`-2`. -/
theorem isWeilNumber_inv_natCast {q : ℕ} (hq : 2 ≤ q) :
    IsWeilNumber (q : ℝ) (-2) ((q : ℚ)⁻¹) := by
  have hq' : (1 : ℚ) < q := by exact_mod_cast hq
  simpa using (isWeilNumber_ratCast (K := ℚ) hq').inv

/- For a natural number `q ≥ 2`, the rational number `q⁻¹` is not an algebraic integer, although
it is a Weil `q`-number (`TauCeti.isWeilNumber_inv_natCast`): being a Weil number does not imply
integrality. -/
example {q : ℕ} (hq : 2 ≤ q) : ¬IsIntegral ℤ ((q : ℚ)⁻¹) := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  rintro ⟨y, hy⟩
  rw [eq_intCast] at hy
  have hq' : (1 : ℚ) < q := by exact_mod_cast hq
  have h0 : (0 : ℚ) < y := hy ▸ by positivity
  have h1 : (y : ℚ) < 1 := hy ▸ inv_lt_one_of_one_lt₀ hq'
  have : (0 : ℤ) < y ∧ y < 1 := ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
  omega

end TauCeti
