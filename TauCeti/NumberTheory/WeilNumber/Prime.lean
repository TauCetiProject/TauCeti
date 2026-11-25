/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import TauCeti.NumberTheory.WeilNumber.Basic

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.RingTheory.DedekindDomain.SInteger.Localization

/-!
# `l`-Weil numbers

Fix a natural number `l > 1`, in practice a prime, and an integer `w`. An element `α` of a field
of characteristic zero is an *`l`-Weil number of weight `w`* if it is a Weil `l`-number of weight
`w` (every complex conjugate of `α` has absolute value `l ^ (w / 2)`) and it is a unit at every
finite place not above `l`. The unit condition is stated without a choice of number field: some
`l ^ n * α` and `l ^ n * α⁻¹` are algebraic integers, that is, `α` is a unit of the integral
closure of `ℤ[1/l]`. For `α` in a number field `K` this is the condition that `α` is an `S`-unit
for the set `S` of height-one primes of `𝓞 K` containing `l`, that is, `α` has valuation one at
every prime not containing `l` (`TauCeti.isPrimeWeilNumber_iff_mem_unit`). Since field
homomorphisms preserve and reflect the whole predicate (`TauCeti.isPrimeWeilNumber_map_iff`), it
does not depend on the number field containing `α`. Negative weights are allowed, and `α` need not
be integral at `l`.

These numbers are the eigenvalues allowed for an `l`-Weil point of a linear algebraic group over
`ℚ`, a rational point all of whose eigenvalues in a faithful representation are `l`-Weil numbers.
The eigenvalues of a geometric Frobenius on `H¹` of an abelian variety over a finite field of
characteristic `p` are `p`-Weil numbers.

## Main definitions

* `TauCeti.IsPrimeWeilNumber l w α`: `α` is an `l`-Weil number of weight `w`.
* `TauCeti.primeWeilNumbers l K`: the subgroup of `Kˣ` of `l`-Weil numbers of all weights.

## Main results

* `TauCeti.IsPrimeWeilNumber.unique`: the weight is unique.
* `TauCeti.isPrimeWeilNumber_map_iff`: field homomorphisms preserve and reflect `l`-Weil
  numbers.
* `TauCeti.IsPrimeWeilNumber.of_aeval_minpoly_eq_zero`: Galois conjugates of an `l`-Weil number
  are `l`-Weil numbers of the same weight.
* `TauCeti.IsPrimeWeilNumber.mul`, `TauCeti.IsPrimeWeilNumber.inv`,
  `TauCeti.IsPrimeWeilNumber.zpow`: weights add under products and are negated by inverses.
* `TauCeti.isPrimeWeilNumber_of_pow_eq_one`: roots of unity are `l`-Weil numbers of weight `0`.
* `TauCeti.isPrimeWeilNumber_iff_mem_unit`: in a number field, the unit condition is
  membership in the `S`-units for the primes `S` containing `l`.
* `TauCeti.isPrimeWeilNumber_natCast`, `TauCeti.not_isPrimeWeilNumber_natCast`: `l` is an
  `l`-Weil number of weight `2`, while a prime `q` not dividing `l` is an `l`-Weil number of no
  weight, although it is a Weil `q`-number of weight `2`.

## References

* M. Kisin, K. Madapusi Pera and S. W. Shin, *Honda–Tate theory for Shimura varieties*, Duke
  Math. J. 171 (2022), §2.2.1.
-/

public section

open Polynomial IsDedekindDomain NumberField

open scoped IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
  {l : ℕ} {w w' : ℤ} {α β : K}

/-- An element `α` of a field of characteristic zero is an *`l`-Weil number of weight `w`* if it is
a Weil `l`-number of weight `w` and a unit at every finite place not above `l`: some `l ^ n * α`
and `l ^ n * α⁻¹` are algebraic integers. -/
structure IsPrimeWeilNumber (l : ℕ) (w : ℤ) (α : K) : Prop where
  /-- An `l`-Weil number of weight `w` is a Weil `l`-number of weight `w`. -/
  isWeilNumber : IsWeilNumber l w α
  /-- An `l`-Weil number is a unit away from `l`: some `l ^ n * α` and `l ^ n * α⁻¹` are
  algebraic integers. -/
  exists_isIntegral : ∃ n : ℕ, IsIntegral ℤ ((l : K) ^ n * α) ∧ IsIntegral ℤ ((l : K) ^ n * α⁻¹)

/-- Unbundled form of the definition of an `l`-Weil number. -/
theorem isPrimeWeilNumber_iff : IsPrimeWeilNumber l w α ↔ IsWeilNumber l w α ∧
    ∃ n : ℕ, IsIntegral ℤ ((l : K) ^ n * α) ∧ IsIntegral ℤ ((l : K) ^ n * α⁻¹) :=
  ⟨fun h ↦ ⟨h.isWeilNumber, h.exists_isIntegral⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

namespace IsPrimeWeilNumber

/-- The base of an `l`-Weil number is greater than `1`. -/
theorem one_lt (h : IsPrimeWeilNumber l w α) : 1 < l := by
  exact_mod_cast h.isWeilNumber.one_lt

/-- An `l`-Weil number is nonzero. -/
theorem ne_zero (h : IsPrimeWeilNumber l w α) : α ≠ 0 :=
  h.isWeilNumber.ne_zero

/-- The weight of an `l`-Weil number is unique. -/
theorem unique (h : IsPrimeWeilNumber l w α) (h' : IsPrimeWeilNumber l w' α) : w = w' :=
  h.isWeilNumber.unique h'.isWeilNumber

end IsPrimeWeilNumber

/-- Zero is an `l`-Weil number of no weight. -/
@[simp]
theorem not_isPrimeWeilNumber_zero : ¬IsPrimeWeilNumber l w (0 : K) :=
  fun h ↦ h.ne_zero rfl

/-- Field homomorphisms preserve and reflect `l`-Weil numbers. In particular the predicate does
not depend on the field containing `α`. -/
@[simp]
theorem isPrimeWeilNumber_map_iff {F : Type*} [FunLike F K L] [RingHomClass F K L] (f : F) :
    IsPrimeWeilNumber l w (f α) ↔ IsPrimeWeilNumber l w α := by
  have hint (x : K) : IsIntegral ℤ (f x) ↔ IsIntegral ℤ x :=
    isIntegral_algHom_iff (f : K →+* L).toIntAlgHom (f : K →+* L).injective
  have hmul (n : ℕ) (x : K) : (l : L) ^ n * f x = f ((l : K) ^ n * x) := by
    rw [map_mul, map_pow, map_natCast]
  simp only [isPrimeWeilNumber_iff, isWeilNumber_map_iff, ← map_inv₀, hmul, hint]

namespace IsPrimeWeilNumber

/-- **Galois conjugates of an `l`-Weil number.** A root `β`, in any field of characteristic zero,
of the minimal polynomial of an `l`-Weil number `α` of weight `w` is an `l`-Weil number of weight
`w`. -/
theorem of_aeval_minpoly_eq_zero (h : IsPrimeWeilNumber l w α) {β : L}
    (hβ : aeval β (minpoly ℚ α) = 0) : IsPrimeWeilNumber l w β := by
  have hα := h.isWeilNumber.isIntegral
  let ψ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := L) hα).symm
    ⟨β, mem_aroots.2 ⟨minpoly.ne_zero hα, hβ⟩⟩
  have hψ : ψ (IntermediateField.AdjoinSimple.gen ℚ α) = β :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hα _
  have hgen : IsPrimeWeilNumber l w (IntermediateField.AdjoinSimple.gen ℚ α) := by
    rwa [← isPrimeWeilNumber_map_iff (IntermediateField.val ℚ⟮α⟯), IntermediateField.coe_val,
      IntermediateField.AdjoinSimple.coe_gen]
  rw [← hψ]
  exact (isPrimeWeilNumber_map_iff ψ).2 hgen

/-- The product of `l`-Weil numbers of weights `w` and `w'` is an `l`-Weil number of weight
`w + w'`. -/
theorem mul (hα : IsPrimeWeilNumber l w α) (hβ : IsPrimeWeilNumber l w' β) :
    IsPrimeWeilNumber l (w + w') (α * β) := by
  obtain ⟨n, hn, hn'⟩ := hα.exists_isIntegral
  obtain ⟨m, hm, hm'⟩ := hβ.exists_isIntegral
  refine ⟨hα.isWeilNumber.mul hβ.isWeilNumber, n + m, ?_, ?_⟩
  · convert hn.mul hm using 1
    ring
  · convert hn'.mul hm' using 1
    rw [mul_inv]
    ring

/-- The inverse of an `l`-Weil number of weight `w` is an `l`-Weil number of weight `-w`. -/
theorem inv (h : IsPrimeWeilNumber l w α) : IsPrimeWeilNumber l (-w) α⁻¹ := by
  obtain ⟨n, hn, hn'⟩ := h.exists_isIntegral
  exact ⟨h.isWeilNumber.inv, n, hn', by simpa using hn⟩

end IsPrimeWeilNumber

/-- The inverse `α⁻¹` is an `l`-Weil number of weight `w` if and only if `α` is an `l`-Weil
number of weight `-w`. -/
@[simp]
theorem isPrimeWeilNumber_inv_iff : IsPrimeWeilNumber l w α⁻¹ ↔ IsPrimeWeilNumber l (-w) α :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, fun h ↦ by simpa only [neg_neg] using h.inv⟩

/-- A root of unity is an `l`-Weil number of weight `0` for every `l > 1`. -/
theorem isPrimeWeilNumber_of_pow_eq_one {k : ℕ} (hl : 1 < l) (hk : k ≠ 0) (hα : α ^ k = 1) :
    IsPrimeWeilNumber l 0 α := by
  have hint {x : K} (hx : x ^ k = 1) : IsIntegral ℤ x :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (hx ▸ isIntegral_one)
  refine ⟨isWeilNumber_of_pow_eq_one (by exact_mod_cast hl) hk hα, 0, ?_, ?_⟩
  · simpa using hint hα
  · simpa using hint (by rw [inv_pow, hα, inv_one])

/-- The element `1` is an `l`-Weil number of weight `0` for every `l > 1`. -/
theorem isPrimeWeilNumber_one (hl : 1 < l) : IsPrimeWeilNumber l 0 (1 : K) :=
  isPrimeWeilNumber_of_pow_eq_one hl one_ne_zero (one_pow 1)

namespace IsPrimeWeilNumber

/-- A natural power `α ^ k` of an `l`-Weil number `α` of weight `w` is an `l`-Weil number of
weight `k * w`. -/
theorem pow (h : IsPrimeWeilNumber l w α) (k : ℕ) : IsPrimeWeilNumber l (k * w) (α ^ k) := by
  induction k with
  | zero => simpa using isPrimeWeilNumber_one h.one_lt
  | succ k ih => simpa [pow_succ, add_mul] using ih.mul h

/-- An integer power `α ^ k` of an `l`-Weil number `α` of weight `w` is an `l`-Weil number of
weight `k * w`. -/
theorem zpow (h : IsPrimeWeilNumber l w α) (k : ℤ) : IsPrimeWeilNumber l (k * w) (α ^ k) := by
  cases k with
  | ofNat k => simpa using h.pow k
  | negSucc k =>
    rw [zpow_negSucc, show Int.negSucc k * w = -(((k + 1 : ℕ) : ℤ) * w) by
      rw [Int.negSucc_eq]; push_cast; ring]
    exact (h.pow (k + 1)).inv

end IsPrimeWeilNumber

/-- The `l`-Weil numbers of all weights in `K` form a subgroup of `Kˣ`; weights add under
products (`TauCeti.IsPrimeWeilNumber.mul`). -/
def primeWeilNumbers (l : ℕ) (K : Type*) [Field K] [Algebra ℚ K] [Fact (1 < l)] :
    Subgroup Kˣ where
  carrier := {u | ∃ w, IsPrimeWeilNumber l w (u : K)}
  mul_mem' := fun ⟨w, h⟩ ⟨w', h'⟩ ↦ ⟨w + w', by simpa using h.mul h'⟩
  one_mem' := ⟨0, by simpa using isPrimeWeilNumber_one (K := K) Fact.out⟩
  inv_mem' := fun ⟨w, h⟩ ↦ ⟨-w, by simpa using h.inv⟩

/-- A unit of `K` lies in `primeWeilNumbers l K` exactly when it is an `l`-Weil number of some
weight. -/
@[simp]
theorem mem_primeWeilNumbers [Fact (1 < l)] {u : Kˣ} :
    u ∈ primeWeilNumbers l K ↔ ∃ w, IsPrimeWeilNumber l w (u : K) :=
  Iff.rfl

/-! ### The unit condition in a number field -/

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The unit condition in a number field.** A unit `u` of a number field `K` is an `l`-Weil
number of weight `w` exactly when it is a Weil `l`-number of weight `w` and an `S`-unit for the
set `S` of height-one primes of `𝓞 K` containing `l`, that is, `u` has valuation one at every
finite place of `K` not above `l` (`Set.mem_unit_iff`). -/
theorem isPrimeWeilNumber_iff_mem_unit {u : Kˣ} :
    IsPrimeWeilNumber l w (u : K) ↔ IsWeilNumber l w (u : K) ∧
      u ∈ {v : HeightOneSpectrum (𝓞 K) | (l : 𝓞 K) ∈ v.asIdeal}.unit K := by
  set S := {v : HeightOneSpectrum (𝓞 K) | (l : 𝓞 K) ∈ v.asIdeal}
  have hint (x : K) : (∃ n : ℕ, IsIntegral ℤ ((l : K) ^ n * x)) ↔ x ∈ S.integer K := by
    rw [← map_natCast (algebraMap (𝓞 K) K) l]
    exact exists_isIntegral_pow_mul_iff_mem_integer K _ x
  have hle {n m : ℕ} {x : K} (hx : IsIntegral ℤ ((l : K) ^ n * x)) :
      IsIntegral ℤ ((l : K) ^ (n + m) * x) := by
    convert ((isIntegral_natCast l).pow m).mul hx using 1
    ring
  rw [isPrimeWeilNumber_iff, and_congr_right_iff]
  refine fun _ ↦ ⟨fun ⟨n, hn, hn'⟩ ↦ ?_, fun hu ↦ ?_⟩
  · let x : (S.integer K)ˣ := ⟨⟨u, (hint _).1 ⟨n, hn⟩⟩, ⟨_, (hint _).1 ⟨n, hn'⟩⟩,
      Subtype.ext (mul_inv_cancel₀ u.ne_zero), Subtype.ext (inv_mul_cancel₀ u.ne_zero)⟩
    convert ((S.unitEquivUnitsInteger K).symm x).property
    rw [Set.unitEquivUnitsInteger_symm_apply_coe]
    exact Units.ext (Units.val_mk0 _).symm
  have hS {y : Kˣ} (hy : y ∈ S.unit K) : (y : K) ∈ S.integer K :=
    Set.val_unitEquivUnitsInteger_apply_coe S K ⟨y, hy⟩ ▸
      (S.unitEquivUnitsInteger K ⟨y, hy⟩).val.property
  obtain ⟨n, hn⟩ := (hint _).2 (hS hu)
  obtain ⟨m, hm⟩ := (hint _).2 (hS (inv_mem hu))
  rw [Units.val_inv_eq_inv_val] at hm
  exact ⟨n + m, hle hn, add_comm m n ▸ hle hm⟩

end NumberField

/-! ### Examples -/

/-- For `l > 1`, the natural number `l` is an `l`-Weil number of weight `2`. -/
theorem isPrimeWeilNumber_natCast (hl : 1 < l) : IsPrimeWeilNumber l 2 (l : K) := by
  have := algebraRat.charZero K
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨?_, 1, ?_, ?_⟩
  · simpa using isWeilNumber_ratCast (K := K) (q := l) (by exact_mod_cast hl)
  · exact (isIntegral_natCast l).pow 1 |>.mul (isIntegral_natCast l)
  · simpa [hl0] using isIntegral_one (R := ℤ) (B := K)

/-- A prime `q` not dividing `l` is an `l`-Weil number of no weight: it is not a unit at `q`.
It is a Weil `q`-number of weight `2` (`TauCeti.isWeilNumber_ratCast`). -/
theorem not_isPrimeWeilNumber_natCast {q : ℕ} (hq : q.Prime) (hql : ¬q ∣ l) :
    ¬IsPrimeWeilNumber l w (q : K) := by
  rintro ⟨-, n, -, hn⟩
  have hcast : (l : K) ^ n * (q : K)⁻¹ = algebraMap ℚ K ((l : ℚ) ^ n / q) := by
    rw [map_div₀, map_pow, map_natCast, map_natCast, div_eq_mul_inv]
  rw [hcast] at hn
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algHom_iff (algebraMap ℚ K).toIntAlgHom (algebraMap ℚ K).injective).1 hn)
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hy' : (((l : ℤ) ^ n : ℤ) : ℚ) = ((q * y : ℤ) : ℚ) := by
    rw [eq_intCast] at hy
    push_cast
    rw [hy]
    field_simp
  have hdvd : (q : ℤ) ∣ (l : ℤ) ^ n := ⟨y, by exact_mod_cast hy'⟩
  exact hql (hq.dvd_of_dvd_pow (by exact_mod_cast hdvd))

end TauCeti
