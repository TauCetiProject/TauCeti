/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The `p`-part and the `p`-free part of an element of finite order

This file defines two power-based constructions, `TauCeti.pFreePart p x` and
`TauCeti.pPart p x`. When `p` is prime and `x` has finite order, they give the unique
factorisation of `x` as a product `x = s * u` of two commuting elements with the order of `s`
prime to `p` and the order of `u` a power of `p`. Their orders are respectively the complementary
part `ordCompl[p] (orderOf x)` and the projected part `ordProj[p] (orderOf x)`. In the
group-theoretic literature the two are the `p'`-part and the `p`-part of `x`.

Both factors are powers of `x`, so anything commuting with `x` commutes with both; this is how the
factorisation gets used, since it lets a `p`-subgroup be attached to `x` inside the centraliser of
its `p`-free factor.

## Main definitions

* `TauCeti.pFreePart p x`: the power-based construction underlying the `p`-free factor.
* `TauCeti.pPart p x`: the complementary construction underlying the `p`-power factor.

## Main results

* `TauCeti.pFreePart_mul_pPart`: the two factors multiply back to `x`.
* `TauCeti.commute_pFreePart_pPart`: the two factors commute.
* `TauCeti.commute_pFreePart`, `TauCeti.commute_pPart`: anything commuting with `x` commutes with
  both factors.
* `TauCeti.orderOf_pFreePart`, `TauCeti.orderOf_pPart`: when `p` is prime and `x` has finite
  order, their orders are `ordCompl[p] (orderOf x)` and `ordProj[p] (orderOf x)`.
* `TauCeti.eq_pFreePart`, `TauCeti.eq_pPart`: the factorisation is the only one of its kind, with
  `TauCeti.pFreePart_eq_self`, `TauCeti.pPart_eq_one`, `TauCeti.pPart_eq_self` and
  `TauCeti.pFreePart_eq_one` its degenerate cases.
* `TauCeti.pFreePart_conj`, `TauCeti.pPart_conj`: conjugation transports both factors.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II, §10.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {p : ℕ} {x : G}

/-- The exponent cutting out the `p`-free part of an element of order `n`: it is divisible by
`ordProj[p] n`, and Euler's theorem makes it congruent to `1` modulo `ordCompl[p] n`. -/
private noncomputable def pFreeExponent (p : ℕ) (x : G) : ℕ :=
  (ordProj[p] (orderOf x)) ^ (ordCompl[p] (orderOf x)).totient

/-- The power of `x` that gives its **`p`-free part** when `p` is prime and `x` has finite order.
Together with `TauCeti.pPart p x`, it factors `x` into two commuting elements. -/
noncomputable def pFreePart (p : ℕ) (x : G) : G := x ^ pFreeExponent p x

/-- The element complementary to `TauCeti.pFreePart p x` in `x`; when `p` is prime and `x` has
finite order, it is the **`p`-part** of `x`. -/
noncomputable def pPart (p : ℕ) (x : G) : G := (pFreePart p x)⁻¹ * x

/-- The `p`-free and `p`-parts of `x` multiply back to `x`. -/
@[simp]
theorem pFreePart_mul_pPart (p : ℕ) (x : G) : pFreePart p x * pPart p x = x :=
  mul_inv_cancel_left _ _

/-- The `p`-free part of `x` is a power of `x`. -/
theorem pFreePart_mem_zpowers (p : ℕ) (x : G) : pFreePart p x ∈ Subgroup.zpowers x := by
  rw [pFreePart]
  exact pow_mem (Subgroup.mem_zpowers x) _

/-- The `p`-part of `x` is a power of `x`. -/
theorem pPart_mem_zpowers (p : ℕ) (x : G) : pPart p x ∈ Subgroup.zpowers x :=
  mul_mem (inv_mem (pFreePart_mem_zpowers p x)) (Subgroup.mem_zpowers x)

/-- The `p`-free and `p`-parts of `x` commute. -/
theorem commute_pFreePart_pPart (p : ℕ) (x : G) : Commute (pFreePart p x) (pPart p x) := by
  obtain ⟨a, ha⟩ := pFreePart_mem_zpowers p x
  obtain ⟨b, hb⟩ := pPart_mem_zpowers p x
  rw [← ha, ← hb]
  exact (Commute.refl x).zpow_zpow a b

/-- An element commuting with `x` commutes with the `p`-free part of `x`. -/
theorem commute_pFreePart (p : ℕ) {y : G} (h : Commute y x) : Commute y (pFreePart p x) :=
  h.pow_right _

/-- An element commuting with `x` commutes with the `p`-part of `x`. -/
theorem commute_pPart (p : ℕ) {y : G} (h : Commute y x) : Commute y (pPart p x) := by
  rw [pPart]
  exact ((commute_pFreePart p h).inv_right).mul_right h

/-- The reversed product of the `p`-part and `p`-free part of `x` is `x`. -/
@[simp]
theorem pPart_mul_pFreePart (p : ℕ) (x : G) : pPart p x * pFreePart p x = x := by
  rw [← (commute_pFreePart_pPart p x).eq, pFreePart_mul_pPart]

@[simp]
theorem pFreePart_one (p : ℕ) : pFreePart p (1 : G) = 1 := one_pow _

@[simp]
theorem pPart_one (p : ℕ) : pPart p (1 : G) = 1 := by rw [pPart, pFreePart_one, inv_one, mul_one]

/-- **Conjugation transports the `p`-free part.**  Both factors are powers of `x` cut out by an
exponent that only depends on the order of `x`, and conjugation preserves orders. -/
@[simp]
theorem pFreePart_conj (p : ℕ) (g x : G) : pFreePart p (g * x * g⁻¹) = g * pFreePart p x * g⁻¹ := by
  have h : orderOf (g * x * g⁻¹) = orderOf x :=
    (SemiconjBy.orderOf_eq g (by simp [SemiconjBy])).symm
  rw [pFreePart, pFreePart, pFreeExponent, pFreeExponent, h, conj_pow]

/-- **Conjugation transports the `p`-part.** -/
@[simp]
theorem pPart_conj (p : ℕ) (g x : G) : pPart p (g * x * g⁻¹) = g * pPart p x * g⁻¹ := by
  rw [pPart, pPart, pFreePart_conj]
  group

section Order

variable (hp : p.Prime) (hx : orderOf x ≠ 0)
include hp hx

omit hp hx in
private theorem pFreeExponent_ne_zero : pFreeExponent p x ≠ 0 :=
  pow_ne_zero _ (Nat.ordProj_pos (orderOf x) p).ne'

omit hp in
private theorem ordProj_dvd_pFreeExponent : ordProj[p] (orderOf x) ∣ pFreeExponent p x :=
  dvd_pow_self _ (Nat.totient_pos.2 (Nat.ordCompl_pos p hx)).ne'

private theorem coprime_pFreeExponent :
    Nat.Coprime (pFreeExponent p x) (ordCompl[p] (orderOf x)) := by
  rw [pFreeExponent]
  exact ((Nat.coprime_ordCompl hp hx).pow_left _).pow_left _

private theorem ordCompl_dvd_pFreeExponent_sub_one :
    ordCompl[p] (orderOf x) ∣ pFreeExponent p x - 1 :=
  (Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.2 (pFreeExponent_ne_zero))).mp
    (Nat.ModEq.pow_totient ((Nat.coprime_ordCompl hp hx).pow_left _)).symm

private theorem gcd_orderOf_pFreeExponent :
    Nat.gcd (orderOf x) (pFreeExponent p x) = ordProj[p] (orderOf x) := by
  obtain ⟨f, hf⟩ := ordProj_dvd_pFreeExponent hx
  have hfm : Nat.Coprime (ordCompl[p] (orderOf x)) f :=
    (Nat.Coprime.coprime_dvd_left ⟨ordProj[p] (orderOf x), by rw [hf, mul_comm]⟩
      (coprime_pFreeExponent hp hx)).symm
  calc Nat.gcd (orderOf x) (pFreeExponent p x)
      = Nat.gcd (ordProj[p] (orderOf x) * ordCompl[p] (orderOf x))
          (ordProj[p] (orderOf x) * f) := by
        rw [Nat.ordProj_mul_ordCompl_eq_self, hf]
    _ = ordProj[p] (orderOf x) := by rw [Nat.gcd_mul_left, hfm.gcd_eq_one, mul_one]

/-- The order of the `p`-free part of `x` is the `p`-free part of the order of `x`. -/
@[simp]
theorem orderOf_pFreePart : orderOf (pFreePart p x) = ordCompl[p] (orderOf x) := by
  rw [pFreePart, orderOf_pow' _ (pFreeExponent_ne_zero),
    gcd_orderOf_pFreeExponent hp hx]

/-- The order of the `p`-free part of `x` is prime to `p`. -/
theorem not_dvd_orderOf_pFreePart : ¬ p ∣ orderOf (pFreePart p x) := by
  rw [orderOf_pFreePart hp hx]
  exact Nat.not_dvd_ordCompl hp hx

private theorem pPart_pow_ordProj : pPart p x ^ ordProj[p] (orderOf x) = 1 := by
  have h1 : 1 ≤ pFreeExponent p x := Nat.one_le_iff_ne_zero.2 (pFreeExponent_ne_zero)
  have hsplit : pFreeExponent p x * ordProj[p] (orderOf x)
      = ordProj[p] (orderOf x) + ordProj[p] (orderOf x) * (pFreeExponent p x - 1) := by
    obtain ⟨d, hd⟩ : ∃ d, pFreeExponent p x = d + 1 := ⟨pFreeExponent p x - 1, by omega⟩
    rw [hd, Nat.add_sub_cancel]
    ring
  have hkill : x ^ (ordProj[p] (orderOf x) * (pFreeExponent p x - 1)) = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    have hd := Nat.mul_dvd_mul_left (ordProj[p] (orderOf x))
      (ordCompl_dvd_pFreeExponent_sub_one hp hx)
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at hd
  have hxeq : x ^ (pFreeExponent p x * ordProj[p] (orderOf x)) = x ^ ordProj[p] (orderOf x) := by
    rw [hsplit, pow_add, hkill, mul_one]
  have hc : Commute ((pFreePart p x)⁻¹) x :=
    ((Commute.refl x).pow_left (pFreeExponent p x)).inv_left
  rw [pPart, hc.mul_pow, inv_pow, pFreePart, ← pow_mul, hxeq, inv_mul_cancel]

/-- The order of the `p`-part of `x` is the `p`-part of the order of `x`. In particular it is a
power of `p`. -/
@[simp]
theorem orderOf_pPart : orderOf (pPart p x) = ordProj[p] (orderOf x) := by
  have hdvd : orderOf (pPart p x) ∣ ordProj[p] (orderOf x) :=
    orderOf_dvd_of_pow_eq_one (pPart_pow_ordProj hp hx)
  have hcop : Nat.Coprime (orderOf (pFreePart p x)) (orderOf (pPart p x)) := by
    rw [orderOf_pFreePart hp hx]
    exact Nat.Coprime.coprime_dvd_right hdvd ((Nat.coprime_ordCompl hp hx).symm.pow_right _)
  have hmul := (commute_pFreePart_pPart p x).orderOf_mul_eq_mul_orderOf_of_coprime hcop
  rw [pFreePart_mul_pPart, orderOf_pFreePart hp hx] at hmul
  refine Nat.eq_of_mul_eq_mul_left (Nat.ordCompl_pos p hx) ?_
  rw [← hmul, mul_comm]
  exact (Nat.ordProj_mul_ordCompl_eq_self (orderOf x) p).symm

omit hx in
/-- **The factorisation is unique.** A commuting factorisation `x = s * u` in which the order of
`s` is prime to `p` and the order of `u` is a power of `p` has `s` the `p`-free part of `x`. -/
theorem eq_pFreePart {s u : G} (hsu : Commute s u) (hmul : s * u = x)
    (hs : ¬ p ∣ orderOf s) {k : ℕ} (hu : orderOf u = p ^ k) : s = pFreePart p x := by
  have hs0 : orderOf s ≠ 0 := fun h => hs (by rw [h]; exact dvd_zero p)
  have hcop : Nat.Coprime (orderOf s) (orderOf u) :=
    hu ▸ ((Nat.Prime.coprime_iff_not_dvd hp).2 hs).symm.pow_right k
  have hord : orderOf x = orderOf s * p ^ k := by
    rw [← hmul, hsu.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hu]
  have hx : orderOf x ≠ 0 := by
    rw [hord]; exact Nat.mul_ne_zero hs0 (pow_ne_zero k hp.pos.ne')
  have hfac : (orderOf x).factorization p = k := by
    rw [hord, Nat.factorization_mul hs0 (pow_ne_zero k hp.pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hs, hp.factorization_pow, Finsupp.single_eq_same,
      zero_add]
  have hu1 : u ^ pFreeExponent p x = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    rw [hu, ← hfac]
    exact ordProj_dvd_pFreeExponent hx
  have hs1 : s ^ pFreeExponent p x = s := by
    have h1 : 1 ≤ pFreeExponent p x := Nat.one_le_iff_ne_zero.2 pFreeExponent_ne_zero
    obtain ⟨d, hd⟩ : ∃ d, pFreeExponent p x = d + 1 := ⟨pFreeExponent p x - 1, by omega⟩
    have hcompl : ordCompl[p] (orderOf x) = orderOf s := by
      rw [hfac, hord]
      exact Nat.mul_div_cancel _ (pow_pos hp.pos k)
    have hsd : s ^ d = 1 := by
      refine orderOf_dvd_iff_pow_eq_one.1 ?_
      have hdvd := ordCompl_dvd_pFreeExponent_sub_one hp hx
      rwa [hcompl, hd, Nat.add_sub_cancel] at hdvd
    rw [hd, pow_succ, hsd, one_mul]
  have key : ∀ e : ℕ, u ^ e = 1 → s ^ e = s → x ^ e = s := fun e h1 h2 => by
    rw [← hmul, hsu.mul_pow, h1, mul_one, h2]
  rw [pFreePart, key _ hu1 hs1]

omit hx in
/-- The companion to `TauCeti.eq_pFreePart`: the `p`-power factor of a commuting factorisation is
the `p`-part. -/
theorem eq_pPart {s u : G} (hsu : Commute s u) (hmul : s * u = x)
    (hs : ¬ p ∣ orderOf s) {k : ℕ} (hu : orderOf u = p ^ k) : u = pPart p x := by
  rw [pPart, ← eq_pFreePart hp hsu hmul hs hu, ← hmul, inv_mul_cancel_left]

end Order

/-- An element whose order is prime to `p` is its own `p`-free part. -/
theorem pFreePart_eq_self (hp : p.Prime) (hx : ¬ p ∣ orderOf x) : pFreePart p x = x :=
  (eq_pFreePart hp (Commute.one_right x) (mul_one x) hx (k := 0) (by simp)).symm

/-- An element whose order is a power of `p` is its own `p`-part. -/
theorem pPart_eq_self (hp : p.Prime) {k : ℕ} (hx : orderOf x = p ^ k) : pPart p x = x :=
  (eq_pPart hp (Commute.one_left x) (one_mul x) (by simpa using hp.ne_one) hx).symm

/-- An element whose order is prime to `p` has trivial `p`-part. -/
theorem pPart_eq_one (hp : p.Prime) (hx : ¬ p ∣ orderOf x) : pPart p x = 1 := by
  have h := pFreePart_mul_pPart p x
  rw [pFreePart_eq_self hp hx] at h
  exact mul_left_cancel (h.trans (mul_one x).symm)

/-- An element whose order is a power of `p` has trivial `p`-free part. -/
theorem pFreePart_eq_one (hp : p.Prime) {k : ℕ} (hx : orderOf x = p ^ k) : pFreePart p x = 1 :=
  (eq_pFreePart hp (Commute.one_left x) (one_mul x) (by simpa using hp.ne_one) hx).symm

end TauCeti
