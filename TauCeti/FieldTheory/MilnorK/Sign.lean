/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.ZMod.Defs
public import TauCeti.FieldTheory.MilnorK.Basic
public import TauCeti.FieldTheory.MilnorK.SteinbergPairing

import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic

/-!
# Order-sign Steinberg pairing and polynomial detector

For any linearly ordered strict ordered ring `R` (in particular, `ℝ`, `ℚ`, or any real closed
field), the sign homomorphism `ε : Rˣ → ZMod 2` sending positive units to `0` and negative units
to `1` defines a Steinberg pairing `c(a, b) = ε(a) * ε(b)` because complementary units `a + b = 1`
cannot both be negative.

When `R` is commutative, this pairing descends to an additive homomorphism
`SymbolGroup R →+ ZMod 2` and extends to a homogeneous ring homomorphism
`MilnorK R →+* Polynomial (ZMod 2)` sending `{a}` to `ε(a) * X` and `{a₁, …, aₙ}` to
`(∏ i, ε(aᵢ)) * X ^ n`. Extracting the `n`-th coefficient gives the degree-`n` signature map
`MilnorK.degree R n →+ ZMod 2`. In particular, the diagonal symbols `{-1, -1}` in `SymbolGroup R`
and `{-1, …, -1}` in `MilnorK R` are nonzero in every degree `n`, witnessing that Milnor symbols
with repeated entries need not vanish integrally.

## Main definitions

* `TauCeti.orderSign`: the sign map `Rˣ → ZMod 2`, taking value `1` on negative units and `0` on
  positive units.
* `TauCeti.orderSignHom`: `orderSign` bundled as an additive homomorphism `Additive Rˣ →+ ZMod 2`.
* `TauCeti.orderSignPairing`: the binary sign pairing `(a, b) ↦ orderSign a * orderSign b`.
* `TauCeti.orderSignSymbolHom`: the induced additive homomorphism `SymbolGroup R →+ ZMod 2`.
* `TauCeti.MilnorK.orderSignRingHom`: the ring homomorphism `MilnorK R →+* Polynomial (ZMod 2)`
  sending `ofUnit a` to `C (orderSign a) * X`.
* `TauCeti.MilnorK.orderSignDegreeHom`: the degree-`n` signature homomorphism
  `MilnorK.degree R n →+ ZMod 2`.

## Main results

* `TauCeti.isSteinbergPairing_orderSignPairing`: `orderSignPairing` is a Steinberg pairing.
* `TauCeti.symbol_neg_one_neg_one_ne_zero`: `{-1, -1} ≠ 0` in `SymbolGroup R`.
* `TauCeti.MilnorK.orderSignRingHom_symbol`: `orderSignRingHom` sends `{a₁, …, aₙ}` to
  `C (∏ i, orderSign aᵢ) * X ^ n`.
* `TauCeti.MilnorK.symbol_replicate_neg_one_ne_zero`: `{-1, …, -1} ≠ 0` in `MilnorK R` for every
  `n : ℕ`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Ch. III, §§6.2.1, 7.2(c).
-/

public section

namespace TauCeti

universe u

section Order

variable {R : Type u} [Monoid R] [Zero R] [LinearOrder R]

/-- The order-sign map `Rˣ → ZMod 2`, taking value `1` on negative units and `0` on positive
units. -/
def orderSign (a : Rˣ) : ZMod 2 :=
  if (a : R) < 0 then 1 else 0

/-- Unfolding lemma for `orderSign`. -/
theorem orderSign_def (a : Rˣ) : orderSign a = if (a : R) < 0 then 1 else 0 := by
  rfl

/-- Positive units have `orderSign = 0`. -/
@[simp]
theorem orderSign_of_pos {a : Rˣ} (ha : (0 : R) < a) : orderSign a = 0 := by
  rw [orderSign, ite_eq_right]
  intro hlt
  exact absurd ha (not_lt.mpr hlt.le)

/-- Negative units have `orderSign = 1`. -/
@[simp]
theorem orderSign_of_neg {a : Rˣ} (ha : (a : R) < 0) : orderSign a = 1 := by
  rw [orderSign, ite_eq_left]
  exact ha

/-- `orderSign a = 1` if and only if `(a : R) < 0`. -/
theorem orderSign_eq_one_iff (a : Rˣ) : orderSign a = 1 ↔ (a : R) < 0 := by
  rw [orderSign_def]
  split_ifs with ha <;> simp [ha]

/-- `orderSign a = 0` if and only if `0 ≤ (a : R)`. -/
theorem orderSign_eq_zero_iff (a : Rˣ) : orderSign a = 0 ↔ (0 : R) ≤ a := by
  rw [orderSign_def]
  split_ifs with ha <;> simp [ha, not_lt.mp]

/-- The binary order-sign pairing `c(a, b) = orderSign a * orderSign b`, equal to `1 : ZMod 2`
precisely when both `a` and `b` are negative. -/
def orderSignPairing (a b : Rˣ) : ZMod 2 :=
  orderSign a * orderSign b

/-- Unfolding lemma for `orderSignPairing`. -/
theorem orderSignPairing_def (a b : Rˣ) : orderSignPairing a b = orderSign a * orderSign b := by
  rfl

/-- `orderSignPairing a b = 1` if and only if both `a` and `b` are negative. -/
theorem orderSignPairing_eq_one_iff (a b : Rˣ) :
    orderSignPairing a b = 1 ↔ (a : R) < 0 ∧ (b : R) < 0 := by
  unfold orderSignPairing orderSign
  split_ifs with ha hb hb <;> simp [ha, hb]

/-- The product of `orderSign` over a list of units is `1` if every entry is negative and `0`
otherwise. -/
theorem prod_map_orderSign_eq_ite (l : List Rˣ) :
    (l.map orderSign).prod = if ∀ a ∈ l, (a : R) < 0 then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases ha : (a : R) < 0
    · simp [ha]
    · simp [orderSign, ha]

end Order

section Ring

variable {R : Type u} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `orderSign 1 = 0`. -/
theorem orderSign_one : orderSign (1 : Rˣ) = 0 :=
  orderSign_of_pos zero_lt_one

/-- `orderSign (-1) = 1`. -/
theorem orderSign_neg_one : orderSign (-1 : Rˣ) = 1 :=
  orderSign_of_neg (by simp)

/-- `orderSign` turns multiplication of units into addition in `ZMod 2`. -/
theorem orderSign_mul (a b : Rˣ) : orderSign (a * b) = orderSign a + orderSign b := by
  rcases lt_trichotomy (a : R) 0 with ha | ha | ha
  · rcases lt_trichotomy (b : R) 0 with hb | hb | hb
    · have hab : (0 : R) < (a * b : Rˣ) := by
        simpa [Units.val_mul] using mul_pos_of_neg_of_neg ha hb
      rw [orderSign_of_pos hab, orderSign_of_neg ha, orderSign_of_neg hb]
      decide
    · exact absurd hb b.ne_zero
    · have hab : ((a * b : Rˣ) : R) < 0 := by
        simpa [Units.val_mul] using mul_neg_of_neg_of_pos ha hb
      rw [orderSign_of_neg hab, orderSign_of_neg ha, orderSign_of_pos hb, add_zero]
  · exact absurd ha a.ne_zero
  · rcases lt_trichotomy (b : R) 0 with hb | hb | hb
    · have hab : ((a * b : Rˣ) : R) < 0 := by
        simpa [Units.val_mul] using mul_neg_of_pos_of_neg ha hb
      rw [orderSign_of_neg hab, orderSign_of_pos ha, orderSign_of_neg hb, zero_add]
    · exact absurd hb b.ne_zero
    · have hab : (0 : R) < (a * b : Rˣ) := by
        simpa [Units.val_mul] using mul_pos ha hb
      rw [orderSign_of_pos hab, orderSign_of_pos ha, orderSign_of_pos hb, add_zero]

/-- `orderSign` is invariant under inversion (`orderSign a⁻¹ = orderSign a`). -/
@[simp]
theorem orderSign_inv (a : Rˣ) : orderSign a⁻¹ = orderSign a := by
  have h := orderSign_mul a a⁻¹
  rw [mul_inv_cancel, orderSign_one] at h
  have htwo : orderSign a + orderSign a = 0 := CharTwo.add_self_eq_zero _
  exact add_left_cancel (h.symm.trans htwo.symm)

variable (R) in
/-- `orderSign` bundled as an additive homomorphism `Additive Rˣ →+ ZMod 2`. -/
def orderSignHom : Additive Rˣ →+ ZMod 2 where
  toFun x := orderSign (Additive.toMul x)
  map_zero' := orderSign_one
  map_add' x y := orderSign_mul (Additive.toMul x) (Additive.toMul y)

/-- Evaluating `orderSignHom` on `Additive.ofMul a` gives `orderSign a`. -/
@[simp]
theorem orderSignHom_apply (a : Rˣ) : orderSignHom R (Additive.ofMul a) = orderSign a := by
  rfl

/-- Evaluating `orderSignPairing` on `(-1, -1)` gives `1`. -/
@[simp]
theorem orderSignPairing_neg_one_neg_one : orderSignPairing (-1 : Rˣ) (-1) = 1 := by
  simp [orderSignPairing]

/-- `orderSignPairing` is a Steinberg pairing on `Rˣ`. -/
theorem isSteinbergPairing_orderSignPairing :
    IsSteinbergPairing (orderSignPairing (R := R)) where
  map_mul_left a₁ a₂ b := by simp only [orderSignPairing, orderSign_mul, add_mul]
  map_mul_right a b₁ b₂ := by simp only [orderSignPairing, orderSign_mul, mul_add]
  map_add_eq_one a b hab := by
    by_cases ha : (a : R) < 0
    · have hb : ¬(b : R) < 0 := fun hb ↦ by
        have hlt : (a : R) + b < 0 := add_neg ha hb
        rw [hab] at hlt
        exact not_lt_of_gt zero_lt_one hlt
      simp [orderSignPairing, orderSign, hb]
    · simp [orderSignPairing, orderSign, ha]

end Ring

section CommRing

variable {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

variable (R) in
/-- The unique additive homomorphism `SymbolGroup R →+ ZMod 2` induced by `orderSignPairing`. -/
noncomputable def orderSignSymbolHom : SymbolGroup R →+ ZMod 2 :=
  (SymbolGroup.lift orderSignPairing isSteinbergPairing_orderSignPairing).toAddMonoidHom

/-- Evaluating `orderSignSymbolHom` on `TauCeti.symbol a b` gives `orderSignPairing a b`. -/
@[simp]
theorem orderSignSymbolHom_symbol (a b : Rˣ) :
    orderSignSymbolHom R (symbol a b) = orderSignPairing a b :=
  SymbolGroup.lift_symbol orderSignPairing isSteinbergPairing_orderSignPairing a b

/-- The diagonal symbol `{-1, -1}` is nonzero in `SymbolGroup R` for every linearly ordered strict
ordered commutative ring `R`. -/
theorem symbol_neg_one_neg_one_ne_zero : symbol (-1 : Rˣ) (-1) ≠ 0 := fun h ↦ by
  have h1 := congrArg (orderSignSymbolHom R) h
  simp at h1

namespace MilnorK

variable (R) in
/-- The ring homomorphism `MilnorK R →+* Polynomial (ZMod 2)` sending `ofUnit a` to
`C (orderSign a) * X`. -/
noncomputable def orderSignRingHom : MilnorK R →+* Polynomial (ZMod 2) :=
  (lift
    { toFun := fun x ↦ Polynomial.C (orderSign (Additive.toMul x)) * Polynomial.X
      map_zero' := by simp
      map_add' := fun x y ↦ by
        rw [toMul_add, orderSign_mul, map_add, add_mul] }
    fun a b hab ↦ by
      dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul]
      have h0 : orderSign a * orderSign b = 0 :=
        isSteinbergPairing_orderSignPairing.map_add_eq_one a b hab
      calc (Polynomial.C (orderSign a) * Polynomial.X) *
              (Polynomial.C (orderSign b) * Polynomial.X)
          = Polynomial.C (orderSign a * orderSign b) * (Polynomial.X * Polynomial.X) := by
            rw [map_mul]; ring
        _ = 0 := by rw [h0, map_zero, zero_mul]).toRingHom

/-- `orderSignRingHom` sends `ofUnit a` to `C (orderSign a) * X`. -/
@[simp]
theorem orderSignRingHom_ofUnit (a : Rˣ) :
    orderSignRingHom R (ofUnit a) = Polynomial.C (orderSign a) * Polynomial.X :=
  lift_ofUnit _ _ a

/-- `orderSignRingHom` sends `{a₁, …, aₙ}` to `C (∏ i, orderSign aᵢ) * X ^ n`. -/
@[simp]
theorem orderSignRingHom_symbol (l : List Rˣ) :
    orderSignRingHom R (symbol l) =
      Polynomial.C (l.map orderSign).prod * Polynomial.X ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [symbol_cons, map_mul, orderSignRingHom_ofUnit, ih, List.map_cons, List.prod_cons,
      List.length_cons, map_mul, pow_succ']
    ring

/-- For every homogeneous element `x ∈ MilnorK.degree R n`, `orderSignRingHom R x` is a monomial of
degree `n`. -/
theorem orderSignRingHom_eq_monomial_of_mem_degree {n : ℕ} {x : MilnorK R} (hx : x ∈ degree R n) :
    orderSignRingHom R x = Polynomial.monomial n ((orderSignRingHom R x).coeff n) := by
  rw [degree_eq_span_symbol] at hx
  refine Submodule.span_induction
    (p := fun y _ ↦
      orderSignRingHom R y = Polynomial.monomial n ((orderSignRingHom R y).coeff n))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨l, rfl, rfl⟩
    rw [orderSignRingHom_symbol, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial_same]
  · simp
  · intro y₁ y₂ _ _ hy₁ hy₂
    rw [map_add, Polynomial.coeff_add, map_add, ← hy₁, ← hy₂]
  · intro r y _ hy
    have hc : (orderSignRingHom R (r • y)).coeff n = r • (orderSignRingHom R y).coeff n := by
      rw [map_zsmul]
      exact map_zsmul (Polynomial.lcoeff (ZMod 2) n).toAddMonoidHom r (orderSignRingHom R y)
    rw [hc, map_zsmul, map_zsmul, ← hy]

/-- Every coefficient of `orderSignRingHom R x` outside degree `n` vanishes for
`x ∈ MilnorK.degree R n`. -/
theorem coeff_orderSignRingHom_of_mem_degree_ne {n m : ℕ} {x : MilnorK R} (hx : x ∈ degree R n)
    (hmn : m ≠ n) : (orderSignRingHom R x).coeff m = 0 := by
  rw [orderSignRingHom_eq_monomial_of_mem_degree hx, Polynomial.coeff_monomial_of_ne _ hmn]

variable (R) in
/-- The degree-`n` order-signature homomorphism `MilnorK.degree R n →+ ZMod 2`, obtained as the
`n`-th coefficient of `orderSignRingHom`. -/
noncomputable def orderSignDegreeHom (n : ℕ) : degree R n →+ ZMod 2 :=
  (Polynomial.lcoeff (ZMod 2) n).toAddMonoidHom.comp
    ((orderSignRingHom R).toAddMonoidHom.comp (degree R n).subtype.toAddMonoidHom)

/-- Evaluating `orderSignDegreeHom` on a symbol `{a₁, …, aₙ}` returns `∏ i, orderSign aᵢ`. -/
@[simp]
theorem orderSignDegreeHom_symbol {n : ℕ} (l : List Rˣ) (hl : l.length = n) :
    orderSignDegreeHom R n ⟨symbol l, hl ▸ symbol_mem_degree l⟩ = (l.map orderSign).prod := by
  subst hl
  simp only [orderSignDegreeHom, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    Submodule.coe_subtype, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    Polynomial.lcoeff_apply, orderSignRingHom_symbol, Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.coeff_monomial_same]

/-- Evaluating `orderSignDegreeHom` on `{a₁, …, aₙ}` returns `1` if every `aᵢ < 0` and `0`
otherwise. -/
theorem orderSignDegreeHom_symbol_eq_ite {n : ℕ} (l : List Rˣ) (hl : l.length = n) :
    orderSignDegreeHom R n ⟨symbol l, hl ▸ symbol_mem_degree l⟩ =
      if ∀ a ∈ l, (a : R) < 0 then 1 else 0 := by
  rw [orderSignDegreeHom_symbol l hl, prod_map_orderSign_eq_ite]

/-- `orderSignRingHom` sends `{-1, …, -1}` (of length `n`) to `X ^ n`. -/
theorem orderSignRingHom_symbol_replicate_neg_one (n : ℕ) :
    orderSignRingHom R (symbol (List.replicate n (-1 : Rˣ))) = Polynomial.X ^ n := by
  rw [orderSignRingHom_symbol, List.length_replicate, List.map_replicate, orderSign_neg_one,
    List.prod_replicate, one_pow, map_one, one_mul]

/-- The `n`-fold symbol `{-1, …, -1}` is nonzero in `MilnorK R` for every `n : ℕ`. -/
theorem symbol_replicate_neg_one_ne_zero (n : ℕ) :
    symbol (List.replicate n (-1 : Rˣ)) ≠ 0 := fun h ↦ by
  have h1 := congrArg (fun p : Polynomial (ZMod 2) ↦ p.coeff n)
    (congrArg (orderSignRingHom R) h)
  rw [orderSignRingHom_symbol_replicate_neg_one, map_zero, Polynomial.coeff_zero,
    Polynomial.coeff_X_pow_self] at h1
  exact one_ne_zero h1

/-- The degree-two diagonal product `{-1} * {-1}` is nonzero in `MilnorK R`. -/
theorem ofUnit_neg_one_mul_self_ne_zero :
    ofUnit (-1 : Rˣ) * ofUnit (-1 : Rˣ) ≠ 0 := by
  have h := symbol_replicate_neg_one_ne_zero (R := R) 2
  simpa [List.replicate_succ] using h

end MilnorK

end CommRing

end TauCeti
