/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.ZMod.Basic
public import TauCeti.FieldTheory.MilnorKTheory.Grading

/-!
# Order-sign detector on Milnor K-theory

On any linearly ordered ring `R`, sending a negative unit to `1 : ZMod 2` and a positive unit to
`0 : ZMod 2` gives an additive homomorphism `TauCeti.orderSignHom : Additive Rˣ →+ ZMod 2`.
Because two negative elements cannot sum to `1 ≥ 0`, the product
`(a, b) ↦ orderSign a * orderSign b` is a Steinberg pairing
(`TauCeti.isSteinbergPairing_orderSignPairing`).

When `R` is commutative, this induces:

* `TauCeti.SymbolGroup.orderSign : SymbolGroup R →ₗ[ℤ] ZMod 2`, showing that `{-1, -1} ≠ 0`
  in `SymbolGroup R` (in particular for `ℝ`, `ℚ`, and `ℤ`);
* `TauCeti.MilnorK.orderSignPoly : MilnorK R →+* Polynomial (ZMod 2)`, sending `ofUnit a` to
  `C (orderSign a) * X` and mapping `MilnorK.degree R n` into degree-`n` homogeneous polynomials;
* `TauCeti.MilnorK.orderSignDegree R n : MilnorK.degree R n →ₗ[ℤ] ZMod 2`, evaluating a
  length-`n` Milnor symbol `{a₁, …, aₙ}` to `1` if every `aᵢ < 0` and `0` otherwise, and proving
  that `{-1, …, -1} ≠ 0` in every degree `n`.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), §1.
* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, §7.
-/

public section

namespace TauCeti

section LinearOrder

variable {R : Type*} [Ring R] [LinearOrder R]

/-- The sign of a unit in a linearly ordered ring, valued in `ZMod 2`: `1` if the unit is
negative and `0` otherwise. -/
def orderSign (a : Rˣ) : ZMod 2 :=
  if (a : R) < 0 then 1 else 0

/-- Unfolding lemma for `TauCeti.orderSign`. -/
theorem orderSign_def (a : Rˣ) : orderSign a = if (a : R) < 0 then 1 else 0 := by
  rfl

theorem orderSign_of_neg {a : Rˣ} (ha : (a : R) < 0) : orderSign a = 1 := by
  simp [orderSign_def, ha]

theorem orderSign_of_nonneg {a : Rˣ} (ha : 0 ≤ (a : R)) : orderSign a = 0 := by
  simp [orderSign_def, not_lt.mpr ha]

theorem orderSign_of_pos {a : Rˣ} (ha : 0 < (a : R)) : orderSign a = 0 :=
  orderSign_of_nonneg ha.le

theorem orderSign_eq_one_iff {a : Rˣ} : orderSign a = 1 ↔ (a : R) < 0 := by
  rw [orderSign_def]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h01 => absurd h01 zero_ne_one, fun ha => absurd ha h⟩

/-- The pairing `(a, b) ↦ orderSign a * orderSign b` on a linearly ordered ring. -/
def orderSignPairing (a b : Rˣ) : ZMod 2 :=
  orderSign a * orderSign b

/-- Unfolding lemma for `TauCeti.orderSignPairing`. -/
theorem orderSignPairing_def (a b : Rˣ) : orderSignPairing a b = orderSign a * orderSign b := by
  rfl

theorem orderSignPairing_eq_ite (a b : Rˣ) :
    orderSignPairing a b = if (a : R) < 0 ∧ (b : R) < 0 then 1 else 0 := by
  rw [orderSignPairing_def, orderSign_def, orderSign_def]
  split_ifs <;> simp_all

end LinearOrder

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

@[simp]
theorem orderSign_one : orderSign (1 : Rˣ) = 0 :=
  orderSign_of_nonneg zero_le_one

@[simp]
theorem orderSign_neg_one : orderSign (-1 : Rˣ) = 1 := by
  apply orderSign_of_neg
  simp

theorem orderSign_eq_zero_iff {a : Rˣ} : orderSign a = 0 ↔ 0 < (a : R) := by
  rw [orderSign_def]
  split_ifs with h
  · exact ⟨fun h10 => absurd h10 one_ne_zero, fun ha => absurd (lt_trans ha h) (lt_irrefl _)⟩
  · exact ⟨fun _ => lt_of_le_of_ne (not_lt.mp h) (Units.ne_zero a).symm, fun _ => rfl⟩

/-- `TauCeti.orderSign` converts multiplication of units into addition in `ZMod 2`. -/
theorem orderSign_mul (a b : Rˣ) : orderSign (a * b) = orderSign a + orderSign b := by
  rcases lt_or_gt_of_ne (Units.ne_zero a) with ha | ha <;>
    rcases lt_or_gt_of_ne (Units.ne_zero b) with hb | hb
  · have hab : 0 < ((a * b : Rˣ) : R) := by
      simpa only [Units.val_mul] using mul_pos_of_neg_of_neg ha hb
    rw [orderSign_of_pos hab, orderSign_of_neg ha, orderSign_of_neg hb]
    decide
  · have hab : ((a * b : Rˣ) : R) < 0 := by
      simpa only [Units.val_mul] using mul_neg_of_neg_of_pos ha hb
    rw [orderSign_of_neg hab, orderSign_of_neg ha, orderSign_of_pos hb, add_zero]
  · have hab : ((a * b : Rˣ) : R) < 0 := by
      simpa only [Units.val_mul] using mul_neg_of_pos_of_neg ha hb
    rw [orderSign_of_neg hab, orderSign_of_pos ha, orderSign_of_neg hb, zero_add]
  · have hab : 0 < ((a * b : Rˣ) : R) := by
      simpa only [Units.val_mul] using mul_pos ha hb
    rw [orderSign_of_pos hab, orderSign_of_pos ha, orderSign_of_pos hb, add_zero]

@[simp]
theorem orderSign_inv (a : Rˣ) : orderSign a⁻¹ = orderSign a := by
  have h := orderSign_mul a a⁻¹
  rw [mul_inv_cancel, orderSign_one] at h
  have hneg : orderSign a⁻¹ = -orderSign a := eq_neg_of_add_eq_zero_right h.symm
  rw [hneg, ZMod.neg_eq_self_mod_two]

variable (R) in
/-- The additive homomorphism `Additive Rˣ →+ ZMod 2` recording the sign of a unit. -/
def orderSignHom : Additive Rˣ →+ ZMod 2 where
  toFun u := orderSign (Additive.toMul u)
  map_zero' := orderSign_one
  map_add' u v := orderSign_mul (Additive.toMul u) (Additive.toMul v)

/-- Unfolding lemma for `TauCeti.orderSignHom`. -/
theorem orderSignHom_apply (u : Additive Rˣ) : orderSignHom R u = orderSign (Additive.toMul u) := by
  rfl

@[simp]
theorem orderSignHom_ofMul (a : Rˣ) : orderSignHom R (Additive.ofMul a) = orderSign a := by
  rfl

/-- The product of order signs is a Steinberg pairing on any linearly ordered ring: two negative
elements cannot sum to `1 ≥ 0`. -/
theorem isSteinbergPairing_orderSignPairing :
    IsSteinbergPairing (orderSignPairing (R := R)) where
  map_mul_left a b d := by simp only [orderSignPairing_def, orderSign_mul, add_mul]
  map_mul_right a b d := by simp only [orderSignPairing_def, orderSign_mul, mul_add]
  steinberg a b hab := by
    rw [orderSignPairing_eq_ite]
    split_ifs with h
    · exfalso
      have hneg : (a : R) + b < 0 := add_neg h.1 h.2
      rw [hab] at hneg
      exact not_lt_of_ge (zero_le_one (α := R)) hneg
    · rfl

end OrderedRing

section OrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

namespace SymbolGroup

variable (R) in
/-- The order-sign detector `SymbolGroup R →ₗ[ℤ] ZMod 2` on the degree-two symbol group of a
linearly ordered commutative ring. -/
noncomputable def orderSign : SymbolGroup R →ₗ[ℤ] ZMod 2 :=
  SymbolGroup.lift (orderSignPairing (R := R)) isSteinbergPairing_orderSignPairing

@[simp]
theorem orderSign_symbol (a b : Rˣ) :
    SymbolGroup.orderSign R (symbol a b) = TauCeti.orderSign a * TauCeti.orderSign b :=
  SymbolGroup.lift_symbol _ _ a b

/-- Over any linearly ordered commutative ring (such as `ℝ`, `ℚ`, or `ℤ`), the Steinberg
symbol `{-1, -1}` is nonzero. -/
theorem symbol_neg_one_neg_one_ne_zero :
    TauCeti.symbol (-1 : Rˣ) (-1 : Rˣ) ≠ 0 := by
  intro h
  have h10 : (1 : ZMod 2) = 0 := by
    simpa only [orderSign_symbol, TauCeti.orderSign_neg_one, mul_one, map_zero] using
      congrArg (SymbolGroup.orderSign R) h
  exact one_ne_zero h10

/-- The symbol group of any linearly ordered commutative ring is nontrivial. -/
theorem nontrivial_of_linearOrder : Nontrivial (SymbolGroup R) :=
  ⟨TauCeti.symbol (-1 : Rˣ) (-1 : Rˣ), 0, symbol_neg_one_neg_one_ne_zero⟩

end SymbolGroup

namespace MilnorK

variable (R) in
/-- The order-sign ring homomorphism `MilnorK R →+* Polynomial (ZMod 2)`, sending `ofUnit a` to
`C (orderSign a) * X`. -/
noncomputable def orderSignPoly : MilnorK R →+* Polynomial (ZMod 2) :=
  MilnorK.lift R
    { toFun := fun u => Polynomial.C (orderSignHom R u) * Polynomial.X
      map_zero' := by simp
      map_add' := fun u v => by simp [map_add, add_mul] }
    fun a b hab => by
      have h0 : orderSign a * orderSign b = 0 :=
        isSteinbergPairing_orderSignPairing.steinberg a b hab
      calc
        Polynomial.C (orderSignHom R (Additive.ofMul a)) * Polynomial.X *
            (Polynomial.C (orderSignHom R (Additive.ofMul b)) * Polynomial.X)
          = Polynomial.C (orderSign a * orderSign b) * (Polynomial.X * Polynomial.X) := by
            simp only [orderSignHom_ofMul, map_mul]
            ring
        _ = 0 := by rw [h0, map_zero, zero_mul]

@[simp]
theorem orderSignPoly_ofUnit (a : Rˣ) :
    orderSignPoly R (ofUnit a) = Polynomial.C (orderSign a) * Polynomial.X :=
  lift_ofUnit _ _ a

@[simp]
theorem orderSignPoly_symbol (l : List Rˣ) :
    orderSignPoly R (symbol l) = Polynomial.C (l.map orderSign).prod * Polynomial.X ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [symbol_cons, map_mul, orderSignPoly_ofUnit, ih, List.map_cons, List.prod_cons,
      List.length_cons, map_mul, pow_succ']
    ring

/-- The degree-`n` coefficient of `orderSignPoly R (symbol l)` is the product of the signs of the
entries of `l` if `l.length = n`, and `0` otherwise. -/
theorem coeff_orderSignPoly_symbol (l : List Rˣ) (n : ℕ) :
    (orderSignPoly R (symbol l)).coeff n =
      if l.length = n then (l.map orderSign).prod else 0 := by
  rw [orderSignPoly_symbol, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : l.length = n
  · simp [h]
  · simp [h, Ne.symm h]

/-- For every `x ∈ MilnorK.degree R n`, `orderSignPoly R x` is homogeneous of degree `n`: all
coefficients in degrees `k ≠ n` vanish. -/
theorem coeff_orderSignPoly_of_mem_degree_ne {n k : ℕ} (hkn : k ≠ n) {x : MilnorK R}
    (hx : x ∈ degree R n) :
    (orderSignPoly R x).coeff k = 0 := by
  rw [degree_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl, rfl⟩ := hy
    rw [coeff_orderSignPoly_symbol]
    simp [hkn.symm]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul m y _ hy =>
    rw [map_zsmul, ← Polynomial.lcoeff_apply, map_zsmul, Polynomial.lcoeff_apply, hy, smul_zero]

variable (R) in
/-- The degree-`n` order-sign homomorphism `MilnorK.degree R n →ₗ[ℤ] ZMod 2`, extracting the
degree-`n` coefficient of `MilnorK.orderSignPoly`. -/
noncomputable def orderSignDegree (n : ℕ) : degree R n →ₗ[ℤ] ZMod 2 :=
  ((Polynomial.lcoeff (ZMod 2) n).restrictScalars ℤ).comp
    ((orderSignPoly R).toIntAlgHom.toLinearMap.comp (degree R n).subtype)

@[simp]
theorem orderSignDegree_apply (n : ℕ) (x : degree R n) :
    orderSignDegree R n x = (orderSignPoly R x.1).coeff n := by
  rfl

theorem orderSignDegree_symbol {n : ℕ} (l : List Rˣ) (hl : l.length = n) :
    orderSignDegree R n ⟨symbol l, symbol_mem_degree_of_length hl⟩ =
      (l.map orderSign).prod := by
  rw [orderSignDegree_apply, coeff_orderSignPoly_symbol]
  simp [hl]

/-- `orderSignDegree R n` evaluates a length-`n` Milnor symbol `{a₁, …, aₙ}` to `1` if every
entry is negative and to `0` otherwise. -/
theorem orderSignDegree_symbol_eq_ite {n : ℕ} (l : List Rˣ) (hl : l.length = n) :
    orderSignDegree R n ⟨symbol l, symbol_mem_degree_of_length hl⟩ =
      if ∀ a ∈ l, (a : R) < 0 then 1 else 0 := by
  rw [orderSignDegree_symbol l hl]
  clear hl
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases ha : (a : R) < 0
    · rw [orderSign_of_neg ha, one_mul]
      simp [ha]
    · rw [orderSign_of_nonneg (not_lt.mp ha), zero_mul]
      simp [ha]

/-- In degree `2`, `MilnorK.orderSignDegree` agrees with `SymbolGroup.orderSign` via
`MilnorK.degreeTwoEquiv`. -/
theorem orderSignDegree_two_eq (x : degree R 2) :
    orderSignDegree R 2 x = SymbolGroup.orderSign R (degreeTwoEquiv R x) := by
  revert x
  refine fun x => LinearMap.congr_fun
    (f := orderSignDegree R 2)
    (g := (SymbolGroup.orderSign R).comp (degreeTwoEquiv R).toLinearMap) ?_ x
  apply degree_linearMap_ext
  intro l hl
  match l, hl with
  | [a, b], _ =>
    rw [orderSignDegree_symbol (n := 2) [a, b] rfl, LinearMap.comp_apply, LinearEquiv.coe_coe,
      degreeTwoEquiv_symbol, SymbolGroup.orderSign_symbol]
    simp

/-- Over any linearly ordered commutative ring (such as `ℝ`, `ℚ`, or `ℤ`), the Milnor symbol
`{-1, …, -1}` of length `n` is nonzero. -/
theorem symbol_neg_one_replicate_ne_zero (n : ℕ) :
    symbol (List.replicate n (-1 : Rˣ)) ≠ 0 := by
  intro h
  have hdeg : (⟨symbol (List.replicate n (-1 : Rˣ)),
      symbol_mem_degree_of_length (List.length_replicate)⟩ : degree R n) = 0 :=
    Subtype.ext h
  have hval := congrArg (orderSignDegree R n) hdeg
  rw [orderSignDegree_symbol _ List.length_replicate, List.map_replicate, orderSign_neg_one,
    List.prod_replicate, one_pow, map_zero] at hval
  exact one_ne_zero hval

/-- Over any linearly ordered commutative ring, `ofUnit (-1) * ofUnit (-1) ≠ 0`. -/
theorem ofUnit_neg_one_mul_ne_zero :
    ofUnit (-1 : Rˣ) * ofUnit (-1 : Rˣ) ≠ 0 := by
  simpa only [List.replicate_succ, List.replicate_zero, symbol_pair] using
    symbol_neg_one_replicate_ne_zero (R := R) 2

/-- Every Milnor K-group `Kₙᴹ(R)` of a linearly ordered commutative ring is nontrivial. -/
theorem nontrivial_degree_of_linearOrder (n : ℕ) : Nontrivial (degree R n) :=
  ⟨⟨symbol (List.replicate n (-1 : Rˣ)), symbol_mem_degree_of_length List.length_replicate⟩,
    0, fun h => symbol_neg_one_replicate_ne_zero (R := R) n (congrArg Subtype.val h)⟩

end MilnorK

end OrderedCommRing

end TauCeti
