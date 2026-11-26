/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.Order.Ring.Units
public import TauCeti.FieldTheory.MatsumotoGroup.OrderedField
public import TauCeti.FieldTheory.MilnorKTheory.Grading

/-!
# Order-sign detector on Milnor K-theory

On a linearly ordered commutative ring `R`, the additive unit-sign homomorphism
`Units.signAddHom R : Additive Rˣ →+ ZMod 2` induces the ring homomorphism
`MilnorK.orderSignPoly : MilnorK R →+* Polynomial (ZMod 2)`, its graded form
`MilnorK.gradedOrderSignPoly`, and the degree-`n` linear map `MilnorK.orderSignDegree R n`,
agreeing with `MatsumotoGroup.sign R` in degree `2` (`MilnorK.orderSignDegree_two_eq`) and proving
`{-1, …, -1} ≠ 0` and nontriviality of every `MilnorK.degree R n`
(`MilnorK.nontrivial_degree_of_linearOrder`).

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), §1.
* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, §7.
-/

public section

namespace TauCeti.MilnorK

section OrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

variable (R) in
/-- The order-sign ring homomorphism `MilnorK R →+* Polynomial (ZMod 2)`, sending `ofUnit a` to
`C (Units.signAddHom R (Additive.ofMul a)) * X`. -/
noncomputable def orderSignPoly : MilnorK R →+* Polynomial (ZMod 2) :=
  MilnorK.lift R
    { toFun := fun u => Polynomial.C (Units.signAddHom R u) * Polynomial.X
      map_zero' := by simp
      map_add' := fun _ _ => by simp [map_add, add_mul] }
    fun a b hab => by
      have h0 : Units.signAddHom R (Additive.ofMul a) *
          Units.signAddHom R (Additive.ofMul b) = 0 := by
        rw [← MatsumotoGroup.signPairing_apply]
        exact MatsumotoGroup.signPairing_of_add_eq_one hab
      calc Polynomial.C (Units.signAddHom R (Additive.ofMul a)) * Polynomial.X *
          (Polynomial.C (Units.signAddHom R (Additive.ofMul b)) * Polynomial.X)
        _ = Polynomial.C (Units.signAddHom R (Additive.ofMul a) *
            Units.signAddHom R (Additive.ofMul b)) * (Polynomial.X * Polynomial.X) := by
          rw [map_mul]; ring
        _ = 0 := by rw [h0, map_zero, zero_mul]

@[simp] theorem orderSignPoly_ofUnit (a : Rˣ) :
    orderSignPoly R (ofUnit a) =
      Polynomial.C (Units.signAddHom R (Additive.ofMul a)) * Polynomial.X :=
  (lift_ofUnit _ _ a).trans (by simp)

@[simp] theorem orderSignPoly_symbol (l : List Rˣ) :
    orderSignPoly R (symbol l) =
      Polynomial.C (l.map fun a => Units.signAddHom R (Additive.ofMul a)).prod *
        Polynomial.X ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [symbol_cons, map_mul, orderSignPoly_ofUnit, ih, List.map_cons, List.prod_cons,
      List.length_cons, map_mul, pow_succ']; ring

theorem coeff_orderSignPoly_symbol (l : List Rˣ) (n : ℕ) :
    (orderSignPoly R (symbol l)).coeff n =
      if l.length = n then (l.map fun a => Units.signAddHom R (Additive.ofMul a)).prod else 0 := by
  rw [orderSignPoly_symbol, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : l.length = n <;> simp [h, Ne.symm]

/-- For every `x ∈ MilnorK.degree R n`, `orderSignPoly R x` is homogeneous of degree `n`. -/
theorem coeff_orderSignPoly_of_mem_degree_ne {n k : ℕ} (hkn : k ≠ n) {x : MilnorK R}
    (hx : x ∈ degree R n) : (orderSignPoly R x).coeff k = 0 := by
  rw [degree_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨l, rfl, rfl⟩ := hy
    rw [coeff_orderSignPoly_symbol, ite_eq_right hkn.symm]
  | zero => simp
  | add _ _ _ _ hy hz => simp [hy, hz]
  | smul _ _ _ hy =>
    rw [map_zsmul, ← Polynomial.lcoeff_apply, map_zsmul, Polynomial.lcoeff_apply, hy, smul_zero]

variable (R) in
/-- The order-sign graded ring homomorphism from `MilnorK.degree R` into polynomials over `ZMod 2`
graded by monomial degree. -/
noncomputable def gradedOrderSignPoly :
    degree R →+*ᵍ fun n : ℕ =>
      LinearMap.range (Polynomial.monomial n : ZMod 2 →ₗ[ZMod 2] Polynomial (ZMod 2)) where
  toRingHom := orderSignPoly R
  map_mem {n x} hx := by
    refine ⟨(orderSignPoly R x).coeff n, ?_⟩
    ext k
    simp only [Polynomial.coeff_monomial_apply]
    split_ifs with hkn
    · rw [hkn]
    · exact (coeff_orderSignPoly_of_mem_degree_ne (Ne.symm hkn) hx).symm

@[simp] theorem gradedOrderSignPoly_toRingHom :
    (gradedOrderSignPoly R).toRingHom = orderSignPoly R := by rfl
@[simp] theorem gradedOrderSignPoly_apply (x : MilnorK R) :
    gradedOrderSignPoly R x = orderSignPoly R x := by rfl

variable (R) in
/-- The degree-`n` order-sign homomorphism `MilnorK.degree R n →ₗ[ℤ] ZMod 2`, extracting the
degree-`n` coefficient of `MilnorK.orderSignPoly`. -/
noncomputable def orderSignDegree (n : ℕ) : degree R n →ₗ[ℤ] ZMod 2 :=
  ((Polynomial.lcoeff (ZMod 2) n).restrictScalars ℤ).comp
    ((orderSignPoly R).toIntAlgHom.toLinearMap.comp (degree R n).subtype)

@[simp] theorem orderSignDegree_apply (n : ℕ) (x : degree R n) :
    orderSignDegree R n x = (orderSignPoly R x.val).coeff n := by rfl
theorem orderSignDegree_symbol {n : ℕ} (l : List Rˣ) (hl : l.length = n) :
    orderSignDegree R n ⟨symbol l, symbol_mem_degree_of_length hl⟩ =
      (l.map fun a => Units.signAddHom R (Additive.ofMul a)).prod := by
  rw [orderSignDegree_apply, coeff_orderSignPoly_symbol, ite_eq_left hl]

/-- `orderSignDegree R n` evaluates `{a₁, …, aₙ}` to `1` iff every entry is negative. -/
theorem orderSignDegree_symbol_eq_ite {n : ℕ} (l : List Rˣ) (hl : l.length = n) :
    orderSignDegree R n ⟨symbol l, symbol_mem_degree_of_length hl⟩ =
      if ∀ a ∈ l, (a : R) < 0 then 1 else 0 := by
  rw [orderSignDegree_symbol l hl]; clear hl
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, Units.signAddHom_ofMul]
    by_cases ha : (a : R) < 0 <;> simp [ha]

/-- In degree `2`, `MilnorK.orderSignDegree` agrees with `MatsumotoGroup.sign`. -/
theorem orderSignDegree_two_eq (x : degree R 2) :
    orderSignDegree R 2 x = MatsumotoGroup.sign R (degreeTwoEquiv R x) :=
  LinearMap.congr_fun (f := orderSignDegree R 2)
    (g := (MatsumotoGroup.sign R).toIntLinearMap.comp (degreeTwoEquiv R).toLinearMap)
    (degreeTwo_linearMap_ext fun a b => by
      have hpoly : orderSignPoly R (ofUnit a * ofUnit b) =
          Polynomial.C (Units.signAddHom R (Additive.ofMul a) *
            Units.signAddHom R (Additive.ofMul b)) * Polynomial.X ^ 2 := by
        rw [map_mul, orderSignPoly_ofUnit, orderSignPoly_ofUnit, mul_mul_mul_comm,
          ← Polynomial.C_mul, ← sq]
      dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AddMonoidHom.coe_toIntLinearMap]
      rw [orderSignDegree_apply, hpoly, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        ite_eq_left rfl, mul_one, degreeTwoEquiv_ofUnit_mul,
        MatsumotoGroup.sign_symbol_eq_signPairing, MatsumotoGroup.signPairing_apply]) x

/-- Over any linearly ordered commutative ring, `{-1, …, -1}` of length `n` is nonzero. -/
theorem symbol_neg_one_replicate_ne_zero (n : ℕ) : symbol (List.replicate n (-1 : Rˣ)) ≠ 0 := by
  intro h
  have hval := congrArg (orderSignDegree R n) (Subtype.ext h :
    (⟨symbol (List.replicate n (-1 : Rˣ)),
      symbol_mem_degree_of_length List.length_replicate⟩ : degree R n) = 0)
  rw [orderSignDegree_symbol _ List.length_replicate, List.map_replicate, Units.signAddHom_ofMul]
    at hval
  have hneg : ((-1 : Rˣ) : R) < 0 := by simp
  simp only [hneg, ↓reduceIte, List.prod_replicate, one_pow, map_zero] at hval
  exact one_ne_zero hval

/-- Over any linearly ordered commutative ring, `ofUnit (-1) * ofUnit (-1) ≠ 0`. -/
theorem ofUnit_neg_one_mul_ne_zero : ofUnit (-1 : Rˣ) * ofUnit (-1 : Rˣ) ≠ 0 := by
  simpa only [List.replicate_succ, List.replicate_zero, symbol_cons, symbol_nil, mul_one] using
    symbol_neg_one_replicate_ne_zero (R := R) 2

/-- Every Milnor K-group `Kₙᴹ(R)` of a linearly ordered commutative ring is nontrivial. -/
theorem nontrivial_degree_of_linearOrder (n : ℕ) : Nontrivial (degree R n) :=
  ⟨⟨symbol (List.replicate n (-1 : Rˣ)), symbol_mem_degree_of_length List.length_replicate⟩,
    0, fun h => symbol_neg_one_replicate_ne_zero (R := R) n (congrArg Subtype.val h)⟩

end OrderedCommRing

end TauCeti.MilnorK
