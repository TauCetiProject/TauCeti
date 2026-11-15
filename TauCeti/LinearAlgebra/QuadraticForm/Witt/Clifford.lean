/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Pfister.Clifford

/-!
# The Clifford invariant on the Witt ring and the homomorphism `I² → Br(K)`

Adding a hyperbolic plane does not change the Clifford invariant `c`, so `c` is a well-defined
function on the Witt ring `W(K)`. It is not additive on `W(K)`. It is additive as soon as one
summand lies in the square `I(K)²` of the fundamental ideal: the correction terms of Lam's
comparison of `c` with the Hasse invariant cancel there. So `c` restricts to an additive map
`I(K)² → Br(K)`, written additively. Its value on the two-fold Pfister class `⟨⟨a, b⟩⟩` is the
quaternion class `[(a, b)]`. Its values are `2`-torsion, and it vanishes on `I(K)³`, because it
vanishes on the three-fold Pfister classes, which additively generate `I(K)³`. It therefore
descends to the quotient `I(K)²/I(K)³`.

The quotient `I(K)²/I(K)³` is formed in the additive group of `I(K)²`, with `I(K)³` viewed as
the subgroup `TauCeti.fundamentalI3InI2`.

## Main definitions

* `TauCeti.WittRing.cliffordInvariant`: the Clifford invariant of a Witt class.
* `TauCeti.cliffordHomI2`: the additive map `I(K)² → Br(K)` given by the Clifford invariant.
* `TauCeti.fundamentalI3InI2`: `I(K)³` as a subgroup of `I(K)²`.
* `TauCeti.cliffordHomI2Bar`: the induced map `I(K)²/I(K)³ → Br(K)`.

## Main results

* `TauCeti.WittRing.cliffordInvariant_wittClass`: `c` of the Witt class of a form is `c` of
  the form.
* `TauCeti.WittRing.cliffordInvariant_add_of_mem_fundamentalIdeal_sq`: `c(x + y) = c(x) · c(y)`
  when `x ∈ I(K)²`.
* `TauCeti.WittRing.cliffordInvariant_eq_one_of_mem_fundamentalIdeal_cube`: `c` is trivial on
  `I(K)³`.
* `TauCeti.cliffordHomI2_pfisterClass`: `c⟨⟨a, b⟩⟩ = [(a, b)]`.
* `TauCeti.cliffordHomI2_two_torsion`: the values of `c` on `I(K)²` are `2`-torsion.
* `TauCeti.cliffordHomI2Bar_mk`: the induced map on `I(K)²/I(K)³` computes `c` on
  representatives.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V, §3, especially
  Theorem 3.4 and Theorem 3.20.
-/

public section

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-! ### The Clifford invariant of a Witt class -/

namespace WittRing

/-- **The Clifford invariant of a Witt class**: the Clifford invariant of any form representing
it. This is well defined because adding a hyperbolic plane does not change the Clifford invariant;
see `TauCeti.WittRing.cliffordInvariant_wittClass`. -/
noncomputable def cliffordInvariant (x : WittRing K) : BrauerGroup K :=
  RegularFormClass.cliffordInvariant (Function.surjInv wittClass_surjective x)

/-- The Clifford invariant of the Witt class of a form is the Clifford invariant of the form. -/
@[simp]
theorem cliffordInvariant_wittClass (x : RegularFormClass K) :
    cliffordInvariant (wittClass x) = RegularFormClass.cliffordInvariant x := by
  obtain ⟨m, n, h⟩ := wittClass_eq_iff_exists_nsmul.mp
    (Function.surjInv_eq wittClass_surjective (wittClass x))
  rw [cliffordInvariant, ← RegularFormClass.cliffordInvariant_nsmul_hyperbolicClass_add m, h,
    RegularFormClass.cliffordInvariant_nsmul_hyperbolicClass_add]

/-- The zero Witt class has trivial Clifford invariant. -/
@[simp]
theorem cliffordInvariant_zero : cliffordInvariant (0 : WittRing K) = 1 := by
  rw [← map_zero (wittClass (K := K)), cliffordInvariant_wittClass,
    RegularFormClass.cliffordInvariant_zero]

/-- The Clifford invariant of a Witt class is `2`-torsion. -/
@[simp]
theorem cliffordInvariant_sq (x : WittRing K) : cliffordInvariant x ^ 2 = 1 := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  rw [cliffordInvariant_wittClass, RegularFormClass.cliffordInvariant_sq]

/-- **Additivity of the Clifford invariant on `I(K)²`**: `c(x + y) = c(x) · c(y)` when `x` lies
in the square of the fundamental ideal, for every Witt class `y`. -/
theorem cliffordInvariant_add_of_mem_fundamentalIdeal_sq {x : WittRing K}
    (hx : x ∈ fundamentalIdeal K ^ 2) (y : WittRing K) :
    cliffordInvariant (x + y) = cliffordInvariant x * cliffordInvariant y := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  obtain ⟨r, rfl⟩ := wittClass_surjective y
  obtain ⟨he, hd⟩ := (wittClass_mem_fundamentalIdeal_sq_iff q).mp hx
  rw [← map_add, cliffordInvariant_wittClass, cliffordInvariant_wittClass,
    cliffordInvariant_wittClass,
    RegularFormClass.cliffordInvariant_add_of_signedDiscr_eq_zero he hd]

/-- The Clifford invariant of the two-fold Pfister class `⟨⟨a, b⟩⟩` is `[(a, b)]`. -/
theorem cliffordInvariant_pfisterClass_two (a b : Kˣ) :
    cliffordInvariant (pfisterClass ![a, b]) = BrauerGroup.quaternionClass a b := by
  rw [← wittClass_pfisterFormClass, cliffordInvariant_wittClass,
    RegularFormClass.cliffordInvariant_pfisterFormClass_two]

/-- **The Clifford invariant is trivial on `I(K)³`**, because it is trivial on the three-fold
Pfister classes, which additively generate `I(K)³`. -/
theorem cliffordInvariant_eq_one_of_mem_fundamentalIdeal_cube {x : WittRing K}
    (hx : x ∈ fundamentalIdeal K ^ 3) : cliffordInvariant x = 1 := by
  have hsq {y : WittRing K} (hy : y ∈ AddSubgroup.closure (Set.range (pfisterClass (n := 3)))) :
      y ∈ fundamentalIdeal K ^ 2 := by
    rw [← fundamentalIdeal_cube_eq_addClosure, Submodule.mem_toAddSubgroup] at hy
    exact Ideal.pow_le_pow_right (by norm_num) hy
  rw [← Submodule.mem_toAddSubgroup, fundamentalIdeal_cube_eq_addClosure] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have ha : a = ![a 0, a 1, a 2] := by
      funext i
      fin_cases i <;> rfl
    rw [ha, ← wittClass_pfisterFormClass, cliffordInvariant_wittClass,
      RegularFormClass.cliffordInvariant_pfisterFormClass_three]
  | zero => exact cliffordInvariant_zero
  | add y z hy _ hy1 hz1 =>
    rw [cliffordInvariant_add_of_mem_fundamentalIdeal_sq (hsq hy), hy1, hz1, one_mul]
  | neg y hy hy1 =>
    have h := cliffordInvariant_add_of_mem_fundamentalIdeal_sq (hsq hy) (-y)
    rwa [add_neg_cancel, cliffordInvariant_zero, hy1, one_mul, eq_comm] at h

end WittRing

/-! ### The homomorphism `I(K)² → Br(K)` -/

/-- **The Clifford homomorphism on `I(K)²`**: the Clifford invariant, as an additive map from
the square of the fundamental ideal to the Brauer group written additively. It is additive by
`TauCeti.WittRing.cliffordInvariant_add_of_mem_fundamentalIdeal_sq`, its values are `2`-torsion
by `TauCeti.cliffordHomI2_two_torsion`, and it vanishes on `I(K)³` by
`TauCeti.cliffordHomI2_eq_zero`. -/
noncomputable def cliffordHomI2 : ↥(fundamentalIdeal K ^ 2) →+ Additive (BrauerGroup K) where
  toFun x := Additive.ofMul (WittRing.cliffordInvariant (x : WittRing K))
  map_zero' := by rw [ZeroMemClass.coe_zero, WittRing.cliffordInvariant_zero, ofMul_one]
  map_add' x y := by
    rw [AddMemClass.coe_add, WittRing.cliffordInvariant_add_of_mem_fundamentalIdeal_sq x.2,
      ofMul_mul]

/-- `cliffordHomI2` evaluates the Clifford invariant. -/
@[simp]
theorem cliffordHomI2_apply (x : ↥(fundamentalIdeal K ^ 2)) :
    cliffordHomI2 x = Additive.ofMul (WittRing.cliffordInvariant (x : WittRing K)) :=
  (rfl)

/-- `cliffordHomI2` sends the two-fold Pfister class `⟨⟨a, b⟩⟩` to the quaternion class
`[(a, b)]`. -/
theorem cliffordHomI2_pfisterClass (a b : Kˣ) :
    cliffordHomI2 ⟨pfisterClass ![a, b], pfisterClass_mem_fundamentalIdeal_pow _⟩ =
      Additive.ofMul (BrauerGroup.quaternionClass a b) := by
  rw [cliffordHomI2_apply, WittRing.cliffordInvariant_pfisterClass_two]

/-- The values of `cliffordHomI2` are `2`-torsion in the Brauer group. -/
theorem cliffordHomI2_two_torsion (x : ↥(fundamentalIdeal K ^ 2)) : 2 • cliffordHomI2 x = 0 := by
  rw [cliffordHomI2_apply, ← ofMul_pow, WittRing.cliffordInvariant_sq, ofMul_one]

/-- `cliffordHomI2` vanishes on `I(K)³`. -/
theorem cliffordHomI2_eq_zero {x : ↥(fundamentalIdeal K ^ 2)}
    (hx : (x : WittRing K) ∈ fundamentalIdeal K ^ 3) : cliffordHomI2 x = 0 := by
  rw [cliffordHomI2_apply, WittRing.cliffordInvariant_eq_one_of_mem_fundamentalIdeal_cube hx,
    ofMul_one]

/-! ### The quotient `I(K)²/I(K)³` -/

variable (K) in
/-- `I(K)³`, viewed as an additive subgroup of `I(K)²`. -/
noncomputable def fundamentalI3InI2 : AddSubgroup ↥(fundamentalIdeal K ^ 2) :=
  (fundamentalIdeal K ^ 3).toAddSubgroup.comap (fundamentalIdeal K ^ 2).subtype.toAddMonoidHom

/-- An element of `I(K)²` lies in `fundamentalI3InI2 K` exactly when it lies in `I(K)³`. -/
@[simp]
theorem mem_fundamentalI3InI2 {x : ↥(fundamentalIdeal K ^ 2)} :
    x ∈ fundamentalI3InI2 K ↔ (x : WittRing K) ∈ fundamentalIdeal K ^ 3 :=
  Iff.rfl

/-- **The Clifford homomorphism on `I(K)²/I(K)³`**: `cliffordHomI2` descends to the quotient,
because it vanishes on `I(K)³`. -/
noncomputable def cliffordHomI2Bar :
    ↥(fundamentalIdeal K ^ 2) ⧸ fundamentalI3InI2 K →+ Additive (BrauerGroup K) :=
  QuotientAddGroup.lift _ cliffordHomI2 fun _ hx => cliffordHomI2_eq_zero hx

/-- `cliffordHomI2Bar` computes the Clifford invariant of a representative. -/
@[simp]
theorem cliffordHomI2Bar_mk (x : ↥(fundamentalIdeal K ^ 2)) :
    cliffordHomI2Bar (x : ↥(fundamentalIdeal K ^ 2) ⧸ fundamentalI3InI2 K) = cliffordHomI2 x :=
  QuotientAddGroup.lift_mk _ _ x

end TauCeti
