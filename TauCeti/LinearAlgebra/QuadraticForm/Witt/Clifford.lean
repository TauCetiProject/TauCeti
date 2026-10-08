/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Pfister.Clifford

/-!
# The Clifford homomorphism `I(K)² → Br(K)`

Over a field `K` in which two is invertible, adding a hyperbolic plane does not change the
Clifford invariant `c` of a regular quadratic form, so forms with the same Witt class have the
same Clifford invariant. The invariant is not additive on the whole Witt ring, but it is additive
on forms of even rank with trivial signed discriminant, which are exactly the forms whose Witt
classes lie in the square `I(K)²` of the fundamental ideal
(`TauCeti.RegularFormClass.cliffordInvariant_add_of_signedDiscr_eq_zero`). Hence `c` induces a
group homomorphism

`c : I(K)² → Br(K)`,

written additively. Its values are `2`-torsion, it sends the two-fold Pfister class `⟨⟨a, b⟩⟩` to
the quaternion class `[(a, b)]`, and it vanishes on the three-fold Pfister classes, which
additively generate `I(K)³`. So it descends to a homomorphism `c̄ : I(K)²/I(K)³ → Br(K)` with
values in the `2`-torsion subgroup `Br(K)[2]`. No injectivity or surjectivity statement is made
here.

## Main definitions

* `TauCeti.cliffordHomI2`: the homomorphism `I(K)² → Br(K)` induced by the Clifford invariant.
* `TauCeti.fundamentalI3InI2`: the cube `I(K)³` as a submodule of `I(K)²`.
* `TauCeti.cliffordHomI2Bar`: the induced homomorphism `I(K)²/I(K)³ → Br(K)`.

## Main results

* `TauCeti.RegularFormClass.cliffordInvariant_hyperbolicClass_add`: adding a hyperbolic plane
  does not change the Clifford invariant.
* `TauCeti.RegularFormClass.cliffordInvariant_eq_of_wittClass_eq`: forms with the same Witt class
  have the same Clifford invariant.
* `TauCeti.cliffordHomI2_apply`: `c` sends the Witt class of a form to its Clifford invariant.
* `TauCeti.cliffordHomI2_pfisterClass`: `c⟨⟨a, b⟩⟩ = [(a, b)]`.
* `TauCeti.cliffordHomI2_two_torsion`: the values of `c` are `2`-torsion.
* `TauCeti.cliffordHomI2_eq_zero`: `c` vanishes on `I(K)³`.
* `TauCeti.cliffordHomI2Bar_mk`: `c̄` computes `c` on representatives.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter V, §3.
-/

public section

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

namespace RegularFormClass

/-- **Adding a hyperbolic plane does not change the Clifford invariant**: `c(ℍ ⊥ x) = c(x)` for
every class `x`, of either parity. -/
theorem cliffordInvariant_hyperbolicClass_add (x : RegularFormClass K) :
    cliffordInvariant (hyperbolicClass K + x) = cliffordInvariant x := by
  have heven {y : RegularFormClass K} (hy : Even y.rank) :
      cliffordInvariant (hyperbolicClass K + y) = cliffordInvariant y := by
    rw [hyperbolicClass_def, cliffordInvariant_mk_binary_add 1 (-1) hy,
      BrauerGroup.quaternionClass_one_left, one_mul, one_mul, neg_neg, mk_rankOne_one, one_mul]
  rcases Nat.even_or_odd x.rank with hx | hx
  · exact heven hx
  obtain ⟨a, y, hy, rfl⟩ := exists_eq_add_mk_rankOne (x := x) hx.pos
  have hye : Even y.rank := by
    rw [← hy, Nat.odd_add_one, Nat.not_odd_iff_even] at hx
    exact hx
  rw [← add_assoc, cliffordInvariant_add_mk_rankOne a
      (by rw [rank_add, rank_hyperbolicClass]; exact even_two.add hye),
    mul_add, mk_rankOne_mul_hyperbolicClass, heven (by rw [rank_mul, rank_mk, one_mul]; exact hye),
    cliffordInvariant_add_mk_rankOne a hye]

/-- Adding any number of hyperbolic planes does not change the Clifford invariant. -/
theorem cliffordInvariant_nsmul_hyperbolicClass_add (m : ℕ) (x : RegularFormClass K) :
    cliffordInvariant (m • hyperbolicClass K + x) = cliffordInvariant x := by
  induction m with
  | zero => rw [zero_nsmul, zero_add]
  | succ m ih => rw [succ_nsmul', add_assoc, cliffordInvariant_hyperbolicClass_add, ih]

/-- **The Clifford invariant is an invariant of Witt classes**: forms with the same Witt class
have the same Clifford invariant. -/
theorem cliffordInvariant_eq_of_wittClass_eq {x y : RegularFormClass K}
    (h : wittClass x = wittClass y) : cliffordInvariant x = cliffordInvariant y := by
  obtain ⟨m, n, hmn⟩ := wittClass_eq_iff_exists_nsmul.mp h
  rw [← cliffordInvariant_nsmul_hyperbolicClass_add m x, hmn,
    cliffordInvariant_nsmul_hyperbolicClass_add]

end RegularFormClass

/-! ### The homomorphism on the square of the fundamental ideal -/

open RegularFormClass

/-- The Clifford invariant of the chosen representative of a Witt class is the Clifford invariant
of any form in that class. -/
private theorem cliffordInvariant_surjInv {z : WittRing K} {q : RegularFormClass K}
    (hq : wittClass q = z) :
    cliffordInvariant (Function.surjInv wittClass_surjective z) = cliffordInvariant q :=
  cliffordInvariant_eq_of_wittClass_eq ((Function.surjInv_eq wittClass_surjective z).trans hq.symm)

/-- **The Clifford homomorphism** `c : I(K)² → Br(K)`, written additively: it sends the Witt class
of a form in `I(K)²` to the Clifford invariant of that form
(`TauCeti.cliffordHomI2_apply`). It is additive because the Clifford invariant is additive on
forms of even rank with trivial signed discriminant. -/
noncomputable def cliffordHomI2 : ↥(fundamentalIdeal K ^ 2) →+ Additive (BrauerGroup K) where
  toFun x := Additive.ofMul (cliffordInvariant (Function.surjInv wittClass_surjective x.1))
  map_zero' := by
    rw [ZeroMemClass.coe_zero, cliffordInvariant_surjInv (map_zero wittClass),
      cliffordInvariant_zero, ofMul_one]
  map_add' x y := by
    obtain ⟨q, hq⟩ := wittClass_surjective x.1
    obtain ⟨r, hr⟩ := wittClass_surjective y.1
    have hqI := (wittClass_mem_fundamentalIdeal_sq_iff q).mp (hq ▸ x.2)
    have hrI := (wittClass_mem_fundamentalIdeal_sq_iff r).mp (hr ▸ y.2)
    rw [Submodule.coe_add, cliffordInvariant_surjInv (q := q + r) (by rw [map_add, hq, hr]),
      cliffordInvariant_surjInv hq, cliffordInvariant_surjInv hr,
      cliffordInvariant_add_of_signedDiscr_eq_zero hqI.1 hqI.2 hrI.1 hrI.2, ofMul_mul]

/-- **`c` computes the Clifford invariant**: on the Witt class of a form `q`, it is `c(q)`. -/
theorem cliffordHomI2_apply {x : ↥(fundamentalIdeal K ^ 2)} {q : RegularFormClass K}
    (hq : wittClass q = x) : cliffordHomI2 x = Additive.ofMul (cliffordInvariant q) :=
  congrArg Additive.ofMul (cliffordInvariant_surjInv hq)

/-- `c` sends the Witt class of a form in `I(K)²` to its Clifford invariant. -/
@[simp]
theorem cliffordHomI2_wittClass (q : RegularFormClass K)
    (hq : wittClass q ∈ fundamentalIdeal K ^ 2) :
    cliffordHomI2 ⟨wittClass q, hq⟩ = Additive.ofMul (cliffordInvariant q) :=
  cliffordHomI2_apply rfl

-- Not `@[simp]`: `TauCeti.pfisterClass_two` rewrites `pfisterClass ![a, b]` inside the subtype.
/-- **`c` on a two-fold Pfister generator**: `c⟨⟨a, b⟩⟩ = [(a, b)]`. -/
theorem cliffordHomI2_pfisterClass (a b : Kˣ) :
    cliffordHomI2 ⟨pfisterClass ![a, b], pfisterClass_mem_fundamentalIdeal_pow ![a, b]⟩ =
      Additive.ofMul (BrauerGroup.quaternionClass a b) := by
  rw [cliffordHomI2_apply (wittClass_pfisterFormClass ![a, b]),
    cliffordInvariant_pfisterFormClass_two]

/-- **The values of `c` are `2`-torsion**, so `c` takes values in `Br(K)[2]`. -/
theorem cliffordHomI2_two_torsion (x : ↥(fundamentalIdeal K ^ 2)) :
    cliffordHomI2 x + cliffordHomI2 x = 0 := by
  obtain ⟨q, hq⟩ := wittClass_surjective x.1
  rw [cliffordHomI2_apply hq, ← ofMul_mul, ← pow_two, cliffordInvariant_sq, ofMul_one]

/-- **`c` vanishes on `I(K)³`**, which is additively generated by the three-fold Pfister classes,
each of trivial Clifford invariant. -/
theorem cliffordHomI2_eq_zero (x : ↥(fundamentalIdeal K ^ 2))
    (hx : (x : WittRing K) ∈ fundamentalIdeal K ^ 3) : cliffordHomI2 x = 0 := by
  have hle : (fundamentalIdeal K ^ 3).toAddSubgroup ≤
      (cliffordHomI2 (K := K)).ker.map (fundamentalIdeal K ^ 2).subtype.toAddMonoidHom := by
    rw [fundamentalIdeal_cube_eq_addClosure, AddSubgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    have ha : a = ![a 0, a 1, a 2] := by
      ext i
      fin_cases i <;> rfl
    refine ⟨⟨pfisterClass a, Ideal.pow_le_pow_right (by norm_num)
      (pfisterClass_mem_fundamentalIdeal_pow a)⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker,
      cliffordHomI2_apply (wittClass_pfisterFormClass a), ha,
      cliffordInvariant_pfisterFormClass_three, ofMul_one]
  obtain ⟨y, hy, hyx⟩ := hle hx
  rw [← Subtype.ext hyx]
  exact hy

/-! ### The quotient homomorphism on `I(K)²/I(K)³` -/

/-- The cube `I(K)³` of the fundamental ideal, as a submodule of the square `I(K)²`. -/
noncomputable abbrev fundamentalI3InI2 (K : Type u) [Field K] [Invertible (2 : K)] :
    Submodule (WittRing K) ↥(fundamentalIdeal K ^ 2) :=
  Submodule.comap (fundamentalIdeal K ^ 2).subtype (fundamentalIdeal K ^ 3)

/-- **The Clifford homomorphism** `c̄ : I(K)²/I(K)³ → Br(K)`, written additively: the descent of
`TauCeti.cliffordHomI2`, which vanishes on `I(K)³`. Its values are those of `c`, so they are
`2`-torsion by `TauCeti.cliffordHomI2_two_torsion`. -/
noncomputable def cliffordHomI2Bar :
    (↥(fundamentalIdeal K ^ 2) ⧸ fundamentalI3InI2 K) →+ Additive (BrauerGroup K) :=
  -- A quotient by a submodule is the quotient by its underlying additive subgroup, as in
  -- Mathlib's `Submodule.liftQ`.
  QuotientAddGroup.lift (fundamentalI3InI2 K).toAddSubgroup cliffordHomI2 cliffordHomI2_eq_zero

/-- `c̄` computes `c` on a representative. -/
@[simp]
theorem cliffordHomI2Bar_mk (x : ↥(fundamentalIdeal K ^ 2)) :
    cliffordHomI2Bar (Submodule.Quotient.mk x) = cliffordHomI2 x :=
  QuotientAddGroup.lift_mk' _ _ x

end TauCeti
