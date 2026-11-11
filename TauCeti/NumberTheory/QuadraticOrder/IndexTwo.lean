/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.QuadraticAlgebra.ChangeGenerator
public import TauCeti.Algebra.QuadraticAlgebra.DualNumber
public import TauCeti.Algebra.QuadraticAlgebra.Split
public import TauCeti.NumberTheory.QuadraticOrder.PrimeIdeal
public import TauCeti.NumberTheory.QuadraticOrder.Reduction

/-!
# The index-two comparison of quadratic orders

For `B = QuadraticAlgebra ℤ a b` of discriminant `d = b² + 4a`, the comparison
`ι = QuadraticAlgebra.algHomOfDiscrZero : QuadraticAlgebra ℤ d 0 → B`, `ω ↦ 2ω - b` (defined
over any commutative ring in `TauCeti.Algebra.QuadraticAlgebra.ChangeGenerator`), is injective
with image `{x + yω | y even}` of index two. With `d ≡ 1 (mod 4)`, `a = (d - 1)/4` and `b = 1`,
this is the inclusion of `ℤ[√d]` into `ℤ[(1 + √d)/2]`.

Modulo a natural number `m`, `ι` induces a ring map `ℤ[√d]/(m) → B/(m)` which is bijective
exactly when `m` is odd. At `m = 2` it fails: the quotient `ℤ[√d]/(2)` is the ring of dual
numbers over `ℤ/2`, while `B/(2)` is the field with four elements when `d ≡ 5 (mod 8)` and
`ℤ/2 × ℤ/2` when `d ≡ 1 (mod 8)`.

## Main definitions

* `QuadraticAlgebra.quotientRingHomOfDiscrZero`: the induced ring map
  `QuadraticAlgebra ℤ d e ⧸ (m) →+* QuadraticAlgebra ℤ a b ⧸ (m)`.
* `QuadraticAlgebra.quotientRingEquivOfDiscrZero`: for odd `m`, the induced isomorphism.
* `QuadraticAlgebra.quotientSpanTwoRingEquivDualNumber`: for odd `d` and even `e`,
  `ℤ[√d]/(2) ≃+* (ℤ/2)[ε]`.
* `QuadraticAlgebra.quotientSpanTwoRingEquivProd`: for even `a`,
  `QuadraticAlgebra ℤ a 1 ⧸ (2) ≃+* ℤ/2 × ℤ/2`.

## Main results

* `QuadraticAlgebra.index_range_algHomOfDiscrZero`: over `ℤ` the image of `ι` has index two.
* `QuadraticAlgebra.bijective_quotientRingHomOfDiscrZero_iff`: the reduced map modulo `m` is
  bijective exactly when `m` is odd.
* `QuadraticAlgebra.not_injective_quotientRingHomOfDiscrZero_two`,
  `not_surjective_quotientRingHomOfDiscrZero_two`: at `m = 2` it is neither.
* `QuadraticAlgebra.not_isReduced_quotient_span_two`: for odd `d` and even `e`, `ℤ[√d]/(2)` is
  not reduced.
* `QuadraticAlgebra.isField_quotient_span_two_iff_discr_emod_eight`: the shape of
  `QuadraticAlgebra ℤ a 1 ⧸ (2)` by `d mod 8`.

## References

* J. S. Milne, *Algebraic Number Theory*, Example 2.41, for the integral basis
  `1, (1 + √d)/2` of `ℚ(√d)` when `d` is squarefree and `d ≡ 1 (mod 4)`.
-/

public section

namespace QuadraticAlgebra

section Int

variable {a b d e : ℤ}

/-- Over `ℤ` the index-two comparison is injective. -/
theorem algHomOfDiscrZero_injective (hd : d = discr a b) (he : e = 0) :
    Function.Injective (algHomOfDiscrZero a b hd he) :=
  (injective_algHomOfDiscrZero_iff hd he).mpr (IsRegular.of_ne_zero two_ne_zero)

/-- Over `ℤ` the image of the index-two comparison is `{x + yω | y even}`. -/
theorem mem_range_algHomOfDiscrZero_iff_even (hd : d = discr a b) (he : e = 0)
    {z : QuadraticAlgebra ℤ a b} :
    z ∈ (algHomOfDiscrZero a b hd he).range ↔ Even z.im := by
  rw [mem_range_algHomOfDiscrZero_iff, even_iff_two_dvd]

/-- **Index two.** Over `ℤ` the image of the index-two comparison is an additive subgroup of
index two. -/
theorem index_range_algHomOfDiscrZero (hd : d = discr a b) (he : e = 0) :
    (algHomOfDiscrZero a b hd he).range.toSubring.toAddSubgroup.index = 2 := by
  refine AddSubgroup.index_eq_two_iff.mpr ⟨ω, fun z ↦ ?_⟩
  simp only [Subring.mem_toAddSubgroup, Subalgebra.mem_toSubring,
    mem_range_algHomOfDiscrZero_iff_even, im_add, im_omega, Int.even_add_one]
  by_cases h : Even z.im <;> simp [h]

variable (a b) in
/-- **The index-two comparison modulo `m`.** The ring map
`QuadraticAlgebra ℤ d e ⧸ (m) → QuadraticAlgebra ℤ a b ⧸ (m)` induced by `algHomOfDiscrZero`. -/
def quotientRingHomOfDiscrZero (hd : d = discr a b) (he : e = 0) (m : ℕ) :
    QuadraticAlgebra ℤ d e ⧸ Ideal.span {(m : QuadraticAlgebra ℤ d e)} →+*
      QuadraticAlgebra ℤ a b ⧸ Ideal.span {(m : QuadraticAlgebra ℤ a b)} :=
  Ideal.quotientMap _ (algHomOfDiscrZero a b hd he).toRingHom <| Ideal.span_le.mpr <|
    Set.singleton_subset_iff.mpr <| by simp

@[simp]
theorem quotientRingHomOfDiscrZero_mk (hd : d = discr a b) (he : e = 0) (m : ℕ)
    (z : QuadraticAlgebra ℤ d e) :
    quotientRingHomOfDiscrZero a b hd he m (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (algHomOfDiscrZero a b hd he z) :=
  Ideal.quotientMap_mk

/-- Under the identifications `quotientSpanNatCastEquiv` of both quotients with quadratic
algebras over `ℤ/m`, the reduced comparison is the comparison over `ℤ/m`. -/
theorem quotientSpanNatCastEquiv_quotientRingHomOfDiscrZero (hd : d = discr a b) (he : e = 0)
    (m : ℕ) (x : QuadraticAlgebra ℤ d e ⧸ Ideal.span {(m : QuadraticAlgebra ℤ d e)}) :
    quotientSpanNatCastEquiv a b m (quotientRingHomOfDiscrZero a b hd he m x) =
      algHomOfDiscrZero (a : ZMod m) (b : ZMod m) (by rw [hd, discr_intCast])
        (by rw [he, Int.cast_zero]) (quotientSpanNatCastEquiv d e m x) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  ext <;> simp

/-- **The reduced comparison is an isomorphism exactly for odd `m`.** The map
`QuadraticAlgebra ℤ d e ⧸ (m) → QuadraticAlgebra ℤ a b ⧸ (m)` induced by the index-two
comparison is bijective exactly when `m` is odd. -/
theorem bijective_quotientRingHomOfDiscrZero_iff (hd : d = discr a b) (he : e = 0) {m : ℕ} :
    Function.Bijective (quotientRingHomOfDiscrZero a b hd he m) ↔ Odd m := by
  have h : ⇑(quotientRingHomOfDiscrZero a b hd he m) = (quotientSpanNatCastEquiv a b m).symm ∘
      algHomOfDiscrZero (a : ZMod m) (b : ZMod m) (by rw [hd, discr_intCast])
        (by rw [he, Int.cast_zero]) ∘ quotientSpanNatCastEquiv d e m := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, RingEquiv.eq_symm_apply,
      quotientSpanNatCastEquiv_quotientRingHomOfDiscrZero]
  rw [h, EquivLike.comp_bijective, EquivLike.bijective_comp, bijective_algHomOfDiscrZero_iff]
  simpa [Nat.coprime_two_left] using ZMod.isUnit_iff_coprime 2 m

variable (a b) in
/-- For odd `m`, the index-two comparison induces a ring isomorphism
`QuadraticAlgebra ℤ d e ⧸ (m) ≃+* QuadraticAlgebra ℤ a b ⧸ (m)`. -/
noncomputable def quotientRingEquivOfDiscrZero (hd : d = discr a b) (he : e = 0) {m : ℕ}
    (hm : Odd m) :
    QuadraticAlgebra ℤ d e ⧸ Ideal.span {(m : QuadraticAlgebra ℤ d e)} ≃+*
      QuadraticAlgebra ℤ a b ⧸ Ideal.span {(m : QuadraticAlgebra ℤ a b)} :=
  RingEquiv.ofBijective _ ((bijective_quotientRingHomOfDiscrZero_iff hd he).mpr hm)

@[simp]
theorem quotientRingEquivOfDiscrZero_apply (hd : d = discr a b) (he : e = 0) {m : ℕ}
    (hm : Odd m) (x : QuadraticAlgebra ℤ d e ⧸ Ideal.span {(m : QuadraticAlgebra ℤ d e)}) :
    quotientRingEquivOfDiscrZero a b hd he hm x = quotientRingHomOfDiscrZero a b hd he m x :=
  RingEquiv.ofBijective_apply _ _ _

/-- At `m = 2` the class of `b + ω` lies in the kernel of the reduced comparison:
`algHomOfDiscrZero` sends `b + ω` to `2ω`. -/
theorem quotientRingHomOfDiscrZero_two_mk_eq_zero (hd : d = discr a b) (he : e = 0) :
    quotientRingHomOfDiscrZero a b hd he 2 (Ideal.Quotient.mk _ ⟨b, 1⟩) = 0 := by
  rw [quotientRingHomOfDiscrZero_mk, Ideal.Quotient.eq_zero_iff_mem, mem_span_natCast_iff]
  simp

/-- The class modulo `2` of an element with odd `ω`-coordinate is nonzero. -/
theorem mk_span_two_ne_zero_of_odd_im {z : QuadraticAlgebra ℤ d e} (hz : Odd z.im) :
    Ideal.Quotient.mk (Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ d e)}) z ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, mem_span_natCast_iff, Nat.cast_ofNat,
    ← even_iff_two_dvd, ← even_iff_two_dvd]
  exact fun h ↦ Int.not_even_iff_odd.mpr hz h.2

/-- At `m = 2` the reduced comparison is not injective. -/
theorem not_injective_quotientRingHomOfDiscrZero_two (hd : d = discr a b) (he : e = 0) :
    ¬Function.Injective (quotientRingHomOfDiscrZero a b hd he 2) := fun h ↦
  mk_span_two_ne_zero_of_odd_im (z := ⟨b, 1⟩) odd_one <|
    (injective_iff_map_eq_zero _).mp h _ (quotientRingHomOfDiscrZero_two_mk_eq_zero hd he)

/-- At `m = 2` the reduced comparison is not surjective, both quotients having four
elements. -/
theorem not_surjective_quotientRingHomOfDiscrZero_two (hd : d = discr a b) (he : e = 0) :
    ¬Function.Surjective (quotientRingHomOfDiscrZero a b hd he 2) := fun h ↦
  not_injective_quotientRingHomOfDiscrZero_two hd he <|
    (h.bijective_of_nat_card_le
      (by rw [card_quotient_span_natCast, card_quotient_span_natCast])).1

variable (d e) in
/-- **`ℤ[√d]/(2)` has a repeated root.** For `d` odd and `e` even,
`QuadraticAlgebra ℤ d e ⧸ (2)` is the ring of dual numbers over `ℤ/2`, with `ω ↦ 1 + ε`. -/
noncomputable def quotientSpanTwoRingEquivDualNumber (hd : Odd d) (he : Even e) :
    QuadraticAlgebra ℤ d e ⧸ Ideal.span {(2 : QuadraticAlgebra ℤ d e)} ≃+*
      DualNumber (ZMod 2) :=
  (Ideal.quotEquivOfEq (by rw [Nat.cast_ofNat])).trans <| (quotientSpanNatCastEquiv d e 2).trans
    (algEquivDualNumberOfDoubleRoot 1 (by rw [ZMod.intCast_eq_one_iff_odd.mpr hd]; decide)
      (by rw [ZMod.intCast_eq_zero_iff_even.mpr he]; decide)).toRingEquiv

@[simp]
theorem fst_quotientSpanTwoRingEquivDualNumber_mk (hd : Odd d) (he : Even e)
    (z : QuadraticAlgebra ℤ d e) :
    (quotientSpanTwoRingEquivDualNumber d e hd he
        (Ideal.Quotient.mk (Ideal.span {(2 : QuadraticAlgebra ℤ d e)}) z)).fst =
      ((z.re + z.im : ℤ) : ZMod 2) := by
  rw [quotientSpanTwoRingEquivDualNumber, RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, quotientSpanNatCastEquiv_mk]
  simp

@[simp]
theorem snd_quotientSpanTwoRingEquivDualNumber_mk (hd : Odd d) (he : Even e)
    (z : QuadraticAlgebra ℤ d e) :
    (quotientSpanTwoRingEquivDualNumber d e hd he
        (Ideal.Quotient.mk (Ideal.span {(2 : QuadraticAlgebra ℤ d e)}) z)).snd =
      (z.im : ZMod 2) := by
  rw [quotientSpanTwoRingEquivDualNumber, RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, quotientSpanNatCastEquiv_mk]
  simp

/-- `quotientSpanTwoRingEquivDualNumber` sends the class of `ω` to `1 + ε`. -/
theorem quotientSpanTwoRingEquivDualNumber_mk_omega (hd : Odd d) (he : Even e) :
    quotientSpanTwoRingEquivDualNumber d e hd he
        (Ideal.Quotient.mk (Ideal.span {(2 : QuadraticAlgebra ℤ d e)}) ω) =
      1 + DualNumber.eps := by
  ext <;> simp

/-- The inverse of `quotientSpanTwoRingEquivDualNumber` sends `x + yε` to the class of
`(x - y) + yω`. -/
@[simp]
theorem quotientSpanTwoRingEquivDualNumber_symm_apply (hd : Odd d) (he : Even e)
    (x : DualNumber (ZMod 2)) :
    (quotientSpanTwoRingEquivDualNumber d e hd he).symm x =
      Ideal.Quotient.mk _ ⟨((x.fst - x.snd).val : ℤ), (x.snd.val : ℤ)⟩ := by
  rw [RingEquiv.symm_apply_eq]
  ext <;> simp

/-- For `d` odd and `e` even, `QuadraticAlgebra ℤ d e ⧸ (2)` is not reduced. -/
theorem not_isReduced_quotient_span_two (hd : Odd d) (he : Even e) :
    ¬IsReduced (QuadraticAlgebra ℤ d e ⧸ Ideal.span {(2 : QuadraticAlgebra ℤ d e)}) :=
  fun _ ↦ DualNumber.not_isReduced <| isReduced_of_injective
    (quotientSpanTwoRingEquivDualNumber d e hd he).symm (RingEquiv.injective _)

variable (a) in
/-- For `a` even, `QuadraticAlgebra ℤ a 1 ⧸ (2)` is `ℤ/2 × ℤ/2`, by evaluation at the roots
`1` and `0` of `X² - X`. -/
noncomputable def quotientSpanTwoRingEquivProd (ha : Even a) :
    QuadraticAlgebra ℤ a 1 ⧸ Ideal.span {(2 : QuadraticAlgebra ℤ a 1)} ≃+*
      ZMod 2 × ZMod 2 :=
  (Ideal.quotEquivOfEq (by rw [Nat.cast_ofNat])).trans <| (quotientSpanNatCastEquiv a 1 2).trans
    (algEquivProdOfRoots 1 0 (by simp)
      (by rw [mul_zero, neg_zero, ZMod.intCast_eq_zero_iff_even]; exact ha) (by simp)).toRingEquiv

/-- `quotientSpanTwoRingEquivProd` evaluates the class of `x + yω` at `ω = 1` and `ω = 0`. -/
@[simp]
theorem quotientSpanTwoRingEquivProd_mk (ha : Even a) (z : QuadraticAlgebra ℤ a 1) :
    quotientSpanTwoRingEquivProd a ha
        (Ideal.Quotient.mk (Ideal.span {(2 : QuadraticAlgebra ℤ a 1)}) z) =
      (((z.re + z.im : ℤ) : ZMod 2), (z.re : ZMod 2)) := by
  rw [quotientSpanTwoRingEquivProd, RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, quotientSpanNatCastEquiv_mk]
  simp

/-- The inverse of `quotientSpanTwoRingEquivProd` sends `(s, t)` to the class of
`t + (s - t)ω`. -/
@[simp]
theorem quotientSpanTwoRingEquivProd_symm_apply (ha : Even a) (x : ZMod 2 × ZMod 2) :
    (quotientSpanTwoRingEquivProd a ha).symm x =
      Ideal.Quotient.mk _ ⟨(x.2.val : ℤ), ((x.1 - x.2).val : ℤ)⟩ := by
  rw [RingEquiv.symm_apply_eq]
  ext <;> simp

/-- `QuadraticAlgebra ℤ a 1 ⧸ (2)` is a field exactly when `a` is odd: then `X² - X - 1` has no
root modulo `2`. -/
theorem isField_quotient_span_two_iff :
    IsField (QuadraticAlgebra ℤ a 1 ⧸ Ideal.span {(2 : QuadraticAlgebra ℤ a 1)}) ↔
      Odd a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := isMaximal_span_natCast_iff (a := a) (b := 1) (p := 2)
  simp only [Nat.cast_ofNat] at h2
  rw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, h2]
  refine ⟨fun h ↦ ?_, fun ha r hr ↦ ?_⟩
  · simpa [Int.odd_iff] using h 0
  · rw [← even_iff_two_dvd, show r ^ 2 - 1 * r - a = r * (r - 1) - a by ring,
      Int.even_sub] at hr
    exact Int.not_even_iff_odd.mpr ha (hr.mp (Int.even_mul_pred_self r))

/-- **The shape of `B/(2)` by `d mod 8`.** For `d = discr a 1 = 1 + 4a`,
`QuadraticAlgebra ℤ a 1 ⧸ (2)` is a field exactly when `d ≡ 5 (mod 8)`; otherwise
`d ≡ 1 (mod 8)` and it is `ℤ/2 × ℤ/2` (`quotientSpanTwoRingEquivProd`). -/
theorem isField_quotient_span_two_iff_discr_emod_eight :
    IsField (QuadraticAlgebra ℤ a 1 ⧸ Ideal.span {(2 : QuadraticAlgebra ℤ a 1)}) ↔
      discr a 1 % 8 = 5 := by
  rw [isField_quotient_span_two_iff, discr_def, Int.odd_iff]
  omega

/-- The split case of `quotientSpanTwoRingEquivProd`, read on `d = discr a 1 = 1 + 4a`: `a` is
even exactly when `d ≡ 1 (mod 8)`. -/
theorem even_iff_discr_emod_eight : Even a ↔ discr a 1 % 8 = 1 := by
  rw [discr_def, Int.even_iff]
  omega

end Int

/-! ### Checks: `d = 5`, `d = -3` and `d = 17` -/

section Checks

/-- `d = 5`: `ℤ[(1 + √5)/2]` is `QuadraticAlgebra ℤ 1 1`, of discriminant `5`, and `2ω - 1`
squares to `5`. -/
example : discr (1 : ℤ) 1 = 5 := by norm_num [discr_def]

example : (⟨-1, 2⟩ : QuadraticAlgebra ℤ 1 1) * ⟨-1, 2⟩ = 5 := by
  ext <;> norm_num

/-- `d = 5`, `m = 3`: the reduced comparison is an isomorphism, and `ℤ[√5]/(3)` is a field
since `5 ≡ 2` is not a square modulo `3`. -/
example : Function.Bijective
    (quotientRingHomOfDiscrZero 1 1 (d := 5) (e := 0) (by norm_num [discr_def]) rfl 3) :=
  (bijective_quotientRingHomOfDiscrZero_iff _ _).mpr (by decide)

example :
    IsField (QuadraticAlgebra ℤ 5 0 ⧸ Ideal.span {((3 : ℕ) : QuadraticAlgebra ℤ 5 0)}) := by
  have : Fact (∀ r : ZMod 3, r ^ 2 ≠ ((5 : ℤ) : ZMod 3) + ((0 : ℤ) : ZMod 3) * r) := ⟨by decide⟩
  exact (quotientSpanNatCastEquiv 5 0 3).toMulEquiv.isField_congr.mpr (Field.toIsField _)

/-- `d = 5`, `m = 2`: `B/(2)` is a field, `ℤ[√5]/(2)` is not reduced, and the reduced comparison
is not injective. This is the negative control for reading off the reduction type of the
presented order from that of the maximal order. -/
example : IsField (QuadraticAlgebra ℤ 1 1 ⧸ Ideal.span {(2 : QuadraticAlgebra ℤ 1 1)}) :=
  isField_quotient_span_two_iff.mpr odd_one

example :
    ¬IsReduced (QuadraticAlgebra ℤ 5 0 ⧸ Ideal.span {(2 : QuadraticAlgebra ℤ 5 0)}) :=
  not_isReduced_quotient_span_two (by decide) (by decide)

example : ¬Function.Injective
    (quotientRingHomOfDiscrZero 1 1 (d := 5) (e := 0) (by norm_num [discr_def]) rfl 2) :=
  not_injective_quotientRingHomOfDiscrZero_two _ _

/-- `d = -3`: the Eisenstein integers `QuadraticAlgebra ℤ (-1) 1` have discriminant `-3`, and
`2ω - 1` squares to `-3`. -/
example : discr (-1 : ℤ) 1 = -3 := by norm_num [discr_def]

example : (⟨-1, 2⟩ : QuadraticAlgebra ℤ (-1) 1) * ⟨-1, 2⟩ = -3 := by
  ext <;> norm_num

/-- `d = 17 ≡ 1 (mod 8)`: `B = QuadraticAlgebra ℤ 4 1` and `B/(2)` is `ℤ/2 × ℤ/2`. -/
example : Nonempty (QuadraticAlgebra ℤ 4 1 ⧸ Ideal.span {(2 : QuadraticAlgebra ℤ 4 1)} ≃+*
      ZMod 2 × ZMod 2) :=
  ⟨quotientSpanTwoRingEquivProd 4 (even_iff_discr_emod_eight.mpr (by norm_num [discr_def]))⟩

end Checks

end QuadraticAlgebra
