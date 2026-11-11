/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.QuadraticAlgebra.DualNumber
public import TauCeti.Algebra.QuadraticAlgebra.Split
public import TauCeti.NumberTheory.QuadraticOrder.Reduction

/-!
# The index-two comparison of quadratic orders

For a quadratic algebra `B = QuadraticAlgebra R a b` of discriminant `d = b² + 4a`, the element
`2ω - b` of `B` squares to `d`, so `ω ↦ 2ω - b` defines an `R`-algebra map
`ι : QuadraticAlgebra R d 0 → B` (`QuadraticAlgebra.algHomDiscrZero`). When `2` is invertible it
is the inverse of Mathlib's `algEquivDiscrZero`; in general it sends `x + yω` to
`(x - by) + 2yω`, so it is injective exactly when `2` is regular, bijective exactly when `2` is a
unit, and its image is `{x + yω | 2 ∣ y}`. It commutes with conjugation, norm, trace and every
change of coefficients.

Over `ℤ`, with `d ≡ 1 (mod 4)`, `a = (d - 1)/4` and `b = 1`, this is the inclusion of
`ℤ[√d]` into `ℤ[(1 + √d)/2]`, of index two. Modulo a natural number `m`, `ι` induces a ring map
`ℤ[√d]/(m) → B/(m)` which is bijective exactly when `m` is odd. At `m = 2` it fails: the
quotient `ℤ[√d]/(2)` is the ring of dual numbers over `ℤ/2`, while `B/(2)` is the field with four
elements when `d ≡ 5 (mod 8)` and `ℤ/2 × ℤ/2` when `d ≡ 1 (mod 8)`.

The source parameter `e` of `QuadraticAlgebra R d e` carries a hypothesis `e = 0` rather than
being the literal `0`, so that the map can be formed after a change of coefficients, where the
reduced parameter `f 0` is not syntactically `0`.

## Main definitions

* `QuadraticAlgebra.algHomDiscrZero`: the algebra map `QuadraticAlgebra R (discr a b) 0 → B`
  sending `ω` to `2ω - b`.
* `QuadraticAlgebra.quotientAlgHomDiscrZero`: over `ℤ`, the induced map
  `QuadraticAlgebra ℤ d e ⧸ (m) →+* QuadraticAlgebra ℤ a b ⧸ (m)`.

## Main results

* `QuadraticAlgebra.mem_range_algHomDiscrZero_iff`: the image of `ι` is `{z | 2 ∣ z.im}`, and
  `QuadraticAlgebra.index_range_algHomDiscrZero`: over `ℤ` it has index two.
* `QuadraticAlgebra.star_algHomDiscrZero`, `norm_algHomDiscrZero`, `trace_algHomDiscrZero`,
  `mapRingHom_algHomDiscrZero`: compatibility with conjugation, norm, trace and coefficients.
* `QuadraticAlgebra.bijective_quotientAlgHomDiscrZero_iff`: the reduced map modulo `m` is
  bijective exactly when `m` is odd; `quotientRingEquivDiscrZero` is the isomorphism.
* `QuadraticAlgebra.not_injective_quotientAlgHomDiscrZero_two`,
  `not_surjective_quotientAlgHomDiscrZero_two`: at `m = 2` it is neither.
* `QuadraticAlgebra.quotientSpanTwoEquivDualNumber`, `not_isReduced_quotient_span_two`: for odd
  `d` and even `e`, `ℤ[√d]/(2)` is the ring of dual numbers over `ℤ/2`.
* `QuadraticAlgebra.isField_quotient_span_two_iff_discr_emod_eight`,
  `quotientSpanTwoRingEquivProd`: the shape of `QuadraticAlgebra ℤ a 1 ⧸ (2)` by `d mod 8`.

## References

* J. S. Milne, *Algebraic Number Theory*, Example 2.41, for the integral basis
  `1, (1 + √d)/2` of `ℚ(√d)` when `d` is squarefree and `d ≡ 1 (mod 4)`.
-/

public section

namespace QuadraticAlgebra

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] {a b d e : R}

variable (a b) in
/-- **The index-two comparison.** For `d = discr a b = b² + 4a` and `e = 0`, the `R`-algebra
map `QuadraticAlgebra R d e → QuadraticAlgebra R a b` sending `ω` to `2ω - b`, the change of
generator with `u = 2` and `k = -b`. -/
def algHomDiscrZero (hd : d = discr a b) (he : e = 0) :
    QuadraticAlgebra R d e →ₐ[R] QuadraticAlgebra R a b :=
  changeGenerator a b 2 (-b) (by rw [hd, discr_def]; ring) (by rw [he]; ring)

@[simp]
theorem re_algHomDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    (algHomDiscrZero a b hd he z).re = z.re - b * z.im := by
  simp [algHomDiscrZero]
  ring

@[simp]
theorem im_algHomDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    (algHomDiscrZero a b hd he z).im = 2 * z.im := by
  simp [algHomDiscrZero, mul_comm]

/-- `algHomDiscrZero` sends `ω` to `2ω - b`, whose square is `discr a b`. -/
theorem algHomDiscrZero_omega (hd : d = discr a b) (he : e = 0) :
    algHomDiscrZero a b hd he ω = ⟨-b, 2⟩ := by
  ext <;> simp

/-- When `2` is invertible, `algHomDiscrZero` is the inverse of Mathlib's `algEquivDiscrZero`. -/
theorem algHomDiscrZero_eq_algEquivDiscrZero_symm [Invertible (2 : R)] :
    algHomDiscrZero a b rfl rfl = ((algEquivDiscrZero a b).symm : _ →ₐ[R] _) :=
  algHom_ext (by ext <;> simp)

/-- `algHomDiscrZero` is injective exactly when `2` is regular in `R`. -/
theorem injective_algHomDiscrZero_iff (hd : d = discr a b) (he : e = 0) :
    Function.Injective (algHomDiscrZero a b hd he) ↔ IsRegular (2 : R) := by
  rw [← isRegular_im_omega_iff_injective, im_algHomDiscrZero, im_omega, mul_one]

/-- `algHomDiscrZero` is bijective exactly when `2` is a unit in `R`. -/
theorem bijective_algHomDiscrZero_iff (hd : d = discr a b) (he : e = 0) :
    Function.Bijective (algHomDiscrZero a b hd he) ↔ IsUnit (2 : R) := by
  rw [← isUnit_im_omega_iff_bijective, im_algHomDiscrZero, im_omega, mul_one]

/-- **The image of the index-two comparison.** An element of `QuadraticAlgebra R a b` lies in
the image of `algHomDiscrZero` exactly when `2` divides its `ω`-coordinate. -/
theorem mem_range_algHomDiscrZero_iff (hd : d = discr a b) (he : e = 0)
    {z : QuadraticAlgebra R a b} :
    z ∈ (algHomDiscrZero a b hd he).range ↔ 2 ∣ z.im := by
  refine ⟨?_, fun ⟨y, hy⟩ ↦ ⟨⟨z.re + b * y, y⟩, ?_⟩⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.im, im_algHomDiscrZero hd he w⟩
  · ext <;> simp [hy]

/-- `algHomDiscrZero` commutes with conjugation. -/
theorem star_algHomDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    algHomDiscrZero a b hd he (star z) = star (algHomDiscrZero a b hd he z) := by
  subst he
  ext <;> simp
  ring

/-- `algHomDiscrZero` preserves norms. -/
theorem norm_algHomDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    norm (algHomDiscrZero a b hd he z) = norm z := by
  subst hd he
  simp [norm_def, discr_def]
  ring

/-- `algHomDiscrZero` preserves traces. -/
theorem trace_algHomDiscrZero (hd : d = discr a b) (he : e = 0) (z : QuadraticAlgebra R d e) :
    trace (algHomDiscrZero a b hd he z) = trace z := by
  subst he
  simp [trace_def]
  ring

/-- **Compatibility with a change of coefficients.** For a ring map `f : R →+* S`,
`algHomDiscrZero` commutes with the coefficientwise maps `mapRingHom f`. -/
theorem mapRingHom_algHomDiscrZero (f : R →+* S) (hd : d = discr a b) (he : e = 0)
    (z : QuadraticAlgebra R d e) :
    mapRingHom f a b (algHomDiscrZero a b hd he z) =
      algHomDiscrZero (f a) (f b) (by rw [hd, discr_def, discr_def]; simp [map_ofNat])
        (by rw [he, map_zero]) (mapRingHom f d e z) := by
  ext <;> simp [map_ofNat]

end CommRing

section Int

variable {a b d e : ℤ}

/-- Over `ℤ` the index-two comparison is injective. -/
theorem algHomDiscrZero_injective (hd : d = discr a b) (he : e = 0) :
    Function.Injective (algHomDiscrZero a b hd he) :=
  (injective_algHomDiscrZero_iff hd he).mpr (IsRegular.of_ne_zero two_ne_zero)

/-- Over `ℤ` the image of the index-two comparison is `{x + yω | y even}`. -/
theorem mem_range_algHomDiscrZero_iff_even (hd : d = discr a b) (he : e = 0)
    {z : QuadraticAlgebra ℤ a b} :
    z ∈ (algHomDiscrZero a b hd he).range ↔ Even z.im := by
  rw [mem_range_algHomDiscrZero_iff, even_iff_two_dvd]

/-- **Index two.** Over `ℤ` the image of the index-two comparison is an additive subgroup of
index two. -/
theorem index_range_algHomDiscrZero (hd : d = discr a b) (he : e = 0) :
    (algHomDiscrZero a b hd he).range.toSubring.toAddSubgroup.index = 2 := by
  refine AddSubgroup.index_eq_two_iff.mpr ⟨ω, fun z ↦ ?_⟩
  simp only [Subring.mem_toAddSubgroup, Subalgebra.mem_toSubring,
    mem_range_algHomDiscrZero_iff_even, im_add, im_omega, Int.even_add_one]
  by_cases h : Even z.im <;> simp [h]

variable (a b) in
/-- **The index-two comparison modulo `m`.** The ring map
`QuadraticAlgebra ℤ d e ⧸ (m) → QuadraticAlgebra ℤ a b ⧸ (m)` induced by `algHomDiscrZero`. -/
def quotientAlgHomDiscrZero (hd : d = discr a b) (he : e = 0) (m : ℕ) :
    QuadraticAlgebra ℤ d e ⧸ Ideal.span {(m : QuadraticAlgebra ℤ d e)} →+*
      QuadraticAlgebra ℤ a b ⧸ Ideal.span {(m : QuadraticAlgebra ℤ a b)} :=
  Ideal.quotientMap _ (algHomDiscrZero a b hd he).toRingHom <| Ideal.span_le.mpr <|
    Set.singleton_subset_iff.mpr <| by simp

@[simp]
theorem quotientAlgHomDiscrZero_mk (hd : d = discr a b) (he : e = 0) (m : ℕ)
    (z : QuadraticAlgebra ℤ d e) :
    quotientAlgHomDiscrZero a b hd he m (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (algHomDiscrZero a b hd he z) :=
  Ideal.quotientMap_mk

/-- Under the identifications `quotientSpanNatCastEquiv` of both quotients with quadratic
algebras over `ℤ/m`, the reduced comparison is the comparison over `ℤ/m`. -/
theorem quotientSpanNatCastEquiv_quotientAlgHomDiscrZero (hd : d = discr a b) (he : e = 0)
    (m : ℕ) (x : QuadraticAlgebra ℤ d e ⧸ Ideal.span {(m : QuadraticAlgebra ℤ d e)}) :
    quotientSpanNatCastEquiv a b m (quotientAlgHomDiscrZero a b hd he m x) =
      algHomDiscrZero (a : ZMod m) (b : ZMod m) (by rw [hd, discr_def, discr_def]; push_cast; rfl)
        (by rw [he, Int.cast_zero]) (quotientSpanNatCastEquiv d e m x) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  ext <;> simp

/-- **The reduced comparison is an isomorphism exactly for odd `m`.** The map
`QuadraticAlgebra ℤ d e ⧸ (m) → QuadraticAlgebra ℤ a b ⧸ (m)` induced by the index-two
comparison is bijective exactly when `m` is odd. -/
theorem bijective_quotientAlgHomDiscrZero_iff (hd : d = discr a b) (he : e = 0) {m : ℕ} :
    Function.Bijective (quotientAlgHomDiscrZero a b hd he m) ↔ Odd m := by
  have h : ⇑(quotientAlgHomDiscrZero a b hd he m) = (quotientSpanNatCastEquiv a b m).symm ∘
      algHomDiscrZero (a : ZMod m) (b : ZMod m) (by rw [hd, discr_def, discr_def]; push_cast; rfl)
        (by rw [he, Int.cast_zero]) ∘ quotientSpanNatCastEquiv d e m := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, RingEquiv.eq_symm_apply,
      quotientSpanNatCastEquiv_quotientAlgHomDiscrZero]
  rw [h, EquivLike.comp_bijective, EquivLike.bijective_comp, bijective_algHomDiscrZero_iff,
    ← Nat.cast_ofNat, ZMod.isUnit_iff_coprime, Nat.coprime_two_left]

variable (a b) in
/-- For odd `m`, the index-two comparison induces a ring isomorphism
`QuadraticAlgebra ℤ d e ⧸ (m) ≃+* QuadraticAlgebra ℤ a b ⧸ (m)`. -/
noncomputable def quotientRingEquivDiscrZero (hd : d = discr a b) (he : e = 0) {m : ℕ}
    (hm : Odd m) :
    QuadraticAlgebra ℤ d e ⧸ Ideal.span {(m : QuadraticAlgebra ℤ d e)} ≃+*
      QuadraticAlgebra ℤ a b ⧸ Ideal.span {(m : QuadraticAlgebra ℤ a b)} :=
  RingEquiv.ofBijective _ ((bijective_quotientAlgHomDiscrZero_iff hd he).mpr hm)

@[simp]
theorem quotientRingEquivDiscrZero_apply (hd : d = discr a b) (he : e = 0) {m : ℕ}
    (hm : Odd m) (x : QuadraticAlgebra ℤ d e ⧸ Ideal.span {(m : QuadraticAlgebra ℤ d e)}) :
    quotientRingEquivDiscrZero a b hd he hm x = quotientAlgHomDiscrZero a b hd he m x :=
  RingEquiv.ofBijective_apply _ _ _

/-- At `m = 2` the class of `b + ω` is a nonzero element of the kernel of the reduced
comparison: `algHomDiscrZero` sends `b + ω` to `2ω`. -/
theorem quotientAlgHomDiscrZero_two_mk (hd : d = discr a b) (he : e = 0) :
    quotientAlgHomDiscrZero a b hd he 2 (Ideal.Quotient.mk _ ⟨b, 1⟩) = 0 ∧
      Ideal.Quotient.mk (Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ d e)}) ⟨b, 1⟩ ≠ 0 := by
  rw [quotientAlgHomDiscrZero_mk, Ideal.Quotient.eq_zero_iff_mem, Ne,
    Ideal.Quotient.eq_zero_iff_mem, mem_span_natCast_iff, mem_span_natCast_iff]
  simp

/-- At `m = 2` the reduced comparison is not injective. -/
theorem not_injective_quotientAlgHomDiscrZero_two (hd : d = discr a b) (he : e = 0) :
    ¬Function.Injective (quotientAlgHomDiscrZero a b hd he 2) := fun h ↦
  (quotientAlgHomDiscrZero_two_mk hd he).2 <|
    (injective_iff_map_eq_zero _).mp h _ (quotientAlgHomDiscrZero_two_mk hd he).1

/-- At `m = 2` the reduced comparison is not surjective, both quotients having four
elements. -/
theorem not_surjective_quotientAlgHomDiscrZero_two (hd : d = discr a b) (he : e = 0) :
    ¬Function.Surjective (quotientAlgHomDiscrZero a b hd he 2) := fun h ↦
  not_injective_quotientAlgHomDiscrZero_two hd he <|
    (h.bijective_of_nat_card_le
      (by rw [card_quotient_span_natCast, card_quotient_span_natCast])).1

variable (d e) in
/-- **`ℤ[√d]/(2)` has a repeated root.** For `d` odd and `e` even,
`QuadraticAlgebra ℤ d e ⧸ (2)` is the ring of dual numbers over `ℤ/2`, with `ω ↦ 1 + ε`. -/
noncomputable def quotientSpanTwoEquivDualNumber (hd : Odd d) (he : Even e) :
    QuadraticAlgebra ℤ d e ⧸ Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ d e)} ≃+*
      DualNumber (ZMod 2) :=
  (quotientSpanNatCastEquiv d e 2).trans
    (algEquivDualNumberOfDoubleRoot 1 (by
      rw [← sub_eq_zero, sub_neg_eq_add, one_pow, ← Int.cast_one, ← Int.cast_add,
        ZMod.intCast_eq_zero_iff_even]
      exact hd.add_one) (by
      rw [mul_one, ZMod.intCast_eq_zero_iff_even.mpr he]; rfl)).toRingEquiv

/-- For `d` odd and `e` even, `QuadraticAlgebra ℤ d e ⧸ (2)` is not reduced. -/
theorem not_isReduced_quotient_span_two (hd : Odd d) (he : Even e) :
    ¬IsReduced (QuadraticAlgebra ℤ d e ⧸ Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ d e)}) :=
  fun _ ↦ DualNumber.not_isReduced <| isReduced_of_injective
    (quotientSpanTwoEquivDualNumber d e hd he).symm (RingEquiv.injective _)

variable (a) in
/-- For `a` even, `QuadraticAlgebra ℤ a 1 ⧸ (2)` is `ℤ/2 × ℤ/2`, by evaluation at the roots
`1` and `0` of `X² - X`. -/
noncomputable def quotientSpanTwoRingEquivProd (ha : Even a) :
    QuadraticAlgebra ℤ a 1 ⧸ Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ a 1)} ≃+*
      ZMod 2 × ZMod 2 :=
  (quotientSpanNatCastEquiv a 1 2).trans
    (algEquivProdOfRoots 1 0 (by simp)
      (by rw [mul_zero, neg_zero, ZMod.intCast_eq_zero_iff_even]; exact ha) (by simp)).toRingEquiv

/-- `QuadraticAlgebra ℤ a 1 ⧸ (2)` is a field exactly when `a` is odd: then `X² - X - 1` has no
root modulo `2`. -/
theorem isField_quotient_span_two_iff :
    IsField (QuadraticAlgebra ℤ a 1 ⧸ Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ a 1)}) ↔
      Odd a := by
  rcases Int.even_or_odd a with ha | ha
  · refine iff_of_false (fun h ↦ ?_) (Int.not_odd_iff_even.mpr ha)
    obtain ⟨x, hx⟩ := ((quotientSpanTwoRingEquivProd a ha).toMulEquiv.isField_congr.mp
      h).mul_inv_cancel (a := ((1, 0) : ZMod 2 × ZMod 2)) (by simp)
    simpa using congr($hx.2)
  · refine iff_of_true ?_ ha
    have : Fact (∀ r : ZMod 2, r ^ 2 ≠ (a : ZMod 2) + ((1 : ℤ) : ZMod 2) * r) :=
      ⟨by rw [ZMod.intCast_eq_one_iff_odd.mpr ha, Int.cast_one]; decide⟩
    exact (quotientSpanNatCastEquiv a 1 2).toMulEquiv.isField_congr.mpr (Field.toIsField _)

/-- **The shape of `B/(2)` by `d mod 8`.** For `d = discr a 1 = 1 + 4a`,
`QuadraticAlgebra ℤ a 1 ⧸ (2)` is a field exactly when `d ≡ 5 (mod 8)`; otherwise
`d ≡ 1 (mod 8)` and it is `ℤ/2 × ℤ/2` (`quotientSpanTwoRingEquivProd`). -/
theorem isField_quotient_span_two_iff_discr_emod_eight :
    IsField (QuadraticAlgebra ℤ a 1 ⧸ Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ a 1)}) ↔
      discr a 1 % 8 = 5 := by
  rw [isField_quotient_span_two_iff, discr_def, Int.odd_iff]
  omega

/-- The split case of `quotientSpanTwoRingEquivProd`, read on `d = discr a 1 = 1 + 4a`: `a` is
even exactly when `d ≡ 1 (mod 8)`. -/
theorem even_iff_discr_emod_eight : Even a ↔ discr a 1 % 8 = 1 := by
  rw [discr_def, Int.even_iff]
  omega

end Int

/-! ### Checks: `d = 5` and `d = -3` -/

section Checks

/-- `d = 5`: `ℤ[(1 + √5)/2]` is `QuadraticAlgebra ℤ 1 1`, of discriminant `5`, and `2ω - 1`
squares to `5`. -/
example : discr (1 : ℤ) 1 = 5 := by norm_num [discr_def]

example : (⟨-1, 2⟩ : QuadraticAlgebra ℤ 1 1) * ⟨-1, 2⟩ = 5 := by
  ext <;> norm_num

/-- `d = 5`, `m = 3`: the reduced comparison is an isomorphism, and `ℤ[√5]/(3)` is a field
since `5 ≡ 2` is not a square modulo `3`. -/
example : Function.Bijective
    (quotientAlgHomDiscrZero 1 1 (d := 5) (e := 0) (by norm_num [discr_def]) rfl 3) :=
  (bijective_quotientAlgHomDiscrZero_iff _ _).mpr (by decide)

example :
    IsField (QuadraticAlgebra ℤ 5 0 ⧸ Ideal.span {((3 : ℕ) : QuadraticAlgebra ℤ 5 0)}) := by
  have : Fact (∀ r : ZMod 3, r ^ 2 ≠ ((5 : ℤ) : ZMod 3) + ((0 : ℤ) : ZMod 3) * r) := ⟨by decide⟩
  exact (quotientSpanNatCastEquiv 5 0 3).toMulEquiv.isField_congr.mpr (Field.toIsField _)

/-- `d = 5`, `m = 2`: `B/(2)` is a field, `ℤ[√5]/(2)` is not reduced, and the reduced comparison
is not injective. This is the negative control for reading off the reduction type of the
presented order from that of the maximal order. -/
example : IsField (QuadraticAlgebra ℤ 1 1 ⧸ Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ 1 1)}) :=
  isField_quotient_span_two_iff.mpr odd_one

example :
    ¬IsReduced (QuadraticAlgebra ℤ 5 0 ⧸ Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ 5 0)}) :=
  not_isReduced_quotient_span_two (by decide) (by decide)

example : ¬Function.Injective
    (quotientAlgHomDiscrZero 1 1 (d := 5) (e := 0) (by norm_num [discr_def]) rfl 2) :=
  not_injective_quotientAlgHomDiscrZero_two _ _

/-- `d = -3`: the Eisenstein integers `QuadraticAlgebra ℤ (-1) 1` have discriminant `-3`, and
`2ω - 1` squares to `-3`. -/
example : discr (-1 : ℤ) 1 = -3 := by norm_num [discr_def]

example : (⟨-1, 2⟩ : QuadraticAlgebra ℤ (-1) 1) * ⟨-1, 2⟩ = -3 := by
  ext <;> norm_num

/-- `d = 17 ≡ 1 (mod 8)`: `B = QuadraticAlgebra ℤ 4 1` and `B/(2)` is `ℤ/2 × ℤ/2`. -/
example : Nonempty (QuadraticAlgebra ℤ 4 1 ⧸ Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ 4 1)} ≃+*
      ZMod 2 × ZMod 2) :=
  ⟨quotientSpanTwoRingEquivProd 4 (even_iff_discr_emod_eight.mpr (by norm_num [discr_def]))⟩

end Checks

end QuadraticAlgebra
