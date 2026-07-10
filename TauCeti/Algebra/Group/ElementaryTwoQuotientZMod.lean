/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import TauCeti.Algebra.Group.ElementaryTwoQuotientProd

/-!
# The elementary-2 quotient of `ZMod 2`

The genus-theory layer of the multiquadratic roadmap computes maximal elementary-2 quotients
`G/G^2` of finite abelian class groups. The product API in
`TauCeti.Algebra.Group.ElementaryTwoQuotientProd` reduces product computations to cyclic factors;
this file supplies the first cyclic factor needed by the worked examples, namely the multiplicative
group attached to the additive cyclic group `ZMod 2`.

For `Multiplicative (ZMod 2)`, every element is already killed by squaring, so the quotient by
squares is the group itself. We record this as a `ZMod 2`-linear equivalence and derive the
cardinality and 2-rank readings, including the finite product `ι -> Multiplicative (ZMod 2)`.

This is a prerequisite for the Layer 2 class-group quotient API and the Layer 3 examples in the
multiquadratic roadmap, where class groups such as `(ZMod 2)^2` have to be read as elementary-2
quotients of rank equal to the number of cyclic `ZMod 2` factors.
-/

public section

namespace TauCeti

/-- In `Multiplicative (ZMod 2)`, every element squares to `1`. -/
@[simp] theorem sq_multiplicative_zmod_two (g : Multiplicative (ZMod 2)) : g ^ 2 = 1 := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  exact CharTwo.add_self_eq_zero (Multiplicative.toAdd g)

/-- The maximal elementary-2 quotient of `Multiplicative (ZMod 2)` is additively equivalent to
`ZMod 2`: the doubling submodule is zero, so the quotient is the original additive group. -/
private noncomputable def elementaryTwoQuotientMultiplicativeZModTwoAddEquiv :
    ElementaryTwoQuotient (Multiplicative (ZMod 2)) ≃+ ZMod 2 :=
  (elementaryTwoQuotientAddEquivOfForallSqEqOne
    (Multiplicative (ZMod 2)) sq_multiplicative_zmod_two).trans
      (AddEquiv.additiveMultiplicative (ZMod 2))

private theorem elementaryTwoQuotientMultiplicativeZModTwoAddEquiv_mk
    (g : Multiplicative (ZMod 2)) :
    elementaryTwoQuotientMultiplicativeZModTwoAddEquiv (elementaryTwoQuotientMk g) =
      Multiplicative.toAdd g := by
  simp [elementaryTwoQuotientMultiplicativeZModTwoAddEquiv]

/-- The maximal elementary-2 quotient of `Multiplicative (ZMod 2)` is the one-dimensional
`ZMod 2`-vector space `ZMod 2`. -/
noncomputable def elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv :
    ElementaryTwoQuotient (Multiplicative (ZMod 2)) ≃ₗ[ZMod 2] ZMod 2 where
  __ := elementaryTwoQuotientMultiplicativeZModTwoAddEquiv
  map_smul' c x := ZMod.map_smul elementaryTwoQuotientMultiplicativeZModTwoAddEquiv c x

private theorem elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv_apply
    (x : ElementaryTwoQuotient (Multiplicative (ZMod 2))) :
    elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv x =
      elementaryTwoQuotientMultiplicativeZModTwoAddEquiv x := rfl

/-- The equivalence `G/G^2` with `ZMod 2` sends the class of `g` to the underlying element of
`ZMod 2`. -/
@[simp] theorem elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv_mk
    (g : Multiplicative (ZMod 2)) :
    elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv (elementaryTwoQuotientMk g) =
      Multiplicative.toAdd g := by
  rw [elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv_apply,
    elementaryTwoQuotientMultiplicativeZModTwoAddEquiv_mk]

/-- The inverse equivalence sends an element of `ZMod 2` to its class in the elementary-2
quotient of the corresponding multiplicative element. -/
@[simp] theorem elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv_symm_apply
    (z : ZMod 2) :
    (elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv).symm z =
      elementaryTwoQuotientMk (Multiplicative.ofAdd z) := by
  rw [LinearEquiv.symm_apply_eq, elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv_mk,
    toAdd_ofAdd]

/-- The elementary-2 quotient of `Multiplicative (ZMod 2)` has fintype cardinality `2`. -/
@[simp] theorem fintype_card_elementaryTwoQuotient_multiplicative_zmod_two :
    Fintype.card (ElementaryTwoQuotient (Multiplicative (ZMod 2))) = 2 := by
  rw [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv.toEquiv, Nat.card_zmod]

/-- The elementary-2 quotient of `Multiplicative (ZMod 2)` has cardinality `2`. -/
theorem card_elementaryTwoQuotient_multiplicative_zmod_two :
    Nat.card (ElementaryTwoQuotient (Multiplicative (ZMod 2))) = 2 := by
  simpa only [Nat.card_eq_fintype_card]
    using fintype_card_elementaryTwoQuotient_multiplicative_zmod_two

/-- The elementary-2 quotient of the multiplicative cyclic group of order two has dimension `1`. -/
@[simp] theorem finrank_elementaryTwoQuotient_multiplicative_zmod_two :
    Module.finrank (ZMod 2) (ElementaryTwoQuotient (Multiplicative (ZMod 2))) = 1 := by
  rw [elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv.finrank_eq]
  norm_num

/-- The multiplicative cyclic group of order two has 2-rank `1`. -/
theorem twoRank_multiplicative_zmod_two : twoRank (Multiplicative (ZMod 2)) = 1 := by
  simpa only [twoRank_def] using finrank_elementaryTwoQuotient_multiplicative_zmod_two

/-- A finite product of copies of the multiplicative cyclic group of order two has 2-rank equal
to the number of factors. -/
@[simp] theorem finrank_elementaryTwoQuotient_pi_multiplicative_zmod_two {ι : Type*} [Fintype ι] :
    Module.finrank (ZMod 2) (ElementaryTwoQuotient (ι → Multiplicative (ZMod 2))) =
      Fintype.card ι := by
  have h := twoRank_pi (G := fun _ : ι => Multiplicative (ZMod 2))
  simp only [twoRank_def, finrank_elementaryTwoQuotient_multiplicative_zmod_two,
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at h
  exact h

/-- A finite product of copies of the multiplicative cyclic group of order two has 2-rank equal
to the number of factors. -/
theorem twoRank_pi_multiplicative_zmod_two {ι : Type*} [Fintype ι] :
    twoRank (ι → Multiplicative (ZMod 2)) = Fintype.card ι := by
  simpa only [twoRank_def] using finrank_elementaryTwoQuotient_pi_multiplicative_zmod_two

/-- The elementary-2 quotient of a finite product of copies of `Multiplicative (ZMod 2)` has
cardinality `2 ^ |ι|`. -/
@[simp] theorem card_elementaryTwoQuotient_pi_multiplicative_zmod_two {ι : Type*} [Fintype ι] :
    Nat.card (ElementaryTwoQuotient (ι → Multiplicative (ZMod 2))) = 2 ^ Fintype.card ι := by
  rw [card_elementaryTwoQuotient_pi]
  rw [card_elementaryTwoQuotient_multiplicative_zmod_two]
  simp [Finset.prod_const]

/-- The natural multiplicative tag on `(ZMod 2)^ι` has 2-rank equal to the number of factors. -/
@[simp] theorem finrank_elementaryTwoQuotient_multiplicative_pi_zmod_two {ι : Type*}
    [Fintype ι] :
    Module.finrank (ZMod 2) (ElementaryTwoQuotient (Multiplicative (ι → ZMod 2))) =
      Fintype.card ι := by
  rw [finrank_elementaryTwoQuotient_eq_of_mulEquiv
    (G := Multiplicative (ι → ZMod 2)) (H := ι → Multiplicative (ZMod 2))
    (MulEquiv.funMultiplicative ι (ZMod 2))]
  exact finrank_elementaryTwoQuotient_pi_multiplicative_zmod_two

/-- The natural multiplicative tag on `(ZMod 2)^ι` has 2-rank equal to the number of factors. -/
theorem twoRank_multiplicative_pi_zmod_two {ι : Type*} [Fintype ι] :
    twoRank (Multiplicative (ι → ZMod 2)) = Fintype.card ι := by
  simpa only [twoRank_def] using finrank_elementaryTwoQuotient_multiplicative_pi_zmod_two

/-- The elementary-2 quotient of the natural multiplicative tag on `(ZMod 2)^ι` has cardinality
`2 ^ |ι|`. -/
@[simp] theorem card_elementaryTwoQuotient_multiplicative_pi_zmod_two {ι : Type*} [Fintype ι] :
    Nat.card (ElementaryTwoQuotient (Multiplicative (ι → ZMod 2))) = 2 ^ Fintype.card ι := by
  rw [card_elementaryTwoQuotient_eq_two_pow_twoRank]
  rw [twoRank_multiplicative_pi_zmod_two]

end TauCeti
