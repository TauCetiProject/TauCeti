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

/-- The doubling submodule of `Additive (Multiplicative (ZMod 2))` is zero. This is the
`ModN` model's version of the fact that every element of `Multiplicative (ZMod 2)` has square
`1`. -/
private theorem range_lsmul_two_additive_multiplicative_zmod_two_eq_bot :
    LinearMap.range
        (LinearMap.lsmul ℤ (Additive (Multiplicative (ZMod 2))) ((2 : ℕ) : ℤ)) = ⊥ := by
  ext x
  simp only [LinearMap.mem_range, Submodule.mem_bot]
  constructor
  · rintro ⟨y, rfl⟩
    exact by
      simpa using (show (2 : ℤ) • y = 0 by
        cases y with
        | ofMul g =>
          apply Additive.toMul.injective
          simp only [toMul_zsmul]
          exact sq_multiplicative_zmod_two g)
  · intro hx
    exact ⟨0, by simp [hx]⟩

/-- The additive subgroup underlying the doubling submodule of
`Additive (Multiplicative (ZMod 2))` is zero. -/
theorem range_lsmul_two_additive_multiplicative_zmod_two_toAddSubgroup_eq_bot :
    (LinearMap.range
      (LinearMap.lsmul ℤ (Additive (Multiplicative (ZMod 2))) ((2 : ℕ) : ℤ))).toAddSubgroup =
        ⊥ := by
  rw [range_lsmul_two_additive_multiplicative_zmod_two_eq_bot]
  rfl

/-- The maximal elementary-2 quotient of `Multiplicative (ZMod 2)` is additively equivalent to
`ZMod 2`: the doubling submodule is zero, so the quotient is the original additive group. -/
@[expose] noncomputable def elementaryTwoQuotientMultiplicativeZModTwoAddEquiv :
    ElementaryTwoQuotient (Multiplicative (ZMod 2)) ≃+ ZMod 2 :=
  ((QuotientAddGroup.quotientAddEquivOfEq
    range_lsmul_two_additive_multiplicative_zmod_two_toAddSubgroup_eq_bot).trans
      (QuotientAddGroup.quotientBot :
        Additive (Multiplicative (ZMod 2)) ⧸
          (⊥ : AddSubgroup (Additive (Multiplicative (ZMod 2)))) ≃+
            Additive (Multiplicative (ZMod 2)))).trans
              (AddEquiv.additiveMultiplicative (ZMod 2))

/-- The maximal elementary-2 quotient of `Multiplicative (ZMod 2)` is the one-dimensional
`ZMod 2`-vector space `ZMod 2`. -/
@[expose] noncomputable def elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv :
    ElementaryTwoQuotient (Multiplicative (ZMod 2)) ≃ₗ[ZMod 2] ZMod 2 where
  __ := elementaryTwoQuotientMultiplicativeZModTwoAddEquiv
  map_smul' c x := ZMod.map_smul elementaryTwoQuotientMultiplicativeZModTwoAddEquiv c x

/-- The equivalence `G/G^2` with `ZMod 2` sends the class of `g` to the underlying element of
`ZMod 2`. -/
@[simp] theorem elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv_mk
    (g : Multiplicative (ZMod 2)) :
    elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv (elementaryTwoQuotientMk g) =
      Multiplicative.toAdd g := by
  rw [elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv]
  change elementaryTwoQuotientMultiplicativeZModTwoAddEquiv (elementaryTwoQuotientMk g) =
    Multiplicative.toAdd g
  rw [elementaryTwoQuotientMultiplicativeZModTwoAddEquiv, elementaryTwoQuotientMk_eq_mkQ]
  change (AddEquiv.additiveMultiplicative (ZMod 2))
    ((QuotientAddGroup.quotientBot :
      Additive (Multiplicative (ZMod 2)) ⧸
        (⊥ : AddSubgroup (Additive (Multiplicative (ZMod 2)))) ≃+
          Additive (Multiplicative (ZMod 2)))
      ((QuotientAddGroup.quotientAddEquivOfEq
        range_lsmul_two_additive_multiplicative_zmod_two_toAddSubgroup_eq_bot)
          (Submodule.Quotient.mk (Additive.ofMul g)))) = Multiplicative.toAdd g
  rfl

/-- The elementary-2 quotient of `Multiplicative (ZMod 2)` has cardinality `2`. -/
theorem card_elementaryTwoQuotient_multiplicative_zmod_two :
    Nat.card (ElementaryTwoQuotient (Multiplicative (ZMod 2))) = 2 := by
  rw [Nat.card_congr elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv.toEquiv, Nat.card_zmod]

/-- The multiplicative cyclic group of order two has 2-rank `1`. -/
theorem twoRank_multiplicative_zmod_two : twoRank (Multiplicative (ZMod 2)) = 1 := by
  rw [twoRank_def, elementaryTwoQuotientMultiplicativeZModTwoLinearEquiv.finrank_eq]
  norm_num

/-- A finite product of copies of the multiplicative cyclic group of order two has 2-rank equal
to the number of factors. -/
theorem twoRank_pi_multiplicative_zmod_two {ι : Type*} [Fintype ι] :
    twoRank (ι → Multiplicative (ZMod 2)) = Fintype.card ι := by
  rw [twoRank_pi]
  simp only [twoRank_multiplicative_zmod_two, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_univ]
  norm_num

/-- The elementary-2 quotient of a finite product of copies of `Multiplicative (ZMod 2)` has
cardinality `2 ^ |ι|`. -/
theorem card_elementaryTwoQuotient_pi_multiplicative_zmod_two {ι : Type*} [Fintype ι] :
    Nat.card (ElementaryTwoQuotient (ι → Multiplicative (ZMod 2))) = 2 ^ Fintype.card ι := by
  rw [card_elementaryTwoQuotient_pi]
  rw [card_elementaryTwoQuotient_multiplicative_zmod_two]
  simp [Finset.prod_const]

end TauCeti
