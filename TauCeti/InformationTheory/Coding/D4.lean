/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.FieldTheory.Finite.Four
public import TauCeti.InformationTheory.Coding.Basic
public import TauCeti.InformationTheory.Hamming
public import TauCeti.LinearAlgebra.FiniteBilinearModule.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Basic

import Mathlib.Tactic.LinearCombination

/-!
# Quaternary codes in the `D₄` discriminant alphabet

The discriminant quadratic module of the `D₄` root lattice is the Klein four-group whose three
nonzero classes — the vector class and the two spinor classes — all have half-norm value `1 / 2`.
Additively this is a field `F₄` of four elements, identified by sending `1` to the vector class
and the two roots `ω, ω²` of `X² + X + 1` to the spinor and cospinor classes. In these
coordinates the half-norm quadratic value and its polar pairing are

```text
q(x) = 1 / 2 for x ≠ 0,    b(x, y) = Tr_{F₄/F₂}(x y²) / 2    in ℚ/ℤ.
```

Neither formula depends on the choice of `ω`. On a coordinate power the quadratic value of a
quaternary word is its Hamming weight divided by two, and the pairing of two words is
`Tr(∑ᵢ xᵢ yᵢ²) / 2`.

This file constructs this quaternary alphabet as a finite quadratic module and identifies it with
the actual discriminant module of `D₄` (the checkerboard lattice of rank four). The hexacode
application is in `TauCeti.InformationTheory.Coding.Hexacode.D4`.

## Main declarations

* `TauCeti.typeD4QuaternaryQuadraticModule`: a field of four elements with quadratic value `1 / 2`
  at every nonzero element.
* `TauCeti.typeD4QuaternaryQuadraticModule_pairing`: its polar pairing is `Tr(x y²) / 2`.
* `TauCeti.typeD4QuaternaryDiscriminantQuadraticIsometry`: its isometry onto the discriminant
  quadratic module of `D₄`, sending `1, ω, ω²` to the vector, spinor and cospinor classes.
* `TauCeti.coordinatePower_typeD4QuaternaryQuadraticModule_quadratic` and
  `TauCeti.coordinatePower_typeD4QuaternaryQuadraticModule_pairing`: the coordinate formulas
  `q(x) = wt(x) / 2` and `b(x, y) = Tr(∑ᵢ xᵢ yᵢ²) / 2`.
* `TauCeti.codeInTypeD4Discriminant`: transport a quaternary additive code to a coordinate power
  of the `D₄` discriminant group.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3 for
  glue coordinates and §7.1 for the lattices `Dₙ`, and Chapter 7, §§8–9 for the nonbinary
  constructions.
* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Example 1.3.4, for the
  hexacode.
-/

public section

namespace TauCeti

open IntegralLattice

variable {F : Type*} [Field F] [Finite F]

/-! ## The quaternary `D₄` alphabet -/

private theorem two_zsmul_half : (2 : ℤ) • (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 :=
  AddCircle.zsmul_coe_eq_zero (c := 1) (by norm_num)

private theorem four_zsmul_half : (4 : ℤ) • (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 :=
  AddCircle.zsmul_coe_eq_zero (c := 2) (by norm_num)

private theorem half_add_half :
    (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) + (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  rw [← two_zsmul, two_zsmul_half]

/-- The quadratic map on `(ℤ/2)²` with value `1 / 2` at each nonzero element. -/
private noncomputable def halfKleinFourMap : QuadraticMap ℤ (ZMod 2 × ZMod 2) (AddCircle (1 : ℚ)) :=
  FiniteQuadraticModule.kleinFourMap _ _ _ four_zsmul_half four_zsmul_half two_zsmul_half

private theorem halfKleinFourMap_apply (p : ZMod 2 × ZMod 2) :
    halfKleinFourMap p = if p = 0 then 0 else (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨a, b⟩ := p
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
  · rw [Prod.mk_zero_zero, QuadraticMap.map_zero]
    simp
  · simp [halfKleinFourMap]
  · simp [halfKleinFourMap]
  · rw [halfKleinFourMap, FiniteQuadraticModule.kleinFourMap_apply_one_one, half_add_half,
      zero_add]
    simp

private theorem halfKleinFourMap_symm_apply [DecidableEq F] (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (x : F) :
    halfKleinFourMap ((zmodTwoProdAddEquiv hF hω).symm x) =
      if x = 0 then 0 else (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [halfKleinFourMap_apply]
  by_cases hx : x = 0 <;> simp [hx]

open Classical in
/-- The quadratic map of the quaternary `D₄` alphabet: every nonzero element of a field of order
four has value `1 / 2`. It is transported from the Klein four-group along an additive
identification, which shows it is a quadratic map; the result does not depend on that choice. -/
noncomputable def typeD4QuaternaryQuadraticMap (hF : Nat.card F = 4) :
    QuadraticMap ℤ F (AddCircle (1 : ℚ)) :=
  let hω := (exists_sq_add_self_add_one_eq_zero_of_card_eq_four hF).choose_spec
  (halfKleinFourMap.comp (zmodTwoProdAddEquiv hF hω).symm.toIntLinearEquiv.toLinearMap).copy
    (fun x ↦ if x = 0 then 0 else (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)))
    (funext fun x ↦ (halfKleinFourMap_symm_apply hF hω x).symm)

/-- **The quaternary `D₄` alphabet**: a field of four elements whose nonzero elements all have
quadratic value `1 / 2` in `ℚ/ℤ`, with the polar form as pairing. It is isometric to the
discriminant quadratic module of the `D₄` root lattice
(`typeD4QuaternaryDiscriminantQuadraticIsometry`).

Reducible, as `TauCeti.FiniteBilinearModule.zmodStandard` is, so that its carrier is the field
itself and quaternary additive codes are directly subgroups of its coordinate powers. -/
noncomputable abbrev typeD4QuaternaryQuadraticModule (hF : Nat.card F = 4) :
    FiniteQuadraticModule where
  carrier := F
  pairing := LinearMap.toAddMonoidHom'.comp
    (typeD4QuaternaryQuadraticMap hF).polarBilin.toAddMonoidHom
  pairing_comm x y := QuadraticMap.polar_comm (typeD4QuaternaryQuadraticMap hF) x y
  quadratic := typeD4QuaternaryQuadraticMap hF
  polar_eq_pairing' _ _ := (rfl)

/-- Every nonzero element of a field of order four has `D₄` quadratic value `1 / 2`. -/
@[simp]
theorem typeD4QuaternaryQuadraticMap_apply [DecidableEq F] (hF : Nat.card F = 4) (x : F) :
    typeD4QuaternaryQuadraticMap hF x =
      if x = 0 then 0 else (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [typeD4QuaternaryQuadraticMap, QuadraticMap.coe_copy]
  congr

/-- **The polar pairing of the quaternary `D₄` alphabet is `b(x, y) = Tr(x y²) / 2`**, where
`Tr` is the absolute trace to the prime field. -/
@[simp↓]
theorem typeD4QuaternaryQuadraticModule_pairing [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (x y : F) :
    (typeD4QuaternaryQuadraticModule hF).toFiniteBilinearModule.pairing x y =
      ZMod.toRatAddCircle 2 (Algebra.trace (ZMod 2) F (x * y ^ 2)) := by
  classical
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ 2 := Nat.card_eq_fintype_card.symm.trans hF
  let := charP_of_card_eq_prime_pow hcard
  have hcube (z : F) (hz : z ≠ 0) : z ^ 3 = 1 := by
    simpa [hcard] using FiniteField.pow_card_sub_one_eq_one z hz
  have htrace := algebraMap_trace_eq_add_sq_of_natCard_eq_four hF (x * y ^ 2)
  rw [← FiniteQuadraticModule.polar_eq_pairing]
  by_cases hx : x = 0
  · subst hx
    simp [QuadraticMap.polar_zero_left]
  by_cases hy : y = 0
  · subst hy
    simp [QuadraticMap.polar_zero_right]
  have hx3 := hcube x hx
  have hy3 := hcube y hy
  -- `x y² + (x y²)² = x y (x + y)` once `x³ = y³ = 1`.
  have hsum : x * y ^ 2 + (x * y ^ 2) ^ 2 = x * y * (x + y) := by
    linear_combination x ^ 2 * y * hy3
  rw [QuadraticMap.polar, typeD4QuaternaryQuadraticMap_apply, typeD4QuaternaryQuadraticMap_apply,
    typeD4QuaternaryQuadraticMap_apply]
  simp only [hx, hy, ↓reduceIte]
  by_cases hxy : x = y
  · subst hxy
    have htr : Algebra.trace (ZMod 2) F (x * x ^ 2) = 0 := by
      apply (algebraMap (ZMod 2) F).injective
      rw [htrace, hsum, CharTwo.add_self_eq_zero, mul_zero, map_zero]
    rw [CharTwo.add_self_eq_zero, htr, map_zero]
    simp only [↓reduceIte, zero_sub, ← neg_add', half_add_half, neg_zero]
  · have hxy' : x + y ≠ 0 := fun h ↦
      hxy ((eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq y))
    have htr : Algebra.trace (ZMod 2) F (x * y ^ 2) = 1 := by
      have hne : Algebra.trace (ZMod 2) F (x * y ^ 2) ≠ 0 := by
        intro h
        have := htrace
        rw [h, map_zero, hsum] at this
        exact mul_ne_zero (mul_ne_zero hx hy) hxy' this.symm
      have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact (hcases _).resolve_left hne
    have hone : ZMod.toRatAddCircle 2 1 = (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
      simpa using ZMod.toRatAddCircle_natCast 2 1
    simp only [hxy', ↓reduceIte]
    rw [htr, hone, sub_self, zero_sub, neg_eq_iff_add_eq_zero, half_add_half]

/-! ## Identification with the discriminant module of `D₄` -/

private theorem typeD4QuaternaryDiscriminantEquiv_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (x : F) :
    (((zmodTwoProdAddEquiv hF hω).symm.trans
      (zmodTwoProdAddEquivCheckerboardDiscriminantGroup 4 (by decide))).toIntLinearEquiv :
        (typeD4QuaternaryQuadraticModule hF).carrier ≃ₗ[ℤ]
          ((checkerboardLattice 4).discriminantQuadraticModule
            (isEven_checkerboardLattice 4)).carrier).toFun x =
      zmodTwoProdAddEquivCheckerboardDiscriminantGroup 4 (by decide)
        ((zmodTwoProdAddEquiv hF hω).symm x) :=
  rfl

/-- **The quaternary `D₄` alphabet is isometric to the discriminant quadratic module of the `D₄`
root lattice**, by the identification sending `1` to the vector class and `ω, ω²` to the spinor
and cospinor classes. -/
noncomputable def typeD4QuaternaryDiscriminantQuadraticIsometry (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) :
    FiniteQuadraticModule.Isometry (typeD4QuaternaryQuadraticModule hF)
      ((checkerboardLattice 4).discriminantQuadraticModule (isEven_checkerboardLattice 4)) where
  toLinearEquiv := ((zmodTwoProdAddEquiv hF hω).symm.trans
    (zmodTwoProdAddEquivCheckerboardDiscriminantGroup 4 (by decide))).toIntLinearEquiv
  map_app' x := by
    classical
    obtain ⟨p, rfl⟩ := (zmodTwoProdAddEquiv hF hω).surjective x
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    have hspin : ((((4 : ℕ) : ℚ) / 8 : ℚ) : AddCircle (1 : ℚ)) = (((1 : ℚ) / 2 : ℚ)) := by
      norm_num
    rw [typeD4QuaternaryDiscriminantEquiv_apply]
    -- The evaluation rewrite removes the isometry and linear-equivalence wrappers; this only
    -- unfolds the target quadratic module to its defining quadratic map.
    change (checkerboardLattice 4).discriminantQuadraticMap (isEven_checkerboardLattice 4)
        (zmodTwoProdAddEquivCheckerboardDiscriminantGroup 4 (by decide)
          ((zmodTwoProdAddEquiv hF hω).symm (zmodTwoProdAddEquiv hF hω p))) =
      (typeD4QuaternaryQuadraticModule hF).quadratic (zmodTwoProdAddEquiv hF hω p)
    rw [AddEquiv.symm_apply_apply, typeD4QuaternaryQuadraticMap_apply,
      ← halfKleinFourMap_symm_apply hF hω, AddEquiv.symm_apply_apply, halfKleinFourMap_apply]
    obtain ⟨a, b⟩ := p
    rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
    · rw [Prod.mk_zero_zero, map_zero, QuadraticMap.map_zero]
      simp
    · simp only [zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_zero_one,
        discriminantQuadraticMap_checkerboardSpinorClass, hspin]
      simp
    · simp
    · simp only [zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_one,
        discriminantQuadraticMap_checkerboardCospinorClass, hspin]
      simp

/-- The underlying additive equivalence of the `D₄` identification is the composite of the
Klein four-group identifications of `F` and of the discriminant group. -/
theorem typeD4QuaternaryDiscriminantQuadraticIsometry_toAddEquiv (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).toAddEquiv =
      (zmodTwoProdAddEquiv hF hω).symm.trans
        (zmodTwoProdAddEquivCheckerboardDiscriminantGroup 4 (by decide)) :=
  (rfl)

/-- The `D₄` identification acts through the two Klein four-group identifications. -/
theorem typeD4QuaternaryDiscriminantQuadraticIsometry_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (x : F) :
    typeD4QuaternaryDiscriminantQuadraticIsometry hF hω x =
      zmodTwoProdAddEquivCheckerboardDiscriminantGroup 4 (by decide)
        ((zmodTwoProdAddEquiv hF hω).symm x) :=
  (rfl)

/-- The `D₄` identification sends `1` to the vector class. -/
@[simp]
theorem typeD4QuaternaryDiscriminantQuadraticIsometry_one (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) :
    typeD4QuaternaryDiscriminantQuadraticIsometry hF hω (1 : F) = checkerboardVectorClass 4 := by
  rw [typeD4QuaternaryDiscriminantQuadraticIsometry_apply, zmodTwoProdAddEquiv_symm_one,
    zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_zero]

/-- The `D₄` identification sends `ω` to the spinor class. -/
@[simp]
theorem typeD4QuaternaryDiscriminantQuadraticIsometry_root (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) :
    typeD4QuaternaryDiscriminantQuadraticIsometry hF hω ω = checkerboardSpinorClass 4 := by
  rw [typeD4QuaternaryDiscriminantQuadraticIsometry_apply, zmodTwoProdAddEquiv_symm_root,
    zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_zero_one]

/-- The `D₄` identification sends `ω²` to the cospinor class. -/
@[simp]
theorem typeD4QuaternaryDiscriminantQuadraticIsometry_root_sq (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) :
    typeD4QuaternaryDiscriminantQuadraticIsometry hF hω (ω ^ 2 : F) =
      checkerboardCospinorClass 4 := by
  rw [typeD4QuaternaryDiscriminantQuadraticIsometry_apply, zmodTwoProdAddEquiv_symm_root_sq,
    zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_one]

/-- The quaternary `D₄` alphabet is nondegenerate. -/
theorem isNondegenerate_typeD4QuaternaryQuadraticModule (hF : Nat.card F = 4) :
    (typeD4QuaternaryQuadraticModule hF).IsNondegenerate :=
  (typeD4QuaternaryDiscriminantQuadraticIsometry hF
      (exists_sq_add_self_add_one_eq_zero_of_card_eq_four hF).choose_spec).isNondegenerate_iff.mpr
    (isNondegenerate_discriminantQuadraticModule _ _)

/-! ## Coordinate powers -/

variable {ι : Type*} [Fintype ι]

/-- **The `D₄` quadratic value of a quaternary word is its Hamming weight divided by two.** -/
@[simp↓]
theorem coordinatePower_typeD4QuaternaryQuadraticModule_quadratic [DecidableEq F]
    (hF : Nat.card F = 4) (x : ι → F) :
    ((typeD4QuaternaryQuadraticModule hF).coordinatePower ι).quadratic x =
      (((hammingNorm x : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  calc
    _ = ∑ i, (typeD4QuaternaryQuadraticModule hF).quadratic (x i) :=
      FiniteQuadraticModule.coordinatePower_quadratic (typeD4QuaternaryQuadraticModule hF) ι x
    _ = ∑ i, (((if x i ≠ 0 then 1 else 0 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) :=
      Finset.sum_congr rfl fun i _ ↦ by by_cases hx : x i = 0 <;> simp [hx]
    _ = (((∑ i, (if x i ≠ 0 then 1 else 0 : ℚ) / 2 : ℚ)) : AddCircle (1 : ℚ)) :=
      (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
        (fun i ↦ (if x i ≠ 0 then 1 else 0 : ℚ) / 2) Finset.univ).symm
    _ = _ := by
      have hsum : ∑ i, (if x i ≠ 0 then 1 else 0 : ℚ) = (hammingNorm x : ℚ) := by
        simp only [Finset.sum_boole, hammingNorm]
      rw [← Finset.sum_div, hsum]

/-- **The `D₄` pairing of two quaternary words is `Tr(∑ᵢ xᵢ yᵢ²) / 2`.** -/
@[simp↓]
theorem coordinatePower_typeD4QuaternaryQuadraticModule_pairing [Algebra (ZMod 2) F]
    (hF : Nat.card F = 4) (x y : ι → F) :
    ((typeD4QuaternaryQuadraticModule hF).coordinatePower ι).toFiniteBilinearModule.pairing x y =
      ZMod.toRatAddCircle 2 (Algebra.trace (ZMod 2) F (∑ i, x i * y i ^ 2)) := by
  rw [FiniteQuadraticModule.coordinatePower_pairing, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ typeD4QuaternaryQuadraticModule_pairing hF (x i) (y i)

/-- A quaternary additive code is quadratic-isotropic in the `D₄` coordinate alphabet exactly
when all of its Hamming weights are even. -/
@[simp high]
theorem isIsotropic_coordinatePower_typeD4QuaternaryQuadraticModule_iff [DecidableEq F]
    (hF : Nat.card F = 4) (C : AdditiveCode F ι) :
    ((typeD4QuaternaryQuadraticModule hF).coordinatePower ι).IsIsotropic C ↔
      ∀ x ∈ C, 2 ∣ hammingNorm x := by
  have hpoint (x : ι → F) :
      ((typeD4QuaternaryQuadraticModule hF).coordinatePower ι).quadratic x = 0 ↔
        2 ∣ hammingNorm x := by
    have hden : ((2 : ℕ) : ℚ) = 2 := by norm_num
    rw [coordinatePower_typeD4QuaternaryQuadraticModule_quadratic, ← hden,
      ← Int.cast_natCast (hammingNorm x),
      AddCircle.coe_intCast_div_natCast_eq_zero_iff (by norm_num : 2 ≠ 0)]
    exact Int.natCast_dvd_natCast
  rw [FiniteQuadraticModule.isIsotropic_def]
  exact forall₂_congr fun x _ ↦ hpoint x

/-! ## Transport to the discriminant groups of `D₄` -/

/-- Coordinatewise identification of quaternary words with words in the discriminant groups of
copies of `D₄`: in each coordinate `1, ω, ω²` go to the vector, spinor and cospinor classes. -/
noncomputable def typeD4CoordinateDiscriminantEquiv (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (ι → F) ≃+ (ι → (checkerboardLattice 4).DiscriminantGroup) :=
  AddEquiv.piCongrRight fun _ ↦ (zmodTwoProdAddEquiv hF hω).symm.trans
    (zmodTwoProdAddEquivCheckerboardDiscriminantGroup 4 (by decide))

omit [Fintype ι] in
/-- The coordinatewise `D₄` identification applies the alphabet identification in each
coordinate. -/
@[simp]
theorem typeD4CoordinateDiscriminantEquiv_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (x : ι → F) (i : ι) :
    typeD4CoordinateDiscriminantEquiv hF hω x i =
      typeD4QuaternaryDiscriminantQuadraticIsometry hF hω (x i) :=
  (rfl)

omit [Fintype ι] in
/-- The inverse coordinatewise `D₄` identification applies the inverse alphabet identification in
each coordinate. -/
@[simp]
theorem typeD4CoordinateDiscriminantEquiv_symm_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (x : ι → (checkerboardLattice 4).DiscriminantGroup) (i : ι) :
    (typeD4CoordinateDiscriminantEquiv hF hω).symm x i =
      (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).symm (x i) :=
  (rfl)

/-- The additive equivalence underlying the coordinatewise `D₄` quadratic isometry is the
coordinatewise discriminant-group identification. -/
@[simp]
theorem typeD4QuaternaryDiscriminantQuadraticIsometry_coordinatePower_toAddEquiv
    (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePower ι).toAddEquiv =
      typeD4CoordinateDiscriminantEquiv (ι := ι) hF hω := by
  rw [FiniteQuadraticModule.Isometry.coordinatePower_toAddEquiv,
    typeD4QuaternaryDiscriminantQuadraticIsometry_toAddEquiv]
  rfl

/-- A quaternary additive code transported coordinatewise to the discriminant groups of copies of
the `D₄` root lattice. In every coordinate `1, ω, ω²` are sent to the vector, spinor and cospinor
classes. -/
noncomputable def codeInTypeD4Discriminant (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (C : AdditiveCode F ι) :
    AddSubgroup (ι → (checkerboardLattice 4).DiscriminantGroup) :=
  C.map (typeD4CoordinateDiscriminantEquiv (ι := ι) hF hω)

omit [Fintype ι] in
/-- Membership in the transported `D₄` discriminant subgroup is detected by applying the inverse
identification. -/
@[simp]
theorem mem_codeInTypeD4Discriminant_iff (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (C : AdditiveCode F ι)
    (x : ι → (checkerboardLattice 4).DiscriminantGroup) :
    x ∈ codeInTypeD4Discriminant hF hω C ↔
      (typeD4CoordinateDiscriminantEquiv hF hω).symm x ∈ C :=
  AddSubgroup.mem_map_equiv (f := typeD4CoordinateDiscriminantEquiv (ι := ι) hF hω)

/-- Transport to the `D₄` discriminant groups preserves and reflects quadratic isotropy. -/
@[simp]
theorem isIsotropic_codeInTypeD4Discriminant_iff (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (C : AdditiveCode F ι) :
    (((checkerboardLattice 4).discriminantQuadraticModule
        (isEven_checkerboardLattice 4)).coordinatePower ι).IsIsotropic
      (codeInTypeD4Discriminant hF hω C) ↔
    ((typeD4QuaternaryQuadraticModule hF).coordinatePower ι).IsIsotropic C := by
  rw [codeInTypeD4Discriminant,
    ← typeD4QuaternaryDiscriminantQuadraticIsometry_coordinatePower_toAddEquiv]
  exact FiniteQuadraticModule.Isometry.isIsotropic_map_iff _
    ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePower ι) C

/-- Transport to the `D₄` discriminant groups preserves and reflects the quadratic Lagrangian
condition. -/
@[simp]
theorem isLagrangian_codeInTypeD4Discriminant_iff (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (C : AdditiveCode F ι) :
    (((checkerboardLattice 4).discriminantQuadraticModule
        (isEven_checkerboardLattice 4)).coordinatePower ι).IsLagrangian
      (codeInTypeD4Discriminant hF hω C) ↔
    ((typeD4QuaternaryQuadraticModule hF).coordinatePower ι).IsLagrangian C := by
  rw [codeInTypeD4Discriminant,
    ← typeD4QuaternaryDiscriminantQuadraticIsometry_coordinatePower_toAddEquiv]
  exact FiniteQuadraticModule.Isometry.isLagrangian_map_iff _
    ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePower ι) C

end TauCeti
