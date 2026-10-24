/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Class
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Automorphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Place
public import TauCeti.FieldTheory.FunctionField.Divisor.Equiv
public import TauCeti.FieldTheory.FunctionField.Elliptic.Weierstrass.Model
public import TauCeti.FieldTheory.FunctionField.Place.Existence

/-!
# Automorphisms of elliptic function fields

Let `F / k` be an elliptic function field: genus one, a divisor of degree one, and exact constant
field `k`. Its degree-zero divisor class group `Cl⁰(F)` is infinite exactly when there are
infinitely many places of degree one
(`TauCeti.IsEllipticFunctionField.infinite_degreeClass_ker_iff`), as happens over an
algebraically closed field (`TauCeti.infinite_degreeClass_ker_of_genus_eq_one`).

Over a perfect constant field `F` is the function field of an elliptic curve `E`
(`TauCeti.IsEllipticFunctionField.exists_isWeierstrassCoordinates_isElliptic`). The translations
of `E` by its points act faithfully on `F`, form a normal subgroup of `Aut(F / k)` of finite
index, and the points of `E` are the classes of `Cl⁰(F)`
(`WeierstrassCurve.Affine.normal_range_translationHom`,
`WeierstrassCurve.Affine.finiteIndex_range_translationHom`,
`WeierstrassCurve.Affine.pointEquivDegreeZeroDivisorClass`). Transporting these facts along the
identification of `F` with the function field of `E` shows that **`Cl⁰(F)` embeds into
`Aut(F / k)` as a normal subgroup of finite index** (Stichtenoth, Exercise 6.14), for any
elliptic function field over a perfect field. The embedding attached to Weierstrass coordinates
moves each place `Q` of degree one by the class it translates by: the automorphism `σ_c` attached
to `c ∈ Cl⁰(F)` satisfies `[Q - σ_c(Q)] = c`.

Consequently `Aut(F / k)` is infinite as soon as `F` has infinitely many places of degree one, in
particular over an algebraically closed field. So the hypothesis `g ≥ 2` in the finiteness of the
automorphism group over an algebraically closed field (`TauCeti.finite_algEquiv_of_two_le_genus`)
cannot be weakened to `g ≥ 1`. The genus-zero counterpart is `RatFunc.infinite_algEquiv`.

## Main definitions

* `TauCeti.Place.IsWeierstrassCoordinates.translationHom`: the translations
  `Cl⁰(F) →* Aut(F / k)` read through Weierstrass coordinates at a place of degree one.

## Main results

* `TauCeti.Place.IsWeierstrassCoordinates.translationHom_injective`,
  `TauCeti.Place.IsWeierstrassCoordinates.normal_range_translationHom` and
  `TauCeti.Place.IsWeierstrassCoordinates.finiteIndex_range_translationHom`: the translations act
  faithfully and form a normal subgroup of finite index.
* `TauCeti.Place.IsWeierstrassCoordinates.divisorClass_pointDifference_translationHom_smul`: the
  translation by `c` moves a place `Q` of degree one to the place `σ_c(Q)` with
  `[Q - σ_c(Q)] = c`.
* `TauCeti.IsEllipticFunctionField.exists_injective_monoidHom_degreeClass_ker`: over a perfect
  field, `Cl⁰(F)` embeds into `Aut(F / k)` as a normal subgroup of finite index.
* `TauCeti.IsEllipticFunctionField.infinite_algEquiv`: over a perfect field, an elliptic function
  field with infinitely many places of degree one has infinitely many automorphisms.
* `TauCeti.infinite_algEquiv_of_genus_eq_one`: over an algebraically closed field, a function
  field of genus one has infinitely many automorphisms.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 6.1.7 and Exercise 6.14.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3 and III.10.
-/

public section

namespace TauCeti

open AlgebraicGeometry WeierstrassCurve

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### Translations -/

namespace Place.IsWeierstrassCoordinates

variable {P : Place k F} {W : WeierstrassCurve k} [W.IsElliptic] {x y : F}

/-- Weierstrass coordinates at a place of degree one identify the function field of the
Weierstrass model with `F`. -/
private noncomputable def functionFieldEquiv (hF : IsFunctionField k F) (hP : P.degree = 1)
    (h : P.IsWeierstrassCoordinates W x y) : W.toAffine.FunctionField ≃ₐ[k] F :=
  W.toAffine.functionFieldEquivOfAdjoinEqTop h.equation h.transcendental_x (h.adjoin_eq_top hF hP)

/-- The degree-zero divisor class group `Cl⁰(F)` is the point group of the Weierstrass model. -/
private noncomputable def degreeZeroClassGroupEquivPoint [DecidableEq k]
    (hF : IsFunctionField k F) (hP : P.degree = 1) (h : P.IsWeierstrassCoordinates W x y) :
    (Divisor.degreeClass hF).ker ≃+ W.toAffine.Point :=
  (Divisor.degreeZeroClassGroupEquivOfRingEquiv (RingEquiv.refl k)
    (functionFieldEquiv hF hP h).symm.toRingEquiv
      (functionFieldEquiv hF hP h).symm.toRingEquiv_algebraMap_of_tower hF
      W.toAffine.isFunctionField).trans W.toAffine.pointEquivDegreeZeroDivisorClass.symm

/-- The point attached to a class `c` has as its class the transport of `c` to the model. -/
private theorem pointEquivDegreeZeroDivisorClass_degreeZeroClassGroupEquivPoint [DecidableEq k]
    (hF : IsFunctionField k F) (hP : P.degree = 1) (h : P.IsWeierstrassCoordinates W x y)
    (c : (Divisor.degreeClass hF).ker) :
    W.toAffine.pointEquivDegreeZeroDivisorClass (degreeZeroClassGroupEquivPoint hF hP h c) =
      Divisor.degreeZeroClassGroupEquivOfRingEquiv (RingEquiv.refl k)
        (functionFieldEquiv hF hP h).symm.toRingEquiv
        (functionFieldEquiv hF hP h).symm.toRingEquiv_algebraMap_of_tower hF
        W.toAffine.isFunctionField c := by
  simp [degreeZeroClassGroupEquivPoint]

/-- **The translations of an elliptic function field** (Stichtenoth, Exercise 6.14), read
through Weierstrass coordinates `(x, y)` at a place `P` of degree one: the model identifies
`Cl⁰(F)` with the points of the elliptic curve `W`, and a point goes to the pullback of functions
along the translation by that point, transported to `F`.

The automorphism attached to a class `c` moves every place `Q` of degree one so that
`[Q - σ_c(Q)] = c`
(`TauCeti.Place.IsWeierstrassCoordinates.divisorClass_pointDifference_translationHom_smul`). -/
noncomputable def translationHom [DecidableEq k] (hF : IsFunctionField k F) (hP : P.degree = 1)
    (h : P.IsWeierstrassCoordinates W x y) :
    Multiplicative (Divisor.degreeClass hF).ker →* (F ≃ₐ[k] F) :=
  (AlgEquiv.autCongr (functionFieldEquiv hF hP h)).toMonoidHom.comp
    ((Affine.translationHom W.toAffine).comp (AddEquiv.toMultiplicative
      ((degreeZeroClassGroupEquivPoint hF hP h).trans
        (Affine.Point.equivBaseChangeSelf W.toAffine))).toMonoidHom)

variable [DecidableEq k] (hF : IsFunctionField k F) (hP : P.degree = 1)
  (h : P.IsWeierstrassCoordinates W x y)

/-- The unfolding of `translationHom`: the class `c` acts through the translation by its point,
transported to `F`. -/
private theorem translationHom_apply (c : Multiplicative (Divisor.degreeClass hF).ker) :
    h.translationHom hF hP c = AlgEquiv.autCongr (functionFieldEquiv hF hP h)
      (Affine.translation W.toAffine (Affine.Point.equivBaseChangeSelf W.toAffine
        (degreeZeroClassGroupEquivPoint hF hP h (Multiplicative.toAdd c)))) := by
  simp [translationHom, Affine.translationHom_apply]

/-- The translations of an elliptic function field act faithfully. -/
theorem translationHom_injective : Function.Injective (h.translationHom hF hP) :=
  (AlgEquiv.autCongr _).injective.comp
    ((Affine.translationHom_injective W.toAffine).comp (AddEquiv.toMultiplicative _).injective)

/-- The range of `translationHom` is the image of the translations of the Weierstrass model. -/
private theorem range_translationHom :
    (h.translationHom hF hP).range =
      (Affine.translationHom W.toAffine).range.map
        (AlgEquiv.autCongr (functionFieldEquiv hF hP h)).toMonoidHom := by
  rw [translationHom, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (AddEquiv.toMultiplicative _).surjective,
    ← MonoidHom.range_eq_map]

/-- The translations of an elliptic function field form a normal subgroup of `Aut(F / k)`. -/
theorem normal_range_translationHom : (h.translationHom hF hP).range.Normal := by
  rw [range_translationHom]
  exact (Affine.normal_range_translationHom W.toAffine).map _ (AlgEquiv.autCongr _).surjective

/-- The translations of an elliptic function field have finite index in `Aut(F / k)`. -/
theorem finiteIndex_range_translationHom : (h.translationHom hF hP).range.FiniteIndex := by
  rw [range_translationHom]
  exact .map_of_surjective _ (AlgEquiv.autCongr _).surjective

/-- **A translation moves each place of degree one by its class**: the automorphism attached to
`c ∈ Cl⁰(F)` sends a place `Q` of degree one to the place `σ_c(Q)` with `[Q - σ_c(Q)] = c`. In
genus one a place of degree one is determined by this class
(`TauCeti.Place.eq_of_linearlyEquivalent_ofPoint_of_genus_pos`), so the action on the places of
degree one depends on `c` only, not on the Weierstrass coordinates. -/
theorem divisorClass_pointDifference_translationHom_smul
    (c : Multiplicative (Divisor.degreeClass hF).ker) {Q : Place k F} (hQ : Q.degree = 1) :
    (Place.orderSystem hF).divisorClass
        (WeilDivisor.pointDifference Q (h.translationHom hF hP c • Q)) =
      ((Multiplicative.toAdd c : (Divisor.degreeClass hF).ker) :
        (Place.orderSystem hF).ClassGroup) := by
  set e := functionFieldEquiv hF hP h
  set T := Place.equivOfRingEquiv (RingEquiv.refl k) e.symm.toRingEquiv
    e.symm.toRingEquiv_algebraMap_of_tower
  set Pt := degreeZeroClassGroupEquivPoint hF hP h (Multiplicative.toAdd c) with hPt
  -- `Q` is the transport of the place of a point `R` of the model
  set R := (W.toAffine.pointEquivDegreeOnePlace).symm
    ⟨T Q, (Place.degree_equivOfRingEquiv _ _ _ Q).trans hQ⟩
  have hR : (W.toAffine.pointEquivDegreeOnePlace R).1 = T Q := by
    rw [Equiv.apply_symm_apply]
  have hσ : T (h.translationHom hF hP c • Q) =
      (W.toAffine.pointEquivDegreeOnePlace (R - Pt)).1 := by
    rw [translationHom_apply, Place.equivOfRingEquiv_autCongr_smul, ← hR]
    exact Affine.translation_smul_pointEquivDegreeOnePlace W.toAffine Pt R
  -- compare both sides in the class group of the model
  apply (Divisor.classGroupEquivOfRingEquiv (RingEquiv.refl k) e.symm.toRingEquiv
    e.symm.toRingEquiv_algebraMap_of_tower hF W.toAffine.isFunctionField).injective
  -- the class of `Pt = R - (R - Pt)` is the class of `(R) - (R - Pt)` on the model
  rw [Divisor.classGroupEquivOfRingEquiv_divisorClass,
    ← Divisor.coe_degreeZeroClassGroupEquivOfRingEquiv_apply,
    ← pointEquivDegreeZeroDivisorClass_degreeZeroClassGroupEquivPoint, ← hPt, ← sub_sub_cancel R Pt,
    Affine.val_pointEquivDegreeZeroDivisorClass_sub, ← hσ, hR]
  simp only [T, WeilDivisor.pointDifference, map_sub, WeilDivisor.domCongr_ofPoint]

end Place.IsWeierstrassCoordinates

/-- **The translations of an elliptic function field** (Stichtenoth, Exercise 6.14): over a
perfect field, the degree-zero divisor class group `Cl⁰(F)` of an elliptic function field with
exact constants embeds into `Aut(F / k)` as a normal subgroup of finite index.

The embedding is `TauCeti.Place.IsWeierstrassCoordinates.translationHom` for a Weierstrass model
of `F`. -/
theorem IsEllipticFunctionField.exists_injective_monoidHom_degreeClass_ker [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (he : IsEllipticFunctionField k F) :
    ∃ φ : Multiplicative (Divisor.degreeClass hF).ker →* (F ≃ₐ[k] F),
      Function.Injective φ ∧ φ.range.Normal ∧ φ.range.FiniteIndex := by
  classical
  obtain ⟨P, W, x, y, hP, hW, h⟩ := he.exists_isWeierstrassCoordinates_isElliptic hF hex
  exact ⟨h.translationHom hF hP, h.translationHom_injective hF hP,
    h.normal_range_translationHom hF hP, h.finiteIndex_range_translationHom hF hP⟩

/-- **An elliptic function field with infinitely many places of degree one has infinitely many
automorphisms**, over a perfect field: the group `Cl⁰(F)` of translations is then infinite. -/
theorem IsEllipticFunctionField.infinite_algEquiv [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (he : IsEllipticFunctionField k F)
    (hinf : {P : Place k F | P.degree = 1}.Infinite) : Infinite (F ≃ₐ[k] F) := by
  obtain ⟨φ, hφ, -⟩ := he.exists_injective_monoidHom_degreeClass_ker hF hex
  have := (he.infinite_degreeClass_ker_iff hF hex).mpr hinf
  exact Infinite.of_injective φ hφ

/-- **Over an algebraically closed field, a function field of genus one has infinitely many
automorphisms**: the translations by the points of its elliptic curve. So the genus hypothesis
of `TauCeti.finite_algEquiv_of_two_le_genus` cannot be weakened to genus one. -/
theorem infinite_algEquiv_of_genus_eq_one [IsAlgClosed k] (hF : IsFunctionField k F)
    (hg : genus k F = 1) : Infinite (F ≃ₐ[k] F) :=
  (isEllipticFunctionField_of_genus_eq_one hF hg).infinite_algEquiv hF
    isIntegrallyClosedIn_of_isAlgClosed (Place.infinite_setOf_degree_eq_one hF)

end TauCeti
