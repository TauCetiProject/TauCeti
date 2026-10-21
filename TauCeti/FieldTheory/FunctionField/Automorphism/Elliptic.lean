/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Class
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Automorphism
public import TauCeti.FieldTheory.FunctionField.Divisor.Equiv
public import TauCeti.FieldTheory.FunctionField.Elliptic.Weierstrass.Model
public import TauCeti.FieldTheory.FunctionField.Place.Existence

/-!
# Automorphisms of elliptic function fields

Let `F / k` be an elliptic function field: genus one, a divisor of degree one, and exact constant
field `k`. Its degree-zero divisor class group `Cl⁰(F)` is in bijection with the places of degree
one (`TauCeti.Place.degreeOneEquivDegreeZeroClassGroup`), so it is infinite exactly when there are
infinitely many places of degree one. This holds over an algebraically closed field, where every
place has degree one.

Over a perfect constant field `F` is the function field of an elliptic curve `E`
(`TauCeti.IsEllipticFunctionField.exists_isWeierstrassCoordinates_isElliptic`). The translations
of `E` by its points act faithfully on `F`, form a normal subgroup of `Aut(F / k)` of finite
index, and the points of `E` are the classes of `Cl⁰(F)`
(`WeierstrassCurve.Affine.normal_range_translationHom`,
`WeierstrassCurve.Affine.finiteIndex_range_translationHom`,
`WeierstrassCurve.Affine.pointEquivDegreeZeroDivisorClass`). Transporting these facts along the
identification of `F` with the function field of `E` shows that **`Cl⁰(F)` embeds into
`Aut(F / k)` as a normal subgroup of finite index** (Stichtenoth, Exercise 6.14), for any
elliptic function field over a perfect field.

Consequently `Aut(F / k)` is infinite as soon as `F` has infinitely many places of degree one, in
particular over an algebraically closed field. So the hypothesis `g ≥ 2` in the finiteness of the
automorphism group over an algebraically closed field (`TauCeti.finite_algEquiv_of_two_le_genus`)
cannot be weakened to `g ≥ 1`. The genus-zero counterpart is `RatFunc.infinite_algEquiv`.

## Main results

* `TauCeti.IsEllipticFunctionField.infinite_degreeClass_ker_iff`: `Cl⁰(F)` is infinite exactly
  when `F` has infinitely many places of degree one.
* `TauCeti.infinite_degreeClass_ker_of_genus_eq_one`: over an algebraically closed field, a
  function field of genus one has an infinite group `Cl⁰(F)`.
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

/-! ### The degree-zero divisor class group -/

/-- **`Cl⁰(F)` is infinite exactly when there are infinitely many places of degree one**, for an
elliptic function field `F` with exact constants: the places of degree one are in bijection with
`Cl⁰(F)` (Stichtenoth, Proposition 6.1.7). -/
theorem IsEllipticFunctionField.infinite_degreeClass_ker_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (he : IsEllipticFunctionField k F) :
    Infinite (Divisor.degreeClass hF).ker ↔ {P : Place k F | P.degree = 1}.Infinite := by
  obtain ⟨P₀, hP₀⟩ := he.exists_place_degree_eq_one hF hex
  rw [← Set.infinite_coe_iff]
  exact (Place.degreeOneEquivDegreeZeroClassGroup hF hex he.genus_eq_one hP₀).infinite_iff.symm

/-- **Over an algebraically closed field, the degree-zero divisor class group of a function field
of genus one is infinite**: every place has degree one, and there are infinitely many places. -/
theorem infinite_degreeClass_ker_of_genus_eq_one [IsAlgClosed k] (hF : IsFunctionField k F)
    (hg : genus k F = 1) : Infinite (Divisor.degreeClass hF).ker := by
  have hex : IsIntegrallyClosedIn k F := isIntegrallyClosedIn_of_isAlgClosed
  obtain ⟨P₀, hP₀⟩ := (Place.infinite_setOf_degree_eq_one hF).nonempty
  have he := (isEllipticFunctionField_iff_genus_eq_one_and_exists_place_degree_eq_one hF hex).mpr
    ⟨hg, P₀, hP₀⟩
  exact (he.infinite_degreeClass_ker_iff hF hex).mpr (Place.infinite_setOf_degree_eq_one hF)

/-! ### Translations -/

/-- **The translations of an elliptic function field** (Stichtenoth, Exercise 6.14): over a
perfect field, the degree-zero divisor class group `Cl⁰(F)` of an elliptic function field with
exact constants embeds into `Aut(F / k)` as a normal subgroup of finite index.

The embedding comes from a Weierstrass model `E` of `F`: it identifies `Cl⁰(F)` with the points of
`E` and sends a point to the pullback of functions along the translation by that point. -/
theorem IsEllipticFunctionField.exists_injective_monoidHom_degreeClass_ker [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (he : IsEllipticFunctionField k F) :
    ∃ φ : Multiplicative (Divisor.degreeClass hF).ker →* (F ≃ₐ[k] F),
      Function.Injective φ ∧ φ.range.Normal ∧ φ.range.FiniteIndex := by
  classical
  obtain ⟨P, W, x, y, hP, hW, h⟩ := he.exists_isWeierstrassCoordinates_isElliptic hF hex
  -- the function field of the Weierstrass model is `F`
  let e : W.toAffine.FunctionField ≃ₐ[k] F := W.toAffine.functionFieldEquivOfAdjoinEqTop
    h.equation h.transcendental_x (h.adjoin_eq_top hF hP)
  -- `Cl⁰(F)` is the point group of the model, in the form the translations take
  let ψ : (Divisor.degreeClass hF).ker ≃+ (W.toAffine⁄k).toAffine.Point :=
    ((Divisor.degreeZeroClassGroupEquivOfRingEquiv (RingEquiv.refl k) e.symm.toRingEquiv
      (fun c ↦ by simp) hF W.toAffine.isFunctionField).trans
        W.toAffine.pointEquivDegreeZeroDivisorClass.symm).trans
      (Affine.Point.equivBaseChangeSelf W.toAffine)
  let τ := Affine.translationHom W.toAffine
  have hrange : ((AlgEquiv.autCongr e).toMonoidHom.comp
      (τ.comp (AddEquiv.toMultiplicative ψ).toMonoidHom)).range =
      τ.range.map (AlgEquiv.autCongr e).toMonoidHom := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ (AddEquiv.toMultiplicative ψ).surjective,
      ← MonoidHom.range_eq_map]
  refine ⟨(AlgEquiv.autCongr e).toMonoidHom.comp (τ.comp (AddEquiv.toMultiplicative ψ).toMonoidHom),
    (AlgEquiv.autCongr e).injective.comp
      ((Affine.translationHom_injective W.toAffine).comp (AddEquiv.toMultiplicative ψ).injective),
    ?_, ?_⟩
  · rw [hrange]
    exact (Affine.normal_range_translationHom W.toAffine).map _ (AlgEquiv.autCongr e).surjective
  · rw [hrange]
    exact ⟨by
      rw [Subgroup.index_map_of_bijective (AlgEquiv.autCongr e).bijective]
      exact (Affine.finiteIndex_range_translationHom W.toAffine).index_ne_zero⟩

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
    (hg : genus k F = 1) : Infinite (F ≃ₐ[k] F) := by
  have hex : IsIntegrallyClosedIn k F := isIntegrallyClosedIn_of_isAlgClosed
  obtain ⟨P₀, hP₀⟩ := (Place.infinite_setOf_degree_eq_one hF).nonempty
  have he := (isEllipticFunctionField_iff_genus_eq_one_and_exists_place_degree_eq_one hF hex).mpr
    ⟨hg, P₀, hP₀⟩
  exact he.infinite_algEquiv hF hex (Place.infinite_setOf_degree_eq_one hF)

end TauCeti
