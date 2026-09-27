/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Basic
-- Proof-only: a separable isogeny over a separably closed field splits every place completely.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
-- Proof-only: the relative norm of a prime over a maximal ideal with trivial residue extensions.
import TauCeti.NumberTheory.DedekindDomain.RelNorm
-- Proof-only: the dictionary between places over the place of a prime and the primes above it.
import TauCeti.FieldTheory.FunctionField.AffineModel.Extension
-- Proof-only: a normalized valuation bounded by `1` on a Dedekind domain is the valuation of one
-- of its height one primes.
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# The class-group point map at an affine point

`Isogeny.toPointHom φ` is defined through class groups: the class of a point is extended into the
intermediate ring and normed down to the target coordinate ring. Its geometric reading is that
`φ` sends a point `P` of `W₁` to the point lying under it — the point `Q` of `W₂` whose place is
the restriction along `φ^*` of the place of `P`. `PointHom/Basic.lean` proves this when `Q` is the
point at infinity; this file proves it when `Q` is affine. Together, for a separable isogeny over
a separably closed field, they show that the class-group construction computes the value of the
rational map at every rational point.

The affine case is a computation of the relative norm of the prime of the intermediate ring over
the ideal `𝔮` of `Q`. The core theorem assumes only that every prime of the intermediate ring over
`𝔮` has residue degree one — the condition under which
`Ideal.relNorm_eq_of_forall_inertiaDeg_eq_one` computes that norm — and nothing about `F` or the
separability of `φ`. Over a separably closed field a separable isogeny splits every place
completely (`Isogeny.isSplitCompletely`), which discharges the condition and gives the corollary.

## Main results

* `TauCeti.Isogeny.toPointHom_some_eq_some_of_isEquiv_comap_pointPlace_of_forall_inertiaDeg_eq_one`:
  if the place of the affine point `P` of `W₁` restricts along `φ` to the place of the affine point
  `Q` of `W₂`, and every prime of the intermediate ring over the ideal of `Q` has inertia degree
  one, then `φ.toPointHom P = Q`.
* `TauCeti.Isogeny.toPointHom_some_eq_some_of_isEquiv_comap_pointPlace`: the same conclusion over
  a separably closed field for a separable isogeny, where the residue-degree condition always holds.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 (the pushforward of
  divisors along a map of curves, computed by the norm), III.4.8 (an isogeny is a homomorphism on
  points: the identification of the additive class-group map `toPointHom` with the map on points
  that `φ^* x₂`, `φ^* y₂` define is this theorem in the form the repository consumes), and III.4.10
  (a separable isogeny over a separably closed field has fibres of full size).
-/

public section

open Polynomial WeierstrassCurve.Affine IsDedekindDomain

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂)

local instance : IsIntegrallyClosed W₁.CoordinateRing := W₁.isIntegrallyClosed_coordinateRing

local instance : IsIntegrallyClosed W₂.CoordinateRing := W₂.isIntegrallyClosed_coordinateRing

local instance : IsDedekindDomain W₁.CoordinateRing :=
  W₁.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

local instance : IsDedekindDomain W₂.CoordinateRing :=
  W₂.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **The class-group point map evaluates at affine points, given trivial residue extensions over
the target point.** If the place of the affine point `(x, y)` of `W₁` restricts along `φ^*` to the
place of the affine point `(x', y')` of `W₂` — that is, if `φ^* x₂` and `φ^* y₂` take the values
`x'` and `y'` at `(x, y)` — and every prime of the intermediate ring over the ideal of `(x', y')`
has inertia degree one, then `φ.toPointHom` sends `(x, y)` to `(x', y')`.

Nothing is assumed of `F` or of the separability of `φ`: the residue-degree hypothesis is the whole
input beyond the places, and `toPointHom_some_eq_some_of_isEquiv_comap_pointPlace` discharges it
over a separably closed field for a separable isogeny. The algebra structure of `W₂.CoordinateRing`
on the intermediate ring is the caller's, pinned to the pullback one by `halg` exactly as
`Isogeny.isScalarTower_intermediateRing` pins it, so that the hypothesis can be stated. -/
theorem toPointHom_some_eq_some_of_isEquiv_comap_pointPlace_of_forall_inertiaDeg_eq_one
    [inst : Algebra W₂.CoordinateRing φ.intermediateRing]
    (halg : inst = φ.pullbackToIntermediateRing.toAlgebra)
    {x y : F} (h : W₁.Nonsingular x y) {x' y' : F} (h' : W₂.Nonsingular x' y')
    (hP : (((CoordinateRing.pointPlace h.1).valuation W₁.FunctionField).comap
      (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField)).IsEquiv
        ((CoordinateRing.pointPlace h'.1).valuation W₂.FunctionField))
    (hf : ∀ Q ∈ (CoordinateRing.pointPlace h'.1).asIdeal.primesOver φ.intermediateRing,
      Q.inertiaDeg W₂.CoordinateRing = 1) :
    φ.toPointHom (.some x y h) = .some x' y' h' := by
  subst halg
  -- the structures `pushClassMonoidHom_mk0` builds, re-introduced to compute the norm
  let _ : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
  let _ : Algebra W₂.FunctionField W₁.FunctionField := φ.fieldPullback.toRingHom.toAlgebra
  have : IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField :=
    .of_algebraMap_eq fun x ↦ (φ.fieldPullback_algebraMap x).symm
  let _ : Algebra W₁.CoordinateRing φ.intermediateRing := φ.toIntermediateRing.toAlgebra
  let _ : Algebra W₂.CoordinateRing φ.intermediateRing := φ.pullbackToIntermediateRing.toAlgebra
  have : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl fun _ ↦ rfl
  have := φ.isDedekindDomain_intermediateRing fun _ ↦ rfl
  have : Module.Finite W₂.CoordinateRing φ.intermediateRing :=
    φ.moduleFinite_intermediateRing fun _ ↦ rfl
  have : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.toIntermediateRing_injective
  have : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.pullbackToIntermediateRing_injective
  have : FaithfulSMul W₂.CoordinateRing φ.intermediateRing :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr φ.pullbackToIntermediateRing_injective
  -- `φ^* x₂` has no pole at `P`, because `x₂` has none at the affine point `Q`
  have hxle : (CoordinateRing.pointPlace h.1).valuation W₁.FunctionField
      (φ.pullback (algebraMap F[X] W₂.CoordinateRing X)) ≤ 1 := by
    have hQ := (CoordinateRing.pointPlace h'.1).valuation_le_one (K := W₂.FunctionField)
      (algebraMap F[X] W₂.CoordinateRing X)
    rw [← Valuation.isEquiv_iff_val_le_one.mp hP, Valuation.comap_apply, RingHom.coe_coe,
      fieldPullback_algebraMap] at hQ
    exact hQ
  -- so the intermediate ring lies in the valuation ring of `P`, and `v_P` is the valuation of a
  -- height one prime `𝔓` of the intermediate ring
  obtain ⟨𝔓, h𝔓, -⟩ := Valuation.existsUnique_heightOneSpectrum_valuation_eq φ.intermediateRing
    ((CoordinateRing.pointPlace h.1).valuation_surjective W₁.FunctionField)
    (φ.valuation_le_one_of_valuation_pullback_X_le_one h.1 hxle)
  -- the ideal of `P` extends to `𝔓`
  have hmap : (CoordinateRing.XYIdeal W₁ x (C y)).map φ.toIntermediateRing = 𝔓.asIdeal :=
    φ.map_XYIdeal_eq_asIdeal_of_valuation_eq h.1 𝔓 h𝔓
  -- `𝔓` lies over the ideal of `Q`: a function of `W₂` vanishes at `Q` exactly when its pullback
  -- vanishes at `P`
  have hlies : 𝔓.asIdeal.LiesOver (CoordinateRing.pointPlace h'.1).asIdeal := ⟨Ideal.ext fun r ↦ by
    -- the value at `P` of the pullback of `r`, in the form `valuation_lt_one_iff_mem` produces
    have hval : (CoordinateRing.pointPlace h.1).valuation W₁.FunctionField
        (algebraMap φ.intermediateRing W₁.FunctionField
          (algebraMap W₂.CoordinateRing φ.intermediateRing r)) =
        (((CoordinateRing.pointPlace h.1).valuation W₁.FunctionField).comap
          (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField))
          (algebraMap W₂.CoordinateRing W₂.FunctionField r) := by
      rw [Valuation.comap_apply, RingHom.coe_coe, fieldPullback_algebraMap,
        RingHom.algebraMap_toAlgebra, Algebra.algebraMap_ofSubsemiring_apply,
        coe_pullbackToIntermediateRing]
    rw [Ideal.mem_under,
      ← (CoordinateRing.pointPlace h'.1).valuation_lt_one_iff_mem (K := W₂.FunctionField),
      ← 𝔓.valuation_lt_one_iff_mem (K := W₁.FunctionField), h𝔓, hval]
    exact (Valuation.isEquiv_iff_val_lt_one.mp hP).symm⟩
  -- hence the norm of `𝔓` is the ideal of `Q`
  have hnorm : Ideal.relNorm W₂.CoordinateRing 𝔓.asIdeal =
      (CoordinateRing.pointPlace h'.1).asIdeal :=
    Ideal.relNorm_eq_of_forall_inertiaDeg_eq_one (CoordinateRing.pointPlace h'.1).ne_bot hf
      𝔓.asIdeal
  -- read the class-group computation off these ideals
  rw [toPointHom_eq_iff, Point.toClass_some_eq_ofMul_mk0 h, Point.toClass_some_eq_ofMul_mk0 h',
    pushClass_apply, toMul_ofMul, pushClassMonoidHom_mk0]
  refine congrArg Additive.ofMul (congrArg ClassGroup.mk0 (Subtype.ext ?_))
  rw [Ideal.coe_relNorm0]
  -- `ClassGroup.extendedIdeal` is an `abbrev` with no coercion lemma of its own, so its underlying
  -- ideal — the extension along the structure map, which here is `toIntermediateRing` — is
  -- exposed by unfolding
  change Ideal.relNorm W₂.CoordinateRing ((CoordinateRing.XYIdeal W₁ x (C y)).map
    (algebraMap W₁.CoordinateRing φ.intermediateRing)) = _
  rw [RingHom.algebraMap_toAlgebra, hmap, hnorm, CoordinateRing.pointPlace_asIdeal]

/-- **The class-group point map evaluates at affine points.** Over a separably closed field, a
separable isogeny `φ` sends the affine point `(x, y)` of `W₁` to the affine point `(x', y')` of
`W₂` as soon as the place of `(x, y)` restricts along `φ^*` to the place of `(x', y')` — that is,
as soon as `φ^* x₂` and `φ^* y₂` take the values `x'` and `y'` at `(x, y)`.

Together with `Isogeny.toPointHom_some_eq_zero_of_isEquiv_comap_infinityPlace` this identifies
the class-group construction with the map on points that the rational functions `φ^* x₂`, `φ^* y₂`
define. -/
theorem toPointHom_some_eq_some_of_isEquiv_comap_pointPlace [IsSepClosed F]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]
    {x y : F} (h : W₁.Nonsingular x y) {x' y' : F} (h' : W₂.Nonsingular x' y')
    (hP : (((CoordinateRing.pointPlace h.1).valuation W₁.FunctionField).comap
      (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField)).IsEquiv
        ((CoordinateRing.pointPlace h'.1).valuation W₂.FunctionField)) :
    φ.toPointHom (.some x y h) = .some x' y' h' := by
  -- the pullback-induced structures, as `IntermediateRing/Basic.lean` prescribes
  let _ : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
  let _ : Algebra W₂.FunctionField W₁.FunctionField := φ.fieldPullback.toRingHom.toAlgebra
  have : IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField :=
    .of_algebraMap_eq fun x ↦ (φ.fieldPullback_algebraMap x).symm
  let _ : Algebra W₂.CoordinateRing φ.intermediateRing := φ.pullbackToIntermediateRing.toAlgebra
  have : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl fun _ ↦ rfl
  have := φ.isDedekindDomain_intermediateRing fun _ ↦ rfl
  have : FaithfulSMul W₂.CoordinateRing φ.intermediateRing :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr φ.pullbackToIntermediateRing_injective
  -- the function-field extension along `φ`, over the base field
  have hfp : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z := fun _ ↦ rfl
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback hfp
  have := φ.finiteDimensional_functionField hfp
  have := φ.isSeparable_functionField hfp
  -- the constants land in the intermediate ring, which makes its primes places over `F`
  let _ : Algebra F φ.intermediateRing :=
    ((algebraMap F W₁.FunctionField).codRestrict φ.intermediateRing fun c ↦ by
      rw [IsScalarTower.algebraMap_apply F W₁.CoordinateRing W₁.FunctionField]
      exact φ.algebraMap_mem_intermediateRing _).toAlgebra
  have : IsScalarTower F φ.intermediateRing W₁.FunctionField := .of_algebraMap_eq fun _ ↦ rfl
  -- every prime over the ideal of `Q` has residue degree one, the place of `Q` splitting
  -- completely in the separable extension `F(W₁) / F(W₂)` over the separably closed field `F`
  refine φ.toPointHom_some_eq_some_of_isEquiv_comap_pointPlace_of_forall_inertiaDeg_eq_one rfl h h'
    hP fun Q hQ ↦ ?_
  have hQp : Q.IsPrime := hQ.1
  have hQl : Q.LiesOver (CoordinateRing.pointPlace h'.1).asIdeal := hQ.2
  let Q' : HeightOneSpectrum φ.intermediateRing :=
    ⟨Q, hQp, Ideal.ne_bot_of_mem_primesOver (CoordinateRing.pointPlace h'.1).ne_bot hQ⟩
  have hsplit := φ.isSplitCompletely hfp
    (Place.ofPrime F W₂.FunctionField (CoordinateRing.pointPlace h'.1))
  rw [← Place.relativeDegree_ofPrime F W₂.FunctionField (k' := F) (F' := W₁.FunctionField) Q']
  exact hsplit.relativeDegree_eq_one (Place.restrict_ofPrime F W₂.FunctionField (k' := F)
    (F' := W₁.FunctionField) (CoordinateRing.pointPlace h'.1) Q')

end Isogeny

end TauCeti

end
