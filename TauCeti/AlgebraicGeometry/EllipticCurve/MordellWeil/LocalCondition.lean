/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange

/-!
# Base change of the étale algebra, and the local condition of `2`-descent

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, with étale algebra `A = K[X]⧸⟨f⟩` and descent map
`μ : W(K) → M = Aˣ/(Aˣ)²`, as set up in
`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`.

Everything in that construction base-changes along a field extension `L/K` — in the arithmetic
application `L` is a completion of `K`. This file builds that base change and uses it to define
the **local condition** at `L`: the subgroup

`W.localCondition L : Subgroup W.M`

of square classes whose image in `(W⁄L).M` lies in the image of the local descent map `μ_L`. The
`2`-Selmer group of `W` is cut out of `W.M` by these conditions at all completions of `K`, so
`localCondition` is the object every later descent statement is phrased in.

The underlying cubic quotient algebra, its square-class group, and their base-change maps are
defined over arbitrary commutative rings. The discriminant identity holds at this generality
as well, and a root of the cubic gives a nonsingular point after base change to any nontrivial
commutative algebra, provided the curve is elliptic and in characteristic-≠-2 normal form.

## Main definitions

* `WeierstrassCurve.Affine.mapA`: the base-change homomorphism `R[X]⧸⟨f⟩ →+* S[X]⧸⟨f⟩` of
  cubic quotient algebras, which are étale in the elliptic characteristic-≠-2 setting.
* `WeierstrassCurve.Affine.localRes`: the induced map `W.M →* (W⁄S).M` on square classes over
  commutative rings.
* `WeierstrassCurve.Affine.localCondition`: the local `2`-descent condition at `L`.

## Main statements

* `WeierstrassCurve.Affine.baseChange_discr_f`: the discriminant of the cubic `f` commutes with
  base change.
* `WeierstrassCurve.Affine.nonsingular_baseChange_of_aeval_eq_zero`: a root `x` of `f` in a
  nontrivial algebra `S` gives the point `(x, 0)` of `W⁄S`.
* `WeierstrassCurve.Affine.localRes_μX` and `WeierstrassCurve.Affine.localRes_comp_μ`: the
  descent map is natural under base change — restricting square classes after the global `μ` is
  applying the local `μ` after the base change of points.
* `WeierstrassCurve.Affine.range_μ_le_localCondition`: the image of the global descent map
  satisfies the local condition at every extension field. This is what makes `localCondition` a
  *condition*: it is a constraint the classes coming from `W(K)` are known to satisfy, so the
  intersection of the local conditions bounds `W(K)/2W(K)` from above.
* `WeierstrassCurve.Affine.card_range_μ_of_surjective_algebraMap`: base change along an
  *isomorphism* preserves the size of the descent image, via
  `WeierstrassCurve.Affine.range_μ_of_surjective_algebraMap`, which identifies the two images.
  This is the transport step: a count of `#(im μ)` established over a concrete field carries to
  any field isomorphic to it. Its inputs are
  `WeierstrassCurve.Affine.bijective_mapA_of_bijective_algebraMap` and
  `WeierstrassCurve.Affine.localRes_bijective_of_bijective_algebraMap`.

## Implementation notes

Square classes are spelled `W.M`, the quotient of `W.Aˣ` by the range of `powMonoidHom 2`,
following `XSubT.lean`; the source uses a local abbreviation `Units.modPow` for the same group,
which is not a Mathlib declaration and which TauCeti deliberately does not carry, so that the
repository has a single spelling of square classes. Accordingly `localRes` is built from
`QuotientGroup.map` rather than from the source's `Units.modPow.map`.

The base change of points is `WeierstrassCurve.Affine.pointMap`, from
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/BaseChange.lean`.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, revision `66889eada51a`),
`EllipticCurves/SelmerGroup.lean` lines 85-323 — that file's `BaseChange` section: lines 85-295
give the base change up to the local condition and its compatibility with `μ`, and lines 296-323
give the isomorphism-invariance block — `range_μ_of_bijective_algebraMap` and
`card_range_μ_of_bijective_algebraMap` upstream, renamed here for the weaker hypothesis — plus the
étale-algebra bijectivity at line 168.

The square-class isomorphism statement `localRes_bijective_of_bijective_algebraMap` follows from
`QuotientGroup.congrRangePowMonoidHom` applied to the induced equivalence of unit groups.
`baseChange_discr_f` is the source's lemma of that name at its later revision `3bfe124`.
`nonsingular_baseChange_of_aeval_eq_zero` is not from the source: it is
`WeierstrassCurve.Affine.nonsingular_of_eval_f_eq_zero` after base change.
-/

public section

open Polynomial

namespace WeierstrassCurve

namespace Affine

section CommRing

variable {R : Type*} [CommRing R] (W : Affine R)

section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)

lemma map_f : (W.map σ).toAffine.f = W.f.map σ := by
  simp only [f, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, map_a₂, map_a₄, map_a₆]

lemma eval_map_f (x : R) : (W.map σ).toAffine.f.eval (σ x) = σ (W.f.eval x) := by
  rw [map_f, Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma map_fCofactor (x : R) : (W.fCofactor x).map σ = (W.map σ).toAffine.fCofactor (σ x) := by
  simp only [fCofactor, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, map_a₂, map_a₄, map_add, map_mul, map_pow]

end Map

section Algebra

variable (S : Type*) [CommRing S] [Algebra R S]

lemma eval_baseChange_f (x : R) :
    (W⁄S).toAffine.f.eval (algebraMap R S x) = algebraMap R S (W.f.eval x) :=
  W.eval_map_f (algebraMap R S) x

lemma baseChange_fCofactor (x : R) :
    (W.fCofactor x).map (algebraMap R S) = (W⁄S).toAffine.fCofactor (algebraMap R S x) :=
  W.map_fCofactor (algebraMap R S) x

lemma baseChange_f : (W⁄S).toAffine.f = W.f.map (algebraMap R S) :=
  W.map_f (algebraMap R S)

/-- The discriminant of the cubic `f` commutes with base change. -/
lemma baseChange_discr_f : (W⁄S).toAffine.f.discr = algebraMap R S W.f.discr := by
  nontriviality S
  let := (algebraMap R S).domain_nontrivial
  simp [discr_f, toAffine, map_ofNat]

variable {S} in
/-- A root `x` of the cubic `f` in a nontrivial `R`-algebra `S` gives the nonsingular point
`(x, 0)` of the base-changed curve `W⁄S`. -/
lemma nonsingular_baseChange_of_aeval_eq_zero [Nontrivial S] [W.IsElliptic] [W.IsCharNeTwoNF]
    {x : S} (hx : aeval x W.f = 0) : (W⁄S).toAffine.Nonsingular x 0 :=
  (W⁄S).toAffine.nonsingular_of_eval_f_eq_zero <| by
    rw [W.baseChange_f, eval_map_algebraMap, hx]

/-- The base-change homomorphism `R[X]⧸⟨f⟩ →+* S[X]⧸⟨f⟩` of cubic quotient algebras, as an
instance of `AdjoinRoot.map`. In the elliptic characteristic-≠-2 setting these algebras are étale.
-/
noncomputable def mapA : W.A →+* (W⁄S).toAffine.A :=
  AdjoinRoot.map (algebraMap R S) W.f (W⁄S).toAffine.f (W.baseChange_f S).dvd

@[simp]
lemma mapA_mk (p : R[X]) :
    W.mapA S (AdjoinRoot.mk W.f p) = AdjoinRoot.mk (W⁄S).toAffine.f (p.map (algebraMap R S)) :=
  AdjoinRoot.map_mk _ _

/-- Base change of the cubic quotient algebra along an isomorphism of commutative rings is
bijective. -/
lemma bijective_mapA_of_bijective_algebraMap (h : Function.Bijective (algebraMap R S)) :
    Function.Bijective (W.mapA S) :=
  (AdjoinRoot.mapRingEquiv (RingEquiv.ofBijective (algebraMap R S) h)
    W.f (W⁄S).toAffine.f (by rw [W.baseChange_f]; exact Associated.refl _)).bijective

/-- The base-change map on square classes of units of the cubic quotient algebra, over
commutative rings. -/
noncomputable def localRes : W.M →* (W⁄S).toAffine.M :=
  QuotientGroup.map _ _ (Units.map (W.mapA S).toMonoidHom) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map (W.mapA S).toMonoidHom u, by simp [powMonoidHom]⟩

@[simp]
lemma localRes_mk (u : W.Aˣ) :
    W.localRes S (QuotientGroup.mk u) = QuotientGroup.mk (Units.map (W.mapA S).toMonoidHom u) :=
  QuotientGroup.map_mk _ _ _ _ u

/-- The base-change map on square classes, on the class of a unit given as `IsUnit a`. -/
-- Deliberately NOT `@[simp]`: the left-hand side is not in simp-normal form, because
-- `localRes_mk` rewrites `W.localRes S ↑ha.unit` first, so the attribute could never fire —
-- use it for explicit rewriting at the `localRes_μX` call sites below.
lemma localRes_unit {a : W.A} (ha : IsUnit a) :
    W.localRes S (ha.unit : W.M) = ((ha.map (W.mapA S)).unit : (W⁄S).toAffine.M) := by
  rw [localRes_mk]
  exact congrArg _ (Units.ext rfl)

/-- Base change along an isomorphism of commutative rings is bijective on square classes. -/
lemma localRes_bijective_of_bijective_algebraMap (h : Function.Bijective (algebraMap R S)) :
    Function.Bijective (W.localRes S) := by
  let e := MulEquiv.ofBijective (Units.map (W.mapA S).toMonoidHom)
    (Units.map_bijective (W.bijective_mapA_of_bijective_algebraMap S h))
  have he : W.localRes S = (QuotientGroup.congrRangePowMonoidHom e 2).toMonoidHom := by
    refine MonoidHom.ext fun m ↦ ?_
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective m
    simp [e]
  rw [he]
  exact (QuotientGroup.congrRangePowMonoidHom e 2).bijective

end Algebra

end CommRing

variable {K : Type*} [Field K] (W : Affine K)

section BaseChange

variable (L : Type*) [Field L] [Algebra K L]

variable [W.IsElliptic] [W.IsCharNeTwoNF]

open scoped Classical in
/-- The local `2`-descent condition at the extension field `L` of `K` (in the applications,
`L` is a completion of `K`): the subgroup of square classes in the étale algebra of `W`
whose image over `L` comes from an `L`-point of the curve. -/
noncomputable def localCondition : Subgroup W.M :=
  ((μ (W := (W⁄L).toAffine)).range).comap (W.localRes L)

open scoped Classical in
@[simp]
lemma mem_localCondition_iff {m : W.M} :
    m ∈ W.localCondition L ↔ W.localRes L m ∈ (μ (W := (W⁄L).toAffine)).range :=
  Subgroup.mem_comap

open scoped Classical in
/-- The local restriction map is compatible with the `x - T` maps: the square class of
`x - T` restricts to that of `σ(x) - T`, and likewise for the modified class at a
`2`-torsion `x`-coordinate. -/
theorem localRes_μX (x : K) :
    W.localRes L (W.μX x) = μX (W := (W⁄L).toAffine) (algebraMap K L x) := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) = 0 := by
      rw [W.eval_baseChange_f, hx, map_zero]
    rw [μX_of_eval_f_eq_zero hxL, μX_of_eval_f_eq_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [mapA_mk, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, W.baseChange_fCofactor]
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) ≠ 0 := by
      rw [W.eval_baseChange_f]
      exact fun h0 ↦ hx ((map_eq_zero _).mp h0)
    rw [μX_of_eval_f_ne_zero hxL, μX_of_eval_f_ne_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [mapA_mk, Polynomial.map_sub,
      Polynomial.map_C, Polynomial.map_X]


open scoped Classical in
/-- Naturality of the descent map under base change: restricting square classes after the
global `μ` is applying the local `μ` after the base change of points. -/
theorem localRes_comp_μ : (W.localRes L).comp (μ (W := W)) =
      (μ (W := (W⁄L).toAffine)).comp (AddMonoidHom.toMultiplicative (W.pointMap L)) := by
  refine MonoidHom.ext fun P' ↦ ?_
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
    μ_apply]
  cases P with
  | zero =>
      rw [← Point.zero_def, μ₀_zero, map_one, map_zero (W.pointMap L),
        μ₀_zero (W := (W⁄L).toAffine)]
  | some x y hP =>
      rw [μ₀_some, W.pointMap_some L hP, μ₀_some (W := (W⁄L).toAffine), W.localRes_μX L x]

open scoped Classical in
/-- The image of the global descent map `μ` satisfies the local condition at every extension
field: this is formal from the naturality `localRes_comp_μ`. -/
theorem range_μ_le_localCondition : (μ (W := W)).range ≤ W.localCondition L := by
  rw [localCondition, ← Subgroup.map_le_iff_le_comap, MonoidHom.map_range, localRes_comp_μ]
  rintro _ ⟨P, rfl⟩
  exact ⟨_, rfl⟩

/-!
### Base change along an isomorphism

If `L/K` is an isomorphism rather than a proper extension, nothing is lost: the étale algebras
are isomorphic, so the descent map has the same image over `L` as over `K`. This is what lets a
count established over a concrete field — `ℝ`, say — be transported to a completion that is
merely isomorphic to it.
-/

open scoped Classical in
/-- Along an isomorphism, the descent image over `L` is the image of the descent image over `K`
under the local restriction of square classes. Formal from the naturality `localRes_comp_μ`,
once base change of points is seen to be surjective. -/
lemma range_μ_of_surjective_algebraMap (h : Function.Surjective (algebraMap K L)) :
    (μ (W := (W⁄L).toAffine)).range = Subgroup.map (W.localRes L) (μ (W := W)).range := by
  have hpm : Function.Surjective (W.pointMap L) := by
    rintro (_ | ⟨x, y, hP⟩)
    · exact ⟨0, map_zero (W.pointMap L)⟩
    · obtain ⟨x', rfl⟩ := h x
      obtain ⟨y', rfl⟩ := h y
      exact ⟨Point.some x' y'
        ((W.map_nonsingular (algebraMap K L).injective _ _).mp hP), W.pointMap_some L _⟩
  have hsurj : Function.Surjective (AddMonoidHom.toMultiplicative (W.pointMap L)) :=
    fun P ↦ (hpm P.toAdd).imp fun _ hQ ↦ congrArg Multiplicative.ofAdd hQ
  rw [MonoidHom.map_range, localRes_comp_μ, ← MonoidHom.map_range,
    MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map]

open scoped Classical in
/-- **Base change along an isomorphism preserves the size of the descent image.** This is the
transport step: a count of `#(im μ)` established over one field carries to any field isomorphic
to it. -/
theorem card_range_μ_of_surjective_algebraMap (h : Function.Surjective (algebraMap K L)) :
    Nat.card (μ (W := (W⁄L).toAffine)).range = Nat.card (μ (W := W)).range := by
  rw [W.range_μ_of_surjective_algebraMap L h]
  exact Subgroup.card_map_of_injective
    (W.localRes_bijective_of_bijective_algebraMap L ⟨(algebraMap K L).injective, h⟩).1

end BaseChange

end Affine

end WeierstrassCurve

end
