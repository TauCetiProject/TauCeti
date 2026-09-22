/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Dedekind
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Rank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Finite
public import TauCeti.RingTheory.ClassGroup.ExtendedRelNorm
-- Public: `isDedekindDomain_coordinateRing_of_isIntegrallyClosed` turns target normality into the
-- Dedekind instance, and `pushClassMonoidHom_mk0` also uses it for the source inside its statement.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing

/-!
# The class-group map induced by an isogeny

For an isogeny `φ : Isogeny W₁ W₂`, extending an ideal of `W₁.CoordinateRing` into the
intermediate ring and taking the relative norm down to `W₂.CoordinateRing` gives a homomorphism
of class groups.

## Main definitions

* `TauCeti.Isogeny.pushClassMonoidHom`: the multiplicative form,
  `ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing`.
* `TauCeti.Isogeny.pushClass`: the same map written additively, which is the form the point
  group consumes.

## Main results

* `TauCeti.Isogeny.pushClassMonoidHom_apply`: the map on a class is the relative norm of that
  class extended into the intermediate ring.
* `TauCeti.Isogeny.pushClassMonoidHom_mk0`: when the source coordinate ring is normal, the map on
  the class of an integral ideal is the relative norm of its extension.
* `TauCeti.Isogeny.pushClass_apply`: the additive form is the multiplicative one transported
  along `Additive`.
* `TauCeti.Isogeny.pushClassMonoidHom_id` and `TauCeti.Isogeny.pushClass_id`: the identity
  isogeny induces the identity on class groups.

## Design

**Every algebra structure is built here, not accepted.**
`Isogeny.intermediateRing` is a `Subring W₁.FunctionField` carrying no `Algebra` instance over
either coordinate ring — `IntermediateRing/Basic.lean` records that an instance would reintroduce a
diamond — so the two structures have to come from somewhere. Taking them as arguments would leave
the exported map a *family indexed by the caller's choice*: the hypotheses do not force them to be
`toIntermediateRing` and `pullbackToIntermediateRing`, since injectivity, finiteness and
Dedekindness are all stable under precomposing with an `F`-automorphism of the coordinate ring. So
nothing in the signature would pin the map to the one `φ` induces, nor even make
`(Isogeny.id W).pushClass` the identity. The definitions below therefore build both structures
internally from the corestricted embeddings, which is what makes them *the* maps induced by `φ`,
and what a functoriality statement and `toPointHom` need.

The same applies to the ambient structures the intermediate-ring suppliers ask for,
`Algebra W₂.CoordinateRing W₁.FunctionField` and `Algebra W₂.FunctionField W₁.FunctionField`:
they are `φ.pullback` and `φ.fieldPullback` read as algebra structures, and their tower is
`Isogeny.fieldPullback_algebraMap`. Taking them as arguments would need a hypothesis pinning the
first to the pullback for `Isogeny.isScalarTower_intermediateRing` to consume; building them makes
that hypothesis `rfl` and removes it from the signature.

**Every other hypothesis is discharged internally**, from suppliers that live with the object they
describe, in the one-property-per-file `IntermediateRing/` series:

* the target coordinate ring's Dedekind property —
  `WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed`, which is why
  target normality is what the maps ask for and the Dedekind property is not assumed;
* `IsDedekindDomain φ.intermediateRing` — `Isogeny.isDedekindDomain_intermediateRing`, which asks
  nothing of the function-field extension and so covers inseparable isogenies;
* `Module.Finite W₂.CoordinateRing φ.intermediateRing` —
  `Isogeny.moduleFinite_intermediateRing`, whose finite-normalization proof asks neither
  separability nor normality of the source;
* both `Module.IsTorsionFree` instances — Mathlib's `Module.isTorsionFree_iff_algebraMap_injective`
  applied to `Isogeny.toIntermediateRing_injective` and
  `Isogeny.pullbackToIntermediateRing_injective`. These are what make
  `ClassGroup.extendedRelNormHom` applicable at all: its variable block requires them.

What remains in the maps' signature is normality of the target coordinate ring. Source normality
is needed only by `pushClassMonoidHom_mk0`, because Mathlib's computation rule for
`ClassGroup.mk0` assumes its source is Dedekind.

`ClassGroup.extendedRelNormHom` orders its rings `A M R` — source, middle, target — so the
instantiation is `A := W₁.CoordinateRing`, `M := φ.intermediateRing`, `R := W₂.CoordinateRing`.

## Provenance

⚠ *mathlib-track*. Adapted from D. Angdinata's shared isogeny development, `Isogeny.lean`, by
David Kurniadi Angdinata, declarations `pushClassMonoidHom` and `pushClass`, which builds
`pushClass` by ideal extension and relative norm (`ClassGroup.extendedRelNormHom`) on the way to
`toPointHom`.

Two adaptations are forced by how this repository states the surrounding API:

* the source writes `ClassGroup.extendedRelNormHom W₂.CoordinateRing W₁.CoordinateRing
  f.IntermediateRing`, ordering the rings target-source-middle; `TauCeti.ClassGroup`'s own
  `extendedRelNormHom` orders them source-middle-target, so the arguments are permuted here;
* the source obtains its algebra structures from a `letI := f.pullback.coordinateRingAlgebra`
  inside each proof; `intermediateRing` here carries no such instance by design, so the same is
  done from the corestricted embeddings, but inside the definition rather than inside a proof —
  which is what lets the exported map be canonical.
-/

public section

namespace TauCeti

namespace Isogeny

open scoped nonZeroDivisors

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

section PushClass

variable (φ : Isogeny W₁ W₂) [IsIntegrallyClosed W₂.CoordinateRing]

/-- **The class-group map induced by an isogeny**, multiplicatively: extend a class of
`W₁.CoordinateRing` into the intermediate ring, then norm it down to `W₂.CoordinateRing`.

The two coordinate rings carry no map between them; the intermediate ring is what connects
them, receiving `W₁.CoordinateRing` by inclusion and lying module-finite over
`W₂.CoordinateRing`. -/
noncomputable def pushClassMonoidHom :
    ClassGroup W₁.CoordinateRing →* ClassGroup W₂.CoordinateRing :=
  haveI := _root_.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed W₂
  letI : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
  letI : Algebra W₂.FunctionField W₁.FunctionField := φ.fieldPullback.toRingHom.toAlgebra
  haveI : IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField :=
    .of_algebraMap_eq fun x ↦ (φ.fieldPullback_algebraMap x).symm
  letI : Algebra W₁.CoordinateRing φ.intermediateRing := φ.toIntermediateRing.toAlgebra
  letI : Algebra W₂.CoordinateRing φ.intermediateRing := φ.pullbackToIntermediateRing.toAlgebra
  haveI : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
    φ.isScalarTower_intermediateRing rfl fun _ ↦ rfl
  haveI := φ.isDedekindDomain_intermediateRing fun _ ↦ rfl
  have : Module.Finite W₂.CoordinateRing φ.intermediateRing :=
    φ.moduleFinite_intermediateRing fun _ ↦ rfl
  haveI : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.toIntermediateRing_injective
  haveI : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.pullbackToIntermediateRing_injective
  ClassGroup.extendedRelNormHom W₁.CoordinateRing φ.intermediateRing W₂.CoordinateRing

/-- **The induced map on an integral ideal's class** is the relative norm, down to
`W₂.CoordinateRing`, of the ideal extended into the intermediate ring. -/
-- The algebra structures are built by the definition rather than taken from the caller, so the
-- statement restates them — verbatim, so that the two elaborate to the same terms.
@[simp]
theorem pushClassMonoidHom_mk0 [IsIntegrallyClosed W₁.CoordinateRing]
    (I : (Ideal W₁.CoordinateRing)⁰) :
    haveI := _root_.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed W₁
    haveI := _root_.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed W₂
    letI : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
    letI : Algebra W₂.FunctionField W₁.FunctionField := φ.fieldPullback.toRingHom.toAlgebra
    haveI : IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField :=
      .of_algebraMap_eq fun x ↦ (φ.fieldPullback_algebraMap x).symm
    letI : Algebra W₁.CoordinateRing φ.intermediateRing := φ.toIntermediateRing.toAlgebra
    letI : Algebra W₂.CoordinateRing φ.intermediateRing := φ.pullbackToIntermediateRing.toAlgebra
    haveI : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
      φ.isScalarTower_intermediateRing rfl fun _ ↦ rfl
    haveI := φ.isDedekindDomain_intermediateRing fun _ ↦ rfl
    haveI : Module.Finite W₂.CoordinateRing φ.intermediateRing :=
      φ.moduleFinite_intermediateRing fun _ ↦ rfl
    haveI : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr φ.toIntermediateRing_injective
    haveI : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr φ.pullbackToIntermediateRing_injective
    φ.pushClassMonoidHom (ClassGroup.mk0 I) =
      ClassGroup.mk0 (Ideal.relNorm0 W₂.CoordinateRing
        (ClassGroup.extendedIdeal W₁.CoordinateRing φ.intermediateRing I)) := by
  -- the `letI`s above bind inside the statement only, so the same instances are re-introduced
  -- here to bring them into scope for the proof term
  have := _root_.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed W₁
  have := _root_.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed W₂
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
  exact ClassGroup.extendedRelNormHom_mk0 _ _ _ I

/-- **The induced map on a class** is the relative norm, down to `W₂.CoordinateRing`, of that
class extended into the intermediate ring. This is `ClassGroup.extendedRelNormHom_apply` for the
structures the definition builds, so that consumers never have to unfold `pushClassMonoidHom`
itself. -/
-- The algebra structures are built by the definition rather than taken from the caller, so the
-- statement restates them — verbatim, so that the two elaborate to the same terms.
theorem pushClassMonoidHom_apply (c : ClassGroup W₁.CoordinateRing) :
    haveI := _root_.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed W₂
    letI : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
    letI : Algebra W₂.FunctionField W₁.FunctionField := φ.fieldPullback.toRingHom.toAlgebra
    haveI : IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField :=
      .of_algebraMap_eq fun x ↦ (φ.fieldPullback_algebraMap x).symm
    letI : Algebra W₁.CoordinateRing φ.intermediateRing := φ.toIntermediateRing.toAlgebra
    letI : Algebra W₂.CoordinateRing φ.intermediateRing := φ.pullbackToIntermediateRing.toAlgebra
    haveI : IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField :=
      φ.isScalarTower_intermediateRing rfl fun _ ↦ rfl
    haveI := φ.isDedekindDomain_intermediateRing fun _ ↦ rfl
    haveI : Module.Finite W₂.CoordinateRing φ.intermediateRing :=
      φ.moduleFinite_intermediateRing fun _ ↦ rfl
    haveI : Module.IsTorsionFree W₁.CoordinateRing φ.intermediateRing :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr φ.toIntermediateRing_injective
    haveI : Module.IsTorsionFree W₂.CoordinateRing φ.intermediateRing :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr φ.pullbackToIntermediateRing_injective
    φ.pushClassMonoidHom c =
      ClassGroup.relNorm (ClassGroup.extendedHom W₁.CoordinateRing φ.intermediateRing c) := by
  -- the `letI`s above bind inside the statement only, so the same instances are re-introduced
  -- here to bring them into scope for the proof term
  have := _root_.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed W₂
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
  exact ClassGroup.extendedRelNormHom_apply _ _ _ c

/-- **The additive form of `Isogeny.pushClassMonoidHom`.** The point group is described additively
by its class group, so this is the shape the induced map on points is built from. -/
noncomputable def pushClass :
    Additive (ClassGroup W₁.CoordinateRing) →+ Additive (ClassGroup W₂.CoordinateRing) :=
  MonoidHom.toAdditive φ.pushClassMonoidHom

/-- **The additive form is the multiplicative one**, transported along `Additive`. -/
@[simp]
theorem pushClass_apply (x : Additive (ClassGroup W₁.CoordinateRing)) :
    φ.pushClass x = Additive.ofMul (φ.pushClassMonoidHom x.toMul) :=
  (rfl)

/-- **The identity isogeny induces the identity on class groups.** Its intermediate ring is the
coordinate ring itself, so extending a class into it and norming it back down leaves the class
unchanged. -/
@[simp]
theorem pushClassMonoidHom_id (W : WeierstrassCurve.Affine F)
    [IsIntegrallyClosed W.CoordinateRing] :
    (Isogeny.id W).pushClassMonoidHom = MonoidHom.id (ClassGroup W.CoordinateRing) := by
  have := _root_.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed W
  -- extend and norm along the single map `toIntermediateRing`; the definition norms along
  -- `pullbackToIntermediateRing`, which `id_pullbackToIntermediateRing` says is the same map
  let _ := (Isogeny.id W).toIntermediateRing.toAlgebra
  have : IsScalarTower W.CoordinateRing (Isogeny.id W).intermediateRing W.FunctionField :=
    (Isogeny.id W).isScalarTower_intermediateRing
      (id_pullbackToIntermediateRing_toAlgebra W).symm (id_algebraMap_eq_pullback W)
  have : IsDedekindDomain (Isogeny.id W).intermediateRing :=
    (Isogeny.id W).isDedekindDomain_intermediateRing (id_algebraMap_eq_pullback W)
  have : Module.Finite W.CoordinateRing (Isogeny.id W).intermediateRing :=
    (Isogeny.id W).moduleFinite_intermediateRing (id_algebraMap_eq_pullback W)
  have : Module.IsTorsionFree W.CoordinateRing (Isogeny.id W).intermediateRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (toIntermediateRing_injective _)
  refine MonoidHom.ext fun c ↦ ?_
  -- the norm of an extension is the `Module.finrank`-th power, and here that rank is one
  have key : ClassGroup.relNorm (R := W.CoordinateRing)
      (ClassGroup.extendedHom W.CoordinateRing (Isogeny.id W).intermediateRing c) = c := by
    rw [ClassGroup.relNorm_extendedHom, finrank_intermediateRing_id_eq_one, pow_one]
  rw [pushClassMonoidHom_apply, MonoidHom.id_apply]
  -- `key` norms along `toIntermediateRing`, the goal along `pullbackToIntermediateRing`; the two
  -- sides agree once those algebra structures are identified, which is the single goal `convert`
  -- leaves behind (`rw` cannot do it: the norm's scalar-tower argument depends on the structure)
  convert key using 3
  exact id_pullbackToIntermediateRing_toAlgebra W

/-- **The identity isogeny induces the identity**, additively. -/
@[simp]
theorem pushClass_id (W : WeierstrassCurve.Affine F) [IsIntegrallyClosed W.CoordinateRing] :
    (Isogeny.id W).pushClass = AddMonoidHom.id (Additive (ClassGroup W.CoordinateRing)) := by
  refine AddMonoidHom.ext fun c ↦ ?_
  rw [pushClass_apply, pushClassMonoidHom_id, MonoidHom.id_apply, AddMonoidHom.id_apply]
  rfl

end PushClass

end Isogeny

end TauCeti
