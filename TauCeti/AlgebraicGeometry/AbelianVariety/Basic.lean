/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian

/-!
# Abelian varieties

This file opens the Jacobian roadmap's Layer E by defining an **abelian variety** over a field
`K` and recording its first structural property, commutativity of the group law.

Following Milne, an abelian variety is a *proper, geometrically integral group scheme* over `K`.
Geometric integrality is the robust "variety" condition (it is the standing hypothesis of
Mathlib's commutativity theorem and is stable under base change and insensitive to imperfect
base fields); for a group scheme over a field it is equivalent to the more familiar
smooth-plus-geometrically-connected packaging, which needs the harder "reduced connected group
scheme is irreducible" input not yet in Mathlib. We therefore take geometric integrality as the
definition and leave the smooth/connected reconciliation as later work.

We bundle the data as a structure `AbelianVariety K`, so that later roadmap targets can write
`JacobianVariety X x₀ : AbelianVariety k` and refer to `(JacobianVariety X x₀).toScheme` and
its base changes, matching `TauCetiRoadmap/JacobianChallenge/Suggested.lean`. From the bundled
hypotheses we derive:

* `AbelianVariety.isCommMonObj`: the group law is commutative, straight from Mathlib's rigidity
  theorem `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`
  (a proper geometrically integral group scheme over a field is commutative);
* `AbelianVariety.isIntegral`: the underlying scheme is integral (hence nonempty, irreducible,
  and reduced), since geometric integrality over the one-point base `Spec K` descends to
  absolute integrality;
* `AbelianVariety.baseChange`: the base change of an abelian variety along a field extension
  `K → L` is again an abelian variety, since properness and geometric integrality are stable
  under base change and the monoidal pullback functor carries the group-object structure.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API ... Commutativity is automatic
(rigidity, `Group/Abelian.lean`)", and the roadmap's base-change compatibility. No external
mathematics is vendored; the proofs reuse Mathlib's `Over`/`GrpObj` monoidal API, the
`GeometricallyIntegral`/`IsProper` morphism-property instances, and the commutativity theorem in
`Mathlib.AlgebraicGeometry.Group.Abelian`.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- An **abelian variety** over a field `K`: a proper, geometrically integral group scheme over
`Spec K`.

The group-object structure lives on `toOver : Over (Spec (.of K))`; the underlying scheme is
`toScheme = toOver.left`. The fields are the standing hypotheses of the theory: `grpObj` is the
group law, `isProper` says the structure morphism to `Spec K` is proper, and
`geometricallyIntegral` is the "variety" condition. -/
structure AbelianVariety (K : Type u) [Field K] where
  /-- The underlying group scheme over `Spec K`. -/
  toOver : Over (Spec (.of K))
  /-- The group-object structure on `toOver`. -/
  grpObj : GrpObj toOver
  /-- The structure morphism to `Spec K` is proper. -/
  isProper : IsProper toOver.hom
  /-- `toOver` is geometrically integral over `Spec K`: the "variety" condition. -/
  geometricallyIntegral : GeometricallyIntegral toOver.hom

namespace AbelianVariety

variable {K : Type u} [Field K]

attribute [instance] AbelianVariety.grpObj AbelianVariety.isProper
  AbelianVariety.geometricallyIntegral

/-- The underlying scheme of an abelian variety. -/
noncomputable abbrev toScheme (A : AbelianVariety K) : Scheme.{u} :=
  A.toOver.left

/-- The group law of an abelian variety is commutative: a proper geometrically integral group
scheme over a field is a commutative group object. This is the abstract rigidity theorem
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, packaged for the bundled
`AbelianVariety`. -/
instance isCommMonObj (A : AbelianVariety K) : IsCommMonObj A.toOver :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.toOver

/-- The underlying scheme of an abelian variety is integral: geometric integrality over the
one-point base `Spec K` descends to absolute integrality. In particular the underlying space is
nonempty, irreducible, and reduced. -/
instance isIntegral (A : AbelianVariety K) : IsIntegral A.toScheme :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.toOver.hom

/-! ### Base change along a field extension -/

/-- The base change of an abelian variety along a field extension `K → L`, obtained by pulling
back the group scheme along `Spec L → Spec K`.

Properness and geometric integrality are stable under base change, and the monoidal pullback
functor carries the group-object structure (`Functor.grpObjObj`), so the result is again an
abelian variety. This realizes the roadmap's base-change compatibility of the Jacobian at the
level of abelian varieties. -/
@[expose] noncomputable def baseChange (A : AbelianVariety K) (L : Type u) [Field L]
    [Algebra K L] : AbelianVariety L where
  toOver := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.toOver
  grpObj := Functor.grpObjObj
  isProper := inferInstanceAs
    (IsProper (Limits.pullback.snd A.toOver.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
  geometricallyIntegral := inferInstanceAs
    (GeometricallyIntegral (Limits.pullback.snd A.toOver.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))))

@[simp]
lemma baseChange_toOver (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    (A.baseChange L).toOver =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.toOver :=
  rfl

/-- The underlying scheme of a base change is the fibre product of the abelian variety with
`Spec L` over `Spec K`. -/
lemma baseChange_toScheme (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    (A.baseChange L).toScheme =
      Limits.pullback A.toOver.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  rfl

end AbelianVariety

end AlgebraicGeometry

end TauCeti
