/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Geometrically.Reduced
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Scheme
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.GroupAction.Orbit.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Equivariance

/-!
# Flat orbit projections

Over any field `k`, the map from a geometrically reduced finite-type group scheme onto the scheme
of any of its orbits is faithfully flat and locally of finite presentation. In particular, this
holds whenever `G` is smooth over `k`, or reduced over a perfect field. Thus it gives an fppf
cover of the actual locally closed orbit, even in positive characteristic and with nonreduced
stabilizers. Neither connectedness of the group nor reducedness of the ambient scheme is
required, and local finite presentation holds without any reducedness assumption.

Over an algebraically closed field, generic flatness on the reduced orbit scheme propagates by
orbit translations (`Scheme.Hom.flat_of_transitive_closedPoints_of_finiteType`). Over a general
field `k`, extending scalars to `AlgebraicClosure k` identifies the orbit projection with the
base change of `toOrbit` (`isPullback_toOrbit_baseChange`), and flatness descends along the
faithfully flat base-change projection.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- The orbit projection is locally of finite type, without a reducedness hypothesis. -/
instance locallyOfFiniteType_toOrbit : LocallyOfFiniteType (toOrbit G x) := by
  have : LocallyOfFiniteType (toOrbit G x ≫ orbitToBase G x) := by
    rw [toOrbit_toBase]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (orbitToBase G x)

/-- The orbit projection is locally of finite presentation, without a reducedness hypothesis. -/
instance locallyOfFinitePresentation_toOrbit : LocallyOfFinitePresentation (toOrbit G x) := by
  have : IsLocallyNoetherian (orbitScheme G x) :=
    LocallyOfFiniteType.isLocallyNoetherian (orbitToBase G x)
  infer_instance

private theorem flat_toOrbit_of_isAlgClosed [IsAlgClosed k] [IsReduced G.left] :
    Flat (toOrbit G x) := by
  have : JacobsonSpace (orbitScheme G x) :=
    LocallyOfFiniteType.jacobsonSpace (orbitToBase G x)
  have : IsLocallyNoetherian (orbitScheme G x) :=
    LocallyOfFiniteType.isLocallyNoetherian (orbitToBase G x)
  exact (toOrbit G x).flat_of_transitive_closedPoints_of_finiteType
    (fun g ↦ (Over.forget _).mapIso (leftTranslation g)) (orbitTranslation G x)
    (fun g ↦ (toOrbit_orbitTranslation_hom G x g).symm)
    (fun _ _ hy hz ↦ exists_orbitTranslation_eq G x hy hz)

/-- Over any field, the surjective projection from a geometrically reduced finite-type group onto
any orbit scheme is flat. Together with local finite presentation, it is an fppf cover. -/
instance flat_toOrbit [GeometricallyReduced G.hom] : Flat (toOrbit G x) := by
  let K : Type u := AlgebraicClosure k
  let f : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let := (Over.pullback f).modObjObj G X
  have : IsReduced ((Over.pullback f).obj G).left :=
    pullback_of_geometrically ‹GeometricallyReduced G.hom›.1 K f
  have hcov : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      ((orbitBaseChangeIso f G x).hom ≫ pullback.fst (orbitToBase G x) f) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (isPullback_toOrbit_baseChange f G x) hcov
    (flat_toOrbit_of_isAlgClosed ((Over.pullback f).obj G) _)

end TauCeti.SchemeAction
