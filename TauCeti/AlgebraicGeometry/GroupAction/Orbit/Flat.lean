/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Scheme
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Equivariance

/-!
# Flat orbit projections

The map from a reduced finite-type group scheme onto the scheme of any of its orbits
is faithfully flat and locally of finite presentation. Thus it gives an fppf cover of
the actual locally closed orbit, even in positive characteristic and with nonreduced
stabilizers. Neither connectedness of the group nor reducedness of the ambient scheme
is required.

The proof applies `Scheme.Hom.flat_of_transitive_closedPoints_of_finiteType` to the
existing orbit translations, as in `Comodule.instFlatToProjectiveOrbit` for projective
representation orbits. Generic flatness on the reduced orbit scheme propagates by
translations to every point. The finite-presentation assertion holds without reducedness.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
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

/-- The surjective projection from a reduced finite-type group onto any orbit scheme is flat.
Together with local finite presentation, it is an fppf cover. -/
instance flat_toOrbit [IsReduced G.left] : Flat (toOrbit G x) := by
  have : JacobsonSpace (orbitScheme G x) :=
    LocallyOfFiniteType.jacobsonSpace (orbitToBase G x)
  have : IsLocallyNoetherian (orbitScheme G x) :=
    LocallyOfFiniteType.isLocallyNoetherian (orbitToBase G x)
  exact (toOrbit G x).flat_of_transitive_closedPoints_of_finiteType
    (fun g ↦ (Over.forget _).mapIso (leftTranslation g)) (orbitTranslation G x)
    (fun g ↦ (toOrbit_orbitTranslation_hom G x g).symm)
    (fun _ _ hy hz ↦ exists_orbitTranslation_eq G x hy hz)

end TauCeti.SchemeAction
