/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Monoidal.Cartesian.Stabilizer.Preservation
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.AlgebraicGeometry.Group.Cartier
public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic

/-!
# Geometry of scheme-theoretic stabilizers

For a monoid scheme acting on a scheme, the fibre of an orbit map over a closed
section is a closed subscheme of the monoid. If the monoid is affine and of
finite type, so is this fibre. In particular the scheme-theoretic stabilizer of
a rational point of an affine finite-type group scheme is an affine finite-type
group scheme. Stabilizers commute with arbitrary base change, with a cartesian
square of the actual subgroup inclusions. In characteristic zero Cartier's theorem makes it smooth,
without assuming it reduced or connected.

The stabilizer and its group structure are `TauCeti.stabilizer`, constructed from
the native action on all test-scheme points. Its closed immersion follows from
its defining pullback square. The isomorphism
`TauCeti.stabilizer.fiberSmulIso` transports these properties to the orbit fibre
over every translate of the base section. This supplies smooth fibres for the
characteristic-zero study of orbit maps; it does not assert that an arbitrary
orbit map to the ambient scheme is smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 7, actions and homogeneous spaces.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

section Fibers

variable {S : Scheme.{u}} (G : Over S) {X : Over S} [MonObj G] [ModObj G X]
    (x y : 𝟙_ (Over S) ⟶ X) [IsClosedImmersion y.left]

/-- The fibre over a closed section is a closed subscheme of the acting monoid. -/
instance isClosedImmersion_orbitFiber_incl :
    IsClosedImmersion (orbitFiber.incl G x y).left :=
  MorphismProperty.of_isPullback
    ((orbitFiber.isPullback G x y).map (Over.forget S)).flip
    (show IsClosedImmersion y.left from inferInstance)

/-- An orbit fibre over a closed section is affine when the acting monoid is affine. -/
instance isAffine_orbitFiber [IsAffine G.left] : IsAffine (orbitFiber G x y).left :=
  isAffine_of_isAffineHom (orbitFiber.incl G x y).left

/-- An orbit fibre over a closed section is locally of finite type over the base when the
acting monoid is. -/
instance locallyOfFiniteType_orbitFiber [LocallyOfFiniteType G.hom] :
    LocallyOfFiniteType (orbitFiber G x y).hom := by
  rw [← Over.w (orbitFiber.incl G x y)]
  infer_instance

end Fibers

section BaseChange

open scoped CategoryTheory.Obj

attribute [local instance] Functor.modObjObj

variable {S T : Scheme.{u}} (f : T ⟶ S) (G : Over S) {X : Over S}
    [GrpObj G] [ModObj G X] (x : 𝟙_ (Over S) ⟶ X)

/-- Projection from the stabilizer after base change to the original stabilizer.
It is obtained from the group-object comparison of orbit fibres. -/
def stabilizerBaseChangeMap :
    (stabilizer ((Over.pullback f).obj G)
      (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x)).left ⟶
        (stabilizer G x).left :=
  ((Over.pullback f).mapOrbitFiberIso G x x).inv.left ≫
    pullback.fst (stabilizer G x).hom f

/-- The scheme-theoretic stabilizer of the transported point is the base change
of the original stabilizer, as a cartesian square of actual subgroup inclusions.
This holds for arbitrary base change, without flatness or reducedness hypotheses. -/
theorem isPullback_stabilizer_baseChange :
    IsPullback
      (stabilizer.incl ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x)).left
      (stabilizerBaseChangeMap f G x)
      (pullback.fst G.hom f) (stabilizer.incl G x).left := by
  apply (Over.isPullback_pullback_map_left f (stabilizer.incl G x)).of_iso'
    ((Over.forget T).mapIso ((Over.pullback f).mapOrbitFiberIso G x x).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Functor.mapIso_hom, Iso.symm_hom, Over.forget_map,
      ← Over.comp_left, Iso.refl_hom, Category.comp_id] using
      congrArg (fun a ↦ a.left) ((Over.pullback f).mapOrbitFiberIso_inv_incl G x x)
  · simp [stabilizerBaseChangeMap]
  · simp
  · simp

/-- The base-change projection respects the subgroup inclusions on every scheme point. -/
@[reassoc (attr := simp)]
theorem stabilizerBaseChangeMap_incl :
    stabilizerBaseChangeMap f G x ≫ (stabilizer.incl G x).left =
      (stabilizer.incl ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x)).left ≫
          pullback.fst G.hom f :=
  (isPullback_stabilizer_baseChange f G x).w.symm

end BaseChange

section CharZero

variable {k : Type u} [Field k] [CharZero k]
    (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
    [IsAffine G.left] [LocallyOfFiniteType G.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- Scheme-theoretic stabilizers of affine finite-type group actions are smooth in
characteristic zero. No reducedness or connectedness assumption is needed. -/
instance smooth_stabilizer : Smooth (stabilizer G x).hom :=
  TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_charZero (stabilizer G x)

/-- The fibre of an orbit map over a translate of its base point is smooth in characteristic
zero, by its translation isomorphism with the scheme-theoretic stabilizer. -/
instance smooth_orbitFiber_smul (h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    Smooth (orbitFiber G x (h • x)).hom := by
  have := smooth_stabilizer G x
  rw [← Over.w (stabilizer.fiberSmulIso G x h).hom]
  infer_instance

end CharZero

end TauCeti.SchemeAction
