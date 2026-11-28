/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Stabilizer.Preservation
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.AlgebraicGeometry.Group.Cartier
public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Stabilizer.KernelPair

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
over every translate of the base section. Over an arbitrary base scheme, smoothness
of an orbit map always descends to its stabilizer
(`TauCeti.SchemeAction.smooth_stabilizer_of_smooth_orbitMap`), and a faithfully flat
quasi-compact orbit map is smooth iff its stabilizer is smooth
(`TauCeti.SchemeAction.smooth_orbitMap_iff`); this supplies smooth fibres for the
characteristic-zero study of orbit maps without asserting that an arbitrary orbit map
to the ambient scheme is smooth.

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

section Smoothness

variable {S : Scheme.{u}} (G : Over S) {X : Over S} [GrpObj G] [ModObj G X]
  (x : 𝟙_ (Over S) ⟶ X)

private theorem isPullback_orbitMap_left :
    IsPullback (stabilizer.incl G x).left (stabilizer G x).hom
      (orbitMap G x).left x.left := by
  simpa only [Over.forget_map, Over.toUnit_left] using
    (orbitFiber.isPullback G x x).map (Over.forget S)

/-- Over an arbitrary base scheme, a faithfully flat and quasi-compact morphism `f : G.left ⟶ Y`
whose fibre over a base section `y` is the stabilizer and whose kernel pair is right
multiplication by the stabilizer is smooth if and only if the stabilizer is smooth over the base
scheme. -/
theorem smooth_iff_smooth_stabilizer {Y : Scheme.{u}} (f : G.left ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f] {y : (𝟙_ (Over S)).left ⟶ Y}
    (hfib : IsPullback (stabilizer.incl G x).left (stabilizer G x).hom f y)
    (hkp : IsPullback (fst G (stabilizer G x)).left (stabilizer.rightMul G x).left f f) :
    Smooth f ↔ Smooth (stabilizer G x).hom := by
  refine ⟨fun h ↦ MorphismProperty.of_isPullback hfib h, fun hs ↦ ?_⟩
  let := hs
  have hp : Smooth (fst G (stabilizer G x)).left := by
    rw [Over.fst_left]
    infer_instance
  exact MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact hkp hp

/-- Smoothness of the orbit morphism implies smoothness of its scheme-theoretic stabilizer, over an
arbitrary base scheme and in every characteristic. -/
theorem smooth_stabilizer_of_smooth_orbitMap (h : Smooth (orbitMap G x).left) :
    Smooth (stabilizer G x).hom :=
  MorphismProperty.of_isPullback (isPullback_orbitMap_left G x) h

/-- Over an arbitrary base scheme, a faithfully flat and quasi-compact orbit morphism is smooth if
and only if its scheme-theoretic stabilizer is smooth over the base scheme. -/
theorem smooth_orbitMap_iff [Flat (orbitMap G x).left] [Surjective (orbitMap G x).left]
    [QuasiCompact (orbitMap G x).left] :
    Smooth (orbitMap G x).left ↔ Smooth (stabilizer G x).hom :=
  smooth_iff_smooth_stabilizer G x (orbitMap G x).left
    (isPullback_orbitMap_left G x)
    (by
      simpa only [Over.forget_map] using
        (stabilizer.isPullback_rightMul G x).map (Over.forget S))

end Smoothness

end TauCeti.SchemeAction
