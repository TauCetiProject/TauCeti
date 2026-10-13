/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem

/-!
# Moduli problems of homomorphisms to the group of points

Let `A` be a group. Many level structures on an elliptic curve `E` over a scheme `S` are
homomorphisms `φ : A →* E(S)` to the group of `S`-points of `E` satisfying a condition `p`: the
naive level structures (`ModuliProblem.naiveLevel`) ask that `φ` be injective on every fibre, and
the `[Γ(N)]`-structures (`ModuliProblem.gamma`) that `φ` be a Drinfeld basis of `E[N]`.

An arrow `(E'/S') ⟶ (E/S)` of `Ell/B` exhibits `E'` as the base change of `E`, and composing with
base change of points (`EllipticCurveGeom.pointsPullback`) turns a homomorphism `A →* E(S)` into
a homomorphism `A →* E'(S')`. When the condition `p` is stable under this pull-back, the
homomorphisms satisfying it form a moduli problem over `Ell/B` (`ModuliProblem.homLevel`).
Restriction along a homomorphism `A' →* A` which carries the condition on `A` to the condition on
`A'` is a morphism of such moduli problems (`ModuliProblem.homLevelMap`).

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.homLevel B A p hp`: the moduli problem of
  homomorphisms `A →* E(S)` satisfying a condition `p` stable under base change.
* `TauCeti.AlgebraicGeometry.ModuliProblem.homLevelEquiv`: its level structures on an object
  `(E/S)` of `Ell/B` are the homomorphisms `A →* E(S)` satisfying `p`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.homLevelMap`: restriction of level structures along a
  homomorphism of groups.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.homLevelEquiv_map`: the pull-back of a level structure
  along an arrow of `Ell/B` is its composite with base change of points.
* `TauCeti.AlgebraicGeometry.ModuliProblem.homLevelEquiv_homLevelMap_app`: restriction along `ψ`
  composes a level structure with `ψ`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

variable {B : Scheme.{u}}

namespace ModuliProblem

variable (B) (A : Type) [Group A]

/-- **The moduli problem of homomorphisms `A →* E(S)` satisfying `p`** over `Ell/B`, for a
condition `p` stable under base change of points. Its level structures on an object `(E/S)` of
`Ell/B` are the homomorphisms `A →* E(S)` satisfying `p` (`homLevelEquiv`), and they pull back
along an arrow of `Ell/B` by base change of points (`homLevelEquiv_map`). The group `A` lies in
`Type`, as the groups `(ℤ/Nℤ)ʳ` of level structures do, so that the level structures lie in the
universe `Type (u + 1)` of moduli problems. -/
noncomputable def homLevel
    (p : ∀ X : EllObj B, (A →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)) → Prop)
    (hp : ∀ {X Y : EllObj B} {φ} (f : X ⟶ Y), p Y φ →
      p X ((EllipticCurveGeom.pointsPullback f.isPullback f.zero_total).comp φ)) :
    ModuliProblem B where
  obj X := ULift.{u + 1}
    {φ : A →* (𝟙_ (Over X.unop.base) ⟶ Over.mk X.unop.curve.structureMap) // p X.unop φ}
  map f := TypeCat.ofHom fun α ↦
    ⟨⟨(EllipticCurveGeom.pointsPullback f.unop.isPullback f.unop.zero_total).comp α.down.1,
      hp f.unop α.down.2⟩⟩
  map_id X := by
    ext α a
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm
  map_comp f g := by
    ext α a
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm

variable {B A}
  {p : ∀ X : EllObj B, (A →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)) → Prop}
  {hp : ∀ {X Y : EllObj B} {φ} (f : X ⟶ Y), p Y φ →
    p X ((EllipticCurveGeom.pointsPullback f.isPullback f.zero_total).comp φ)}

/-- The level structures of `homLevel B A p hp` on an object `(E/S)` of `Ell/B` are the
homomorphisms `A →* E(S)` satisfying `p`. Unification cannot recover the proof `hp` from the type
of a level structure, by proof irrelevance, so instances of `homLevel` pass it by name. -/
noncomputable def homLevelEquiv (X : EllObj B) :
    (homLevel B A p hp).obj (op X) ≃
      {φ : A →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap) // p X φ} :=
  Equiv.ulift

/-- The pull-back of a level structure of `homLevel B A p hp` along an arrow `f` of `Ell/B` is its
composite with base change of points along `f`. -/
@[simp]
theorem homLevelEquiv_map {X Y : EllObj B} (f : X ⟶ Y) (α : (homLevel B A p hp).obj (op Y)) :
    (homLevelEquiv X ((homLevel B A p hp).map f.op α)).1 =
      (EllipticCurveGeom.pointsPullback f.isPullback f.zero_total).comp (homLevelEquiv Y α).1 :=
  (rfl)

section Map

variable {A' : Type} [Group A']
  {p' : ∀ X : EllObj B, (A' →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)) → Prop}
  {hp' : ∀ {X Y : EllObj B} {φ} (f : X ⟶ Y), p' Y φ →
    p' X ((EllipticCurveGeom.pointsPullback f.isPullback f.zero_total).comp φ)}

variable (B) in
/-- **Restriction of level structures.** A homomorphism `ψ : A' →* A` carrying homomorphisms
satisfying `p` to homomorphisms satisfying `p'` restricts level structures of `homLevel B A p hp`
to level structures of `homLevel B A' p' hp'`, `φ ↦ φ ∘ ψ`. -/
noncomputable def homLevelMap (ψ : A' →* A) (hψ : ∀ X φ, p X φ → p' X (φ.comp ψ)) :
    homLevel B A p hp ⟶ homLevel B A' p' hp' where
  app X := TypeCat.ofHom fun α ↦ ULift.up ⟨α.down.1.comp ψ, hψ _ _ α.down.2⟩

/-- Restriction along `ψ` composes a level structure with `ψ`. -/
@[simp]
theorem homLevelEquiv_homLevelMap_app (ψ : A' →* A) (hψ : ∀ X φ, p X φ → p' X (φ.comp ψ))
    (X : EllObj B) (α : (homLevel B A p hp).obj (op X)) :
    (homLevelEquiv X
      ((homLevelMap B ψ hψ : homLevel B A p hp ⟶ homLevel B A' p' hp').app (op X) α)).1 =
      (homLevelEquiv X α).1.comp ψ :=
  (rfl)

end Map

end ModuliProblem

end TauCeti.AlgebraicGeometry
