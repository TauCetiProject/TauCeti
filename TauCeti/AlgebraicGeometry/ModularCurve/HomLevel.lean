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
* `TauCeti.AlgebraicGeometry.ModuliProblem.homLevelAction`: the right action of automorphisms
  of the source group, for a condition invariant under precomposition.

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

/-- Two morphisms into `homLevel` agree if their underlying homomorphisms agree on every
level structure. -/
@[ext]
theorem homLevel_hom_ext {P : ModuliProblem B} {f g : P ⟶ homLevel B A p hp}
    (h : ∀ (X : EllObj B) (α : P.obj (op X)),
      (homLevelEquiv X (f.app (op X) α)).1 = (homLevelEquiv X (g.app (op X) α)).1) :
    f = g := by
  ext X α
  exact (homLevelEquiv X.unop).injective (Subtype.ext (h X.unop α))

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

section Action

variable (B A)
  (hσ : ∀ (X : EllObj B) φ (σ : MulAut A), p X φ → p X (φ.comp σ.toMonoidHom))

/-- The right action of automorphisms of `A` on level structures whose condition is invariant
under precomposition. An automorphism `σ` sends a homomorphism `φ` to `φ ∘ σ`. -/
noncomputable def homLevelAction : (MulAut A)ᵐᵒᵖ →* Aut (homLevel B A p hp) where
  toFun σ := Aut.of
    { hom := homLevelMap B σ.unop.toMonoidHom fun X φ h ↦ hσ X φ σ.unop h
      inv := homLevelMap B σ.unop.symm.toMonoidHom fun X φ h ↦ hσ X φ σ.unop.symm h
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp }
  map_one' := by
    apply Aut.ext
    rw [Aut.one_asIso]
    apply Iso.ext
    refine homLevel_hom_ext fun X α ↦ MonoidHom.ext fun a ↦ ?_
    simp
  map_mul' σ τ := by
    apply Aut.ext
    rw [Aut.mul_asIso]
    apply Iso.ext
    refine homLevel_hom_ext fun X α ↦ MonoidHom.ext fun a ↦ ?_
    simp

variable {B A}

/-- The action of `σ` precomposes a level structure with `σ`. -/
@[simp]
theorem homLevelEquiv_homLevelAction_hom_app (σ : (MulAut A)ᵐᵒᵖ) (X : EllObj B)
    (α : (homLevel B A p hp).obj (op X)) :
    (homLevelEquiv X ((homLevelAction B A hσ σ).asIso.hom.app (op X) α)).1 =
      (homLevelEquiv X α).1.comp σ.unop.toMonoidHom :=
  homLevelEquiv_homLevelMap_app _ (fun X φ h ↦ hσ X φ σ.unop h) X α

/-- The inverse action precomposes a level structure with `σ⁻¹`. -/
@[simp]
theorem homLevelEquiv_homLevelAction_inv_app (σ : (MulAut A)ᵐᵒᵖ) (X : EllObj B)
    (α : (homLevel B A p hp).obj (op X)) :
    (homLevelEquiv X ((homLevelAction B A hσ σ).asIso.inv.app (op X) α)).1 =
      (homLevelEquiv X α).1.comp σ.unop.symm.toMonoidHom :=
  homLevelEquiv_homLevelMap_app _ (fun X φ h ↦ hσ X φ σ.unop.symm h) X α

end Action

end ModuliProblem

end TauCeti.AlgebraicGeometry
