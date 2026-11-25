/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor
public import TauCeti.CategoryTheory.Sites.Point.Basic
public import TauCeti.CategoryTheory.Sites.Point.GrpStalk

/-!
# Stalks of torsors at a point of a site

Let `Φ` be a point of a site `(C, J)`, `G` a sheaf of groups and `P` a `G`-torsor. The stalk
`Φ.TorsorStalk P` of the sheaf of sets underlying `P` is a torsor under the group stalk
`Φ.GrpStalk G.obj` (`CategoryTheory.GrothendieckTopology.Point.instTorsorTorsorStalk`).

The action is defined on germs, `[g] • [p] = [g • p]` for sections `g` and `p` over the same
object (`CategoryTheory.GrothendieckTopology.Point.grpGerm_smul_toPresheafFiber`): the stalk of
the presheaf of pairs `U ↦ G(U) × P(U)` (Mathlib's `CategoryTheory.FunctorToTypes.prod`) is the
product of the two stalks (`CategoryTheory.GrothendieckTopology.Point.presheafFiberProdEquiv`),
and the action is the map of stalks induced by the action map on pairs. The action is free and
transitive because it is so on sections, and the stalk is nonempty because `P` has sections
locally.

## Main definitions

* `CategoryTheory.Sheaf.Torsor.pairsAct P`: the action map from the presheaf of pairs
  `U ↦ G(U) × P(U)` to `P`.
* `CategoryTheory.GrothendieckTopology.Point.TorsorStalk Φ P`: the stalk of a torsor.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.grpGerm_smul_toPresheafFiber`: the action on germs.
* `CategoryTheory.GrothendieckTopology.Point.instTorsorTorsorStalk`: the stalk of a `G`-torsor
  is a torsor under the stalk of `G`.

## References

* [The Stacks project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG), torsors
  on a site.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Sheaf J GrpCat.{w}}
  (P : Torsor G)

/-- The action map `(g, p) ↦ g • p` from the presheaf of pairs `U ↦ G(U) × P(U)` to `P`. -/
@[expose, simps]
def pairsAct : FunctorToTypes.prod (G.obj ⋙ forget GrpCat) P.sheaf.obj ⟶ P.sheaf.obj where
  app U := ↾fun a : G.obj.obj U × P.sheaf.obj.obj U ↦ a.1 • a.2
  naturality U V f := by
    ext a
    exact (P.map_smul f a.1 a.2).symm

end CategoryTheory.Sheaf.Torsor

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {G : Sheaf J GrpCat.{w}} (P : Sheaf.Torsor G)

/-- The stalk at `Φ` of the sheaf of sets underlying a torsor. -/
abbrev TorsorStalk : Type w := Φ.presheafFiber.obj P.sheaf.obj

variable [LocallySmall.{w} C]

/-- The action of the stalk of `G` on the stalk of a `G`-torsor, induced by the action map on
pairs. -/
noncomputable instance : SMul (Φ.GrpStalk G.obj) (Φ.TorsorStalk P) where
  smul g p := Φ.presheafFiber.map P.pairsAct
    ((Φ.presheafFiberProdEquiv (G.obj ⋙ forget GrpCat) P.sheaf.obj).symm (g, p))

/-- The action on the stalk of a torsor is the map of stalks induced by the action map on pairs,
through the identification of the stalk of pairs with the product of the stalks. -/
theorem smul_torsorStalk_def (g : Φ.GrpStalk G.obj) (p : Φ.TorsorStalk P) :
    g • p = Φ.presheafFiber.map P.pairsAct
      ((Φ.presheafFiberProdEquiv (G.obj ⋙ forget GrpCat) P.sheaf.obj).symm (g, p)) :=
  rfl

/-- **The action on germs**: `[g] • [p] = [g • p]`. -/
@[simp]
theorem grpGerm_smul_toPresheafFiber (X : C) (x : Φ.fiber.obj X) (g : G.obj.obj (op X))
    (p : P.sheaf.obj.obj (op X)) :
    Φ.grpGerm G.obj X x g • Φ.toPresheafFiber X x P.sheaf.obj p =
      Φ.toPresheafFiber X x P.sheaf.obj (g • p) := by
  let a : (FunctorToTypes.prod (G.obj ⋙ forget GrpCat) P.sheaf.obj).obj (op X) := (g, p)
  have : (Φ.presheafFiberProdEquiv (G.obj ⋙ forget GrpCat) P.sheaf.obj).symm
      (Φ.toPresheafFiber X x (G.obj ⋙ forget GrpCat) g, Φ.toPresheafFiber X x P.sheaf.obj p) =
        Φ.toPresheafFiber X x (FunctorToTypes.prod (G.obj ⋙ forget GrpCat) P.sheaf.obj) a :=
    (Equiv.symm_apply_eq _).2
      (Φ.presheafFiberProdEquiv_toPresheafFiber (G.obj ⋙ forget GrpCat) P.sheaf.obj X x a).symm
  rw [smul_torsorStalk_def, grpGerm_apply, this, toPresheafFiber_naturality_apply,
    Sheaf.Torsor.pairsAct_app]
  exact congrArg _ (TypeCat.ofHom_apply _ a)

/-- The stalk of `G` acts on the stalk of a `G`-torsor. -/
noncomputable instance instMulActionTorsorStalk : MulAction (Φ.GrpStalk G.obj) (Φ.TorsorStalk P)
    where
  one_smul p := by
    obtain ⟨X, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := P.sheaf.obj) p
    rw [← map_one (Φ.grpGerm G.obj X x), grpGerm_smul_toPresheafFiber, one_smul]
  mul_smul g h p := by
    obtain ⟨X, x, a, b, rfl, rfl⟩ := Φ.exists_grpGerm_eq₂ G.obj g h
    obtain ⟨Y, y, c, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := P.sheaf.obj) p
    obtain ⟨Z, z, f₁, f₂, rfl, rfl⟩ := Φ.exists_fiber_map_eq_fiber_map_eq x y
    rw [← grpGerm_map, ← grpGerm_map, ← toPresheafFiber_w_apply, ← map_mul,
      grpGerm_smul_toPresheafFiber, grpGerm_smul_toPresheafFiber, grpGerm_smul_toPresheafFiber,
      mul_smul]

/-- The action on the stalk of a torsor is free. -/
theorem smul_left_injective_torsorStalk (p : Φ.TorsorStalk P) :
    Function.Injective fun g : Φ.GrpStalk G.obj ↦ g • p := by
  intro g h hgh
  obtain ⟨X, x, a, b, rfl, rfl⟩ := Φ.exists_grpGerm_eq₂ G.obj g h
  obtain ⟨Y, y, c, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := P.sheaf.obj) p
  obtain ⟨Z, z, f₁, f₂, rfl, rfl⟩ := Φ.exists_fiber_map_eq_fiber_map_eq x y
  simp only [← grpGerm_map, ← toPresheafFiber_w_apply, grpGerm_smul_toPresheafFiber] at hgh ⊢
  obtain ⟨W, f, w, rfl, hf⟩ := (Φ.toPresheafFiber_eq_iff' Z z _ _).1 hgh
  rw [← Φ.grpGerm_map G.obj f w, ← Φ.grpGerm_map G.obj f w]
  congr 1
  apply P.smul_left_injective (P.sheaf.obj.map f.op (P.sheaf.obj.map f₂.op c))
  simpa only [P.map_smul] using hf

/-- The action on the stalk of a torsor is transitive. -/
theorem exists_smul_eq_torsorStalk (p q : Φ.TorsorStalk P) :
    ∃ g : Φ.GrpStalk G.obj, g • q = p := by
  obtain ⟨X, x, b, c, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ (P := P.sheaf.obj) p q
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (G.obj.obj (op X)) c b
  exact ⟨Φ.grpGerm G.obj X x a, by rw [grpGerm_smul_toPresheafFiber, ha]⟩

omit [LocallySmall.{w} C] in
/-- The stalk of a torsor is nonempty, since a torsor has sections locally. -/
theorem nonempty_torsorStalk : Nonempty (Φ.TorsorStalk P) := by
  obtain ⟨e⟩ : Nonempty Φ.fiber.Elements := IsCofiltered.nonempty
  obtain ⟨Y, f, ⟨i, ⟨g⟩⟩, y, -⟩ := Φ.jointly_surjective _ (P.coversTop e.obj) e.val
  obtain ⟨s⟩ := i.property
  exact ⟨Φ.toPresheafFiber Y y P.sheaf.obj (P.sheaf.obj.map g.op s)⟩

/-- **The stalk of a `G`-torsor is a torsor under the stalk of `G`.** -/
noncomputable instance instTorsorTorsorStalk : Torsor (Φ.GrpStalk G.obj) (Φ.TorsorStalk P) where
  nonempty := Φ.nonempty_torsorStalk P
  sdiv p q := (Φ.exists_smul_eq_torsorStalk P p q).choose
  sdiv_smul' p q := (Φ.exists_smul_eq_torsorStalk P p q).choose_spec
  smul_sdiv' g p := Φ.smul_left_injective_torsorStalk P p
    (Φ.exists_smul_eq_torsorStalk P (g • p) p).choose_spec

end CategoryTheory.GrothendieckTopology.Point
