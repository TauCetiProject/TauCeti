/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor
public import TauCeti.CategoryTheory.Sites.Point.GrpStalk

/-!
# Stalks of torsors at a point of a site

Let `Φ` be a point of a site `(C, J)`, `G` a sheaf of groups and `P` a `G`-torsor. The stalk
`Φ.TorsorStalk P` of the sheaf of sets underlying `P` is a torsor under the group stalk
`Φ.GrpStalk G.obj` (`CategoryTheory.GrothendieckTopology.Point.instTorsorTorsorStalk`).

The action is defined on germs, `[g] • [p] = [g • p]` for sections `g` and `p` over the same
object (`CategoryTheory.GrothendieckTopology.Point.grpGerm_smul_torsorGerm`): the stalk of the
presheaf of pairs `U ↦ G(U) × P(U)` is the product of the two stalks
(`CategoryTheory.GrothendieckTopology.Point.pairsStalkEquiv`), because the indexing category of a
stalk is cofiltered, and the action is the map of stalks induced by the action map on pairs. The
action is free and transitive because it is so on sections, and the stalk is nonempty because `P`
has sections locally.

## Main definitions

* `CategoryTheory.Sheaf.Torsor.pairs P`: the presheaf of pairs `U ↦ G(U) × P(U)`, with its
  projections and the action map to `P`.
* `CategoryTheory.GrothendieckTopology.Point.TorsorStalk Φ P`: the stalk of a torsor.
* `CategoryTheory.GrothendieckTopology.Point.pairsStalkEquiv Φ P`: the stalk of the presheaf of
  pairs is the product of the stalks.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.grpGerm_smul_torsorGerm`: the action on germs.
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

/-- The presheaf of pairs `U ↦ G(U) × P(U)` of a section of `G` and a section of a `G`-torsor
`P`. -/
@[expose, simps]
def pairs : Cᵒᵖ ⥤ Type w where
  obj U := G.obj.obj U × P.sheaf.obj.obj U
  map f := ↾fun a ↦ (G.obj.map f a.1, P.sheaf.obj.map f a.2)

/-- A section of `G` and a section of `P` over the same object, as a section of `P.pairs`. -/
abbrev pairsMk {U : Cᵒᵖ} (g : G.obj.obj U) (p : P.sheaf.obj.obj U) : P.pairs.obj U :=
  (g, p)

/-- The first projection from the presheaf of pairs. -/
@[expose, simps]
def pairsFst : P.pairs ⟶ G.obj ⋙ forget GrpCat where
  app U := ↾fun a ↦ a.1

/-- The second projection from the presheaf of pairs. -/
@[expose, simps]
def pairsSnd : P.pairs ⟶ P.sheaf.obj where
  app U := ↾fun a ↦ a.2

/-- The action map `(g, p) ↦ g • p` from the presheaf of pairs to `P`. -/
@[expose, simps]
def pairsAct : P.pairs ⟶ P.sheaf.obj where
  app U := ↾fun a ↦ a.1 • a.2
  naturality U V f := by
    ext a
    exact (P.map_smul f a.1 a.2).symm

end CategoryTheory.Sheaf.Torsor

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {G : Sheaf J GrpCat.{w}} (P : Sheaf.Torsor G)

/-- Two points of the fibre functor of `Φ` both come from a single one. -/
theorem exists_fiber_map_eq_fiber_map_eq {X Y : C} (x : Φ.fiber.obj X) (y : Φ.fiber.obj Y) :
    ∃ (Z : C) (z : Φ.fiber.obj Z) (f : Z ⟶ X) (g : Z ⟶ Y),
      Φ.fiber.map f z = x ∧ Φ.fiber.map g z = y := by
  let a := Φ.fiber.elementsMk X x
  let b := Φ.fiber.elementsMk Y y
  exact ⟨(IsCofiltered.min a b).obj, (IsCofiltered.min a b).val, (IsCofiltered.minToLeft a b).hom,
    (IsCofiltered.minToRight a b).hom, (IsCofiltered.minToLeft a b).map_val,
    (IsCofiltered.minToRight a b).map_val⟩

/-- The stalk at `Φ` of the sheaf of sets underlying a torsor. -/
abbrev TorsorStalk : Type w := Φ.presheafFiber.obj P.sheaf.obj

/-- The germ at `x : Φ.fiber.obj X` of a section of a torsor over `X`. -/
noncomputable abbrev torsorGerm (X : C) (x : Φ.fiber.obj X) (p : P.sheaf.obj.obj (op X)) :
    Φ.TorsorStalk P :=
  Φ.toPresheafFiber X x P.sheaf.obj p

/-- The germ of a restriction is the germ at the image point. -/
theorem torsorGerm_map {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (a : P.sheaf.obj.obj (op Y)) :
    Φ.torsorGerm P X x (P.sheaf.obj.map f.op a) = Φ.torsorGerm P Y (Φ.fiber.map f x) a :=
  Φ.toPresheafFiber_w_apply f x P.sheaf.obj a

variable [LocallySmall.{w} C]

/-- Every element of the stalk of a torsor is a germ. -/
theorem exists_torsorGerm_eq (p : Φ.TorsorStalk P) :
    ∃ (X : C) (x : Φ.fiber.obj X) (a : P.sheaf.obj.obj (op X)), Φ.torsorGerm P X x a = p :=
  Φ.toPresheafFiber_jointly_surjective (P := P.sheaf.obj) p

/-- The map from the stalk of the presheaf of pairs to the product of the stalks. -/
noncomputable def pairsStalkToProd :
    Φ.presheafFiber.obj P.pairs → Φ.GrpStalk G.obj × Φ.TorsorStalk P :=
  fun q ↦ (Φ.presheafFiber.map P.pairsFst q, Φ.presheafFiber.map P.pairsSnd q)

/-- On germs, `pairsStalkToProd` takes the germs of the two components. -/
theorem pairsStalkToProd_germ (X : C) (x : Φ.fiber.obj X) (a : P.pairs.obj (op X)) :
    Φ.pairsStalkToProd P (Φ.toPresheafFiber X x P.pairs a) =
      (Φ.grpGerm G.obj X x a.1, Φ.torsorGerm P X x a.2) := by
  simp only [pairsStalkToProd, toPresheafFiber_naturality_apply, grpGerm_apply]
  rfl

/-- The map from the stalk of the presheaf of pairs to the product of the stalks is bijective,
because the indexing category of the stalk is cofiltered. -/
theorem pairsStalkToProd_bijective : Function.Bijective (Φ.pairsStalkToProd P) := by
  constructor
  · intro q₁ q₂ h
    obtain ⟨X, x, a, b, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ (P := P.pairs) q₁ q₂
    rw [pairsStalkToProd_germ, pairsStalkToProd_germ, Prod.mk.injEq] at h
    obtain ⟨Y, f, y, rfl, hf⟩ := (Φ.grpGerm_eq_iff' G.obj X x a.1 b.1).1 h.1
    have h₂ : Φ.torsorGerm P Y y (P.sheaf.obj.map f.op a.2) =
        Φ.torsorGerm P Y y (P.sheaf.obj.map f.op b.2) := by
      rw [torsorGerm_map, torsorGerm_map]
      exact h.2
    obtain ⟨Z, g, z, rfl, hg⟩ := (Φ.toPresheafFiber_eq_iff' Y y _ _).1 h₂
    rw [← Φ.toPresheafFiber_w_apply f, ← Φ.toPresheafFiber_w_apply f,
      ← Φ.toPresheafFiber_w_apply g, ← Φ.toPresheafFiber_w_apply g]
    congr 1
    exact Prod.ext (congrArg (G.obj.map g.op) hf) hg
  · rintro ⟨g, p⟩
    obtain ⟨X, x, a, rfl⟩ := Φ.exists_grpGerm_eq G.obj g
    obtain ⟨Y, y, b, rfl⟩ := Φ.exists_torsorGerm_eq P p
    obtain ⟨Z, z, f₁, f₂, rfl, rfl⟩ := Φ.exists_fiber_map_eq_fiber_map_eq x y
    refine ⟨Φ.toPresheafFiber Z z P.pairs (P.pairsMk (G.obj.map f₁.op a) (P.sheaf.obj.map f₂.op b)),
      ?_⟩
    rw [pairsStalkToProd_germ, grpGerm_map, torsorGerm_map]

/-- **The stalk of the presheaf of pairs is the product of the stalks** of `G` and of `P`. -/
noncomputable def pairsStalkEquiv :
    Φ.presheafFiber.obj P.pairs ≃ Φ.GrpStalk G.obj × Φ.TorsorStalk P :=
  Equiv.ofBijective _ (Φ.pairsStalkToProd_bijective P)

/-- The action of the stalk of `G` on the stalk of a `G`-torsor, induced by the action map on
pairs. -/
noncomputable instance : SMul (Φ.GrpStalk G.obj) (Φ.TorsorStalk P) where
  smul g p := Φ.presheafFiber.map P.pairsAct ((Φ.pairsStalkEquiv P).symm (g, p))

/-- **The action on germs**: `[g] • [p] = [g • p]`. -/
theorem grpGerm_smul_torsorGerm (X : C) (x : Φ.fiber.obj X) (g : G.obj.obj (op X))
    (p : P.sheaf.obj.obj (op X)) :
    Φ.grpGerm G.obj X x g • Φ.torsorGerm P X x p = Φ.torsorGerm P X x (g • p) := by
  have : (Φ.pairsStalkEquiv P).symm (Φ.grpGerm G.obj X x g, Φ.torsorGerm P X x p) =
      Φ.toPresheafFiber X x P.pairs (P.pairsMk g p) :=
    (Φ.pairsStalkEquiv P).symm_apply_eq.2 (Φ.pairsStalkToProd_germ P X x (P.pairsMk g p)).symm
  change Φ.presheafFiber.map P.pairsAct _ = _
  rw [this, toPresheafFiber_naturality_apply]
  rfl

/-- An element of the stalk of `G` and two elements of the stalk of `P` are germs over a common
object. -/
theorem exists_germs_eq (g : Φ.GrpStalk G.obj) (p q : Φ.TorsorStalk P) :
    ∃ (X : C) (x : Φ.fiber.obj X) (a : G.obj.obj (op X)) (b c : P.sheaf.obj.obj (op X)),
      Φ.grpGerm G.obj X x a = g ∧ Φ.torsorGerm P X x b = p ∧ Φ.torsorGerm P X x c = q := by
  obtain ⟨X, x, a, rfl⟩ := Φ.exists_grpGerm_eq G.obj g
  obtain ⟨Y, y, b, c, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ (P := P.sheaf.obj) p q
  obtain ⟨Z, z, f₁, f₂, rfl, rfl⟩ := Φ.exists_fiber_map_eq_fiber_map_eq x y
  exact ⟨Z, z, G.obj.map f₁.op a, P.sheaf.obj.map f₂.op b, P.sheaf.obj.map f₂.op c,
    Φ.grpGerm_map G.obj f₁ z a, Φ.torsorGerm_map P f₂ z b, Φ.torsorGerm_map P f₂ z c⟩

/-- The stalk of `G` acts on the stalk of a `G`-torsor. -/
noncomputable instance instMulActionTorsorStalk : MulAction (Φ.GrpStalk G.obj) (Φ.TorsorStalk P)
    where
  one_smul p := by
    obtain ⟨X, x, a, rfl⟩ := Φ.exists_torsorGerm_eq P p
    rw [← map_one (Φ.grpGerm G.obj X x), grpGerm_smul_torsorGerm, one_smul]
  mul_smul g h p := by
    obtain ⟨X, x, a, b, rfl, rfl⟩ := Φ.exists_grpGerm_eq₂ G.obj g h
    obtain ⟨Y, y, c, rfl⟩ := Φ.exists_torsorGerm_eq P p
    obtain ⟨Z, z, f₁, f₂, rfl, rfl⟩ := Φ.exists_fiber_map_eq_fiber_map_eq x y
    rw [← grpGerm_map, ← grpGerm_map, ← torsorGerm_map, ← map_mul, grpGerm_smul_torsorGerm,
      grpGerm_smul_torsorGerm, grpGerm_smul_torsorGerm, mul_smul]

/-- The action on the stalk of a torsor is free. -/
theorem smul_left_injective_torsorStalk (p : Φ.TorsorStalk P) :
    Function.Injective fun g : Φ.GrpStalk G.obj ↦ g • p := by
  intro g h hgh
  obtain ⟨X, x, a, b, rfl, rfl⟩ := Φ.exists_grpGerm_eq₂ G.obj g h
  obtain ⟨Y, y, c, rfl⟩ := Φ.exists_torsorGerm_eq P p
  obtain ⟨Z, z, f₁, f₂, rfl, rfl⟩ := Φ.exists_fiber_map_eq_fiber_map_eq x y
  simp only [← grpGerm_map, ← torsorGerm_map, grpGerm_smul_torsorGerm] at hgh ⊢
  obtain ⟨W, f, w, rfl, hf⟩ := (Φ.toPresheafFiber_eq_iff' Z z _ _).1 hgh
  rw [← Φ.grpGerm_map G.obj f w, ← Φ.grpGerm_map G.obj f w]
  congr 1
  apply P.smul_left_injective (P.sheaf.obj.map f.op (P.sheaf.obj.map f₂.op c))
  simpa only [P.map_smul] using hf

/-- The action on the stalk of a torsor is transitive. -/
theorem exists_smul_eq_torsorStalk (p q : Φ.TorsorStalk P) :
    ∃ g : Φ.GrpStalk G.obj, g • q = p := by
  obtain ⟨X, x, -, b, c, -, rfl, rfl⟩ := Φ.exists_germs_eq P 1 p q
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (G.obj.obj (op X)) c b
  exact ⟨Φ.grpGerm G.obj X x a, by rw [grpGerm_smul_torsorGerm, ha]⟩

omit [LocallySmall.{w} C] in
/-- The stalk of a torsor is nonempty, since a torsor has sections locally. -/
theorem nonempty_torsorStalk : Nonempty (Φ.TorsorStalk P) := by
  obtain ⟨e⟩ : Nonempty Φ.fiber.Elements := IsCofiltered.nonempty
  obtain ⟨Y, f, ⟨i, ⟨g⟩⟩, y, -⟩ := Φ.jointly_surjective _ (P.coversTop e.obj) e.val
  obtain ⟨s⟩ := i.property
  exact ⟨Φ.torsorGerm P Y y (P.sheaf.obj.map g.op s)⟩

/-- **The stalk of a `G`-torsor is a torsor under the stalk of `G`.** -/
noncomputable instance instTorsorTorsorStalk : Torsor (Φ.GrpStalk G.obj) (Φ.TorsorStalk P) where
  nonempty := Φ.nonempty_torsorStalk P
  sdiv p q := (Φ.exists_smul_eq_torsorStalk P p q).choose
  sdiv_smul' p q := (Φ.exists_smul_eq_torsorStalk P p q).choose_spec
  smul_sdiv' g p := Φ.smul_left_injective_torsorStalk P p
    (Φ.exists_smul_eq_torsorStalk P (g • p) p).choose_spec

end CategoryTheory.GrothendieckTopology.Point
