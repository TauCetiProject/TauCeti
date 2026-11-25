/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Galois.GroupStalk
public import TauCeti.CategoryTheory.Sites.Point.TorsorStalk
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Torsor

/-!
# Stalks of torsors on finite continuous `G`-sets and continuous nonabelian `H¹`

Let `G` be a topological group and `𝒢` a sheaf of groups on the finite continuous `G`-sets
`ContAction FintypeCat G` with the jointly surjective topology. The stalk of `𝒢` at the point
`ContAction.point G` is a group with a smooth action of `G` by group automorphisms
(`ContAction.instMulDistribMulActionGrpStalk`, `ContAction.isOpen_stabilizer_grpStalk`). The stalk
of a `𝒢`-torsor `P` is a torsor under it
(`CategoryTheory.GrothendieckTopology.Point.instTorsorTorsorStalk`), and `G` acts on it by
translating the point, as on the stalk of any presheaf of sets (`ContAction.stalk`). On germs both
actions are explicit, `[a]_s • [p]_s = [a • p]_s` and `g • [p]_s = [p]_{g • s}`, so they satisfy
`g • (a • x) = (g • a) • (g • x)`, and the stabilizers of `G` are open. The stalk of `P` is
therefore a smooth torsor (`ContAction.torsorStalkSmoothTorsor`).

A morphism of `𝒢`-torsors induces a map of stalks commuting with both actions, so isomorphic
torsors have smooth torsor stalks with the same class in continuous nonabelian `H¹`. This gives the
map `ContAction.nonabelianH1ToStalk` from the classes of `𝒢`-torsors to `H¹(G, 𝒢_x)`, sending
the trivial torsor to the base point (`ContAction.nonabelianH1ToStalk_one`). Any topology on the
stalk can be used: the cocycle of a smooth torsor is locally constant.

## Main definitions

* `ContAction.torsorStalkSmoothTorsor P`: the stalk of a `𝒢`-torsor `P`, a smooth torsor under
  the stalk of `𝒢`.
* `ContAction.nonabelianH1ToStalk`: the map `Sheaf.NonabelianH1 𝒢 → H¹(G, 𝒢_x)` sending the class
  of a torsor to the class of its stalk.

## Main results

* `ContAction.smul_torsorStalk_smul`: the actions of `G` and of the stalk of `𝒢` on the stalk of a
  torsor are compatible.
* `ContAction.nonabelianH1ToStalk_mk`: the class of a torsor goes to the class of its stalk.
* `ContAction.nonabelianH1ToStalk_one`: the map sends the base point to the base point.
-/

public section

open CategoryTheory Opposite PreGaloisCategory FintypeCatDiscrete

universe u

namespace ContAction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {𝒢 : Sheaf (jointlySurjectiveTopology G) GrpCat.{u}} (P : Sheaf.Torsor 𝒢)

/-- `G` acts on the stalk of a torsor as on the stalk of its underlying sheaf of sets, by
translating the point. -/
noncomputable instance instMulActionTorsorStalk : MulAction G ((point G).TorsorStalk P) :=
  inferInstanceAs (MulAction G ((stalk G).obj P.sheaf.obj).V)

/-- `G` acts on germs of a torsor by translating the point. -/
@[simp]
theorem smul_toPresheafFiber_torsorStalk (g : G) (S : ContAction FintypeCat.{u} G)
    (s : (fiberFunctor G).obj S) (p : P.sheaf.obj.obj (op S)) :
    (g • (point G).toPresheafFiber S s P.sheaf.obj p : (point G).TorsorStalk P) =
      (point G).toPresheafFiber S (g • s) P.sheaf.obj p :=
  smul_germ P.sheaf.obj S s p g

/-- **The actions on the stalk of a torsor are compatible**: `g • (a • x) = (g • a) • (g • x)`
for `g : G`, `a` in the stalk of `𝒢` and `x` in the stalk of the torsor. -/
theorem smul_torsorStalk_smul (g : G) (a : (point G).GrpStalk 𝒢.obj)
    (x : (point G).TorsorStalk P) : g • a • x = (g • a) • g • x := by
  obtain ⟨X, s, b, c, rfl, rfl⟩ := (point G).exists_grpGerm_eq_toPresheafFiber_eq P a x
  rw [GrothendieckTopology.Point.grpGerm_smul_toPresheafFiber, smul_toPresheafFiber_torsorStalk,
    smul_grpGerm, smul_toPresheafFiber_torsorStalk,
    GrothendieckTopology.Point.grpGerm_smul_toPresheafFiber]

/-- The stabilizers of the action of `G` on the stalk of a torsor are open. -/
theorem isOpen_stabilizer_torsorStalk (x : (point G).TorsorStalk P) :
    IsOpen (MulAction.stabilizer G x : Set G) :=
  (Action.isSmooth_iff _).1 (isSmooth_stalk P.sheaf.obj) x

/-- **The stalk of a torsor is a smooth torsor** under the stalk of `𝒢`, with `G` acting by
translating the point. -/
@[expose, simps! carrier]
noncomputable def torsorStalkSmoothTorsor :
    TauCeti.NonabelianH1.SmoothTorsor.{u, u, u} G ((point G).GrpStalk 𝒢.obj) where
  carrier := (point G).TorsorStalk P
  smul_distrib_smul := smul_torsorStalk_smul P
  isOpen_stabilizer := isOpen_stabilizer_torsorStalk P

variable [TopologicalSpace ((point G).GrpStalk 𝒢.obj)]

variable (𝒢) in
/-- The map from the classes of `𝒢`-torsors to the continuous nonabelian `H¹` of `G` with
coefficients in the stalk of `𝒢`, sending the class of a torsor to the class of its stalk. -/
noncomputable def nonabelianH1ToStalk :
    Sheaf.NonabelianH1 𝒢 → TauCeti.NonabelianH1 G ((point G).GrpStalk 𝒢.obj) :=
  Sheaf.NonabelianH1.lift (fun P ↦ (torsorStalkSmoothTorsor P).cls) fun _ _ f ↦
    TauCeti.NonabelianH1.SmoothTorsor.cls_eq_cls_of_map ((point G).presheafFiber.map f.hom.hom)
      ((point G).presheafFiber_map_smul f) (presheafFiber_map_smul f.hom.hom)

/-- The class of a torsor goes to the class of its stalk. -/
@[simp]
theorem nonabelianH1ToStalk_mk (P : Sheaf.Torsor 𝒢) :
    nonabelianH1ToStalk 𝒢 (Sheaf.NonabelianH1.mk P) = (torsorStalkSmoothTorsor P).cls := by
  unfold nonabelianH1ToStalk
  exact Sheaf.NonabelianH1.lift_mk _ _ P

/-- The class of the trivial torsor goes to the base point. -/
@[simp]
theorem nonabelianH1ToStalk_one : nonabelianH1ToStalk 𝒢 1 = 1 := by
  rw [Sheaf.NonabelianH1.one_def, nonabelianH1ToStalk_mk,
    TauCeti.NonabelianH1.SmoothTorsor.cls_eq_one_iff]
  have := (point G).isCofiltered
  obtain ⟨e⟩ : Nonempty (point G).fiber.Elements := IsCofiltered.nonempty
  -- The germ of the unit section is fixed by `G`: at every point it is the unit of the stalk of
  -- `𝒢`.
  refine ⟨(point G).toPresheafFiber e.obj e.val (Sheaf.Torsor.trivial 𝒢).sheaf.obj
    (1 : 𝒢.obj.obj (op e.obj)), fun g ↦ ?_⟩
  refine (smul_toPresheafFiber_torsorStalk _ g e.obj e.val _).trans ?_
  rw [GrothendieckTopology.Point.toPresheafFiber_trivial,
    GrothendieckTopology.Point.toPresheafFiber_trivial, map_one, map_one]

end ContAction
