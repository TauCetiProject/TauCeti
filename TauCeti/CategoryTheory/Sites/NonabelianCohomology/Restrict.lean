/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Pullback

/-!
# Restriction of torsors along a cocontinuous functor

Let `u : C ⥤ D` be a functor between sites `(C, J)` and `(D, K)` that is continuous and
cocontinuous, and let `G` be a sheaf of groups on `D`. The restriction `u_* Q` of a `G`-torsor
`Q`, with the action of the restricted sheaf of groups `u_* G`, is a `u_* G`-torsor
(`CategoryTheory.Sheaf.Torsor.restrict J u Q`): it is locally nonempty because `u` is cocontinuous.
This gives a map `NonabelianH1.restrict J u : H¹(G) → H¹(u_* G)`.

When `u` is moreover representably flat, so that it defines a morphism of sites, restriction is
inverse to the pullback of torsors along the unit morphism `u_* G ⟶ u_* G`
(`CategoryTheory.Sheaf.NonabelianH1.pullback`): the class of a torsor is determined by its
restriction (`NonabelianH1.restrictEquiv J u G : H¹(G) ≃ H¹(u_* G)`). This applies to the inclusion
of a dense subsite, and to an equivalence of sites.

## Main declarations

* `CategoryTheory.Sheaf.Torsor.restrict J u Q`: the restriction of the `G`-torsor `Q`.
* `CategoryTheory.Sheaf.NonabelianH1.restrict J u`: the induced map `H¹(G) → H¹(u_* G)`.
* `CategoryTheory.Sheaf.NonabelianH1.restrictEquiv J u G`: for `u` moreover representably flat, the
  bijection `H¹(G) ≃ H¹(u_* G)`, inverse to `NonabelianH1.pullback (𝟙 (u_* G))`.

## References

* [The Stacks project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG), for
  torsors under a sheaf of groups and their classes.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K] {G : Sheaf K GrpCat.{w}}

namespace Torsor

/-- The restriction `u_* Q` of a `G`-torsor `Q` along a continuous and cocontinuous functor `u`,
a torsor under `u_* G`: over `U` its sections are those of `Q` over `u(U)`, with the action of
`G(u(U))`. It is locally nonempty because `u` is cocontinuous. -/
@[expose]
def restrict (Q : Torsor G) : Torsor ((u.sheafPushforwardContinuous GrpCat.{w} J K).obj G) where
  sheaf := (u.sheafPushforwardContinuous (Type w) J K).obj Q.sheaf
  mulAction U := Q.mulAction (u.op.obj U)
  map_smul _ _ f g p := Q.map_smul (u.op.map f) g p
  coversTop X := by
    refine J.superset_covering ?_ (u.cover_lift J K (Q.coversTop (u.obj X)))
    rintro Y f ⟨⟨W, ⟨q⟩⟩, ⟨a⟩⟩
    exact ⟨⟨Y, ⟨Q.sheaf.obj.map a.op q⟩⟩, ⟨𝟙 Y⟩⟩
  bijective U := Q.bijective (u.op.obj U)

@[simp]
lemma restrict_sheaf (Q : Torsor G) :
    (Q.restrict J u).sheaf = (u.sheafPushforwardContinuous (Type w) J K).obj Q.sheaf :=
  rfl

/-- The restriction of a morphism of `G`-torsors. -/
def restrictMap {Q R : Torsor G} (f : Q ⟶ R) : Q.restrict J u ⟶ R.restrict J u where
  hom := (u.sheafPushforwardContinuous (Type w) J K).map f.hom
  map_smul U g p := f.map_smul (u.op.obj U) g p

end Torsor

namespace NonabelianH1

/-- The map `H¹(G) → H¹(u_* G)` sending the class of a `G`-torsor to the class of its restriction
along a continuous and cocontinuous functor `u`. -/
@[expose]
def restrict :
    NonabelianH1 G → NonabelianH1 ((u.sheafPushforwardContinuous GrpCat.{w} J K).obj G) :=
  lift (fun Q ↦ mk (Q.restrict J u)) fun _ _ f ↦ mk_eq_mk_of_hom (Torsor.restrictMap J u f)

@[simp]
lemma restrict_mk (Q : Torsor G) : restrict J u (mk Q) = mk (Q.restrict J u) :=
  lift_mk _ _ Q

variable [RepresentablyFlat u] [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)]

/-- Pulling back the restriction of a `G`-torsor `Q` along the identity of `u_* G` gives back the
class of `Q`: the identity of `u_* Q` is equivariant. -/
lemma pullback_restrict (x : NonabelianH1 G) :
    pullback (𝟙 ((u.sheafPushforwardContinuous GrpCat.{w} J K).obj G)) (restrict J u x) = x := by
  induction x using NonabelianH1.ind with
  | h Q =>
    rw [restrict_mk]
    exact pullback_mk_eq_mk (𝟙 _) fun _ _ _ ↦ rfl

/-- Restricting the pullback of a `u_* G`-torsor `P` along the identity of `u_* G` gives back the
class of `P`, through the equivariant morphism `P ⟶ u_* (P.pullback (𝟙 _))`. -/
lemma restrict_pullback
    (x : NonabelianH1 ((u.sheafPushforwardContinuous GrpCat.{w} J K).obj G)) :
    restrict J u (pullback (𝟙 ((u.sheafPushforwardContinuous GrpCat.{w} J K).obj G)) x) = x := by
  induction x using NonabelianH1.ind with
  | h P =>
    rw [pullback_mk, restrict_mk]
    exact (mk_eq_mk_of_hom ⟨P.toPullback _, fun U g p ↦ P.toPullback_smul _ g p⟩).symm

variable (G) in
/-- For a continuous, cocontinuous and representably flat functor `u`, restriction of torsors is a
bijection `H¹(G) ≃ H¹(u_* G)`, with inverse the pullback along the identity of `u_* G`. -/
@[expose]
def restrictEquiv :
    NonabelianH1 G ≃ NonabelianH1 ((u.sheafPushforwardContinuous GrpCat.{w} J K).obj G) where
  toFun := restrict J u
  invFun := pullback (𝟙 _)
  left_inv := pullback_restrict J u
  right_inv := restrict_pullback J u

@[simp]
lemma restrictEquiv_apply (x : NonabelianH1 G) : restrictEquiv J u G x = restrict J u x :=
  rfl

@[simp]
lemma restrictEquiv_symm_apply
    (x : NonabelianH1 ((u.sheafPushforwardContinuous GrpCat.{w} J K).obj G)) :
    (restrictEquiv J u G).symm x = pullback (𝟙 _) x :=
  rfl

end NonabelianH1

end CategoryTheory.Sheaf
