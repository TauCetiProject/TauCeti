/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.CategoryTheory.Action.Cartesian
public import TauCeti.CategoryTheory.Galois.Topology

/-!
# The monodromy equivalence for finite étale covers of a connected scheme

Let `S` be a connected scheme and `x : Spec Ω ⟶ S` a geometric point, with `Ω` separably closed.
Finite étale `S`-schemes form a Galois category with fibre functor `FiniteEtaleScheme.fiber x`
(`TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category`), so Mathlib's
`CategoryTheory.PreGaloisCategory.functorToContAction` is an equivalence from finite étale
`S`-schemes to finite sets with a continuous action of the étale fundamental group
`π₁(S, x) = Aut (fiber x)`. This file names that equivalence
(`TauCeti.FiniteEtaleScheme.monodromyEquivalence`) and develops the parts of the monodromy
correspondence that live on the side of covers (SGA 1, Exposé V, §§4–7):

* For any profinite group `G` with `PreGaloisCategory.IsFundamentalGroup (fiber x) G`, such as a
  Galois group or a chosen small model of `π₁(S, x)`, the same correspondence lands in finite
  continuous `G`-sets (`TauCeti.FiniteEtaleScheme.monodromyEquivalenceOfIsFundamentalGroup`),
  with `G` acting on each geometric fibre through its given action.
* Both categories are cartesian monoidal and the equivalence preserves finite products, so it
  carries group objects to group objects. Finite étale group schemes over `S` therefore correspond
  to finite groups with a continuous action of `π₁(S, x)` by automorphisms
  (`TauCeti.FiniteEtaleScheme.monodromyEquivalenceGrp`), and finite étale commutative group
  schemes to finite continuous `π₁(S, x)`-modules
  (`TauCeti.FiniteEtaleScheme.monodromyEquivalenceCommGrp`). This is the lisse monodromy
  correspondence for `ℤ`-coefficients on the side of the representing covers.
* An étale path `γ : fiber x ≅ fiber y` changes the base point: the monodromy functor at `y`,
  restricted along conjugation by `γ` (`CategoryTheory.Iso.continuousConjAut`), is isomorphic to
  the monodromy functor at `x`, with components the bijections `γ.app X` of geometric fibres
  (`TauCeti.FiniteEtaleScheme.monodromyEquivalenceChangeBasepoint`).

For the field case, with `Gal(Ω/K)` in place of `π₁`, see
`TauCeti.FiniteEtaleScheme.galoisEquivalence`. There `Gal(Ω/K)` is a fundamental group of the
fibre functor (`TauCeti.FiniteEtaleScheme.instIsFundamentalGroupFiber`), so
`continuousMulEquivAutFiber` identifies it with `π₁(Spec K, x)`.

## Main definitions

* `TauCeti.FiniteEtaleScheme.monodromyEquivalence x`:
  `FiniteEtaleScheme S ≌ ContAction FintypeCat (Aut (fiber x))` for connected `S`.
* `TauCeti.FiniteEtaleScheme.continuousMulEquivAutFiber x G`: `G ≃ₜ* Aut (fiber x)` for a
  fundamental group `G` of the fibre functor; `g` acts on each fibre by `g` (`toAut_hom_app_apply`).
* `TauCeti.FiniteEtaleScheme.monodromyEquivalenceOfIsFundamentalGroup x G`: the monodromy
  equivalence with such a `G` in place of `Aut (fiber x)`.
* `TauCeti.FiniteEtaleScheme.monodromyEquivalenceGrp x` and
  `TauCeti.FiniteEtaleScheme.monodromyEquivalenceCommGrp x`: the induced equivalences of group
  objects and of commutative group objects.
* `TauCeti.FiniteEtaleScheme.monodromyEquivalenceChangeBasepoint γ`: change of base point along
  an étale path `γ`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
* H. W. Lenstra, *Galois theory for schemes*, Section 3.
* The Stacks Project, Section 58.6 (tag 0BND), *Fundamental groups of schemes*.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory FintypeCatDiscrete

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} [ConnectedSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **The monodromy equivalence.** For a connected scheme `S` and a geometric point
`x : Spec Ω ⟶ S`, finite étale `S`-schemes are equivalent to finite sets with a continuous action
of the étale fundamental group `Aut (fiber x)`. A cover `X` goes to its geometric fibre at `x`,
on which `Aut (fiber x)` acts by evaluation. -/
noncomputable def monodromyEquivalence (x : Spec (.of Ω) ⟶ S) :
    FiniteEtaleScheme S ≌ ContAction FintypeCat.{u} (Aut (fiber x)) :=
  (functorToContAction (fiber x)).asEquivalence

variable (x : Spec (.of Ω) ⟶ S)

/-- The finite continuous `Aut (fiber x)`-set attached to a finite étale `S`-scheme `X` has
underlying finite set the geometric fibre of `X` at `x`. -/
theorem monodromyEquivalence_functor_obj_obj_V (X : FiniteEtaleScheme S) :
    ((monodromyEquivalence x).functor.obj X).obj.V = (fiber x).obj X :=
  (rfl)

/-- An automorphism `σ` of the fibre functor acts on the geometric fibre of `X` by its component
at `X`. -/
theorem monodromyEquivalence_functor_obj_obj_ρ_apply (X : FiniteEtaleScheme S)
    (σ : Aut (fiber x)) (a : (fiber x).obj X) :
    (((monodromyEquivalence x).functor.obj X).obj.ρ σ).asHom a = σ.asIso.hom.app X a :=
  (rfl)

section FundamentalGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ X : FiniteEtaleScheme S, MulAction G ((fiber x).obj X)] [IsFundamentalGroup (fiber x) G]

/-- A fundamental group `G` of the geometric fibre functor at `x` is isomorphic, as a topological
group, to `Aut (fiber x)`, through its action on the geometric fibres. -/
noncomputable def continuousMulEquivAutFiber : G ≃ₜ* Aut (fiber x) where
  toMulEquiv := toAutMulEquiv _ _
  continuous_toFun := (toAutMulEquiv_isHomeomorph _ _).continuous
  continuous_invFun := (toAutMulEquiv_isHomeomorph _ _).homeomorph.symm.continuous

/-- **The monodromy equivalence for a fundamental group.** For a connected scheme `S`, a
geometric point `x` and a fundamental group `G` of the geometric fibre functor at `x` (for
instance a Galois group, or a small model of `Aut (fiber x)`), finite étale `S`-schemes are
equivalent to finite sets with a continuous action of `G`. -/
noncomputable def monodromyEquivalenceOfIsFundamentalGroup :
    FiniteEtaleScheme S ≌ ContAction FintypeCat.{u} G :=
  (monodromyEquivalence x).trans (ContAction.resEquiv _ (continuousMulEquivAutFiber x G))

/-- In `monodromyEquivalenceOfIsFundamentalGroup x G`, the finite `G`-set attached to a cover
`X` has underlying set the geometric fibre of `X` at `x`. -/
theorem monodromyEquivalenceOfIsFundamentalGroup_functor_obj_obj_V (X : FiniteEtaleScheme S) :
    ((monodromyEquivalenceOfIsFundamentalGroup x G).functor.obj X).obj.V = (fiber x).obj X :=
  (rfl)

end FundamentalGroup

section GroupObjects

/-- The functor of `monodromyEquivalence x` is monoidal for the cartesian monoidal structures, as
it preserves finite products. -/
noncomputable instance instMonoidalFunctorMonodromyEquivalence :
    (monodromyEquivalence x).functor.Monoidal :=
  .ofChosenFiniteProducts _

/-- The inverse of `monodromyEquivalence x` is monoidal for the cartesian monoidal structures, as
it preserves finite products. -/
noncomputable instance instMonoidalInverseMonodromyEquivalence :
    (monodromyEquivalence x).inverse.Monoidal :=
  .ofChosenFiniteProducts _

/-- The functor of `monodromyEquivalence x` is braided. -/
noncomputable instance instBraidedFunctorMonodromyEquivalence :
    (monodromyEquivalence x).functor.Braided :=
  .ofChosenFiniteProducts _

/-- The inverse of `monodromyEquivalence x` is braided. -/
noncomputable instance instBraidedInverseMonodromyEquivalence :
    (monodromyEquivalence x).inverse.Braided :=
  .ofChosenFiniteProducts _

/-- **Finite étale group schemes over a connected scheme are finite `π₁`-groups.** Group objects
in finite étale `S`-schemes are equivalent to group objects in finite continuous
`Aut (fiber x)`-sets, that is, to finite groups on which the étale fundamental group acts
continuously by group automorphisms. -/
noncomputable def monodromyEquivalenceGrp :
    Grp (FiniteEtaleScheme S) ≌ Grp (ContAction FintypeCat.{u} (Aut (fiber x))) :=
  (monodromyEquivalence x).mapGrp

/-- On underlying objects, `monodromyEquivalenceGrp x` is `monodromyEquivalence x`. -/
theorem monodromyEquivalenceGrp_functor_comp_forget :
    (monodromyEquivalenceGrp x).functor ⋙ Grp.forget _ =
      Grp.forget _ ⋙ (monodromyEquivalence x).functor :=
  (rfl)

/-- On underlying objects, the inverse of `monodromyEquivalenceGrp x` is the inverse of
`monodromyEquivalence x`. -/
theorem monodromyEquivalenceGrp_inverse_comp_forget :
    (monodromyEquivalenceGrp x).inverse ⋙ Grp.forget _ =
      Grp.forget _ ⋙ (monodromyEquivalence x).inverse :=
  (rfl)

/-- **Finite étale commutative group schemes over a connected scheme are finite `π₁`-modules.**
Commutative group objects in finite étale `S`-schemes are equivalent to commutative group objects
in finite continuous `Aut (fiber x)`-sets, that is, to finite abelian groups with a continuous
action of the étale fundamental group by automorphisms. -/
noncomputable def monodromyEquivalenceCommGrp :
    CommGrp (FiniteEtaleScheme S) ≌ CommGrp (ContAction FintypeCat.{u} (Aut (fiber x))) :=
  (monodromyEquivalence x).mapCommGrp

/-- On underlying objects, `monodromyEquivalenceCommGrp x` is `monodromyEquivalence x`. -/
theorem monodromyEquivalenceCommGrp_functor_comp_forget :
    (monodromyEquivalenceCommGrp x).functor ⋙ CommGrp.forget _ =
      CommGrp.forget _ ⋙ (monodromyEquivalence x).functor :=
  (rfl)

/-- On underlying objects, the inverse of `monodromyEquivalenceCommGrp x` is the inverse of
`monodromyEquivalence x`. -/
theorem monodromyEquivalenceCommGrp_inverse_comp_forget :
    (monodromyEquivalenceCommGrp x).inverse ⋙ CommGrp.forget _ =
      CommGrp.forget _ ⋙ (monodromyEquivalence x).inverse :=
  (rfl)

end GroupObjects

section ChangeBasepoint

variable {x} {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {y : Spec (.of Ω') ⟶ S}

/-- **Change of base point.** An étale path `γ : fiber x ≅ fiber y` identifies the monodromy
functor at `x` with the monodromy functor at `y` followed by restriction along conjugation by `γ`,
`Aut (fiber x) ≃ₜ* Aut (fiber y)`. The component at a cover `X` is the bijection `γ.app X` of
geometric fibres. -/
noncomputable def monodromyEquivalenceChangeBasepoint (γ : fiber x ≅ fiber y) :
    (monodromyEquivalence x).functor ≅
      (monodromyEquivalence y).functor ⋙
        ContAction.res _ (γ.continuousConjAut : Aut (fiber x) →ₜ* Aut (fiber y)) :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (Action.mkIso (γ.app X) fun σ ↦ by
      change σ.asIso.hom.app X ≫ γ.hom.app X =
        γ.hom.app X ≫ (γ.continuousConjAut σ).asIso.hom.app X
      simp [Iso.conjAut_apply]))
    fun f ↦ by
      ext : 2
      exact γ.hom.naturality f

/-- The component of `monodromyEquivalenceChangeBasepoint γ` at a cover `X` is `γ.app X` on the
geometric fibres. -/
theorem monodromyEquivalenceChangeBasepoint_hom_app_hom_hom (γ : fiber x ≅ fiber y)
    (X : FiniteEtaleScheme S) :
    ((monodromyEquivalenceChangeBasepoint γ).hom.app X).hom.hom = γ.hom.app X :=
  (rfl)

end ChangeBasepoint

end TauCeti.FiniteEtaleScheme
