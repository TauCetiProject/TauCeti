/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.CategoryTheory.Action.Cartesian
public import TauCeti.CategoryTheory.Galois.Equivalence

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
  continuous `G`-sets, with `G` acting on each geometric fibre through its given action. This is
  the general `CategoryTheory.PreGaloisCategory.functorToContActionEquivOfIsFundamentalGroup`
  applied to the fibre functor `fiber x`: it restricts along the isomorphism of topological groups
  `G ≃ₜ* Aut (fiber x)` of `CategoryTheory.PreGaloisCategory.toAutContinuousMulEquiv`, and its
  simp lemmas apply directly.
* Both categories are cartesian monoidal and the equivalence preserves finite products, so it
  carries group objects to group objects. Finite étale group schemes over `S` therefore correspond
  to finite groups with a continuous action of `π₁(S, x)` by automorphisms
  (`TauCeti.FiniteEtaleScheme.monodromyEquivalenceGrp`), and finite étale commutative group
  schemes to finite continuous `π₁(S, x)`-modules
  (`TauCeti.FiniteEtaleScheme.monodromyEquivalenceCommGrp`). This is the lisse monodromy
  correspondence for `ℤ`-coefficients on the side of the representing covers. The construction
  follows the field case, `TauCeti.FiniteEtaleScheme.galoisEquivalenceGrp` and
  `TauCeti.FiniteEtaleScheme.galoisEquivalenceCommGrp` in
  `TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Basic`, applying Mathlib's
  `CategoryTheory.Equivalence.mapGrp` and `CategoryTheory.Equivalence.mapCommGrp`.
* An étale path `γ : fiber x ≅ fiber y` changes the base point: the monodromy functor at `y`,
  restricted along conjugation by `γ` (`CategoryTheory.Iso.continuousConjAut`), is isomorphic to
  the monodromy functor at `x`, with components the bijections `γ.app X` of geometric fibres. This
  is the general `CategoryTheory.Iso.functorToContActionIso γ` for fibre functors, since
  `(monodromyEquivalence x).functor` is `functorToContAction (fiber x)`
  (`TauCeti.FiniteEtaleScheme.monodromyEquivalence_functor`).

For the field case, with `Gal(Ω/K)` in place of `π₁`, see
`TauCeti.FiniteEtaleScheme.galoisEquivalence`. There `Gal(Ω/K)` is a fundamental group of the
fibre functor (`TauCeti.FiniteEtaleScheme.instIsFundamentalGroupFiber`), so
`toAutContinuousMulEquiv` identifies it with `π₁(Spec K, x)`.

## Main definitions

* `TauCeti.FiniteEtaleScheme.monodromyEquivalence x`:
  `FiniteEtaleScheme S ≌ ContAction FintypeCat (Aut (fiber x))` for connected `S`.
* `TauCeti.FiniteEtaleScheme.monodromyEquivalenceGrp x` and
  `TauCeti.FiniteEtaleScheme.monodromyEquivalenceCommGrp x`: the induced equivalences of group
  objects and of commutative group objects.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
* H. W. Lenstra, *Galois theory for schemes*, Section 3.
* The Stacks Project, Section 58.6 (tag 0BND), *Fundamental groups of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory FintypeCatDiscrete

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} [ConnectedSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **The monodromy equivalence.** For a connected scheme `S` and a geometric point
`x : Spec Ω ⟶ S`, finite étale `S`-schemes are equivalent to finite sets with a continuous action
of the étale fundamental group `Aut (fiber x)`. A cover `X` goes to its geometric fibre at `x`,
on which `Aut (fiber x)` acts by evaluation. -/
@[expose] noncomputable def monodromyEquivalence (x : Spec (.of Ω) ⟶ S) :
    FiniteEtaleScheme S ≌ ContAction FintypeCat.{u} (Aut (fiber x)) :=
  (functorToContAction (fiber x)).asEquivalence

variable (x : Spec (.of Ω) ⟶ S)

/-- The functor of `monodromyEquivalence x` is Mathlib's `functorToContAction` for the geometric
fibre functor at `x`, so general facts about `functorToContAction` (such as the change of base
point `CategoryTheory.Iso.functorToContActionIso`) apply to it. -/
theorem monodromyEquivalence_functor :
    (monodromyEquivalence x).functor = functorToContAction (fiber x) :=
  (rfl)

/-- The finite continuous `Aut (fiber x)`-set attached to a finite étale `S`-scheme `X` has
underlying finite set the geometric fibre of `X` at `x`. -/
@[simp]
theorem monodromyEquivalence_functor_obj_obj_V (X : FiniteEtaleScheme S) :
    ((monodromyEquivalence x).functor.obj X).obj.V = (fiber x).obj X :=
  (rfl)

/-- An automorphism `σ` of the fibre functor acts on the geometric fibre of `X` by its component
at `X`. -/
@[simp]
theorem monodromyEquivalence_functor_obj_obj_ρ_apply (X : FiniteEtaleScheme S)
    (σ : Aut (fiber x)) (a : (fiber x).obj X) :
    (((monodromyEquivalence x).functor.obj X).obj.ρ σ).asHom a = σ.asIso.hom.app X a :=
  (rfl)

/-- On a morphism of covers, the functor of `monodromyEquivalence x` is the induced map of
geometric fibres. -/
@[simp]
theorem monodromyEquivalence_functor_map_hom_hom {X Y : FiniteEtaleScheme S} (f : X ⟶ Y) :
    ((monodromyEquivalence x).functor.map f).hom.hom = (fiber x).map f :=
  (rfl)

section GroupObjects

/-- The functor of `monodromyEquivalence x` is braided, hence monoidal, for the cartesian monoidal
structures, as it preserves finite products. -/
noncomputable instance instBraidedFunctorMonodromyEquivalence :
    (monodromyEquivalence x).functor.Braided :=
  .ofChosenFiniteProducts _

/-- The inverse of `monodromyEquivalence x` is braided, hence monoidal, for the cartesian monoidal
structures, as it preserves finite products. -/
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
@[simp]
theorem monodromyEquivalenceGrp_functor_comp_forget :
    (monodromyEquivalenceGrp x).functor ⋙ Grp.forget _ =
      Grp.forget _ ⋙ (monodromyEquivalence x).functor :=
  (rfl)

/-- On underlying objects, the inverse of `monodromyEquivalenceGrp x` is the inverse of
`monodromyEquivalence x`. -/
@[simp]
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
@[simp]
theorem monodromyEquivalenceCommGrp_functor_comp_forget :
    (monodromyEquivalenceCommGrp x).functor ⋙ CommGrp.forget _ =
      CommGrp.forget _ ⋙ (monodromyEquivalence x).functor :=
  (rfl)

/-- On underlying objects, the inverse of `monodromyEquivalenceCommGrp x` is the inverse of
`monodromyEquivalence x`. -/
@[simp]
theorem monodromyEquivalenceCommGrp_inverse_comp_forget :
    (monodromyEquivalenceCommGrp x).inverse ⋙ CommGrp.forget _ =
      CommGrp.forget _ ⋙ (monodromyEquivalence x).inverse :=
  (rfl)

end GroupObjects

end TauCeti.FiniteEtaleScheme
