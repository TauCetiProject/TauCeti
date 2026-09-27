/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Exact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Functor

import all TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Functor

/-!
# Exactness of the smooth discrete coinduction functor

For a closed subgroup of a profinite group, the functor `coindFunctor` sends a short exact
sequence of smooth discrete representations to a short exact sequence. Exactness is expressed
on the underlying modules: the first map is injective, the second is surjective, and the range
of the first is the kernel of the second. This is the functorial form of the coefficient-level
exactness in `ContCohomology.DiscreteShortExact.coind`.

This exactness supplies the coinduced coefficient sequences used in continuous Shapiro's lemma
and dimension shifting. See Ribes–Zalesskii, *Profinite Groups*, Theorem 6.10.5.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v r

variable (R : Type r) [Ring R] [TopologicalSpace R]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (U : Subgroup G)
  {A B C : SmoothDiscreteTopRep.{r, u, v} R U}

/-- Smooth discrete coinduction preserves short exact sequences of representations: its mapped
inclusion is injective, its mapped projection is surjective, and the maps are exact in the middle.
The subgroup need only be closed; finite index is not required. -/
theorem coindFunctor_map_shortExact (hU : IsClosed (U : Set G))
    (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Injective f.hom.hom) (hg : Function.Surjective g.hom.hom)
    (hex : Function.Exact f.hom.hom g.hom.hom) :
    Function.Injective (((coindFunctor R G U).map f).hom.hom) ∧
    Function.Surjective (((coindFunctor R G U).map g).hom.hom) ∧
    Function.Exact (((coindFunctor R G U).map f).hom.hom)
      (((coindFunctor R G U).map g).hom.hom) := by
  let A' := (ofSmoothDiscrete R U).obj A
  let B' := (ofSmoothDiscrete R U).obj B
  let C' := (ofSmoothDiscrete R U).obj C
  let f' := (ofSmoothDiscrete R U).map f
  let g' := (ofSmoothDiscrete R U).map g
  let S : ContCohomology.DiscreteShortExact U A'.V B'.V C'.V := {
    incl := f'.toLinearMap.toAddMonoidHom
    proj := g'.toLinearMap.toAddMonoidHom
    incl_equivariant := DiscreteRep.equivariant f'
    proj_equivariant := DiscreteRep.equivariant g'
    incl_injective := hf
    proj_surjective := hg
    exact := hex }
  let T := S.coind U hU
  -- `S.coind` is opaque outside its defining module. Its public pointwise lemmas identify its
  -- arrows with those of `DiscreteCoind.map`; the `change` steps only remove the additive-map
  -- wrappers left by the structure literals.
  have hi : T.incl = (DiscreteCoind.map f'.toLinearMap
      (DiscreteRep.equivariant f')).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro a
    apply DiscreteCoind.ext
    intro x
    rw [ContCohomology.DiscreteShortExact.coind_incl_apply]
    change S.incl (a x) = f'.toLinearMap (a x)
    rfl
  have hp : T.proj = (DiscreteCoind.map g'.toLinearMap
      (DiscreteRep.equivariant g')).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro b
    apply DiscreteCoind.ext
    intro x
    rw [ContCohomology.DiscreteShortExact.coind_proj_apply]
    change S.proj (b x) = g'.toLinearMap (b x)
    rfl
  -- The composite definition of `coindFunctor` reduces its mapped arrows to the same
  -- `DiscreteCoind.map` arrows. The statements below use those canonical coordinates.
  constructor
  · change Function.Injective (DiscreteCoind.map f'.toLinearMap
        (DiscreteRep.equivariant f'))
    simpa [hi] using T.incl_injective
  constructor
  · change Function.Surjective (DiscreteCoind.map g'.toLinearMap
        (DiscreteRep.equivariant g'))
    simpa [hp] using T.proj_surjective
  · change Function.Exact (DiscreteCoind.map f'.toLinearMap
        (DiscreteRep.equivariant f')) (DiscreteCoind.map g'.toLinearMap
        (DiscreteRep.equivariant g'))
    simpa [hi, hp] using T.exact

end TauCeti
