/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.RepresentationTheory.WeightSpace

/-!
# The level subalgebra of a group algebra

For a representation `ρ` of a group `G` on an `A`-module `M` and a subgroup `K ≤ G`, the elements
of the group algebra `A[G]` whose action `ρ.asAlgebraHom a` preserves the `K`-fixed submodule
`Representation.weightSpace (ρ.comp K.subtype) 1` form a subalgebra `TauCeti.levelAlgebra ρ K`,
acting on the `K`-fixed submodule via `TauCeti.levelAction ρ K`. Taking the intersection over all
representations of `G` on `A`-modules in `Type u` gives the universal level algebra
`TauCeti.universalLevelAlgebra A K`.

## Main definitions

* `TauCeti.levelAlgebra`: the subalgebra of `A[G]` preserving the `K`-fixed vectors of `ρ`.
* `TauCeti.levelAction`: the algebra homomorphism from `levelAlgebra ρ K` to the endomorphisms of
  the `K`-fixed vectors.
* `TauCeti.universalLevelAlgebra`: the intersection of `levelAlgebra ρ K` over all representations
  of `G` on `A`-modules in `Type u`.

## Main results

* `TauCeti.asAlgebraHom_mapDomain`: pushing an element of `A[H]` forward along `f : H →* G` acts
  by the restricted representation `ρ.comp f`.
* `TauCeti.mem_levelAlgebra_iff`, `TauCeti.mem_universalLevelAlgebra_iff`,
  `TauCeti.universalLevelAlgebra_le`.

## References

* Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0),
  `src/Lib/Adelic/TraceFormula/LevelAlgebra.lean` (`New.asAlgebraHom_mapDomain`,
  `New.levelAlgebra`, `New.levelAction`, `New.universalLevelAlgebra`,
  `New.universalLevelAlgebra_le`).
-/

public section

noncomputable section

open MonoidAlgebra

namespace TauCeti

universe u

variable {A G M : Type*} [CommSemiring A] [Group G] [AddCommMonoid M] [Module A M]
  (ρ : Representation A G M) (K : Subgroup G)

/-- Pushing an element of `A[H]` forward along `f : H →* G` and acting via `ρ` agrees with the
action of the restricted representation `ρ.comp f`. -/
theorem asAlgebraHom_mapDomain {H : Type*} [Group H] (f : H →* G) (a : MonoidAlgebra A H) :
    ρ.asAlgebraHom (mapDomain f a) = Representation.asAlgebraHom (ρ.comp f) a := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp [mapDomain_add, ha, hb]
  | single h c => simp

/-- The subalgebra of `A[G]` consisting of elements that map `K`-fixed vectors of `ρ` to `K`-fixed
vectors. -/
def levelAlgebra : Subalgebra A (MonoidAlgebra A G) where
  carrier := {a | ∀ y ∈ Representation.weightSpace (ρ.comp K.subtype) 1,
    ρ.asAlgebraHom a y ∈ Representation.weightSpace (ρ.comp K.subtype) 1}
  mul_mem' {a b} ha hb y hy := by
    simpa using ha _ (hb y hy)
  add_mem' {a b} ha hb y hy := by
    simpa using add_mem (ha y hy) (hb y hy)
  algebraMap_mem' c y hy := by
    simpa using Submodule.smul_mem _ c hy

/-- Membership in `levelAlgebra ρ K`. -/
@[simp]
theorem mem_levelAlgebra_iff {ρ : Representation A G M} {K : Subgroup G}
    {a : MonoidAlgebra A G} :
    a ∈ levelAlgebra ρ K ↔
      ∀ y ∈ Representation.weightSpace (ρ.comp K.subtype) 1,
        ρ.asAlgebraHom a y ∈ Representation.weightSpace (ρ.comp K.subtype) 1 :=
  Iff.rfl

/-- The action of `levelAlgebra ρ K` on the `K`-fixed vectors of `ρ`. -/
def levelAction :
    levelAlgebra ρ K →ₐ[A] Module.End A (Representation.weightSpace (ρ.comp K.subtype) 1) where
  toFun a := (ρ.asAlgebraHom a).restrict a.property
  map_one' := by simp [LinearMap.ext_iff, Subtype.ext_iff]
  map_mul' a b := by
    ext y
    exact LinearMap.congr_fun (map_mul ρ.asAlgebraHom a.val b.val) y
  map_zero' := by simp [LinearMap.ext_iff, Subtype.ext_iff]
  map_add' a b := by
    ext y
    exact LinearMap.congr_fun (map_add ρ.asAlgebraHom a.val b.val) y
  commutes' c := by
    ext y
    simp

/-- The elements of `A[G]` that preserve the `K`-fixed vectors in every representation of `G` on
an `A`-module in `Type u`. -/
def universalLevelAlgebra (A : Type*) [CommSemiring A] {G : Type*} [Group G] (K : Subgroup G) :
    Subalgebra A (MonoidAlgebra A G) :=
  ⨅ (M : Type u) (_ : AddCommMonoid M) (_ : Module A M) (ρ : Representation A G M),
    levelAlgebra ρ K

/-- Membership in `universalLevelAlgebra A K`. -/
theorem mem_universalLevelAlgebra_iff {A G : Type*} [CommSemiring A] [Group G] {K : Subgroup G}
    {a : MonoidAlgebra A G} :
    a ∈ universalLevelAlgebra.{u} A K ↔
      ∀ (M : Type u) [AddCommMonoid M] [Module A M] (ρ : Representation A G M),
        a ∈ levelAlgebra ρ K := by
  simp only [universalLevelAlgebra, Algebra.mem_iInf]

/-- For every representation `ρ` of `G` on an `A`-module in `Type u`, `universalLevelAlgebra A K`
is contained in `levelAlgebra ρ K`. -/
theorem universalLevelAlgebra_le {A G : Type*} [CommSemiring A] [Group G] {K : Subgroup G}
    {M : Type u} [AddCommMonoid M] [Module A M] (ρ : Representation A G M) :
    universalLevelAlgebra.{u} A K ≤ levelAlgebra ρ K :=
  fun _ ha ↦ mem_universalLevelAlgebra_iff.mp ha M ρ

end TauCeti

end
