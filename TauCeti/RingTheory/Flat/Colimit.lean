/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Category.Ring.FilteredColimits
import TauCeti.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Filtered colimits and flatness

A small filtered colimit of flat modules is flat (Stacks, Lemma 10.39.3 (05UU)). The proof uses
the equational criterion for flatness: a relation `∑ fᵢ xᵢ = 0` in the colimit comes from a
relation at some stage, because finitely many elements and the vanishing of one element are
witnessed at a common stage of a filtered diagram. Flatness of that stage makes the relation
trivial there, and the trivialization maps to the colimit.

The same criterion applies when the base ring, rather than the module, is a filtered colimit
`B = colim Bⱼ` of commutative rings: a `B`-module `C` is flat as soon as it is flat over every
`Bⱼ`. A relation `∑ bᵢ xᵢ = 0` in `C` has its finitely many coefficients `bᵢ` at a common stage
`Bⱼ`, where it is trivial, and the trivialization maps to `B`.

Dually, a filtered colimit `colim Cⱼ` of commutative `R`-algebras is flat over `R` as soon as every
`Cⱼ` is: a relation `∑ rᵢ xᵢ = 0` with coefficients in `R` holds at some stage `Cⱼ`, where it is
trivial.

## Main results

* `Module.Flat.of_isColimit`: the point of a colimit cocone of a small filtered diagram of flat
  modules is flat.
* `RingHom.Flat.of_isColimit`: a ring homomorphism out of the point of a colimit cocone of a small
  filtered diagram of commutative rings is flat if its composite with every leg is flat.
* `RingHom.Flat.of_isColimit_codomain`: a ring homomorphism into the point of a colimit cocone of a
  small filtered diagram of commutative rings is flat if it is induced by compatible flat ring
  homomorphisms into the stages.

## References

* [Stacks Project, Tag 05UU](https://stacks.math.columbia.edu/tag/05UU)
-/

public section

open CategoryTheory Limits

universe u

namespace Module.Flat

variable {R : Type u} [CommRing R]

/-- A small filtered colimit of flat modules is flat. -/
@[stacks 05UU]
theorem of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ ModuleCat.{u} R}
    [∀ j, Module.Flat R (F.obj j)] {c : Cocone F} (hc : IsColimit c) : Module.Flat R c.pt := by
  refine of_forall_isTrivialRelation fun {l f x} hfx => ?_
  -- The finitely many elements `x i` come from a common stage `k`.
  obtain ⟨k, y', hy'⟩ := Concrete.isColimit_exists_rep_fin F hc x
  -- The relation holds at stage `k` up to an element dying in the colimit, so it holds at a
  -- later stage `m`.
  have h0 : c.ι.app k (∑ i, f i • y' i) = c.ι.app k 0 := by
    simp only [map_sum, map_smul, map_zero, hy', hfx]
  obtain ⟨m, g, g', hg⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ h0
  have hrel : ∑ i, f i • F.map g (y' i) = 0 := by
    simpa only [map_sum, map_smul, map_zero] using hg
  -- Flatness of the stage `m` trivializes the relation, and the trivialization maps to the
  -- colimit.
  obtain ⟨n, a, z, hz, ha⟩ := isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨n, a, fun t => c.ι.app m (z t), fun i => ?_, ha⟩
  have hi := congrArg (c.ι.app m) (hz i)
  simp only [map_sum, map_smul] at hi
  rw [← hi, ← hy' i, ← c.w g, ConcreteCategory.comp_apply]

end Module.Flat

namespace RingHom.Flat

/-- Let `c` be a colimit cocone of a small filtered diagram of commutative rings. A ring
homomorphism out of its point is flat as soon as its composite with every leg is flat. -/
theorem of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
    {c : Cocone F} (hc : IsColimit c) {C : Type*} [CommRing C] (g : c.pt →+* C)
    (hg : ∀ j, (g.comp (c.ι.app j).hom).Flat) : g.Flat := by
  algebraize [g]
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx => ?_
  -- The finitely many coefficients `f i` come from a common stage `k`.
  obtain ⟨k, y', hy'⟩ := Concrete.isColimit_exists_rep_fin F hc f
  -- Over the stage `k`, the relation has coefficients `y' i`, and flatness trivializes it.
  let := (g.comp (c.ι.app k).hom).toAlgebra
  have : Module.Flat (F.obj k) C := hg k
  have hrel : ∑ i, y' i • x i = 0 := by
    simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hy'] using hfx
  obtain ⟨n, a, z, hz, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨n, fun i t => c.ι.app k (a i t), z, fun i => ?_, fun t => ?_⟩
  · simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hz i
  · simpa [hy'] using congrArg (c.ι.app k) (ha t)

/-- Let `c` be a colimit cocone of a small filtered diagram `F` of commutative rings, and let
`ψ j : R →+* F.obj j` be ring homomorphisms compatible with the transition maps of `F`. If every
`ψ j` is flat, then so is the ring homomorphism `R →+* c.pt` they induce: a filtered colimit of
flat `R`-algebras is flat over `R`. -/
@[stacks 05UU]
theorem of_isColimit_codomain {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c) {R : Type*} [CommRing R]
    (g : R →+* c.pt) (ψ : ∀ j, R →+* F.obj j)
    (hψ : ∀ {j k : J} (t : j ⟶ k), (F.map t).hom.comp (ψ j) = ψ k)
    (hg : ∀ j, (c.ι.app j).hom.comp (ψ j) = g) (hflat : ∀ j, (ψ j).Flat) : g.Flat := by
  algebraize [g]
  have hι (j : J) (r : R) : c.ι.app j (ψ j r) = g r := congr($(hg j) r)
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx => ?_
  -- The finitely many elements `x i` come from a common stage `k`.
  obtain ⟨k, y', hy'⟩ := Concrete.isColimit_exists_rep_fin F hc x
  -- The relation holds at stage `k` up to an element dying in the colimit, so it holds at a
  -- later stage `m`.
  have h0 : c.ι.app k (∑ i, ψ k (f i) * y' i) = c.ι.app k 0 := by
    simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hι, hy'] using hfx
  obtain ⟨m, t, t', ht⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ h0
  let := (ψ m).toAlgebra
  have : Module.Flat R (F.obj m) := hflat m
  have hm (r : R) : F.map t (ψ k r) = ψ m r := congr($(hψ t) r)
  have hrel : ∑ i, f i • F.map t (y' i) = 0 := by
    simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hm] using ht
  -- Flatness of the stage `m` trivializes the relation, and the trivialization maps to the
  -- colimit.
  obtain ⟨n, a, z, hz, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨n, a, fun s => c.ι.app m (z s), fun i => ?_, ha⟩
  have hi := congrArg (c.ι.app m) (hz i)
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, map_mul, hι] at hi ⊢
  rw [← hi, ← hy' i, ← c.w t, ConcreteCategory.comp_apply]

end RingHom.Flat
