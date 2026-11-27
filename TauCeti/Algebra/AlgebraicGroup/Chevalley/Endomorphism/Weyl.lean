/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Weyl conjugation as a standard endomorphism

Conjugation by any pinned simple Weyl representative (`isStandardEndomorphism_conj_weylElement`)
over any commutative ring, and conjugation by any element of `D.weylSubgroup K` over a field
(`isStandardEndomorphism_conj_weylSubgroup`), are standard endomorphisms. Over a nontrivial
commutative ring, conjugation by a pinned simple Weyl representative is never based
(`not_isBasedEndomorphism_conj_weylElement`).

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.isStandardEndomorphism_conj_weylElement`: conjugation by a
  pinned simple Weyl representative is standard over every commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.isStandardEndomorphism_conj_weylSubgroup`: conjugation by
  any element of `D.weylSubgroup K` is standard over every field.
* `TauCeti.DynkinType.ChevalleyDatum.not_isBasedEndomorphism_conj_weylElement`: conjugation by a
  pinned simple Weyl representative is never based over a nontrivial commutative ring.

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  §§1.15–1.17.
-/

public section

open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type v) [CommRing A]

/-- Conjugation by a pinned simple Weyl representative is a standard endomorphism over every
commutative ring. -/
theorem isStandardEndomorphism_conj_weylElement (i : Fin t.rank) :
    D.IsStandardEndomorphism A
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom :=
  isStandardEndomorphism_iff.mpr fun α => by
    refine ⟨(t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) α, ?_⟩
    let ε : Aˣ := Units.map (Int.castRingHom A).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i) α)
    refine MonoidHom.map_range_eq_range_of_comp_eq _ _ _
      ((ofAdd.surjective.comp (Units.mulLeft_bijective ε).surjective).comp toAdd.surjective)
      fun u => ?_
    simpa [ε, MulAut.conj_apply] using D.weylElement_conj_rootSubgroupPoints i α A (toAdd u)

/-- Conjugation by any element of the Weyl subgroup is a standard endomorphism over every field. -/
theorem isStandardEndomorphism_conj_weylSubgroup (K : Type v) [Field K] (g : D.weylSubgroup K) :
    D.IsStandardEndomorphism K (MulAut.conj (g : D.points K)).toMonoidHom :=
  isStandardEndomorphism_iff.mpr fun α =>
    ⟨(t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) α,
      D.map_range_rootSubgroupPoints_conj K g α⟩

/-- Conjugation by a pinned simple Weyl representative is never based over a nontrivial ring:
it sends the `i`-th positive simple root subgroup to its opposite negative root subgroup. -/
theorem not_isBasedEndomorphism_conj_weylElement [Nontrivial A] (i : Fin t.rank) :
    ¬ D.IsBasedEndomorphism A
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom := fun hbased => by
  have hB := (isBasedEndomorphism_iff_map_borelSubgroup_le_of_isCharacterMap
    (D.isStandardEndomorphism_conj_weylElement A i)
    (D.isCharacterMap_conj_weylElement i A)).mp hbased
  obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup A i
  exact hb (hB ⟨b.val, b.property, rfl⟩)

end TauCeti.DynkinType.ChevalleyDatum
