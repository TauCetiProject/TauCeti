/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.FixedPoints
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup

/-!
# Frobenius on every root subgroup of the Geck carrier

Every root subgroup of the Geck carrier is obtained by conjugating a numbered raising subgroup by
an integral Weyl-word representative. Since those representatives are defined over `ℤ`, Frobenius
fixes them. It consequently preserves the subgroup at every root and raises its parameter to the
corresponding prime-power exponent:

```text
Frob_{p^k}(x_{w αᵢ}(u)) = x_{w αᵢ}(u^{p^k}).
```

The fixed points in such a root subgroup are therefore exactly the elements whose parameters lie
in the Frobenius-fixed subring. The bundled map
`TauCeti.DynkinType.geckWeylRootSubgroupFixedPoints` realizes that copy of the additive group of
the fixed subring inside the fixed subgroup of the carrier.

## Main results

* `TauCeti.DynkinType.geckFrobenius_geckWeylWordPoint`: Frobenius fixes every integral Weyl-word
  representative.
* `TauCeti.DynkinType.geckFrobenius_geckWeylRootSubgroupPoints`: Frobenius preserves every root
  subgroup and raises its parameter.
* `TauCeti.DynkinType.geckWeylRootSubgroupPoints_mem_fixedSubgroup_geckFrobenius_iff`: a point in a
  root subgroup is Frobenius-fixed exactly when its parameter is.
* `TauCeti.DynkinType.geckWeylRootSubgroupFixedPoints`: the root subgroup over the fixed subring,
  as a subgroup of the Frobenius-fixed carrier points.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.
-/

public section

namespace TauCeti.DynkinType

universe v

noncomputable section

-- Matrices form a Lie ring through their commutator in the defining Geck representation.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat
-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid) (p k : ℕ)
variable (A : Type v) [CommRing A] [ExpChar A p]

/-- **Frobenius fixes every Weyl-word representative of the Geck carrier.** These points are
defined over `ℤ`, so functoriality along the `p ^ k`-power Frobenius leaves them unchanged. -/
@[simp]
theorem geckFrobenius_geckWeylWordPoint (l : List (Fin t.rank)) :
    t.geckFrobenius ht p k A (t.geckWeylWordPoint ht l A) =
      t.geckWeylWordPoint ht l A := by
  apply Subtype.ext
  rw [coe_geckFrobenius]
  have h := congrArg Subtype.val
    (t.map_geckWeylWordPoint ht (iterateFrobenius A p k) l)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  exact h

/-- **Frobenius raises the parameter of every root subgroup of the Geck carrier to its
`p ^ k`-th power.** The root `w αᵢ` itself is unchanged. -/
-- Not a `simp` lemma: the existing pointwise and map lemmas already prove it, so `simpNF` rejects
-- the annotation as a duplicate.
theorem geckFrobenius_geckWeylRootSubgroupPoints (l : List (Fin t.rank))
    (i : Fin t.rank) (u : Multiplicative A) :
    t.geckFrobenius ht p k A (t.geckWeylRootSubgroupPoints ht l i A u) =
      t.geckWeylRootSubgroupPoints ht l i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  apply Subtype.ext
  rw [coe_geckFrobenius]
  have h := congrArg Subtype.val
    (t.map_geckWeylRootSubgroupPoints ht (iterateFrobenius A p k) l i u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map, iterateFrobenius_def] at h
  exact h

/-- A point in a root subgroup of the Geck carrier is fixed by Frobenius exactly when its
parameter belongs to the Frobenius-fixed subring. -/
-- Not a `simp` lemma: simplification unfolds membership in `fixedSubgroup` first, so `simpNF`
-- rejects this left-hand side as non-normal.
theorem geckWeylRootSubgroupPoints_mem_fixedSubgroup_geckFrobenius_iff
    (l : List (Fin t.rank))
    (i : Fin t.rank) (u : Multiplicative A) :
    t.geckWeylRootSubgroupPoints ht l i A u ∈ fixedSubgroup (t.geckFrobenius ht p k A) ↔
      Multiplicative.toAdd u ∈ frobeniusFixedSubring A p k := by
  rw [TauCeti.mem_fixedSubgroup, t.geckFrobenius_geckWeylRootSubgroupPoints ht p k A]
  rw [(t.geckWeylRootSubgroupPoints_injective ht l i A).eq_iff,
    ← Multiplicative.toAdd.injective.eq_iff, toAdd_ofAdd, mem_frobeniusFixedSubring]

/-- **The root subgroup over the Frobenius-fixed subring**, embedded in the fixed points of the
Geck carrier. Its underlying point is `x_{w αᵢ}(u)` after including the parameter into `A`. -/
def geckWeylRootSubgroupFixedPoints (l : List (Fin t.rank)) (i : Fin t.rank) :
    Multiplicative (frobeniusFixedSubring A p k) →*
      fixedSubgroup (t.geckFrobenius ht p k A) :=
  (t.geckPointsMulEquivFixedSubgroupGeckFrobenius ht p k A).toMonoidHom.comp
    (t.geckWeylRootSubgroupPoints ht l i ↥(frobeniusFixedSubring A p k))

/-- The fixed-root-subgroup map is the original root-subgroup parametrization after including the
parameter from the Frobenius-fixed subring into `A`. -/
@[simp]
theorem coe_geckWeylRootSubgroupFixedPoints (l : List (Fin t.rank)) (i : Fin t.rank)
    (u : Multiplicative (frobeniusFixedSubring A p k)) :
    (t.geckWeylRootSubgroupFixedPoints ht p k A l i u : t.geckPoints ht A) =
      t.geckWeylRootSubgroupPoints ht l i A
        (Multiplicative.ofAdd
          ((Multiplicative.toAdd u : frobeniusFixedSubring A p k) : A)) := by
  rw [geckWeylRootSubgroupFixedPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  apply Subtype.ext
  rw [coe_geckPointsMulEquivFixedSubgroupGeckFrobenius]
  have h := congrArg Subtype.val
    (t.map_geckWeylRootSubgroupPoints ht (frobeniusFixedSubring A p k).subtype l i u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  exact h

/-- The parametrization of a root subgroup inside the Frobenius-fixed carrier is injective. -/
theorem geckWeylRootSubgroupFixedPoints_injective (l : List (Fin t.rank)) (i : Fin t.rank) :
    Function.Injective (t.geckWeylRootSubgroupFixedPoints ht p k A l i) :=
  (t.geckPointsMulEquivFixedSubgroupGeckFrobenius ht p k A).injective.comp
    (t.geckWeylRootSubgroupPoints_injective ht l i ↥(frobeniusFixedSubring A p k))

/-- **The fixed points in a Geck root subgroup are exactly its points over the Frobenius-fixed
subring.** This identifies the intersection inside the ambient carrier, not merely a one-sided
inclusion. -/
theorem map_subtype_range_geckWeylRootSubgroupFixedPoints_eq
    (l : List (Fin t.rank)) (i : Fin t.rank) :
    (t.geckWeylRootSubgroupFixedPoints ht p k A l i).range.map
        (fixedSubgroup (t.geckFrobenius ht p k A)).subtype =
      (t.geckWeylRootSubgroupPoints ht l i A).range ⊓
        fixedSubgroup (t.geckFrobenius ht p k A) := by
  ext g
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨⟨_, (t.coe_geckWeylRootSubgroupFixedPoints ht p k A l i u).symm⟩,
      (t.geckWeylRootSubgroupFixedPoints ht p k A l i u).2⟩
  · rintro ⟨⟨u, rfl⟩, hu⟩
    have hu' : Multiplicative.toAdd u ∈ frobeniusFixedSubring A p k :=
      (t.geckWeylRootSubgroupPoints_mem_fixedSubgroup_geckFrobenius_iff ht p k A l i u).mp hu
    let u' : Multiplicative (frobeniusFixedSubring A p k) :=
      Multiplicative.ofAdd ⟨Multiplicative.toAdd u, hu'⟩
    refine ⟨t.geckWeylRootSubgroupFixedPoints ht p k A l i u', ⟨u', rfl⟩, ?_⟩
    have hroot := t.coe_geckWeylRootSubgroupFixedPoints ht p k A l i u'
    rw [Subgroup.coe_subtype, hroot]
    simp only [u', toAdd_ofAdd, ofAdd_toAdd]

end

end TauCeti.DynkinType
