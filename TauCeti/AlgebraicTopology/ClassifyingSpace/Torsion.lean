/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Schreier
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.AlgebraicTopology.SerreClass.Torsion
public import TauCeti.RepresentationTheory.Homological.GroupHomology.LocallyFinite

/-!
# The homology of the classifying space of a locally finite group is torsion

Let `G` be a finite group. The singular homology of Milnor's classifying space `classifyingSpace G`
with coefficients in a commutative ring `k` is killed by the order of `G` in every positive degree:
`#G • x = 0` for `x ∈ Hₙ₊₁(BG; k)`
(`TauCeti.natCard_nsmul_classifyingSpace_singularHomology_eq_zero`). It vanishes when `#G` is a
unit of `k` (`TauCeti.subsingleton_classifyingSpace_singularHomology_of_isUnit_natCard`), for
instance with rational coefficients, or with coefficients in `𝔽₂` when `G` has odd order.

More generally, let `G` be locally finite, every finitely generated subgroup being finite
(`TauCeti.Group.IsLocallyFinite`). Then `Hₙ₊₁(BG; k)` is a torsion group
(`TauCeti.isAddTorsion_classifyingSpace_singularHomology`), and it vanishes when the order of every
element of `G` is a unit of `k`
(`TauCeti.subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_orderOf`).

These are transported from group homology, through the identification `Hₙ(BG; k) ≅ Hₙ(G, k)`
(`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`), where the order of a finite group
kills positive-degree homology because corestriction after transfer to the trivial subgroup is
multiplication by `#G` (`groupHomology.natCard_nsmul_eq_zero`), and where every class of a locally
finite group comes from a finite subgroup (`groupHomology.exists_finite_subgroup_map_eq`).

For an abelian group `A`, the classifying space `B(Multiplicative A)` is an Eilenberg--MacLane
space `K(A, 1)`. Serre's axiom on the homology of `K(A, 1)` for a class `C` of abelian groups asks
that `A ∈ C` imply `Hₙ₊₁(K(A, 1)) ∈ C`.

* For the class `AddCommGrpCat.isTorsion` of torsion groups it holds for every `A`
  (`TauCeti.isTorsion_classifyingSpace_singularHomology`): a torsion abelian group is locally
  finite.
* For the class `AddCommGrpCat.isKilledBySomePower d` it holds for finite `A`
  (`TauCeti.isKilledBySomePower_classifyingSpace_singularHomology`): the order of `A` then divides
  a power of `d`.

If the order of every element of `A` is a unit of `k`, then the positive-degree `k`-homology of
`K(A, 1)` vanishes
(`TauCeti.subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_addOrderOf`); for
instance the positive-degree mod-two homology of `K(A, 1)` vanishes for every abelian group `A`
all of whose elements have odd order.

## Main results

* `TauCeti.natCard_nsmul_classifyingSpace_singularHomology_eq_zero`: `#G` kills `Hₙ₊₁(BG; k)`.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_isUnit_natCard`: `Hₙ₊₁(BG; k) = 0`
  when `#G` is a unit of `k`.
* `TauCeti.isAddTorsion_classifyingSpace_singularHomology`: `Hₙ₊₁(BG; k)` is a torsion group for
  locally finite `G`.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_orderOf`:
  `Hₙ₊₁(BG; k) = 0` for locally finite `G` when the order of every element is a unit of `k`.
* `TauCeti.isTorsion_classifyingSpace_singularHomology`: if `A` is a torsion abelian group, so is
  `Hₙ₊₁(K(A, 1); k)`.
* `TauCeti.isKilledBySomePower_classifyingSpace_singularHomology`: if a finite abelian group `A`
  is annihilated by some power of `d`, so is `Hₙ₊₁(K(A, 1); k)`.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_addOrderOf`:
  `Hₙ₊₁(K(A, 1); k) = 0` when the order of every element of `A` is a unit of `k`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, Section 10.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

variable (k : Type u) [CommRing k]

section LocallyFinite

variable {G : Type u} [Group G] [Group.IsLocallyFinite G]

/-- **The positive-degree homology of the classifying space of a locally finite group is
torsion.** In particular this holds for finite groups and for torsion abelian groups. -/
theorem isAddTorsion_classifyingSpace_singularHomology (n : ℕ) :
    IsAddTorsion (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :=
  let e := (classifyingSpaceSingularHomologyIsoGroupHomology k G (n + 1)).toLinearEquiv.symm
  IsAddTorsion.of_surjective (f := e.toLinearMap.toAddMonoidHom) e.surjective
    (groupHomology.isAddTorsion_groupHomology_succ (Rep.trivial k G k) n)

/-- **The positive-degree homology of the classifying space of a locally finite group vanishes
when the orders of its elements are invertible**: `Hₙ₊₁(BG; k) = 0` when the order of every
element of `G` is a unit of `k`. -/
theorem subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_orderOf
    (h : ∀ g : G, IsUnit (orderOf g : k)) (n : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :=
  have := groupHomology.subsingleton_of_forall_isUnit_orderOf (Rep.trivial k G k) h n
  (classifyingSpaceSingularHomologyIsoGroupHomology k G (n + 1)).toLinearEquiv.toEquiv.subsingleton

end LocallyFinite

section Finite

variable {G : Type u} [Group G] [Finite G]

/-- **The order of a finite group kills the positive-degree homology of its classifying space**:
`#G • x = 0` for every `x ∈ Hₙ₊₁(BG; k)`. -/
theorem natCard_nsmul_classifyingSpace_singularHomology_eq_zero {n : ℕ}
    (x : ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :
    Nat.card G • x = 0 := by
  apply (classifyingSpaceSingularHomologyIsoGroupHomology k G (n + 1)).toLinearEquiv.injective
  rw [map_nsmul, groupHomology.natCard_nsmul_eq_zero, map_zero]

/-- **The positive-degree homology of the classifying space of a finite group vanishes when the
order of the group is a unit of the coefficients**: `Hₙ₊₁(BG; k) = 0` when `#G` is invertible
in `k`. -/
theorem subsingleton_classifyingSpace_singularHomology_of_isUnit_natCard
    (h : IsUnit (Nat.card G : k)) (n : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :=
  subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_orderOf k
    (isUnit_natCard_iff_forall_isUnit_orderOf.1 h) n

end Finite

/-- **Serre's `K(A, 1)` axiom for the torsion groups.** If `A` is a torsion abelian group, then so
is the positive-degree homology of the Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)`,
with coefficients in any commutative ring. -/
theorem isTorsion_classifyingSpace_singularHomology {A : AddCommGrpCat.{u}}
    (hA : AddCommGrpCat.isTorsion A) (n : ℕ) :
    AddCommGrpCat.isTorsion (AddCommGrpCat.of
      (((singularChains k).obj (TopCat.of (classifyingSpace (Multiplicative A)))).homology
        (n + 1))) :=
  have := Group.isLocallyFinite_multiplicative_iff.2 ((AddCommGrpCat.prop_isTorsion_iff A).1 hA)
  (AddCommGrpCat.prop_isTorsion_iff _).2 (isAddTorsion_classifyingSpace_singularHomology k n)

/-- **`K(A, 1)` is `k`-acyclic when the orders of the elements of `A` are invertible in `k`.** If
the order of every element of an abelian group `A` is a unit of `k`, then the positive-degree
`k`-homology of the Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)` vanishes:
`Hₙ₊₁(K(A, 1); k) = 0`. Over a nonzero ring the hypothesis forces `A` to be a torsion group. -/
theorem subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_addOrderOf
    {A : Type u} [AddCommGroup A] (h : ∀ a : A, IsUnit (addOrderOf a : k)) (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative A)))).homology (n + 1)) := by
  cases subsingleton_or_nontrivial k
  · exact Module.subsingleton k _
  -- over a nonzero ring the orders are nonzero, so `A` is torsion, hence locally finite
  have := Group.isLocallyFinite_multiplicative_iff.2 fun a ↦
    not_not.1 <| addOrderOf_eq_zero_iff.not.1 fun h0 ↦ (h a).ne_zero (by rw [h0, Nat.cast_zero])
  exact subsingleton_classifyingSpace_singularHomology_of_forall_isUnit_orderOf k
    (fun g ↦ orderOf_ofAdd_eq_addOrderOf g.toAdd ▸ h g.toAdd) n

/-- **Serre's `K(A, 1)` axiom for the groups annihilated by a power of `d`, for finite `A`.** If a
finite abelian group `A` is annihilated by some power of `d`, then so is the positive-degree
homology of the Eilenberg--MacLane space `K(A, 1) = B(Multiplicative A)`, with coefficients in
any commutative ring. -/
theorem isKilledBySomePower_classifyingSpace_singularHomology {d : ℕ} {A : AddCommGrpCat.{u}}
    [Finite A] (hA : AddCommGrpCat.isKilledBySomePower d A) (n : ℕ) :
    AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of
      (((singularChains k).obj (TopCat.of (classifyingSpace (Multiplicative A)))).homology
        (n + 1))) := by
  obtain ⟨m, hm⟩ := (AddCommGrpCat.prop_isKilledBySomePower_iff d A).1 hA
  -- The order of `A` divides `(d ^ m) ^ r`, where `r` is the rank of `A`.
  obtain ⟨c, hc⟩ : Nat.card A ∣ d ^ (m * AddGroup.rank A) := by
    rw [pow_mul]
    exact card_dvd_exponent_nsmul_rank' A fun a ↦ by
      simpa [← natCast_zsmul] using hm a
  refine (AddCommGrpCat.prop_isKilledBySomePower_iff d _).2 ⟨m * AddGroup.rank A, fun x ↦ ?_⟩
  have hx := natCard_nsmul_classifyingSpace_singularHomology_eq_zero k x
  rw [Nat.card_congr Multiplicative.toAdd] at hx
  rw [← Nat.cast_pow, natCast_zsmul, hc, mul_nsmul, hx, nsmul_zero]

end TauCeti
