/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Schreier
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.AlgebraicTopology.SerreClass.PowerTorsion
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic

/-!
# The homology of the classifying space of a finite group is torsion

Let `G` be a finite group. The singular homology of Milnor's classifying space `classifyingSpace G`
with coefficients in a commutative ring `k` is killed by the order of `G` in every positive degree:
`#G • x = 0` for `x ∈ Hₙ₊₁(BG; k)`
(`TauCeti.natCard_nsmul_classifyingSpace_singularHomology_eq_zero`). So it is a torsion group
(`TauCeti.isAddTorsion_classifyingSpace_singularHomology`), and it vanishes when `#G` is a unit of
`k` (`TauCeti.subsingleton_classifyingSpace_singularHomology_of_isUnit_natCard`), for instance
with rational coefficients, or with coefficients in `𝔽₂` when `G` has odd order.

These are transported from group homology, through the identification `Hₙ(BG; k) ≅ Hₙ(G, k)`
(`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`), where the order of the group kills
positive-degree homology because corestriction after transfer to the trivial subgroup is
multiplication by `#G` (`groupHomology.natCard_nsmul_eq_zero`).

For an abelian group `A`, the classifying space `B(Multiplicative A)` is an Eilenberg--MacLane
space `K(A, 1)`. When `A` is finite and annihilated by some power of an integer `d`, the order of
`A` divides a power of `d`, so the positive-degree homology of `K(A, 1)` is again annihilated by
a power of `d` (`TauCeti.isKilledBySomePower_classifyingSpace_singularHomology`). This is Serre's
axiom on the homology of `K(A, 1)` for the class `AddCommGrpCat.isKilledBySomePower d`, and,
by the torsion statement above, for the class `AddCommGrpCat.isTorsion`, for finite `A`.

## Main results

* `TauCeti.natCard_nsmul_classifyingSpace_singularHomology_eq_zero`: `#G` kills `Hₙ₊₁(BG; k)`.
* `TauCeti.isAddTorsion_classifyingSpace_singularHomology`: `Hₙ₊₁(BG; k)` is a torsion group.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_isUnit_natCard`: `Hₙ₊₁(BG; k) = 0`
  when `#G` is a unit of `k`.
* `TauCeti.isKilledBySomePower_classifyingSpace_singularHomology`: if a finite abelian group `A`
  is annihilated by some power of `d`, so is `Hₙ₊₁(K(A, 1); k)`.

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

variable (k : Type u) [CommRing k] {G : Type u} [Group G] [Finite G]

/-- **The order of a finite group kills the positive-degree homology of its classifying space**:
`#G • x = 0` for every `x ∈ Hₙ₊₁(BG; k)`. -/
theorem natCard_nsmul_classifyingSpace_singularHomology_eq_zero {n : ℕ}
    (x : ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :
    Nat.card G • x = 0 := by
  apply (classifyingSpaceSingularHomologyIsoGroupHomology k G (n + 1)).toLinearEquiv.injective
  rw [map_nsmul, groupHomology.natCard_nsmul_eq_zero, map_zero]

/-- **The positive-degree homology of the classifying space of a finite group is torsion.** -/
theorem isAddTorsion_classifyingSpace_singularHomology (n : ℕ) :
    IsAddTorsion (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :=
  fun x ↦ isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨Nat.card G, Nat.card_pos, natCard_nsmul_classifyingSpace_singularHomology_eq_zero k x⟩

/-- **The positive-degree homology of the classifying space of a finite group vanishes when the
order of the group is a unit of the coefficients**: `Hₙ₊₁(BG; k) = 0` when `#G` is invertible
in `k`. -/
theorem subsingleton_classifyingSpace_singularHomology_of_isUnit_natCard
    (h : IsUnit (Nat.card G : k)) (n : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) :=
  have := groupHomology.subsingleton_of_isUnit_natCard (Rep.trivial k G k) h n
  (classifyingSpaceSingularHomologyIsoGroupHomology k G (n + 1)).toLinearEquiv.toEquiv.subsingleton

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
