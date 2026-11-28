/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Fiber

/-!
# Counting classes under change of level

Passing from a level `K` to a subgroup `J` splits each orbit into at most `[K : J]` orbits.
This bounds the number of double cosets at a smaller level without any freeness assumption
on the class stabilizers.
-/

public section

open MulAction

namespace TauCeti

/-- For a finite-index inclusion `J ≤ K`, the number of `J`-orbits is at most the number of
`K`-orbits times the relative index. If there are infinitely many `K`-orbits, both orbit counts
are zero by the `Nat.card` convention. -/
theorem natCard_orbitRelQuotient_le_mul_relIndex {G X : Type*} [Group G] [MulAction G X]
    {J K : Subgroup G} (hJK : J ≤ K) [J.IsFiniteRelIndex K] :
    Nat.card (orbitRel.Quotient J X) ≤ Nat.card (orbitRel.Quotient K X) * J.relIndex K := by
  classical
  let Q := orbitRel.Quotient K X
  rcases finite_or_infinite Q with hQ | hQ
  swap
  · have := Infinite.of_surjective _ (Setoid.map_of_le_surjective
      (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) hJK))
    simp only [Nat.card_eq_zero_of_infinite, zero_le]
  let C := K ⧸ J.subgroupOf K
  let F : Q → C → orbitRel.Quotient J X := fun q c ↦ (cosetToOrbitRelMapFiber hJK q.out c).val
  have hF : Function.Surjective (fun p : Q × C ↦ F p.1 p.2) := by
    intro y
    let q : Q := Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) hJK) y
    have hy : Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) hJK) y =
        (Quotient.mk'' q.out : Q) := (Quotient.out_eq q).symm
    obtain ⟨c, hc⟩ := cosetToOrbitRelMapFiber_surjective hJK q.out ⟨y, hy⟩
    exact ⟨(q, c), congrArg Subtype.val hc⟩
  simpa only [Nat.card_prod, Subgroup.relIndex, Subgroup.index_eq_card] using
    Nat.card_le_card_of_surjective _ hF

end TauCeti

namespace DoubleCoset

/-- Replacing `K` by a finite-index subgroup `J` multiplies the double-coset count by at most
`[K : J]`. Infinite class spaces count as zero. -/
theorem natCard_quotient_le_mul_relIndex {G : Type*} [Group G] (Γ : Subgroup G)
    {J K : Subgroup G} (hJK : J ≤ K) [J.IsFiniteRelIndex K] :
    Nat.card (Quotient (Γ : Set G) J) ≤ Nat.card (Quotient (Γ : Set G) K) * J.relIndex K := by
  rw [Nat.card_congr (TauCeti.doubleCosetQuotientEquivOrbitRelQuotient Γ J),
    Nat.card_congr (TauCeti.doubleCosetQuotientEquivOrbitRelQuotient Γ K)]
  exact TauCeti.natCard_orbitRelQuotient_le_mul_relIndex hJK

/-- If `J ≤ K` contains the kernel of a finite quotient map of `K`, the class count at `J`
is bounded by the count at `K` times the size of the reduction image. The map need not be onto
its codomain, and `J` need not be normal in `K`. -/
theorem natCard_quotient_le_mul_natCard_range_of_ker_le {G B : Type*} [Group G] [Group B]
    (Γ : Subgroup G) {J K : Subgroup G} (hJK : J ≤ K)
    (reduction : K →* B) [Finite reduction.range] (hker : reduction.ker ≤ J.subgroupOf K) :
    Nat.card (Quotient (Γ : Set G) J) ≤
      Nat.card (Quotient (Γ : Set G) K) * Nat.card reduction.range := by
  have hfin := Subgroup.finiteIndex_of_le hker
  let : J.IsFiniteRelIndex K := ⟨hfin.index_ne_zero⟩
  refine (natCard_quotient_le_mul_relIndex Γ hJK).trans (Nat.mul_le_mul_left _ ?_)
  calc
    J.relIndex K ≤ reduction.ker.index := Subgroup.index_antitone hker
    _ = Nat.card reduction.range := Subgroup.index_ker _

end DoubleCoset
