/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations
public import TauCeti.Algebra.Lie.E7.Minuscule.Frobenius
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Centralizer

/-!
# Scalar centers of the minuscule E7 carrier

The unique highest weight and connected weight diagram make the simultaneous centralizer of
all raising and lowering operators scalar over every commutative ring. The nested commutator
relations at adjacent simple roots place every simple-root point of a subgroup containing the
parameter-one simple-root points in its derived subgroup. Consequently the centers of both that
subgroup and its derived subgroup consist precisely of the elements whose matrices are scalar.

## Main results

* `TauCeti.E7Minuscule.commute_raising_lowering_iff_eq_smul_one`: the joint centralizer of the
  fourteen simple-root operators is scalar.
* `TauCeti.E7Minuscule.rootSubgroupPoints_mem_commutator`: in a subgroup containing the
  parameter-one simple-root points, every simple-root point lies in the derived subgroup.
* `TauCeti.E7Minuscule.mem_center_iff_eq_smul_one` and
  `TauCeti.E7Minuscule.mem_center_commutator_iff_eq_smul_one`: the centers of such a subgroup and
  of its derived subgroup are its scalar elements.
* `TauCeti.E7Minuscule.mem_center_commutator_fixedSubgroup_frobenius_iff`: the same for the
  derived subgroup of the Frobenius fixed points.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2 for the commutator formula, and
  Chapter 11 for the centre and perfectness of the Chevalley groups.
* R. Steinberg, *Lectures on Chevalley Groups*, §3, for the perfectness and the centre.
-/

public section

open scoped Matrix commutatorElement

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

/-- The joint centralizer of the fourteen simple-root operators is scalar, over any
commutative coefficient ring. -/
theorem commute_raising_lowering_iff_eq_smul_one {R : Type*} [CommRing R]
    (M : Matrix (Fin 56) (Fin 56) R) :
    (∀ i, Commute M ((raisingMatrix i).map (Int.cast : ℤ → R)) ∧
      Commute M ((loweringMatrix i).map (Int.cast : ℤ → R))) ↔ M = M 0 0 • 1 := by
  have hnot : ∀ i, weightTable.weight 0 i ≠ -1 := by
    rw [weightTable_weight]
    intro i hi
    exact (exists_e7MinusculeWeight_apply_eq_neg_one_iff_ne_zero 0).mp ⟨i, hi⟩ rfl
  have hhighest : ∀ a, a ≠ 0 → ∃ i, weightTable.weight a i = -1 := by
    rw [weightTable_weight]
    exact fun a ↦ (exists_e7MinusculeWeight_apply_eq_neg_one_iff_ne_zero a).mpr
  have hconnected : ∀ a, ∃ l : List (Fin 7),
      l.foldl (fun b i ↦ weightTable.reflection i b) 0 = a := by
    simpa only [weightTable_reflection] using exists_e7MinusculeReflections_eq
  simpa only [weightTable_raisingMatrix, weightTable_loweringMatrix] using
    weightTable.commute_raising_lowering_iff_eq_smul_one 0 hnot hhighest hconnected M

/-- In a subgroup containing the fourteen simple-root points with parameter one, every
simple-root point of the subgroup lies in its derived subgroup. -/
theorem rootSubgroupPoints_mem_commutator {R : Type*} [CommRing R] (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H) (k : Fin 7 ⊕ Fin 7)
    (u : R) (hu : rootSubgroupPoints k R (Multiplicative.ofAdd u) ∈ H) :
    (⟨rootSubgroupPoints k R (Multiplicative.ofAdd u), hu⟩ : H) ∈ commutator H := by
  have hadj : ∀ i : Fin 7, ∃ j : Fin 7, (CartanMatrix.E 7 : Matrix (Fin 7) (Fin 7) ℤ) i j = -1 := by
    rw [CartanMatrix.E_seven_eq]
    simp [Fin.forall_fin_succ, Fin.exists_fin_succ]
  have hmem (a b c : H) : ⁅⁅a, b⁆, c⁆ ∈ commutator H :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  cases k with
  | inl i =>
    obtain ⟨j, hij⟩ := hadj i
    have heq : ⁅⁅(⟨_, hu⟩ : H), (⟨_, hroots (.inl j)⟩ : H)⁆, (⟨_, hroots (.inr j)⟩ : H)⁆ =
        (⟨_, hu⟩ : H) := by
      apply H.subtype_injective
      simp only [map_commutatorElement, Subgroup.subtype_apply]
      simpa only [mul_one] using
        commutatorElement_commutatorElement_rootSubgroupPoints_inl hij R u 1 1
    exact heq ▸ hmem _ _ _
  | inr i =>
    obtain ⟨j, hij⟩ := hadj i
    have heq : ⁅⁅(⟨_, hu⟩ : H), (⟨_, hroots (.inr j)⟩ : H)⁆, (⟨_, hroots (.inl j)⟩ : H)⁆ =
        (⟨_, hu⟩ : H) := by
      apply H.subtype_injective
      simp only [map_commutatorElement, Subgroup.subtype_apply]
      simpa only [mul_one] using
        commutatorElement_commutatorElement_rootSubgroupPoints_inr hij R u 1 1
    exact heq ▸ hmem _ _ _

private theorem mem_center_iff_eq_smul_one_of_range {R G : Type*} [CommRing R] [Group G]
    (f : G →* points R) (hf : Function.Injective f)
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ f.range) (g : G) :
    g ∈ Subgroup.center G ↔
      ((f g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
        ((f g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) 0 0 • 1 := by
  constructor
  · intro hg
    apply (commute_raising_lowering_iff_eq_smul_one _).mp
    -- a central element commutes with every parameter-one simple-root point of the range, and
    -- hence with the nilpotent part `N` of that point's matrix `1 + N`
    have hcomm (k : Fin 7 ⊕ Fin 7) (N : Matrix (Fin 56) (Fin 56) R)
        (hN : ((rootSubgroupPoints k R (Multiplicative.ofAdd 1) :
          Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) = 1 + N) :
        Commute ((f g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) N := by
      obtain ⟨x, hx⟩ := hroots k
      have hc : Commute
          ((f g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R)
          ((f x : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) :=
        ((((commute_iff_eq g x).mpr (Subgroup.mem_center_iff.mp hg x).symm).map f).map
          (points R).subtype).map (Units.coeHom _)
      rw [hx, hN] at hc
      simpa only [add_sub_cancel_left] using hc.sub_right (Commute.one_right _)
    intro i
    exact ⟨hcomm (.inl i) _ (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, one_smul]),
      hcomm (.inr i) _ (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, one_smul])⟩
  · intro hg
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply hf
    rw [map_mul, map_mul]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hg]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- A subgroup containing the fourteen parameter-one simple-root points has scalar center. -/
theorem mem_center_iff_eq_smul_one {R : Type*} [CommRing R] (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H) (g : H) :
    g ∈ Subgroup.center H ↔
      ((g.val : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
        ((g.val : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) 0 0 • 1 := by
  apply mem_center_iff_eq_smul_one_of_range H.subtype Subtype.val_injective
  intro k
  exact ⟨⟨_, hroots k⟩, rfl⟩

/-- The center of the derived subgroup of a subgroup containing the fourteen parameter-one
simple-root points is exactly its scalar elements. This is the center
`TauCeti.DerivedCentralQuotient` quotients the derived subgroup by. -/
theorem mem_center_commutator_iff_eq_smul_one {R : Type*} [CommRing R]
    (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H)
    (g : commutator H) :
    g ∈ Subgroup.center (commutator H) ↔
      ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
        ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) R) :
          Matrix (Fin 56) (Fin 56) R) 0 0 • 1 := by
  apply mem_center_iff_eq_smul_one_of_range (H.subtype.comp (commutator H).subtype)
    (Subtype.val_injective.comp Subtype.val_injective)
  intro k
  exact ⟨⟨⟨_, hroots k⟩, rootSubgroupPoints_mem_commutator H hroots k 1 (hroots k)⟩, rfl⟩

/-- The center of the derived subgroup of the Frobenius fixed points is exactly its scalar
elements. -/
theorem mem_center_commutator_fixedSubgroup_frobenius_iff (p k : ℕ)
    (R : Type*) [CommRing R] [ExpChar R p]
    (g : commutator (fixedSubgroup (frobenius p k R))) :
    g ∈ Subgroup.center (commutator (fixedSubgroup (frobenius p k R))) ↔
      ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
        ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) R) :
          Matrix (Fin 56) (Fin 56) R) 0 0 • 1 :=
  mem_center_commutator_iff_eq_smul_one _
    (fun i ↦ rootSubgroupPoints_mem_fixedSubgroup_frobenius p k R i 1 (one_mem _)) g

end TauCeti.E7Minuscule
