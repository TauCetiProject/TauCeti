/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Frobenius
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Centralizer
public import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Scalar centers of the minuscule E7 carrier

The unique highest weight and connected weight diagram make the simultaneous centralizer of
all raising and lowering operators scalar over every commutative ring. Adjacent simple roots
give a nested commutator identity, placing the unit-parameter root points in the intrinsic
derived subgroup of any subgroup containing them. Consequently the centers of both that
subgroup and its derived subgroup consist precisely of the elements whose matrices are scalar.
-/

public section

open scoped Matrix commutatorElement

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The joint centralizer of the fourteen simple-root operators is scalar, over any
commutative coefficient ring. -/
theorem commute_raising_lowering_iff_eq_smul_one {R : Type*} [CommRing R]
    (M : Matrix (Fin 56) (Fin 56) R) :
    (∀ i, Commute M ((raisingMatrix i).map (Int.cast : ℤ → R)) ∧
      Commute M ((loweringMatrix i).map (Int.cast : ℤ → R))) ↔ M = M 0 0 • 1 := by
  have hnot : ∀ i, weightTable.weight 0 i ≠ -1 := by
    rw [weightTable_weight]
    intro i hi
    exact (e7MinusculeWeight_has_negative_iff 0).mp ⟨i, hi⟩ rfl
  have hhighest : ∀ a, a ≠ 0 → ∃ i, weightTable.weight a i = -1 := by
    rw [weightTable_weight]
    exact fun a ↦ (e7MinusculeWeight_has_negative_iff a).mpr
  have hconnected : ∀ a, ∃ l : List (Fin 7),
      l.foldl (fun b i ↦ weightTable.reflection i b) 0 = a := by
    simpa only [weightTable_reflection] using exists_e7MinusculeReflections_eq
  have hF (i : Fin 7) : weightTable.loweringMatrix i = loweringMatrix i := by
    ext a b
    rw [weightTable.loweringMatrix_apply, loweringMatrix_apply,
      weightTable_weight, weightTable_reflection]
  simpa only [weightTable_raisingMatrix, hF] using
    weightTable.commute_raising_lowering_iff_eq_smul_one 0 hnot hhighest hconnected M

private theorem adjacent_ne {i j : Fin 7} (hij : CartanMatrix.E 7 i j = -1) : i ≠ j := by
  rintro rfl
  rw [CartanMatrix.E_diag] at hij
  norm_num at hij

private theorem raising_lie_lie_eq_zero {i j : Fin 7}
    (hij : CartanMatrix.E 7 i j = -1) :
    ⁅raisingMatrix i, ⁅raisingMatrix i, raisingMatrix j⁆⁆ = 0 := by
  simpa [hij] using isSerreSystem.ad_pow_lie_E_E i j

private theorem lowering_lie_lie_eq_zero {i j : Fin 7}
    (hij : CartanMatrix.E 7 i j = -1) :
    ⁅loweringMatrix i, ⁅loweringMatrix i, loweringMatrix j⁆⁆ = 0 := by
  simpa [hij] using isSerreSystem.ad_pow_lie_F_F i j

/-- Adjacent positive simple-root points are explicit nested commutators. -/
theorem nested_commutator_rootSubgroupPoints_inl {i j : Fin 7}
    (hij : CartanMatrix.E 7 i j = -1) (R : Type*) [CommRing R] (u : R) :
    ⁅⁅rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd u),
        rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1)⁆,
      rootSubgroupPoints (.inr j) R (Multiplicative.ofAdd 1)⁆ =
        rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd u) := by
  have hji : CartanMatrix.E 7 j i = -1 := by
    rw [(CartanMatrix.E_isSymm 7).apply, hij]
  have hAC := isSerreSystem.lie_E_F_of_ne i j (adjacent_ne hij)
  have hABC : ⁅⁅raisingMatrix i, raisingMatrix j⁆, loweringMatrix j⁆ = raisingMatrix i := by
    rw [lie_lie, isSerreSystem.lie_E_F_self, hAC, lie_zero, sub_zero,
      ← lie_skew (raisingMatrix i) (cartanMatrix j), isSerreSystem.lie_H_E, hji]
    simp
  apply Subtype.ext
  apply Units.ext
  rw [coe_rootSubgroupPoints_inl]
  exact coe_nested_commutator_eq_one_add_smul (raisingMatrix i) (raisingMatrix j)
    (loweringMatrix j) (raisingMatrix_mul_self i) (raisingMatrix_mul_self j)
    (loweringMatrix_mul_self j) hAC hABC (raising_lie_lie_eq_zero hij)
    (raising_lie_lie_eq_zero hji) u _ _ _ (coe_rootSubgroupPoints_inl i R _)
    (by simpa using coe_rootSubgroupPoints_inl j R (Multiplicative.ofAdd 1))
    (by simpa using coe_rootSubgroupPoints_inr j R (Multiplicative.ofAdd 1))

/-- Adjacent negative simple-root points satisfy the same nested commutator formula. -/
theorem nested_commutator_rootSubgroupPoints_inr {i j : Fin 7}
    (hij : CartanMatrix.E 7 i j = -1) (R : Type*) [CommRing R] (u : R) :
    ⁅⁅rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd u),
        rootSubgroupPoints (.inr j) R (Multiplicative.ofAdd 1)⁆,
      rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1)⁆ =
        rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd u) := by
  have hji : CartanMatrix.E 7 j i = -1 := by
    rw [(CartanMatrix.E_isSymm 7).apply, hij]
  have hAC : ⁅loweringMatrix i, raisingMatrix j⁆ = 0 := by
    rw [← lie_skew, isSerreSystem.lie_E_F_of_ne j i (adjacent_ne hji), neg_zero]
  have hABC : ⁅⁅loweringMatrix i, loweringMatrix j⁆, raisingMatrix j⁆ = loweringMatrix i := by
    rw [lie_lie, ← lie_skew (loweringMatrix j) (raisingMatrix j),
      isSerreSystem.lie_E_F_self, hAC, lie_zero, sub_zero, lie_neg,
      ← lie_skew (loweringMatrix i) (cartanMatrix j), isSerreSystem.lie_H_F, hji]
    simp
  apply Subtype.ext
  apply Units.ext
  rw [coe_rootSubgroupPoints_inr]
  exact coe_nested_commutator_eq_one_add_smul (loweringMatrix i) (loweringMatrix j)
    (raisingMatrix j) (loweringMatrix_mul_self i) (loweringMatrix_mul_self j)
    (raisingMatrix_mul_self j) hAC hABC (lowering_lie_lie_eq_zero hij)
    (lowering_lie_lie_eq_zero hji) u _ _ _ (coe_rootSubgroupPoints_inr i R _)
    (by simpa using coe_rootSubgroupPoints_inr j R (Multiplicative.ofAdd 1))
    (by simpa using coe_rootSubgroupPoints_inl j R (Multiplicative.ofAdd 1))

/-- In a subgroup containing all fourteen unit-parameter simple-root points, those points
already belong to the intrinsic derived subgroup. -/
theorem rootSubgroupPoints_one_mem_commutator {R : Type*} [CommRing R]
    (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H)
    (k : Fin 7 ⊕ Fin 7) :
    (⟨rootSubgroupPoints k R (Multiplicative.ofAdd 1), hroots k⟩ : H) ∈ commutator H := by
  have hadj : ∀ i : Fin 7, ∃ j : Fin 7, (CartanMatrix.E 7 : Matrix (Fin 7) (Fin 7) ℤ) i j = -1 := by
    rw [CartanMatrix.E_seven_eq]
    simp [Fin.forall_fin_succ, Fin.exists_fin_succ]
  let x (k : Fin 7 ⊕ Fin 7) : H := ⟨rootSubgroupPoints k R (Multiplicative.ofAdd 1), hroots k⟩
  have hmem (a b c : H) : ⁅⁅a, b⁆, c⁆ ∈ commutator H :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  cases k with
  | inl i =>
    obtain ⟨j, hij⟩ := hadj i
    have heq : ⁅⁅x (.inl i), x (.inl j)⁆, x (.inr j)⁆ = x (.inl i) := by
      apply Subtype.ext
      exact nested_commutator_rootSubgroupPoints_inl hij R 1
    change x (.inl i) ∈ commutator H
    rw [← heq]
    exact hmem (x (.inl i)) (x (.inl j)) (x (.inr j))
  | inr i =>
    obtain ⟨j, hij⟩ := hadj i
    have heq : ⁅⁅x (.inr i), x (.inr j)⁆, x (.inl j)⁆ = x (.inr i) := by
      apply Subtype.ext
      exact nested_commutator_rootSubgroupPoints_inr hij R 1
    change x (.inr i) ∈ commutator H
    rw [← heq]
    exact hmem (x (.inr i)) (x (.inr j)) (x (.inl j))

private theorem mem_center_iff_eq_smul_one_of_range {R G : Type*} [CommRing R] [Group G]
    (f : G →* points R) (hf : Function.Injective f)
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ f.range) (g : G) :
    g ∈ Subgroup.center G ↔
      ((f g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
        ((f g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) 0 0 • 1 := by
  let M : points R → Matrix (Fin 56) (Fin 56) R := fun x ↦ x.val.val
  constructor
  · intro hg
    apply (commute_raising_lowering_iff_eq_smul_one (M (f g))).mp
    have heq (k : Fin 7 ⊕ Fin 7) :
        M (rootSubgroupPoints k R (Multiplicative.ofAdd 1)) * M (f g) =
          M (f g) * M (rootSubgroupPoints k R (Multiplicative.ofAdd 1)) := by
      obtain ⟨x, hx⟩ := hroots k
      have h := congrArg (fun y ↦ M (f y)) ((Subgroup.mem_center_iff.mp hg) x)
      simpa only [map_mul, hx, M, Subgroup.coe_mul, Units.val_mul] using h
    intro i
    constructor
    · have h := heq (.inl i)
      change _ * M (f g) = M (f g) * _ at h
      rw [show M (rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1)) =
        1 + (raisingMatrix i).map (Int.cast : ℤ → R) by
          dsimp only [M]
          simpa only [toAdd_ofAdd, one_smul] using
            coe_rootSubgroupPoints_inl i R (Multiplicative.ofAdd 1)] at h
      simp only [add_mul, mul_add, one_mul, mul_one] at h
      exact (add_left_cancel h).symm
    · have h := heq (.inr i)
      rw [show M (rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd 1)) =
        1 + (loweringMatrix i).map (Int.cast : ℤ → R) by
          dsimp only [M]
          simpa only [toAdd_ofAdd, one_smul] using
            coe_rootSubgroupPoints_inr i R (Multiplicative.ofAdd 1)] at h
      simp only [add_mul, mul_add, one_mul, mul_one] at h
      exact (add_left_cancel h).symm
  · intro hg
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply hf
    rw [map_mul, map_mul]
    apply Subtype.ext
    apply Units.ext
    change M (f x) * M (f g) = M (f g) * M (f x)
    change M (f g) = M (f g) 0 0 • 1 at hg
    rw [hg]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- A subgroup containing the fourteen unit-parameter simple-root points has scalar center. -/
theorem mem_center_iff_eq_smul_one {R : Type*} [CommRing R] (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H) (g : H) :
    g ∈ Subgroup.center H ↔
      ((g.val : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
        ((g.val : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) 0 0 • 1 := by
  apply mem_center_iff_eq_smul_one_of_range H.subtype Subtype.val_injective
  intro k
  exact ⟨⟨_, hroots k⟩, rfl⟩

/-- The center of the intrinsic derived subgroup is likewise exactly its scalar elements.
This is the center used in the native derived central quotient. -/
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
  exact ⟨⟨⟨_, hroots k⟩, rootSubgroupPoints_one_mem_commutator H hroots k⟩, rfl⟩

/-- Frobenius fixes all fourteen simple-root points with parameter one. -/
theorem rootSubgroupPoints_one_mem_fixedSubgroup_frobenius (p k : ℕ)
    (R : Type*) [CommRing R] [ExpChar R p] (i : Fin 7 ⊕ Fin 7) :
    rootSubgroupPoints i R (Multiplicative.ofAdd 1) ∈ fixedSubgroup (frobenius p k R) := by
  rw [mem_fixedSubgroup, frobenius_rootSubgroupPoints]
  simp

/-- The center of the intrinsic derived subgroup of Frobenius fixed points is scalar. -/
theorem mem_center_commutator_fixedSubgroup_frobenius_iff (p k : ℕ)
    (R : Type*) [CommRing R] [ExpChar R p]
    (g : commutator (fixedSubgroup (frobenius p k R))) :
    g ∈ Subgroup.center (commutator (fixedSubgroup (frobenius p k R))) ↔
      ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
        ((g.val.val : Matrix.GeneralLinearGroup (Fin 56) R) :
          Matrix (Fin 56) (Fin 56) R) 0 0 • 1 :=
  mem_center_commutator_iff_eq_smul_one _
    (rootSubgroupPoints_one_mem_fixedSubgroup_frobenius p k R) g

end TauCeti.E7Minuscule
