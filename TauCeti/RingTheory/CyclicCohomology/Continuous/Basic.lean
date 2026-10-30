/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.ConnesOperator
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Continuous cyclic and mixed cochain operators

The Hochschild and cyclic operators preserve jointly continuous multilinear cochains on a
topological algebra. This file lifts the algebraic operators to native
`ContinuousMultilinearMap`s and proves the mixed-complex identities there. The comparison
with algebraic cochains is given by the forgetful map `toMultilinearMap`. Preservation of
cyclic cochains does not require associativity; the Hochschild and bar square-zero identities do.

No norm, local convexity, completeness or separation is needed for preservation of continuity.
The scalar action on the target is continuous for each fixed scalar. For a unital algebra,
insertion of the unit gives the continuous bar contraction and hence Connes' operator `B`.
These operations supply the differentials for continuous cyclic cohomology, including on
Fréchet algebras. No topology on the space of cochains or quotient cohomology is imposed here.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.1, 2.1.

The algebraic formulas and identities are those of
`TauCeti.RingTheory.CyclicCohomology.ConnesOperator`.
-/

public section

namespace TauCeti

/-- Multiplication faces of tuples are continuous for a jointly continuous multiplication. -/
theorem continuous_hochschildFace (A : Type*) [TopologicalSpace A] [Mul A]
    [ContinuousMul A] {n : ℕ} (i : Fin (n + 2)) :
    Continuous (hochschildFace (A := A) i) := by
  cases i using Fin.lastCases with
  | last =>
    apply (continuous_congr (fun a ↦ hochschildFace_last_eq_contractNth a)).2
    apply continuous_pi
    intro j
    simp only [Fin.contractNth, Function.comp_apply]
    split_ifs <;> fun_prop
  | cast i =>
    apply (continuous_congr (fun a ↦ hochschildFace_castSucc i a)).2
    apply continuous_pi
    intro j
    simp only [Fin.contractNth]
    split_ifs <;> fun_prop

end TauCeti

namespace ContinuousMultilinearMap

open TauCeti

section

variable {R A M : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [TopologicalSpace A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] {n : ℕ}

/-- Cyclic permutation with its sign preserves joint continuity. -/
theorem continuous_cyclicOperator (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    Continuous (cyclicOperator R A M n φ.toMultilinearMap) := by
  apply (continuous_congr (cyclicOperator_apply φ.toMultilinearMap)).2
  exact (φ.cont.comp (continuous_pi fun _ ↦ continuous_apply _)).zsmul _

/-- The finite cyclic norm preserves joint continuity. -/
theorem continuous_cyclicNorm (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    Continuous (cyclicNorm R A M n φ.toMultilinearMap) := by
  apply (continuous_congr (cyclicNorm_apply φ.toMultilinearMap)).2
  exact continuous_finsetSum _ fun _ _ ↦
    (φ.cont.comp (continuous_pi fun _ ↦ continuous_apply _)).zsmul _

end

section Coface

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [TopologicalSpace A] [AddCommMonoid M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M]
  [IsScalarTower R A A] [SMulCommClass R A A] [ContinuousMul A] {n : ℕ}

/-- Every Hochschild coface preserves joint continuity. -/
theorem continuous_hochschildCoface
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (i : Fin (n + 2)) :
    Continuous (hochschildCoface R A M i φ.toMultilinearMap) := by
  apply (continuous_congr (hochschildCoface_apply R A M i φ.toMultilinearMap)).2
  exact φ.cont.comp (continuous_hochschildFace A i)

end Coface

section Multiplication

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [TopologicalSpace A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] {n : ℕ}
  [IsScalarTower R A A] [SMulCommClass R A A] [ContinuousMul A]

/-- The Hochschild coboundary preserves joint continuity. -/
theorem continuous_hochschildCoboundary
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    Continuous (hochschildCoboundary R A M n φ.toMultilinearMap) := by
  apply (continuous_congr (hochschildCoboundary_apply φ.toMultilinearMap)).2
  exact continuous_finsetSum _ fun i _ ↦
    (φ.cont.comp (continuous_hochschildFace A i)).zsmul _

/-- The bar coboundary preserves joint continuity. -/
theorem continuous_barCoboundary
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    Continuous (barCoboundary R A M n φ.toMultilinearMap) := by
  apply (continuous_congr (barCoboundary_apply φ.toMultilinearMap)).2
  simp_rw [← hochschildFace_castSucc]
  exact continuous_finsetSum _ fun i _ ↦
    (φ.cont.comp (continuous_hochschildFace A i.castSucc)).zsmul _

end Multiplication

section

variable {R A M : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [TopologicalSpace A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] {n : ℕ} [One A]

omit [IsTopologicalAddGroup M] in
/-- Inserting the unit as the first argument preserves joint continuity. -/
theorem continuous_barContraction
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) :
    Continuous (barContraction R A M n φ.toMultilinearMap) := by
  apply (continuous_congr (barContraction_apply φ.toMultilinearMap)).2
  exact φ.cont.comp (continuous_const.finCons continuous_id)

/-- Connes' operator preserves joint continuity. -/
theorem continuous_connesB
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) :
    Continuous (connesB R A M n φ.toMultilinearMap) := by
  let ψ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M :=
    ⟨φ.toMultilinearMap - cyclicOperator R A M (n + 1) φ.toMultilinearMap,
      φ.cont.sub φ.continuous_cyclicOperator⟩
  let η : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M :=
    ⟨barContraction R A M n ψ.toMultilinearMap, ψ.continuous_barContraction⟩
  rw [connesB_apply]
  exact η.continuous_cyclicNorm

end

end ContinuousMultilinearMap

namespace TauCeti

section

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [Module R A]
  [TopologicalSpace A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The signed cyclic rotation on continuous multilinear cochains. -/
def continuousCyclicOperator (n : ℕ) :
    Module.End R (ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) where
  toFun φ := ⟨cyclicOperator R A M n φ.toMultilinearMap, φ.continuous_cyclicOperator⟩
  map_add' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_add _ _ _)
  map_smul' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_smul _ _ _)

/-- Forgetting continuity recovers the algebraic cyclic rotation. -/
@[simp]
theorem toMultilinearMap_continuousCyclicOperator (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    (continuousCyclicOperator R A M n φ).toMultilinearMap =
      cyclicOperator R A M n φ.toMultilinearMap := (rfl)

/-- Evaluation of the continuous cyclic rotation agrees with the algebraic formula. -/
@[simp]
theorem continuousCyclicOperator_apply (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 1) → A) :
    continuousCyclicOperator R A M n φ a = cyclicOperator R A M n φ.toMultilinearMap a := (rfl)

/-- The cyclic norm on continuous multilinear cochains. -/
def continuousCyclicNorm (n : ℕ) :
    Module.End R (ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) where
  toFun φ := ⟨cyclicNorm R A M n φ.toMultilinearMap, φ.continuous_cyclicNorm⟩
  map_add' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_add _ _ _)
  map_smul' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_smul _ _ _)

/-- Forgetting continuity recovers the algebraic cyclic norm. -/
@[simp]
theorem toMultilinearMap_continuousCyclicNorm (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    (continuousCyclicNorm R A M n φ).toMultilinearMap =
      cyclicNorm R A M n φ.toMultilinearMap := (rfl)

/-- Evaluation of the continuous cyclic norm agrees with the algebraic formula. -/
@[simp]
theorem continuousCyclicNorm_apply (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 1) → A) :
    continuousCyclicNorm R A M n φ a = cyclicNorm R A M n φ.toMultilinearMap a := (rfl)

end

section Multiplication

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [TopologicalSpace A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  [IsScalarTower R A A] [SMulCommClass R A A] [ContinuousMul A]

/-- The Hochschild coboundary on continuous multilinear cochains. -/
def continuousHochschildCoboundary (n : ℕ) :
    ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M where
  toFun φ := ⟨hochschildCoboundary R A M n φ.toMultilinearMap,
    φ.continuous_hochschildCoboundary⟩
  map_add' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_add _ _ _)
  map_smul' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_smul _ _ _)

/-- Forgetting continuity recovers the algebraic Hochschild coboundary. -/
@[simp]
theorem toMultilinearMap_continuousHochschildCoboundary (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    (continuousHochschildCoboundary R A M n φ).toMultilinearMap =
      hochschildCoboundary R A M n φ.toMultilinearMap := (rfl)

/-- Evaluation of the continuous Hochschild coboundary agrees with the algebraic formula. -/
@[simp]
theorem continuousHochschildCoboundary_apply (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 2) → A) :
    continuousHochschildCoboundary R A M n φ a =
      hochschildCoboundary R A M n φ.toMultilinearMap a := (rfl)

/-- The bar coboundary on continuous multilinear cochains. -/
def continuousBarCoboundary (n : ℕ) :
    ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M where
  toFun φ := ⟨barCoboundary R A M n φ.toMultilinearMap, φ.continuous_barCoboundary⟩
  map_add' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_add _ _ _)
  map_smul' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_smul _ _ _)

/-- Forgetting continuity recovers the algebraic bar coboundary. -/
@[simp]
theorem toMultilinearMap_continuousBarCoboundary (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    (continuousBarCoboundary R A M n φ).toMultilinearMap =
      barCoboundary R A M n φ.toMultilinearMap := (rfl)

/-- Evaluation of the continuous bar coboundary agrees with the algebraic formula. -/
@[simp]
theorem continuousBarCoboundary_apply (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 2) → A) :
    continuousBarCoboundary R A M n φ a = barCoboundary R A M n φ.toMultilinearMap a := (rfl)

end Multiplication

section Unit

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [Module R A]
  [TopologicalSpace A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M]
  [ContinuousConstSMul R M] [One A]

section Contraction

variable [ContinuousAdd M]

/-- The unit-inserting contraction on continuous multilinear cochains. -/
def continuousBarContraction (n : ℕ) :
    ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M →ₗ[R]
      ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M where
  toFun φ := ⟨barContraction R A M n φ.toMultilinearMap, φ.continuous_barContraction⟩
  map_add' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_add _ _ _)
  map_smul' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_smul _ _ _)

/-- Forgetting continuity recovers the algebraic unit-inserting contraction. -/
@[simp]
theorem toMultilinearMap_continuousBarContraction (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) :
    (continuousBarContraction R A M n φ).toMultilinearMap =
      barContraction R A M n φ.toMultilinearMap := (rfl)

/-- Evaluation of the continuous unit insertion agrees with the algebraic formula. -/
@[simp]
theorem continuousBarContraction_apply (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M)
    (a : Fin (n + 1) → A) :
    continuousBarContraction R A M n φ a = barContraction R A M n φ.toMultilinearMap a := (rfl)

end Contraction

variable [IsTopologicalAddGroup M]

/-- Connes' operator on continuous multilinear cochains. -/
def continuousConnesB (n : ℕ) :
    ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M →ₗ[R]
      ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M where
  -- Lifting the algebraic formula avoids requiring additive inverses in the argument module.
  toFun φ := ⟨connesB R A M n φ.toMultilinearMap, φ.continuous_connesB⟩
  map_add' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_add _ _ _)
  map_smul' _ _ := ContinuousMultilinearMap.toMultilinearMap_injective (map_smul _ _ _)

/-- Forgetting continuity recovers the algebraic Connes operator. -/
@[simp]
theorem toMultilinearMap_continuousConnesB (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) :
    (continuousConnesB R A M n φ).toMultilinearMap =
      connesB R A M n φ.toMultilinearMap := (rfl)

/-- Evaluation of the continuous Connes operator agrees with the algebraic formula. -/
@[simp]
theorem continuousConnesB_apply (n : ℕ)
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M)
    (a : Fin (n + 1) → A) :
    continuousConnesB R A M n φ a = connesB R A M n φ.toMultilinearMap a := (rfl)

end Unit

section Cyclic

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [Module R A]
  [TopologicalSpace A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M]
  [ContinuousConstSMul R M]

section Cochains

variable [ContinuousAdd M]

/-- The submodule of jointly continuous cochains satisfying the signed cyclic relation. -/
def continuousCyclicCochains (n : ℕ) :
    Submodule R (ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :=
  (cyclicCochains R A M n).comap ContinuousMultilinearMap.toMultilinearMapLinear

/-- A continuous cochain is cyclic precisely when its underlying algebraic cochain is cyclic. -/
@[simp]
theorem mem_continuousCyclicCochains_iff {n : ℕ}
    {φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} :
    φ ∈ continuousCyclicCochains R A M n ↔ φ.toMultilinearMap ∈ cyclicCochains R A M n :=
  Iff.rfl

end Cochains

variable [IsTopologicalAddGroup M]

/-- The cyclic norm of a continuous cochain is cyclic. -/
theorem continuousCyclicNorm_mem_continuousCyclicCochains {n : ℕ}
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    continuousCyclicNorm R A M n φ ∈ continuousCyclicCochains R A M n := by
  simpa only [mem_continuousCyclicCochains_iff, toMultilinearMap_continuousCyclicNorm] using
    cyclicNorm_mem_cyclicCochains φ.toMultilinearMap

variable [One A]

/-- Connes' operator takes continuous cochains to continuous cyclic cochains. -/
theorem continuousConnesB_mem_continuousCyclicCochains {n : ℕ}
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) :
    continuousConnesB R A M n φ ∈ continuousCyclicCochains R A M n := by
  simpa only [mem_continuousCyclicCochains_iff, toMultilinearMap_continuousConnesB] using
    connesB_mem_cyclicCochains φ.toMultilinearMap

/-- Connes' operator vanishes on continuous cyclic cochains. -/
theorem continuousConnesB_eq_zero_of_mem_continuousCyclicCochains {n : ℕ}
    {φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M}
    (hφ : φ ∈ continuousCyclicCochains R A M (n + 1)) :
    continuousConnesB R A M n φ = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simpa only [toMultilinearMap_continuousConnesB,
    ContinuousMultilinearMap.toMultilinearMap_zero] using
    connesB_eq_zero_of_mem_cyclicCochains ((mem_continuousCyclicCochains_iff R A M).1 hφ)

/-- The continuous Connes operator squares to zero. -/
@[simp]
theorem continuousConnesB_continuousConnesB {n : ℕ}
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 3) ↦ A) M) :
    continuousConnesB R A M n (continuousConnesB R A M (n + 1) φ) = 0 :=
  continuousConnesB_eq_zero_of_mem_continuousCyclicCochains R A M
    (continuousConnesB_mem_continuousCyclicCochains R A M φ)

end Cyclic

section NonAssocCyclic

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

/-- The Hochschild coboundary preserves continuous cyclic cochains. -/
theorem continuousHochschildCoboundary_mem_continuousCyclicCochains {n : ℕ}
    {φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ continuousCyclicCochains R A M n) :
    continuousHochschildCoboundary R A M n φ ∈ continuousCyclicCochains R A M (n + 1) := by
  simpa only [mem_continuousCyclicCochains_iff,
    toMultilinearMap_continuousHochschildCoboundary] using
    hochschildCoboundary_mem_cyclicCochains R A M
      ((mem_continuousCyclicCochains_iff R A M).1 hφ)

/-- The Hochschild coboundary restricted to continuous cyclic cochains. -/
def continuousCyclicHochschildCoboundary (n : ℕ) :
    continuousCyclicCochains R A M n →ₗ[R] continuousCyclicCochains R A M (n + 1) :=
  (continuousHochschildCoboundary R A M n).restrict
    (fun _ hφ ↦ continuousHochschildCoboundary_mem_continuousCyclicCochains R A M hφ)

/-- The restricted coboundary agrees with the continuous Hochschild coboundary. -/
@[simp]
theorem coe_continuousCyclicHochschildCoboundary {n : ℕ}
    (φ : continuousCyclicCochains R A M n) :
    (continuousCyclicHochschildCoboundary R A M n φ).val =
      continuousHochschildCoboundary R A M n φ.val := (rfl)

end NonAssocCyclic

section NonUnital

variable (R A M : Type*) [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

/-- The continuous Hochschild coboundary squares to zero. -/
@[simp]
theorem continuousHochschildCoboundary_continuousHochschildCoboundary {n : ℕ}
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    continuousHochschildCoboundary R A M (n + 1)
      (continuousHochschildCoboundary R A M n φ) = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simp

/-- The continuous bar coboundary squares to zero. -/
@[simp]
theorem continuousBarCoboundary_continuousBarCoboundary {n : ℕ}
    (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    continuousBarCoboundary R A M (n + 1) (continuousBarCoboundary R A M n φ) = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simp

/-- The restricted continuous cyclic differential squares to zero. -/
@[simp]
theorem continuousCyclicHochschildCoboundary_continuousCyclicHochschildCoboundary {n : ℕ}
    (φ : continuousCyclicCochains R A M n) :
    continuousCyclicHochschildCoboundary R A M (n + 1)
      (continuousCyclicHochschildCoboundary R A M n φ) = 0 := by
  apply Subtype.ext
  simp

end NonUnital

section Unital

variable (R A M : Type*) [Semiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

/-- In degree zero, insertion of the unit contracts the continuous bar differential. -/
@[simp]
theorem continuousBarContraction_continuousBarCoboundary_zero
    (φ : ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A) M) :
    continuousBarContraction R A M 0 (continuousBarCoboundary R A M 0 φ) = φ := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simp

/-- In positive degrees, insertion of the unit contracts the continuous bar differential. -/
theorem continuousBarCoboundary_barContraction_add_barContraction_barCoboundary
    {n : ℕ} (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) :
    continuousBarCoboundary R A M n (continuousBarContraction R A M n φ) +
      continuousBarContraction R A M (n + 1) (continuousBarCoboundary R A M (n + 1) φ) = φ := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simpa only [ContinuousMultilinearMap.toMultilinearMap_add,
    toMultilinearMap_continuousBarCoboundary, toMultilinearMap_continuousBarContraction] using
    barCoboundary_barContraction_add_barContraction_barCoboundary φ.toMultilinearMap

/-- The continuous Hochschild and Connes operators anticommute. -/
theorem continuousHochschildCoboundary_connesB_add_connesB_hochschildCoboundary
    {n : ℕ} (φ : ContinuousMultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) :
    continuousHochschildCoboundary R A M n (continuousConnesB R A M n φ) +
      continuousConnesB R A M (n + 1) (continuousHochschildCoboundary R A M (n + 1) φ) = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simpa only [ContinuousMultilinearMap.toMultilinearMap_add,
    ContinuousMultilinearMap.toMultilinearMap_zero,
    toMultilinearMap_continuousHochschildCoboundary, toMultilinearMap_continuousConnesB] using
    hochschildCoboundary_connesB_add_connesB_hochschildCoboundary φ.toMultilinearMap

end Unital

end TauCeti
