/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.Eigenspace.Diagonal
import TauCeti.Algebra.Lie.GeneralLinear.RootSpace

/-!
# Root spaces of the split even orthogonal Lie algebra

This file computes the root spaces of `LieAlgebra.Orthogonal.typeD ι K` relative to its diagonal
Cartan subalgebra. The two copies of `ι` in the hyperbolic basis have coordinate weights `εᵢ` and
`-εᵢ`. Hence a matrix entry in position `(a, b)` has weight equal to the difference of those two
signed coordinate weights.

Over a reduced ring, generalized root spaces are honest simultaneous eigenspaces because each Cartan
element acts diagonally on the ambient matrix units. This identifies the root space with the
corresponding weight space. The support implication from entries of the requested signed weight to
root-space membership holds over any commutative ring; the converse implication, from root-space
membership to entrywise support, uses the stronger hypothesis that the coefficient ring is a domain.

## Main results

* `TauCeti.rootSpace_typeDDiagonalCartan_eq_weightSpace`: generalized root spaces are honest
  simultaneous eigenspaces.
* `TauCeti.mem_rootSpace_typeDDiagonalCartan_iff`: over a domain, membership is equivalent to
  entrywise support on positions of the requested weight.

The diagonal action on ambient matrix units reduces generalized root-space membership to ordinary
eigenvector equations over a reduced ring, after which those equations become entrywise support
conditions for the signed matrix weights.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8, 12.
-/

public section

namespace TauCeti

open _root_.Matrix _root_.LieAlgebra.Orthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-! ## Signed coordinate weights -/

/-- The weight of a hyperbolic coordinate: `εᵢ` on the first summand and `-εᵢ` on the second. -/
noncomputable def typeDCoordinateWeight (a : ι ⊕ ι) :
    Module.Dual K (typeDDiagonalCartan K ι) :=
  match a with
  | .inl i => typeDEpsilon i
  | .inr i => -typeDEpsilon i

/-- The signed coordinate weight on the first summand is `εᵢ`. -/
@[simp] theorem typeDCoordinateWeight_inl (i : ι) :
    typeDCoordinateWeight (K := K) (.inl i) = typeDEpsilon i := by
  simp [typeDCoordinateWeight]

/-- The signed coordinate weight on the second summand is `-εᵢ`. -/
@[simp] theorem typeDCoordinateWeight_inr (i : ι) :
    typeDCoordinateWeight (K := K) (.inr i) = -typeDEpsilon i := by
  simp [typeDCoordinateWeight]

/-- The weight of the matrix entry `(a, b)`, namely the difference of its signed coordinate
weights. -/
noncomputable def typeDMatrixWeight (a b : ι ⊕ ι) :
    Module.Dual K (typeDDiagonalCartan K ι) :=
  typeDCoordinateWeight a - typeDCoordinateWeight b

/-- The matrix-entry weight is the difference of its two signed coordinate weights. -/
theorem typeDMatrixWeight_def (a b : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a b = typeDCoordinateWeight a - typeDCoordinateWeight b := by
  simp [typeDMatrixWeight]

/-- The signed coordinate weight evaluates through the corresponding diagonal entry. -/
@[simp]
theorem typeDCoordinateWeight_apply (a : ι ⊕ ι) (A : typeDDiagonalCartan K ι) :
    typeDCoordinateWeight a A = (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a a := by
  cases a with
  | inl i => simp [typeDCoordinateWeight]
  | inr i => simp [typeDCoordinateWeight, typeD.apply_inr_inr]

/-- The matrix-entry weight evaluates as the difference of the two signed diagonal coordinates. -/
@[simp]
theorem typeDMatrixWeight_apply (a b : ι ⊕ ι) (A : typeDDiagonalCartan K ι) :
    typeDMatrixWeight a b A =
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a a -
        (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) b b := by
  simp [typeDMatrixWeight]

/-- The coordinate-difference weight `εᵢ - εⱼ` on the split diagonal Cartan. -/
noncomputable def typeDWeightSub (i j : ι) : Module.Dual K (typeDDiagonalCartan K ι) :=
  typeDEpsilon i - typeDEpsilon j

/-- The coordinate-difference weight unfolds to `εᵢ - εⱼ`. -/
theorem typeDWeightSub_def (i j : ι) :
    typeDWeightSub (K := K) i j = typeDEpsilon i - typeDEpsilon j := by
  simp [typeDWeightSub]

/-- The coordinate-sum weight `εᵢ + εⱼ` on the split diagonal Cartan. -/
noncomputable def typeDWeightAdd (i j : ι) : Module.Dual K (typeDDiagonalCartan K ι) :=
  typeDEpsilon i + typeDEpsilon j

/-- The coordinate-sum weight unfolds to `εᵢ + εⱼ`. -/
theorem typeDWeightAdd_def (i j : ι) :
    typeDWeightAdd (K := K) i j = typeDEpsilon i + typeDEpsilon j := by
  simp [typeDWeightAdd]

/-- Coordinate-sum weights are unchanged when their two coordinates are swapped. -/
theorem typeDWeightAdd_comm (i j : ι) :
    typeDWeightAdd (K := K) i j = typeDWeightAdd j i := by
  rw [typeDWeightAdd_def, typeDWeightAdd_def, add_comm]

/-- The coordinate-difference weight evaluates as the difference of the corresponding diagonal
entries. -/
@[simp]
theorem typeDWeightSub_apply (i j : ι) (A : typeDDiagonalCartan K ι) :
    typeDWeightSub i j A =
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i) -
        (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inl j) := by
  simp [typeDWeightSub]

/-- The coordinate-sum weight evaluates as the sum of the corresponding diagonal entries. -/
@[simp]
theorem typeDWeightAdd_apply (i j : ι) (A : typeDDiagonalCartan K ι) :
    typeDWeightAdd i j A =
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i) +
        (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inl j) := by
  simp [typeDWeightAdd]

/-- A coordinate-difference weight vanishes when its two coordinates agree. -/
@[simp]
theorem typeDWeightSub_self (i : ι) : typeDWeightSub (K := K) i i = 0 := by
  ext A
  simp [typeDWeightSub]

/-- The matrix-entry weight on a diagonal entry is the zero functional. -/
@[simp]
theorem typeDMatrixWeight_self (a : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a a = 0 := by
  simp [typeDMatrixWeight]

/-- The `(inl i, inl j)` matrix-entry weight is the coordinate difference `εᵢ - εⱼ`. -/
@[simp]
theorem typeDMatrixWeight_inl_inl (i j : ι) :
    typeDMatrixWeight (K := K) (.inl i) (.inl j) = typeDWeightSub i j := by
  simp [typeDMatrixWeight, typeDCoordinateWeight, typeDWeightSub]

/-- The `(inl i, inr j)` matrix-entry weight is the coordinate sum `εᵢ + εⱼ`. -/
@[simp]
theorem typeDMatrixWeight_inl_inr (i j : ι) :
    typeDMatrixWeight (K := K) (.inl i) (.inr j) = typeDWeightAdd i j := by
  simp [typeDMatrixWeight, typeDCoordinateWeight, typeDWeightAdd]

/-- The `(inr i, inl j)` matrix-entry weight is the negative coordinate-sum weight. -/
@[simp]
theorem typeDMatrixWeight_inr_inl (i j : ι) :
    typeDMatrixWeight (K := K) (.inr i) (.inl j) = -typeDWeightAdd i j := by
  simp [typeDMatrixWeight, typeDCoordinateWeight, typeDWeightAdd]
  abel

/-- The `(inr i, inr j)` matrix-entry weight is the reversed coordinate-difference weight. -/
@[simp]
theorem typeDMatrixWeight_inr_inr (i j : ι) :
    typeDMatrixWeight (K := K) (.inr i) (.inr j) = typeDWeightSub j i := by
  simp [typeDMatrixWeight, typeDCoordinateWeight, typeDWeightSub]
  abel

/-! ## Distinctness of the three root families -/

/-- Away from characteristic two, the nonzero coordinate-difference weights are pairwise
distinct as ordered pairs. -/
@[simp]
theorem typeDWeightSub_eq_typeDWeightSub_iff (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j)
    (a b : ι) :
    typeDWeightSub (K := K) a b = typeDWeightSub i j ↔ a = i ∧ b = j := by
  have : Nontrivial K := nontrivial_of_ne 2 0 h2
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have hfun := congrArg (typeDWeightEquiv (K := K)).symm h
  simp only [typeDWeightSub_def, map_sub, typeDWeightEquiv_symm_epsilon] at hfun
  have hglCoord := congrArg (glWeightEquiv K ι) hfun
  have hgl : glWeightSub K ι a b = glWeightSub K ι i j := by
    ext A
    rw [glWeightSub_apply, glWeightSub_apply]
    have hA := congrArg (fun f : Module.Dual K (diagonalCartan K ι) => f A) hglCoord
    simpa [Pi.single_apply] using hA
  exact (glWeightSub_eq_glWeightSub_iff h2 hij a b).mp hgl

/-- Over a nontrivial ring, two coordinate-sum roots agree exactly when their unordered pairs of
distinct coordinates agree. -/
@[simp]
theorem typeDWeightAdd_eq_typeDWeightAdd_iff [Nontrivial K] {i j : ι} (hij : i ≠ j)
    (a b : ι) :
    typeDWeightAdd (K := K) a b = typeDWeightAdd i j ↔
      (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  refine ⟨fun h => ?_, ?_⟩
  · have hfun := congrArg (typeDWeightEquiv (K := K)).symm h
    simp only [typeDWeightAdd_def, map_add, typeDWeightEquiv_symm_epsilon] at hfun
    have hab : a ≠ b := by
      intro hab
      subst b
      have hi := congrFun hfun i
      rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij] at hi
      by_cases hai : a = i
      · subst a
        simp at hi
      · simp [hai] at hi
    have ha := congrFun hfun a
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab] at ha
    by_cases hai : a = i
    · left
      refine ⟨hai, ?_⟩
      subst a
      have hb := congrFun hfun b
      rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (Ne.symm hab)] at hb
      by_contra hbj
      rw [Pi.single_eq_of_ne hbj] at hb
      have h10 : (1 : K) = 0 := by linear_combination hb
      exact one_ne_zero h10
    · have haj : a = j := by
        by_contra haj
        rw [Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj] at ha
        have h10 : (1 : K) = 0 := by linear_combination ha
        exact one_ne_zero h10
      right
      refine ⟨haj, ?_⟩
      subst a
      have hb := congrFun hfun b
      rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (Ne.symm hab)] at hb
      by_contra hbi
      rw [Pi.single_eq_of_ne hbi] at hb
      have h10 : (1 : K) = 0 := by linear_combination hb
      exact one_ne_zero h10
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact typeDWeightAdd_comm _ _

/-- A coordinate-difference weight is never a coordinate-sum weight away from characteristic
two. -/
@[simp]
theorem typeDWeightSub_ne_typeDWeightAdd (h2 : (2 : K) ≠ 0) (a b i j : ι) :
    typeDWeightSub (K := K) a b ≠ typeDWeightAdd i j := by
  intro h
  have heval := congrArg
    (fun χ : Module.Dual K (typeDDiagonalCartan K ι) =>
      χ (typeDDiagonalEquiv (K := K) (fun _ => 1))) h
  simp [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply] at heval
  norm_num [one_add_one_eq_two] at heval
  exact h2 heval.symm

/-- Away from characteristic two, a negative coordinate-sum weight is never a positive
coordinate-sum weight whose coordinates are distinct. -/
@[simp]
theorem neg_typeDWeightAdd_ne_typeDWeightAdd (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j)
    (a b : ι) : -typeDWeightAdd (K := K) a b ≠ typeDWeightAdd i j := by
  let _ : Nontrivial K := nontrivial_of_ne 2 0 h2
  intro h
  have hfun := congrArg (typeDWeightEquiv (K := K)).symm h
  simp only [map_neg, typeDWeightAdd_def, map_add] at hfun
  have hi := congrFun hfun i
  have hj := congrFun hfun j
  by_cases hai : a = i
  · by_cases hbi : b = i
    · subst a
      subst b
      simp [hij] at hj
    · have hi' : -(1 : K) = 1 := by simpa [hai, hbi, hij] using hi
      apply h2
      calc
        (2 : K) = 1 + 1 := by norm_num
        _ = 0 := neg_eq_iff_add_eq_zero.mp hi'
  · by_cases hbi : b = i
    · have hi' : -(1 : K) = 1 := by simpa [hai, hbi, hij] using hi
      apply h2
      calc
        (2 : K) = 1 + 1 := by norm_num
        _ = 0 := neg_eq_iff_add_eq_zero.mp hi'
    · simp [hai, hbi, hij] at hi

/-- A negative coordinate-sum weight is never a coordinate-difference weight away from
characteristic two. -/
@[simp]
theorem neg_typeDWeightAdd_ne_typeDWeightSub (h2 : (2 : K) ≠ 0) (a b i j : ι) :
    -typeDWeightAdd (K := K) a b ≠ typeDWeightSub i j := by
  intro h
  have heval := congrArg
    (fun χ : Module.Dual K (typeDDiagonalCartan K ι) =>
      χ (typeDDiagonalEquiv (K := K) (fun _ => 1))) h
  have hzero : -(2 : K) = 0 := by
    simpa [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using heval
  exact h2 (neg_eq_zero.mp hzero)

/-! ## Matrix positions carrying each root -/

/-- The two matrix positions of weight `εᵢ - εⱼ` in the split type-`D` model. -/
@[simp]
theorem typeDMatrixWeight_eq_typeDWeightSub_iff (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) (a b : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a b = typeDWeightSub i j ↔
      (a = .inl i ∧ b = .inl j) ∨ (a = .inr j ∧ b = .inr i) := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [typeDMatrixWeight_inl_inl, Sum.inl.injEq, Sum.inl_ne_inr, false_and,
      or_false]
    exact typeDWeightSub_eq_typeDWeightSub_iff h2 hij a b
  · simp only [typeDMatrixWeight_inl_inr, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false, or_self]
    exact iff_false_intro (Ne.symm (typeDWeightSub_ne_typeDWeightAdd h2 i j a b))
  · simp only [typeDMatrixWeight_inr_inl, Sum.inr.injEq, Sum.inr_ne_inl,
      Sum.inl_ne_inr, false_and, and_false, or_self]
    exact iff_false_intro (neg_typeDWeightAdd_ne_typeDWeightSub h2 a b i j)
  · simp only [typeDMatrixWeight_inr_inr, Sum.inr.injEq, Sum.inr_ne_inl, false_and,
      false_or]
    simpa [and_comm] using typeDWeightSub_eq_typeDWeightSub_iff h2 hij b a

/-- The two matrix positions of weight `εᵢ + εⱼ` in the split type-`D` model. -/
@[simp]
theorem typeDMatrixWeight_eq_typeDWeightAdd_iff (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) (a b : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a b = typeDWeightAdd i j ↔
      (a = .inl i ∧ b = .inr j) ∨ (a = .inl j ∧ b = .inr i) := by
  let _ : Nontrivial K := nontrivial_of_ne 2 0 h2
  rcases a with a | a <;> rcases b with b | b
  · simp only [typeDMatrixWeight_inl_inl, Sum.inl.injEq, Sum.inl_ne_inr,
      and_false, or_self]
    exact iff_false_intro (typeDWeightSub_ne_typeDWeightAdd h2 a b i j)
  · simp only [typeDMatrixWeight_inl_inr, Sum.inl.injEq, Sum.inr.injEq]
    exact typeDWeightAdd_eq_typeDWeightAdd_iff hij a b
  · simp only [typeDMatrixWeight_inr_inl, Sum.inr_ne_inl, false_and, false_or]
    exact iff_false_intro (neg_typeDWeightAdd_ne_typeDWeightAdd h2 hij a b)
  · simp only [typeDMatrixWeight_inr_inr, Sum.inr_ne_inl, false_and, false_or]
    exact iff_false_intro (typeDWeightSub_ne_typeDWeightAdd h2 b a i j)

/-- The two matrix positions of weight `-εᵢ - εⱼ` in the split type-`D` model. -/
@[simp]
theorem typeDMatrixWeight_eq_neg_typeDWeightAdd_iff (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) (a b : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a b = -typeDWeightAdd i j ↔
      (a = .inr i ∧ b = .inl j) ∨ (a = .inr j ∧ b = .inl i) := by
  let _ : Nontrivial K := nontrivial_of_ne 2 0 h2
  rcases a with a | a <;> rcases b with b | b
  · simp only [typeDMatrixWeight_inl_inl, Sum.inl_ne_inr, false_and, false_or]
    exact iff_false_intro (Ne.symm (neg_typeDWeightAdd_ne_typeDWeightSub h2 i j a b))
  · simp only [typeDMatrixWeight_inl_inr, Sum.inl_ne_inr, false_and, false_or]
    exact iff_false_intro (fun h => neg_typeDWeightAdd_ne_typeDWeightAdd h2 hij a b (by
      simpa using congrArg Neg.neg h))
  · simp only [typeDMatrixWeight_inr_inl, Sum.inr.injEq, Sum.inl.injEq, neg_inj]
    exact typeDWeightAdd_eq_typeDWeightAdd_iff hij a b
  · simp only [typeDMatrixWeight_inr_inr, Sum.inr_ne_inl, and_false, or_self]
    exact iff_false_intro (Ne.symm (neg_typeDWeightAdd_ne_typeDWeightSub h2 i j b a))

/-! ## Honest weight spaces and entrywise support -/

/-- The adjoint action of an element of the split diagonal Cartan is diagonal in the ambient
matrix-unit basis. -/
theorem toEnd_typeDDiagonalCartan_matrix_eq_toLin_diagonal (A : typeDDiagonalCartan K ι) :
    LieModule.toEnd K (typeDDiagonalCartan K ι) (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A =
      Matrix.toLin (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι))
        (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι))
        (Matrix.diagonal fun p : (ι ⊕ ι) × (ι ⊕ ι) => typeDMatrixWeight p.1 p.2 A) := by
  refine (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι)).ext fun p => ?_
  rw [LieModule.toEnd_apply_apply, Matrix.toLin_self,
    Finset.sum_eq_single p (fun q _ hq => by rw [Matrix.diagonal_apply_ne _ hq, zero_smul])
      (by simp),
    Matrix.diagonal_apply_eq, Matrix.stdBasis_eq_single]
  ext a b
  rw [typeDMatrixWeight_apply]
  simp only [LieSubalgebra.coe_bracket_of_module]
  have hA : (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈ diagonalCartan K (ι ⊕ ι) := by
    rw [mem_diagonalCartan_iff_isDiag]
    exact mem_typeDDiagonalCartan_iff_isDiag.mp A.2
  rw [lie_single_of_mem_diagonalCartan hA]

/-- Over a reduced ring, the root spaces for the split diagonal Cartan are honest simultaneous
eigenspaces rather than merely generalized eigenspaces. -/
theorem rootSpace_typeDDiagonalCartan_eq_weightSpace
    [IsReduced K]
    (χ : Module.Dual K (typeDDiagonalCartan K ι)) :
    LieAlgebra.rootSpace (typeDDiagonalCartan K ι) χ =
      LieModule.weightSpace (LieAlgebra.Orthogonal.typeD ι K)
        (χ : typeDDiagonalCartan K ι → K) := by
  refine le_antisymm (fun X hX => ?_) (LieModule.weightSpace_le_genWeightSpace _ _)
  rw [LieModule.mem_weightSpace]
  intro A
  let inc := ((LieAlgebra.Orthogonal.typeD ι K).incl').restrictLie
    (typeDDiagonalCartan K ι)
  have hambient : (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈
      LieModule.genWeightSpace (Matrix (ι ⊕ ι) (ι ⊕ ι) K) χ := by
    exact LieModule.map_genWeightSpace_le inc ⟨X, hX, rfl⟩
  have hA : (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈ Module.End.maxGenEigenspace
      (LieModule.toEnd K (typeDDiagonalCartan K ι)
        (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A) (χ A) := by
    have := LieModule.genWeightSpace_le_genWeightSpaceOf
      (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A _ hambient
    rwa [LieModule.mem_genWeightSpaceOf, ← Module.End.mem_maxGenEigenspace] at this
  rw [toEnd_typeDDiagonalCartan_matrix_eq_toLin_diagonal,
    maxGenEigenspace_toLin_diagonal_eq_eigenspace_of_isReduced,
    Module.End.mem_eigenspace_iff, ← toEnd_typeDDiagonalCartan_matrix_eq_toLin_diagonal,
    LieModule.toEnd_apply_apply] at hA
  exact Subtype.ext hA

/-- The diagonal Cartan acts on each ambient matrix entry through its signed coordinate-difference
weight. The matrix need not itself lie in the type-`D` subalgebra. -/
@[simp]
theorem typeDDiagonalCartan_lie_apply (A : typeDDiagonalCartan K ι)
    (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (a b : ι ⊕ ι) :
    ⁅(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K),
        X⁆ a b = typeDMatrixWeight a b A * X a b := by
  have hA : (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈ diagonalCartan K (ι ⊕ ι) := by
    rw [mem_diagonalCartan_iff_isDiag]
    exact mem_typeDDiagonalCartan_iff_isDiag.mp A.2
  rw [lie_apply_of_mem_diagonalCartan hA, typeDMatrixWeight_apply]

/-- An entry of a generalized root vector vanishes when its weight difference from the root is
regular at some element of the diagonal Cartan. -/
theorem rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular
    {chi : Module.Dual K (typeDDiagonalCartan K ι)}
    {X : LieAlgebra.Orthogonal.typeD ι K}
    (hX : X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) chi)
    (a b : ι ⊕ ι) (A : typeDDiagonalCartan K ι)
    (hreg : IsRegular (typeDMatrixWeight a b A - chi A)) :
    (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 := by
  let inc := ((LieAlgebra.Orthogonal.typeD ι K).incl').restrictLie
    (typeDDiagonalCartan K ι)
  have hambient : (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈
      LieModule.genWeightSpace (Matrix (ι ⊕ ι) (ι ⊕ ι) K) chi := by
    exact LieModule.map_genWeightSpace_le inc ⟨X, hX, rfl⟩
  have hA : (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈ Module.End.maxGenEigenspace
      (LieModule.toEnd K (typeDDiagonalCartan K ι)
        (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A) (chi A) := by
    have := LieModule.genWeightSpace_le_genWeightSpaceOf
      (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A _ hambient
    rwa [LieModule.mem_genWeightSpaceOf, ← Module.End.mem_maxGenEigenspace] at this
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hA
  have hop :
      LieModule.toEnd K (typeDDiagonalCartan K ι)
          (Matrix (ι ⊕ ι) (ι ⊕ ι) K) A - chi A • 1 =
        Matrix.toLin (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι))
          (Matrix.stdBasis K (ι ⊕ ι) (ι ⊕ ι))
          (Matrix.diagonal
            ((fun p : (ι ⊕ ι) × (ι ⊕ ι) => typeDMatrixWeight p.1 p.2 A) -
              chi A • 1)) := by
    rw [toEnd_typeDDiagonalCartan_matrix_eq_toLin_diagonal, Pi.sub_def,
      ← Matrix.diagonal_sub]
    simp [Module.End.one_eq_id]
  rw [hop, ← Matrix.toLin_pow, Matrix.diagonal_pow,
    Matrix.toLin_apply_eq_zero_iff] at hk
  have hab : (typeDMatrixWeight a b A - chi A) ^ k *
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 := by
    simpa [Matrix.mulVec_diagonal, Matrix.stdBasis] using hk (a, b)
  exact (isRegular_iff_eq_zero_of_mul.mp (hreg.pow k)).1 _ hab

/-- A type-`D` matrix supported on entries of weight `χ` belongs to the `χ` root space. -/
theorem mem_rootSpace_typeDDiagonalCartan_of_forall
    {χ : Module.Dual K (typeDDiagonalCartan K ι)}
    {X : LieAlgebra.Orthogonal.typeD ι K}
    (h : ∀ a b, typeDMatrixWeight a b ≠ χ →
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0) :
    X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) χ := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  apply Subtype.ext
  ext a b
  rw [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul]
  simp only [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket]
  rw [typeDDiagonalCartan_lie_apply]
  by_cases hab : typeDMatrixWeight a b = χ
  · rw [congrArg (fun f : Module.Dual K (typeDDiagonalCartan K ι) => f A) hab]
  · rw [h a b hab, mul_zero, mul_zero]

/-- Over a domain, a matrix in the split type-`D` Lie algebra belongs to the root space of `χ`
exactly when all entries whose signed coordinate difference is not `χ` vanish. -/
@[simp]
theorem mem_rootSpace_typeDDiagonalCartan_iff
    [IsDomain K]
    (χ : Module.Dual K (typeDDiagonalCartan K ι))
    (X : LieAlgebra.Orthogonal.typeD ι K) :
    X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) χ ↔
      ∀ a b, typeDMatrixWeight a b ≠ χ →
        (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 := by
  refine ⟨fun hX a b hab => ?_, mem_rootSpace_typeDDiagonalCartan_of_forall⟩
  obtain ⟨k, hk⟩ : ∃ k, typeDMatrixWeight a b
      (typeDDiagonalCartanBasis (K := K) (ι := ι) k) ≠
        χ (typeDDiagonalCartanBasis (K := K) (ι := ι) k) := by
    by_contra hcon
    push Not at hcon
    exact hab ((typeDDiagonalCartanBasis (K := K) (ι := ι)).ext hcon)
  rw [rootSpace_typeDDiagonalCartan_eq_weightSpace, LieModule.mem_weightSpace] at hX
  let A := typeDDiagonalCartanBasis (K := K) (ι := ι) k
  have hEq := congrArg Subtype.val (hX A)
  have hentry := congrFun (congrFun hEq a) b
  rw [SetLike.val_smul, Matrix.smul_apply] at hentry
  simp only [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket] at hentry
  rw [typeDDiagonalCartan_lie_apply] at hentry
  exact (mul_eq_zero.mp (by linear_combination hentry)).resolve_left (sub_ne_zero.mpr hk)

end TauCeti
