/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space

/-!
# Negative nonsimple long-root spaces of the short-root G₂ carrier

The characters `-(3α₁ + α₂)` and `-(3α₁ + 2α₂)` occur in the adjoint representation of
the short-root carrier over `𝔽₃`, and their weight spaces are one-dimensional. Explicit
conjugates of the negative simple long-root vector span these spaces. Conjugation retains
these directions even though iterated short-root Lie brackets lose them in characteristic three.
The upper bounds follow from differentiated cross-product invariance.

Characters are integral torus characters, not eigenvalues of Cartan matrices modulo three.
These results concern the explicit carrier; they do not identify it with an independently
pinned simply connected group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2 (rank-one representatives).
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, §6.

The tangent-matrix and cross-product computations follow the existing simple-root calculation
in `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

open CategoryTheory

noncomputable section

private def rankOneWord (i : Fin 2) : points (ZMod 3) :=
  rootSubgroupPoints (.inr i) (ZMod 3) (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inl i) (ZMod 3) (Multiplicative.ofAdd (-1)) *
      rootSubgroupPoints (.inr i) (ZMod 3) (Multiplicative.ofAdd 1)

private def conjugator (i : Fin 2) : points (ZMod 3) :=
  if i = 0 then rankOneWord 0 else rankOneWord 1 * rankOneWord 0

/-- The tangent vector at `-(3α₁ + α₂)` (index zero) or `-(3α₁ + 2α₂)` (index one),
obtained by conjugating the negative simple long-root vector by explicit rank-one root words. -/
def negativeLongRootVector (i : Fin 2) :
    Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra) :=
  conjugateTangent (conjugator i) (rootVector (.inr 1))

/-- The negative long-root vectors are conjugates of the negative simple long-root vector
by the indicated products of rank-one root words. -/
theorem negativeLongRootVector_eq_conjugateTangent (i : Fin 2) :
    let w := fun j : Fin 2 =>
      rootSubgroupPoints (.inr j) (ZMod 3) (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inl j) (ZMod 3) (Multiplicative.ofAdd (-1)) *
          rootSubgroupPoints (.inr j) (ZMod 3) (Multiplicative.ofAdd 1)
    negativeLongRootVector i =
      conjugateTangent (if i = 0 then w 0 else w 1 * w 0) (rootVector (.inr 1)) := by
  simp only [negativeLongRootVector, conjugator, rankOneWord]

/-- The two negative nonsimple long roots, in fundamental-weight coordinates. -/
def negativeLongRootWeight (i : Fin 2) : Fin 2 → ℤ :=
  if i = 0 then ![-3, 1] else ![0, -1]

/-- In terms of the numbered simple roots, the two weights are `-(3α₁ + α₂)` and
`-(3α₁ + 2α₂)`, respectively. -/
theorem negativeLongRootWeight_eq_neg_simpleRoots (i : Fin 2) :
    negativeLongRootWeight i =
      -(3 • DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2 (.inl (0 : Fin 2)) +
        (if i = 0 then 1 else 2) •
          DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2 (.inl (1 : Fin 2))) := by
  funext j
  -- The root characters use `Fin G2.rank`; the coordinate family uses `Fin 2`.
  erw [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    DynkinType.rootGeneratorWeight_inl, DynkinType.rootGeneratorWeight_inl,
    DynkinType.cartanMatrix_G2_eq]
  fin_cases i <;> fin_cases j <;> norm_num [negativeLongRootWeight]

private def negativeLongMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  if i = 0 then Matrix.single 4 0 (-1) + Matrix.single 6 2 1
  else Matrix.single 5 0 (-1) + Matrix.single 6 1 (-1)

private theorem tangentMatrix_negativeLongRootVector_eq (i : Fin 2) :
    tangentMatrix (negativeLongRootVector i) = negativeLongMatrix i := by
  unfold negativeLongMatrix
  rw [negativeLongRootVector, tangentMatrix_conjugateTangent, tangentMatrix_rootVector]
  unfold conjugator
  split_ifs <;>
    simp only [rankOneWord,
      Subgroup.coe_mul, Units.val_mul, mul_inv_rev,
      ← map_inv (rootSubgroupPoints _ (ZMod 3)), ← ofAdd_neg,
      neg_neg, coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints,
      toAdd_ofAdd, rootMatrix_inr, rootMatrix_inl,
      rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr] <;>
    decide +kernel

/-- The matrices of the two conjugate tangent vectors, with their exact root normalization. -/
-- Match the named tangent matrix before its quotient presentation is simplified.
@[simp↓]
theorem tangentMatrix_negativeLongRootVector (i : Fin 2) :
    tangentMatrix (negativeLongRootVector i) =
      if i = 0 then Matrix.single 4 0 (-1) + Matrix.single 6 2 1
      else Matrix.single 5 0 (-1) + Matrix.single 6 1 (-1) := by
  rw [tangentMatrix_negativeLongRootVector_eq, negativeLongMatrix]

/-- Both negative long-root vectors are nonzero. -/
theorem negativeLongRootVector_ne_zero (i : Fin 2) : negativeLongRootVector i ≠ 0 := by
  intro h
  have hm := congrArg tangentMatrix h
  rw [tangentMatrix_negativeLongRootVector, map_zero] at hm
  fin_cases i
  · have he := congrFun (congrFun hm 4) 0
    norm_num [Matrix.single_apply] at he
  · have he := congrFun (congrFun hm 5) 0
    norm_num [Matrix.single_apply] at he

private theorem negativeLongMatrix_support (i : Fin 2) (a b : Fin 7)
    (h : weight a - weight b ≠ negativeLongRootWeight i) : negativeLongMatrix i a b = 0 := by
  fin_cases i <;> revert h <;> fin_cases a <;> fin_cases b <;>
    decide +kernel

/-- The conjugate vector has the indicated integral torus character. -/
theorem negativeLongRootVector_mem_adjointWeightSpace (i : Fin 2) :
    negativeLongRootVector i ∈ Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
      (SplitTorus.weightCharacter (negativeLongRootWeight i)) := by
  rw [mem_adjointWeightSpace_iff]
  intro a b h
  rw [tangentMatrix_negativeLongRootVector_eq]
  exact negativeLongMatrix_support i a b (fun he => h (congrArg _ he))

private theorem exists_eq_smul_negativeLongMatrix (i : Fin 2)
    (X : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (hX : ∀ c, X * crossOperatorPrime c =
      ConstantMultiplication.imageStructureMatrix (ZMod 3) 7 crossOperatorPrime X c +
        crossOperatorPrime c * X)
    (hsupp : ∀ a b, weight a - weight b ≠ negativeLongRootWeight i → X a b = 0) :
    ∃ t : ZMod 3, X = t • negativeLongMatrix i := by
  -- Both weights have two possible matrix entries. Only their positions and relative sign vary.
  let a : Fin 7 := if i = 0 then 4 else 5
  let b : Fin 7 := if i = 0 then 2 else 1
  let ε : ZMod 3 := if i = 0 then 1 else -1
  have hXe : X = Matrix.single a 0 (X a 0) + Matrix.single 6 b (X 6 b) := by
    fin_cases i <;> dsimp [a, b] <;> ext r s <;> fin_cases r <;> fin_cases s <;>
      first | (solve | simp) | (simpa using hsupp _ _ (by decide))
  have hrel : X 6 b = -ε * X a 0 := by
    have h := congrFun (congrFun (hX 0) 3) b
    rw [hXe] at h
    fin_cases i <;>
      simp [a, b, ε, Matrix.mul_apply, Fin.sum_univ_succ,
        ConstantMultiplication.imageStructureMatrix_def, crossOperator_def] at h ⊢ <;>
      linear_combination h
  have hM : negativeLongMatrix i = Matrix.single a 0 (-1) + Matrix.single 6 b ε := by
    fin_cases i <;> simp [negativeLongMatrix, a, b, ε]
  refine ⟨-X a 0, ?_⟩
  rw [hM, smul_add, Matrix.smul_single, Matrix.smul_single]
  conv_lhs => rw [hXe, hrel]
  congr 1 <;> congr 1 <;> simp [smul_eq_mul]; ring

/-- Each negative nonsimple long-root space is exactly the line generated by its conjugate
negative simple-root vector. -/
-- Match the named coordinate map before its quotient presentation is simplified.
@[simp↓]
theorem adjointWeightSpace_negativeLongRootWeight_eq_span (i : Fin 2) :
    Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
        (SplitTorus.weightCharacter (negativeLongRootWeight i)) =
      (ZMod 3) ∙ negativeLongRootVector i := by
  apply le_antisymm
  · intro x hx
    have hsupp : ∀ a b, weight a - weight b ≠ negativeLongRootWeight i →
        tangentMatrix x a b = 0 := by
      intro a b h
      apply (mem_adjointWeightSpace_iff _ x).mp hx a b
      intro he
      apply h
      funext l
      simpa only [SplitTorus.toAdd_weightCharacter] using
        congrArg (fun χ : Multiplicative (Fin 2 →₀ ℤ) => Multiplicative.toAdd χ l) he
    obtain ⟨t, ht⟩ := exists_eq_smul_negativeLongMatrix i (tangentMatrix x)
      (tangentMatrix_mul_crossOperatorPrime x) hsupp
    refine Submodule.mem_span_singleton.mpr ⟨t, tangentMatrix_injective ?_⟩
    rw [map_smul, tangentMatrix_negativeLongRootVector_eq, ht]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact negativeLongRootVector_mem_adjointWeightSpace i

/-- The two negative nonsimple long roots occur among the carrier's intrinsic nontrivial
adjoint weights. -/
theorem negativeLongRootWeight_mem_nontrivialAdjointWeights (i : Fin 2) :
    SplitTorus.weightCharacter (negativeLongRootWeight i) ∈
      Derivation.nontrivialAdjointWeights weightTorusCoordinateMap.hom := by
  rw [Derivation.mem_nontrivialAdjointWeights, adjointWeightSpace_negativeLongRootWeight_eq_span]
  refine ⟨?_, ?_⟩
  · exact SplitTorus.weightCharacter_eq_one_iff.not.mpr (by fin_cases i <;> decide)
  · exact Submodule.span_singleton_eq_bot.not.mpr (negativeLongRootVector_ne_zero i)

/-- In the coordinates of the chosen split maximal torus, the negative nonsimple long-root
spaces are the same explicitly normalized lines. -/
-- Match the chosen torus and the character before their coordinate presentations simplify.
@[simp↓]
theorem adjointWeightSpace_splitMaximalTorus_negativeLongRootWeight_eq_span (i : Fin 2) :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (SplitTorus.weightCharacter
          (fun j : ULift.{0} (Fin 2) => negativeLongRootWeight i j.down)) =
      (ZMod 3) ∙ negativeLongRootVector i := by
  rw [adjointWeightSpace_splitMaximalTorus_weightCharacter_eq_weightTorus,
    adjointWeightSpace_negativeLongRootWeight_eq_span]

end

end TauCeti.G2ShortRoot.PrimeField
