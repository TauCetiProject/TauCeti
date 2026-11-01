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

private abbrev Tangent :=
  Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra)

private def rankOneWord (i : Fin 2) : points (ZMod 3) :=
  rootSubgroupPoints (.inr i) (ZMod 3) (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inl i) (ZMod 3) (Multiplicative.ofAdd (-1)) *
      rootSubgroupPoints (.inr i) (ZMod 3) (Multiplicative.ofAdd 1)

private def conjugator (i : Fin 2) : points (ZMod 3) :=
  if i = 0 then rankOneWord 0 else rankOneWord 1 * rankOneWord 0

private def conjugateTangent (g : points (ZMod 3)) (x : Tangent) : Tangent :=
  (Derivation.cotangentLinearEquiv (B := ZMod 3)).symm
    (Derivation.adDerivation (ZMod 3)
      ((Bialgebra.CounitAlgebra.pointsMulEquiv (ZMod 3) carrierAlgebra (ZMod 3)).symm
        ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm g))
      (Derivation.cotangentLinearEquiv (B := ZMod 3) x))

private theorem tangentMatrix_conjugateTangent (g : points (ZMod 3)) (x : Tangent) :
    tangentMatrix (conjugateTangent g x) =
      ((g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *
        tangentMatrix x *
        (((g⁻¹ : points (ZMod 3)) : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
          Matrix (Fin 7) (Fin 7) (ZMod 3)) := by
  let q := ((Bialgebra.CounitAlgebra.pointsMulEquiv (ZMod 3) carrierAlgebra (ZMod 3)).symm
    ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm g))
  have hq : GeneralLinear.counitPointsMulEquiv 7
      (BialgHom.mapDomain (A := Bialgebra.CounitAlgebra (ZMod 3)
        (GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7) (ZMod 3))
        (Bialgebra.Quotient.mkBialgHom
          (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal) q) =
      (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) := by
    apply Units.ext
    have hg := coe_pointsMulEquiv_eq_map_carrierGenericMatrix
      ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm g)
    rw [MulEquiv.apply_symm_apply] at hg
    rw [hg]
    ext a b
    rw [GeneralLinear.counitPointsMulEquiv_apply]
    -- The two counit coefficient algebras have different ambient Hopf-algebra indices.
    erw [BialgHom.mapDomain_apply_apply]
    simp only [q, Bialgebra.CounitAlgebra.algEquivSelf_apply]
    -- Counit transport changes only the coefficient-algebra presentation.
    erw [Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply]
    rw [Bialgebra.CounitAlgebra.algEquivSelf_symm_apply, carrierGenericMatrix_def]
    simp [GeneralLinear.genericMatrix_apply, carrierQuotient]
  rw [conjugateTangent, tangentMatrix_apply, LinearEquiv.apply_symm_apply,
    HopfIdeal.quotientLieHom_adDerivation, GeneralLinear.tangentMatrix_adDerivation,
    hq, ← tangentMatrix_apply]
  rfl

/-- The tangent vector at `-(3α₁ + α₂)` (index zero) or `-(3α₁ + 2α₂)` (index one),
obtained by conjugating the negative simple long-root vector by explicit rank-one root words. -/
def negativeLongRootVector (i : Fin 2) :
    Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra) :=
  conjugateTangent (conjugator i) (rootVector (.inr 1))

/-- The two negative nonsimple long roots, in fundamental-weight coordinates. -/
def negativeLongRootWeight (i : Fin 2) : Fin 2 → ℤ :=
  if i = 0 then ![-3, 1] else ![0, -1]

/-- The coordinates of the negative nonsimple long roots. -/
@[simp] theorem negativeLongRootWeight_apply (i : Fin 2) (j : Fin 2) :
    negativeLongRootWeight i j = (if i = 0 then ![-3, 1] else ![0, -1]) j := by
  rw [negativeLongRootWeight]

private def negativeLongMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  if i = 0 then Matrix.single 4 0 (-1) + Matrix.single 6 2 1
  else Matrix.single 5 0 (-1) + Matrix.single 6 1 (-1)

/-- The matrices of the two conjugate tangent vectors, with their exact root normalization. -/
-- Match the named tangent matrix before its quotient presentation is simplified.
@[simp↓]
theorem tangentMatrix_negativeLongRootVector (i : Fin 2) :
    tangentMatrix (negativeLongRootVector i) =
      if i = 0 then Matrix.single 4 0 (-1) + Matrix.single 6 2 1
      else Matrix.single 5 0 (-1) + Matrix.single 6 1 (-1) := by
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
  rw [tangentMatrix_negativeLongRootVector]
  exact negativeLongMatrix_support i a b (fun he => h (congrArg _ he))

private theorem exists_eq_smul_negativeLongMatrix (i : Fin 2)
    (X : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (hX : ∀ c, X * crossOperatorPrime c =
      ConstantMultiplication.imageStructureMatrix (ZMod 3) 7 crossOperatorPrime X c +
        crossOperatorPrime c * X)
    (hsupp : ∀ a b, weight a - weight b ≠ negativeLongRootWeight i → X a b = 0) :
    ∃ t : ZMod 3, X = t • negativeLongMatrix i := by
  fin_cases i
  · have hXe : X = Matrix.single 4 0 (X 4 0) + Matrix.single 6 2 (X 6 2) := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        first | (solve | simp) | (simpa using hsupp _ _ (by decide))
    have h62 : X 6 2 = -X 4 0 := by
      have h := congrFun (congrFun (hX 0) 3) 2
      rw [hXe] at h
      simp [Matrix.mul_apply, Fin.sum_univ_succ,
        ConstantMultiplication.imageStructureMatrix_def, crossOperator_def] at h
      linear_combination h
    refine ⟨-X 4 0, ?_⟩
    conv_lhs => rw [hXe]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [negativeLongMatrix, h62]
  · have hXe : X = Matrix.single 5 0 (X 5 0) + Matrix.single 6 1 (X 6 1) := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        first | (solve | simp) | (simpa using hsupp _ _ (by decide))
    have h61 : X 6 1 = X 5 0 := by
      have h := congrFun (congrFun (hX 0) 3) 1
      rw [hXe] at h
      simp [Matrix.mul_apply, Fin.sum_univ_succ,
        ConstantMultiplication.imageStructureMatrix_def, crossOperator_def] at h
      linear_combination h
    refine ⟨-X 5 0, ?_⟩
    conv_lhs => rw [hXe]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [negativeLongMatrix, h61]

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
    rw [map_smul, tangentMatrix_negativeLongRootVector, ht]
    rfl
  · rw [Submodule.span_singleton_le_iff_mem]
    exact negativeLongRootVector_mem_adjointWeightSpace i

/-- The two negative nonsimple long roots occur among the carrier's intrinsic nontrivial
adjoint weights. -/
theorem negativeLongRootWeight_mem_nontrivialAdjointWeights (i : Fin 2) :
    SplitTorus.weightCharacter (negativeLongRootWeight i) ∈
      Derivation.nontrivialAdjointWeights weightTorusCoordinateMap.hom := by
  rw [Derivation.mem_nontrivialAdjointWeights, adjointWeightSpace_negativeLongRootWeight_eq_span]
  refine ⟨?_, ?_⟩
  · intro h
    have he := congrArg (fun χ : Multiplicative (Fin 2 →₀ ℤ) => Multiplicative.toAdd χ 1) h
    fin_cases i <;> norm_num [SplitTorus.toAdd_weightCharacter, negativeLongRootWeight] at he
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
