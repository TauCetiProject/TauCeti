/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Padics.SpecialLinearGroup.AlgebraicFunctions
import TauCeti.NumberTheory.Padics.SpecialLinearGroup.FirstCongruence

/-!
# Regression examples: algebraic functions on the first congruence subgroup of `SL₂(ℤ_p)`

These examples check from a downstream module that, on the first congruence subgroup
`G₁ ≤ SL₂(ℤ_p)`,

* `dim C^alg_{≤0} = 1`, the constants;
* `dim C^alg_{≤1} / C^alg_{≤0} = 4`, spanned by the four matrix entries, with no linear relation;
* `dim C^alg_{≤2} / C^alg_{≤1} = 9 = C(5, 3) - C(3, 3)`, the relation `xw - yz = 1` removing one
  of the ten quadrics, so that `dim C^alg_{≤2} = 14` rather than the `15` polynomials of degree at
  most two in four variables;
* restriction to the trivial subgroup, which is not open, kills `x - 1`, which does not lie in the
  ideal `(xw - yz - 1)`: it does not vanish on `G₁`.

The coefficient field `K` is any topological field over `ℚ_p`.
-/

open TauCeti MvPolynomial Matrix

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [TopologicalSpace K]
  [IsTopologicalRing K] [ContinuousSMul ℚ_[p] K]

example :
    Module.finrank K (algebraicFunctionsDegreeLE K (firstCongruenceSubgroup (Fin 2) p) 0) = 1 := by
  rw [finrank_algebraicFunctionsDegreeLE K (isOpen_firstCongruenceSubgroup _ _)]
  rfl

example :
    Module.finrank K
      (algebraicFunctionsDegreeLE K (firstCongruenceSubgroup (Fin 2) p) 1 ⧸
        (algebraicFunctionsDegreeLE K (firstCongruenceSubgroup (Fin 2) p) 0).comap
          (algebraicFunctionsDegreeLE K (firstCongruenceSubgroup (Fin 2) p) 1).subtype) =
      4 :=
  finrank_algebraicFunctionsDegreeLE_quotient K (isOpen_firstCongruenceSubgroup _ _) 0

example :
    Module.finrank K
      (algebraicFunctionsDegreeLE K (firstCongruenceSubgroup (Fin 2) p) 2 ⧸
        (algebraicFunctionsDegreeLE K (firstCongruenceSubgroup (Fin 2) p) 1).comap
          (algebraicFunctionsDegreeLE K (firstCongruenceSubgroup (Fin 2) p) 2).subtype) =
      9 :=
  finrank_algebraicFunctionsDegreeLE_quotient K (isOpen_firstCongruenceSubgroup _ _) 1

example :
    Module.finrank K (algebraicFunctionsDegreeLE K (firstCongruenceSubgroup (Fin 2) p) 2) = 14 := by
  rw [finrank_algebraicFunctionsDegreeLE K (isOpen_firstCongruenceSubgroup _ _)]
  rfl

example : polynomialRestriction K (⊥ : Subgroup (SpecialLinearGroup (Fin 2) ℤ_[p]))
    (X (0, 0) - 1) = 0 := by
  ext ⟨g, hg⟩
  rw [Subgroup.mem_bot] at hg
  subst hg
  simp

example :
    (X (0, 0) - 1 : MvPolynomial (Fin 2 × Fin 2) K) ∉
      Ideal.span {(mvPolynomialX (Fin 2) (Fin 2) K).det - 1} := by
  rw [← ker_polynomialRestriction_fin_two K (isOpen_firstCongruenceSubgroup (Fin 2) p),
    RingHom.mem_ker]
  intro h
  -- The product of the two elementary transvections with coefficient `p` lies in `G₁` and has
  -- upper left entry `1 + p²`.
  have hu := (transvection_mem_firstCongruenceSubgroup_iff (zero_ne_one' (Fin 2))
    (p : ℤ_[p])).mpr dvd_rfl
  have hl := (transvection_mem_firstCongruenceSubgroup_iff (zero_ne_one' (Fin 2)).symm
    (p : ℤ_[p])).mpr dvd_rfl
  have he : ((SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) (p : ℤ_[p]) :
      Matrix (Fin 2) (Fin 2) ℤ_[p]) *
        (SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)).symm (p : ℤ_[p]) :
          Matrix (Fin 2) (Fin 2) ℤ_[p])) 0 0 = 1 + p * p := by
    simp [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply]
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have hentry := congr($h ⟨_, mul_mem hu hl⟩)
  rw [polynomialRestriction_apply, ContinuousMap.zero_apply] at hentry
  simp only [map_sub, eval_X, map_one, SpecialLinearGroup.coe_mul] at hentry
  rw [he] at hentry
  exact (Fact.out : p.Prime).ne_zero (by simpa using hentry)
