/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space
public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Derivation

/-!
# Exhaustion of adjoint weights by the named G₂ roots

Every nontrivial adjoint weight of the short-root carrier over 𝔽₃ is a root of the
named simply connected G₂ datum. The ambient seven-dimensional representation has
six additional nonzero weight differences, the doubled short roots. Cross-product
preservation forces the corresponding matrix entries to vanish, for both signs.
The faithful tangent matrix then excludes all remaining non-root weight spaces.

This is the upper bound needed to recognize the carrier's intrinsic root datum.
It does not assert that all twelve roots occur, identify their coroots, or identify
the carrier with an independently constructed pinned group.

## Main declarations

* `tangentMatrix_apply_eq_zero_of_not_root`: off-diagonal tangent entries have root weights.
* `adjointWeightSpace_eq_bot_of_not_root`: every nontrivial non-root weight space vanishes.
* `nontrivialAdjointWeights_subset_range_g2Root`: all intrinsic roots lie in the named root set.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.

The matrix support and faithful-tangent argument use
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

open DynkinType

/-- An off-diagonal entry of a tangent matrix vanishes unless its integral weight
is a root of the named G₂ datum. -/
theorem tangentMatrix_apply_eq_zero_of_not_root
    (x : Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra))
    (i j : Fin 7) (hij : i ≠ j) (hroot : weight i - weight j ∉ Set.range g2Root) :
    tangentMatrix x i j = 0 := by
  apply crossDerivation_apply_eq_zero_of_not_root (by decide : IsUnit (2 : ZMod 3)).isRegular
    (i := i) (j := j) ?_ hij hroot
  intro c
  convert tangentMatrix_mul_crossOperatorPrime x c using 1 <;>
    ext a b <;> simp [ConstantMultiplication.imageStructureMatrix_def, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.smul_apply]

/-- A nontrivial character not in the named twelve-root set has zero adjoint weight space. -/
theorem adjointWeightSpace_eq_bot_of_not_root
    (α : Multiplicative (Fin 2 →₀ ℤ)) (hα : α ≠ 1)
    (hroot : α ∉ Set.range (fun k => SplitTorus.weightCharacter (g2Root k))) :
    Derivation.adjointWeightSpace weightTorusCoordinateMap.hom α = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  rw [Submodule.mem_bot]
  apply tangentMatrix_injective
  rw [map_zero]
  ext i j
  by_cases h : SplitTorus.weightCharacter (weight i - weight j) = α
  · apply tangentMatrix_apply_eq_zero_of_not_root x i j
    · intro hij
      subst j
      apply hα
      rw [← h]
      simp
    · rintro ⟨k, hk⟩
      exact hroot ⟨k, (congrArg SplitTorus.weightCharacter hk).trans h⟩
  · exact (mem_adjointWeightSpace_iff α x).mp hx i j h

/-- In the lifted coordinates of the chosen split maximal torus, every nonzero exponent
vector outside the named root set has zero adjoint weight space. -/
theorem adjointWeightSpace_splitMaximalTorus_eq_bot_of_not_root (μ : Fin 2 → ℤ)
    (hμ : μ ≠ 0) (hroot : μ ∉ Set.range g2Root) :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
      (SplitTorus.weightCharacter (fun j : ULift.{0} (Fin 2) => μ j.down)) = ⊥ := by
  rw [adjointWeightSpace_splitMaximalTorus_weightCharacter_eq_weightTorus]
  apply adjointWeightSpace_eq_bot_of_not_root
  · intro h
    exact hμ (SplitTorus.weightCharacter_eq_one_iff.mp h)
  · rintro ⟨k, hk⟩
    apply hroot
    refine ⟨k, funext fun j => ?_⟩
    simpa only [SplitTorus.toAdd_weightCharacter] using
      congrArg (fun χ : Multiplicative (Fin 2 →₀ ℤ) => Multiplicative.toAdd χ j) hk

/-- Every nontrivial adjoint weight of the short-root carrier is a root of the named
G₂ datum, in the original fundamental-weight torus coordinates. -/
theorem nontrivialAdjointWeights_subset_range_g2Root :
    Derivation.nontrivialAdjointWeights weightTorusCoordinateMap.hom ⊆
      Set.range (fun k => SplitTorus.weightCharacter (g2Root k)) := by
  intro α hα
  obtain ⟨hne, hspace⟩ := Derivation.mem_nontrivialAdjointWeights.mp hα
  by_contra h
  exact hspace (adjointWeightSpace_eq_bot_of_not_root α hne h)

end TauCeti.G2ShortRoot.PrimeField
