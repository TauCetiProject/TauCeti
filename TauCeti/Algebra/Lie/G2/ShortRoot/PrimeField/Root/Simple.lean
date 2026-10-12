/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Positive
import Mathlib.Tactic.ReduceModChar

/-!
# The intrinsic simple roots of the short-root G₂ carrier

For the chosen split maximal torus and positive subgroup of the short-root type-`G₂` carrier
over `𝔽₃`, the two numbered raising roots `α₁` (short) and `α₂` (long) are the only intrinsic
simple roots. Together with `TauCeti.G2ShortRoot.PrimeField.isSimpleRoot_simpleRootCharacter`
this identifies the intrinsically defined simple roots with the Bourbaki numbering, which is
how a pinning of the carrier indexes its simple root vectors.

An intrinsic positive root has a nonzero root space, so it is a difference of two weights of the
seven-dimensional module, and it has positive height. Of the nine such differences, three
(`2α₁`, `2(α₁ + α₂)` and `2(2α₁ + α₂)`) are not roots: a derivation of the cross product
supported on one of them vanishes, so their root spaces are zero. The remaining six are the
positive roots `α₁`, `α₂`, `α₁ + α₂`, `2α₁ + α₂`, `3α₁ + α₂` and `3α₁ + 2α₂`. The root spaces
of `α₁ + α₂` and `2α₁ + α₂` are the lines spanned by the brackets `[X₁, X₂]` and `[X₁, [X₁, X₂]]`
of the numbered root vectors, which lie in the tangent Lie algebra of the positive subgroup, so
these two are intrinsic positive roots. Each of the four non-simple roots is then a sum of two
intrinsic positive roots: `α₁ + α₂`, `α₁ + (α₁ + α₂)`, `α₁ + (2α₁ + α₂)` and
`(α₁ + α₂) + (2α₁ + α₂)`.

In characteristic three the brackets `[X₁, [X₁, [X₁, X₂]]]` and `[[X₁, X₂], [X₁, [X₁, X₂]]]`
vanish, so the long roots `3α₁ + α₂` and `3α₁ + 2α₂` are not reached this way; their
intrinsic positivity is not asserted here, and it is not needed to exclude them as simple roots.
Nor is it asserted that the positive subgroup is a Borel subgroup, or that the carrier is
identified with an independently pinned simply connected group scheme of type `G₂`.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.isSimpleRoot_iff_exists_simpleRootCharacter`: the intrinsic
  simple roots are exactly the two numbered raising roots.
* `TauCeti.G2ShortRoot.PrimeField.simpleRootCharacterEquiv`: the Bourbaki numbering as an
  equivalence onto the intrinsic simple roots.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The simple-root exhaustion and the numbering equivalence follow
`TauCeti.Symplectic.isSimpleRoot_iff_exists_diagonalSimpleRoot` and
`TauCeti.Symplectic.diagonalSimpleRootEquiv`; the cross-product computations follow
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space`.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

open DynkinType

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Characters in the lifted torus coordinates -/

/-- The character of the chosen split maximal torus with fundamental-weight coordinates `μ`. -/
private def liftCharacter (μ : Fin 2 → ℤ) : ULift.{0} (Fin 2) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun l => μ l.down

private theorem liftCharacter_apply (μ : Fin 2 → ℤ) (l : ULift.{0} (Fin 2)) :
    liftCharacter μ l = μ l.down := by
  simp [liftCharacter]

private theorem liftCharacter_add (μ ν : Fin 2 → ℤ) :
    liftCharacter (μ + ν) = liftCharacter μ + liftCharacter ν := by
  ext l
  simp [liftCharacter]

private theorem liftCharacter_injective : Function.Injective liftCharacter := by
  intro μ ν h
  funext l
  simpa [liftCharacter_apply] using DFunLike.congr_fun h (ULift.up l)

private theorem ofAdd_liftCharacter (μ : Fin 2 → ℤ) :
    Multiplicative.ofAdd (liftCharacter μ) =
      SplitTorus.weightCharacter (fun l : ULift.{0} (Fin 2) => μ l.down) := by
  rw [← SplitTorus.weightCharacter_coe]
  simp [liftCharacter]

/-- The numbered raising roots are the rows of the Cartan matrix `!![2, -1; -3, 2]`. -/
private theorem simpleRootCharacter_eq_liftCharacter (i : Fin 2) :
    simpleRootCharacter i =
      liftCharacter (fun j => (!![2, -1; -3, 2] : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
  have hrow : (G2.simplyConnectedRootDatum valid_G2).root (G2.simpleIndex valid_G2 i) =
      fun j : Fin 2 => (!![2, -1; -3, 2] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    simpa only [rank_G2, cartanMatrix_G2_eq] using root_simpleIndex G2 valid_G2 i
  ext l
  rw [simpleRootCharacter_apply, hrow, liftCharacter_apply]

private theorem simpleRootCharacter_zero : simpleRootCharacter 0 = liftCharacter ![2, -1] := by
  rw [simpleRootCharacter_eq_liftCharacter]
  exact congrArg liftCharacter (funext fun j => by fin_cases j <;> rfl)

private theorem simpleRootCharacter_one : simpleRootCharacter 1 = liftCharacter ![-3, 2] := by
  rw [simpleRootCharacter_eq_liftCharacter]
  exact congrArg liftCharacter (funext fun j => by fin_cases j <;> rfl)

/-- The numbering of the raising roots is injective. -/
theorem simpleRootCharacter_injective : Function.Injective simpleRootCharacter := by
  intro i j h
  have h0 := DFunLike.congr_fun h (ULift.up 0)
  rw [simpleRootCharacter_eq_liftCharacter, simpleRootCharacter_eq_liftCharacter,
    liftCharacter_apply, liftCharacter_apply] at h0
  revert h0
  fin_cases i <;> fin_cases j <;> decide

/-- **The weight-space criterion in fundamental-weight coordinates.** A tangent vector of the
carrier lies in the root space of the chosen torus at the character with coordinates `μ` exactly
when the entries of its matrix vanish off the weight differences equal to `μ`. -/
private theorem mem_adjointWeightSpace_liftCharacter_iff (μ : Fin 2 → ℤ)
    (x : Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra)) :
    x ∈ Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (Multiplicative.ofAdd (liftCharacter μ)) ↔
      ∀ i j, weight i - weight j ≠ μ → tangentMatrix x i j = 0 := by
  have hspace : Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
      (Multiplicative.ofAdd (liftCharacter μ)) =
        Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
          (SplitTorus.weightCharacter μ) :=
    (congrArg (Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom)
      (ofAdd_liftCharacter μ)).trans
        (adjointWeightSpace_splitMaximalTorus_weightCharacter_eq_weightTorus μ)
  rw [hspace, mem_adjointWeightSpace_iff]
  have hinj : ∀ ν : Fin 2 → ℤ,
      SplitTorus.weightCharacter ν = SplitTorus.weightCharacter μ ↔ ν = μ := fun ν =>
    ⟨fun h => funext fun l => by
      simpa only [SplitTorus.toAdd_weightCharacter] using
        congrArg (fun χ : Multiplicative (Fin 2 →₀ ℤ) => Multiplicative.toAdd χ l) h,
      fun h => h ▸ rfl⟩
  simp only [ne_eq, hinj]

/-! ## Cross-product derivations of a positive weight -/

/- Normalization for one entry of the derivation equation of an explicit matrix, as in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space`: expand the matrix products and the
structure constants, then reduce the coefficients modulo three. -/
local macro "cross_entry_norm" : tactic =>
  `(tactic| (simp [Matrix.mul_apply, Fin.sum_univ_succ,
    ConstantMultiplication.imageStructureMatrix_def, crossOperator_def]; ring_nf; reduce_mod_char))

/-- The derivation equation of the cross product, for a matrix over `𝔽₃`. -/
private def IsCrossDerivation (X : Matrix (Fin 7) (Fin 7) (ZMod 3)) : Prop :=
  ∀ c, X * crossOperatorPrime c =
    ConstantMultiplication.imageStructureMatrix (ZMod 3) 7 crossOperatorPrime X c +
      crossOperatorPrime c * X

/-- A cross-product derivation of weight `2α₁` vanishes. -/
private theorem eq_zero_of_weight_twice_short (X : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (hX : IsCrossDerivation X) (hsupp : ∀ i j, weight i - weight j ≠ ![4, -2] → X i j = 0) :
    X = 0 := by
  have hXe : X = !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, X 2 4, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact hsupp _ _ (by decide)
  rw [hXe] at hX
  have h : X 2 4 = 0 := by
    linear_combination (norm := cross_entry_norm) congrFun (congrFun (hX 1) 0) 4
  rw [hXe, h]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A cross-product derivation of weight `2(α₁ + α₂)` vanishes. -/
private theorem eq_zero_of_weight_twice_shortSum (X : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (hX : IsCrossDerivation X) (hsupp : ∀ i j, weight i - weight j ≠ ![-2, 2] → X i j = 0) :
    X = 0 := by
  have hXe : X = !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, X 1 5, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact hsupp _ _ (by decide)
  rw [hXe] at hX
  have h : X 1 5 = 0 := by
    linear_combination (norm := cross_entry_norm) congrFun (congrFun (hX 2) 1) 6
  rw [hXe, h]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A cross-product derivation of weight `2(2α₁ + α₂)` vanishes. -/
private theorem eq_zero_of_weight_twice_highestShort (X : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (hX : IsCrossDerivation X) (hsupp : ∀ i j, weight i - weight j ≠ ![2, 0] → X i j = 0) :
    X = 0 := by
  have hXe : X = !![0, 0, 0, 0, 0, 0, X 0 6;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact hsupp _ _ (by decide)
  rw [hXe] at hX
  have h : X 0 6 = 0 := by
    linear_combination (norm := cross_entry_norm) congrFun (congrFun (hX 4) 1) 6
  rw [hXe, h]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The root generator `E₁` reduced to `𝔽₃`. -/
private theorem map_raisingMatrix_zero :
    (raisingMatrix 0).map (Int.cast : ℤ → ZMod 3) =
      !![0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 2, 0, 0, 0;
        0, 0, 0, 0, 1, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 1;
        0, 0, 0, 0, 0, 0, 0] := by
  decide

/-- The root generator `E₂` reduced to `𝔽₃`. -/
private theorem map_raisingMatrix_one :
    (raisingMatrix 1).map (Int.cast : ℤ → ZMod 3) =
      !![0, 0, 0, 0, 0, 0, 0;
        0, 0, 1, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 1, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
  decide

/-- A cross-product derivation of weight `α₁ + α₂` is a multiple of `[E₁, E₂]`. -/
private theorem exists_eq_smul_of_weight_shortSum (X : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (hX : IsCrossDerivation X) (hsupp : ∀ i j, weight i - weight j ≠ ![-1, 1] → X i j = 0) :
    ∃ t : ZMod 3, X = t •
      !![0, 0, 1, 0, 0, 0, 0;
        0, 0, 0, 1, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 1, 0;
        0, 0, 0, 0, 0, 0, 2;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
  have hXe : X = !![0, 0, X 0 2, 0, 0, 0, 0;
      0, 0, 0, X 1 3, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, X 3 5, 0;
      0, 0, 0, 0, 0, 0, X 4 6;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact hsupp _ _ (by decide)
  rw [hXe] at hX
  have h13 : X 1 3 = X 0 2 := by
    linear_combination (norm := cross_entry_norm) 2 * congrFun (congrFun (hX 2) 0) 3
  have h35 : X 3 5 = X 0 2 := by
    linear_combination (norm := cross_entry_norm) 2 * congrFun (congrFun (hX 0) 0) 5
  have h46 : X 4 6 = 2 * X 0 2 := by
    linear_combination (norm := cross_entry_norm) congrFun (congrFun (hX 6) 1) 0 - h13
  refine ⟨X 0 2, ?_⟩
  conv_lhs => rw [hXe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h13, h35, h46, mul_comm]

/-- A cross-product derivation of weight `2α₁ + α₂` is a multiple of `[E₁, [E₁, E₂]]`. -/
private theorem exists_eq_smul_of_weight_highestShort (X : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (hX : IsCrossDerivation X) (hsupp : ∀ i j, weight i - weight j ≠ ![1, 0] → X i j = 0) :
    ∃ t : ZMod 3, X = t •
      !![0, 0, 0, 2, 0, 0, 0;
        0, 0, 0, 0, 2, 0, 0;
        0, 0, 0, 0, 0, 2, 0;
        0, 0, 0, 0, 0, 0, 1;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
  have hXe : X = !![0, 0, 0, X 0 3, 0, 0, 0;
      0, 0, 0, 0, X 1 4, 0, 0;
      0, 0, 0, 0, 0, X 2 5, 0;
      0, 0, 0, 0, 0, 0, X 3 6;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact hsupp _ _ (by decide)
  rw [hXe] at hX
  have h14 : X 1 4 = X 0 3 := by
    linear_combination (norm := cross_entry_norm) 2 * congrFun (congrFun (hX 2) 0) 4
  have h25 : X 2 5 = X 0 3 := by
    linear_combination (norm := cross_entry_norm) 2 * congrFun (congrFun (hX 5) 0) 1
  have h36 : X 3 6 = 2 * X 0 3 := by
    linear_combination (norm := cross_entry_norm) congrFun (congrFun (hX 3) 3) 6
  refine ⟨2 * X 0 3, ?_⟩
  conv_lhs => rw [hXe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h14, h25, h36] <;> ring_nf <;> reduce_mod_char

/-! ## Root spaces of positive weights -/

/-- A weight whose cross-product derivations all vanish has zero root space. -/
private theorem adjointWeightSpace_liftCharacter_eq_bot (μ : Fin 2 → ℤ)
    (h : ∀ X, IsCrossDerivation X → (∀ i j, weight i - weight j ≠ μ → X i j = 0) → X = 0) :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
      (Multiplicative.ofAdd (liftCharacter μ)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  apply tangentMatrix_injective
  rw [map_zero]
  exact h _ (tangentMatrix_mul_crossOperatorPrime x)
    ((mem_adjointWeightSpace_liftCharacter_iff μ x).mp hx)

/-- A weight whose root space is the line spanned by a nonzero tangent vector of the positive
subgroup is an intrinsic positive root. -/
private theorem isPositiveRoot_liftCharacter (μ : Fin 2 → ℤ) (hμ : μ ≠ 0)
    (v : Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra))
    (hspan : Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
      (Multiplicative.ofAdd (liftCharacter μ)) = (ZMod 3) ∙ v) (hv : v ≠ 0)
    (hmem : Derivation.cotangentLinearEquiv (B := ZMod 3) v ∈
      positiveDefiningIdeal.lieSubalgebra) :
    splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal (liftCharacter μ) := by
  have hvW : v ∈ Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
      (Multiplicative.ofAdd (liftCharacter μ)) :=
    hspan ▸ Submodule.mem_span_singleton_self v
  rw [SplitMaximalTorus.isPositiveRoot_iff, Derivation.mem_nontrivialAdjointWeights]
  refine ⟨⟨fun h => hμ (liftCharacter_injective ?_), (Submodule.ne_bot_iff _).mpr ⟨v, hvW, hv⟩⟩,
    fun x hx => ?_⟩
  · rw [Multiplicative.ofAdd.injective h]
    ext l
    simp [liftCharacter]
  · rw [hspan] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    exact positiveDefiningIdeal.lieSubalgebra.smul_mem c hmem

/-- The tangent vector `[X₁, X₂]` of the carrier, of weight `α₁ + α₂`. -/
private def shortSumVector :
    Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra) :=
  (Derivation.cotangentLinearEquiv (B := ZMod 3)).symm
    ⁅Derivation.cotangentLinearEquiv (B := ZMod 3) (rootVector (.inl 0)),
      Derivation.cotangentLinearEquiv (B := ZMod 3) (rootVector (.inl 1))⁆

/-- The tangent vector `[X₁, [X₁, X₂]]` of the carrier, of weight `2α₁ + α₂`. -/
private def highestShortVector :
    Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra) :=
  (Derivation.cotangentLinearEquiv (B := ZMod 3)).symm
    ⁅Derivation.cotangentLinearEquiv (B := ZMod 3) (rootVector (.inl 0)),
      Derivation.cotangentLinearEquiv (B := ZMod 3) shortSumVector⁆

private theorem tangentMatrix_shortSumVector :
    tangentMatrix shortSumVector =
      !![0, 0, 1, 0, 0, 0, 0;
        0, 0, 0, 1, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 1, 0;
        0, 0, 0, 0, 0, 0, 2;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
  rw [shortSumVector, tangentMatrix_symm_lie, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, tangentMatrix_rootVector, tangentMatrix_rootVector,
    rootMatrix_inl, rootMatrix_inl, map_raisingMatrix_zero, map_raisingMatrix_one, Ring.lie_def]
  decide

private theorem tangentMatrix_highestShortVector :
    tangentMatrix highestShortVector =
      !![0, 0, 0, 2, 0, 0, 0;
        0, 0, 0, 0, 2, 0, 0;
        0, 0, 0, 0, 0, 2, 0;
        0, 0, 0, 0, 0, 0, 1;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0] := by
  rw [highestShortVector, tangentMatrix_symm_lie, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, tangentMatrix_rootVector, tangentMatrix_shortSumVector,
    rootMatrix_inl, map_raisingMatrix_zero, Ring.lie_def]
  decide

private theorem cotangentLinearEquiv_shortSumVector_mem :
    Derivation.cotangentLinearEquiv (B := ZMod 3) shortSumVector ∈
      positiveDefiningIdeal.lieSubalgebra := by
  rw [shortSumVector, LinearEquiv.apply_symm_apply]
  exact LieSubalgebra.lie_mem _
    (cotangentLinearEquiv_rootVector_inl_mem_positiveDefiningIdeal_lieSubalgebra 0)
    (cotangentLinearEquiv_rootVector_inl_mem_positiveDefiningIdeal_lieSubalgebra 1)

private theorem cotangentLinearEquiv_highestShortVector_mem :
    Derivation.cotangentLinearEquiv (B := ZMod 3) highestShortVector ∈
      positiveDefiningIdeal.lieSubalgebra := by
  rw [highestShortVector, LinearEquiv.apply_symm_apply]
  exact LieSubalgebra.lie_mem _
    (cotangentLinearEquiv_rootVector_inl_mem_positiveDefiningIdeal_lieSubalgebra 0)
    cotangentLinearEquiv_shortSumVector_mem

/-- The root space of `α₁ + α₂` is the line spanned by `[X₁, X₂]`. -/
private theorem adjointWeightSpace_shortSum_eq_span :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
      (Multiplicative.ofAdd (liftCharacter ![-1, 1])) = (ZMod 3) ∙ shortSumVector := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht⟩ := exists_eq_smul_of_weight_shortSum (tangentMatrix x)
      (tangentMatrix_mul_crossOperatorPrime x)
      ((mem_adjointWeightSpace_liftCharacter_iff _ x).mp hx)
    refine Submodule.mem_span_singleton.mpr ⟨t, tangentMatrix_injective ?_⟩
    rw [map_smul, tangentMatrix_shortSumVector, ht]
  · rw [Submodule.span_singleton_le_iff_mem, mem_adjointWeightSpace_liftCharacter_iff,
      tangentMatrix_shortSumVector]
    intro i j h
    revert h
    fin_cases i <;> fin_cases j <;> decide

/-- The root space of `2α₁ + α₂` is the line spanned by `[X₁, [X₁, X₂]]`. -/
private theorem adjointWeightSpace_highestShort_eq_span :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
      (Multiplicative.ofAdd (liftCharacter ![1, 0])) = (ZMod 3) ∙ highestShortVector := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht⟩ := exists_eq_smul_of_weight_highestShort (tangentMatrix x)
      (tangentMatrix_mul_crossOperatorPrime x)
      ((mem_adjointWeightSpace_liftCharacter_iff _ x).mp hx)
    refine Submodule.mem_span_singleton.mpr ⟨t, tangentMatrix_injective ?_⟩
    rw [map_smul, tangentMatrix_highestShortVector, ht]
  · rw [Submodule.span_singleton_le_iff_mem, mem_adjointWeightSpace_liftCharacter_iff,
      tangentMatrix_highestShortVector]
    intro i j h
    revert h
    fin_cases i <;> fin_cases j <;> decide

/-- The short root `α₁ + α₂` is an intrinsic positive root. -/
private theorem isPositiveRoot_shortSum :
    splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal (liftCharacter ![-1, 1]) :=
  isPositiveRoot_liftCharacter _ (by decide) _ adjointWeightSpace_shortSum_eq_span
    (fun h => by
      have h' := congrFun (congrFun (congrArg tangentMatrix h) 0) 2
      rw [tangentMatrix_shortSumVector, map_zero] at h'
      exact absurd h' (by decide))
    cotangentLinearEquiv_shortSumVector_mem

/-- The highest short root `2α₁ + α₂` is an intrinsic positive root. -/
private theorem isPositiveRoot_highestShort :
    splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal (liftCharacter ![1, 0]) :=
  isPositiveRoot_liftCharacter _ (by decide) _ adjointWeightSpace_highestShort_eq_span
    (fun h => by
      have h' := congrFun (congrFun (congrArg tangentMatrix h) 3) 6
      rw [tangentMatrix_highestShortVector, map_zero] at h'
      exact absurd h' (by decide))
    cotangentLinearEquiv_highestShortVector_mem

/-! ## Exhaustion of the intrinsic simple roots -/

/-- The weight differences of the seven-dimensional module of positive height `3a + 5b`: the six
positive roots, followed by the three non-roots `2α₁`, `2(α₁ + α₂)` and `2(2α₁ + α₂)`. -/
private theorem weight_sub_cases (i j : Fin 7)
    (h : 0 < 3 * (weight i 0 - weight j 0) + 5 * (weight i 1 - weight j 1)) :
    weight i - weight j = ![2, -1] ∨ weight i - weight j = ![-3, 2] ∨
      weight i - weight j = ![-1, 1] ∨ weight i - weight j = ![1, 0] ∨
      weight i - weight j = ![3, -1] ∨ weight i - weight j = ![0, 1] ∨
      weight i - weight j = ![4, -2] ∨ weight i - weight j = ![-2, 2] ∨
      weight i - weight j = ![2, 0] := by
  revert h
  fin_cases i <;> fin_cases j <;> decide

/-- An intrinsic positive root is a weight difference of positive height with a nonzero root
space. -/
private theorem exists_weight_sub_of_isPositiveRoot (α : ULift.{0} (Fin 2) →₀ ℤ)
    (hα : splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal α) :
    ∃ i j, α = liftCharacter (weight i - weight j) ∧
      Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (Multiplicative.ofAdd α) ≠ ⊥ ∧
      0 < 3 * (weight i 0 - weight j 0) + 5 * (weight i 1 - weight j 1) := by
  have hh := height_pos_of_isPositiveRoot α hα
  rw [SplitMaximalTorus.isPositiveRoot_iff] at hα
  obtain ⟨-, hspace⟩ := Derivation.mem_nontrivialAdjointWeights.mp hα.1
  obtain ⟨x, hx, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hspace
  have hm : tangentMatrix x ≠ 0 := fun h => hxne
    (tangentMatrix_injective (h.trans (map_zero tangentMatrix).symm))
  obtain ⟨i, j, hij⟩ : ∃ i j, tangentMatrix x i j ≠ 0 := by
    contrapose! hm
    ext i j
    exact hm i j
  have heq : SplitTorus.weightCharacter
      (fun b : ULift.{0} (Fin 2) => weight i b.down - weight j b.down) =
        Multiplicative.ofAdd α := by
    by_contra h
    exact hij ((mem_adjointWeightSpace_splitMaximalTorus_iff _ x).mp hx i j h)
  have hα' : α = liftCharacter (weight i - weight j) := by
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_liftCharacter, ← heq]
    simp only [Pi.sub_apply]
  refine ⟨i, j, hα', hspace, ?_⟩
  simpa only [hα', liftCharacter_apply, Pi.sub_apply] using hh

/-- **The numbered raising roots exhaust the intrinsic simple roots.** For the chosen split
maximal torus and positive subgroup of the short-root carrier over `𝔽₃`, a character is an
intrinsic simple root exactly when it is `α₁` or `α₂` in Bourbaki numbering. -/
theorem isSimpleRoot_iff_exists_simpleRootCharacter (α : ULift.{0} (Fin 2) →₀ ℤ) :
    splitMaximalTorus.IsSimpleRoot positiveDefiningIdeal α ↔ ∃ i, α = simpleRootCharacter i := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨hpos, hindec⟩ := (SplitMaximalTorus.isSimpleRoot_iff _ _ α).mp h
    obtain ⟨i, j, rfl, hne, hh⟩ := exists_weight_sub_of_isPositiveRoot _ hpos
    have h₁ := isPositiveRoot_simpleRootCharacter 0
    have h₂ := isPositiveRoot_simpleRootCharacter 1
    rw [simpleRootCharacter_zero] at h₁
    rw [simpleRootCharacter_one] at h₂
    have hsum (μ ν : Fin 2 → ℤ) (hμ : splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal
        (liftCharacter μ)) (hν : splitMaximalTorus.IsPositiveRoot positiveDefiningIdeal
        (liftCharacter ν)) : weight i - weight j ≠ μ + ν := fun hv =>
      hindec _ _ hμ hν (by rw [hv, liftCharacter_add])
    -- The three non-roots have zero root spaces; the four non-simple roots are sums of two
    -- intrinsic positive roots among `α₁`, `α₂`, `α₁ + α₂` and `2α₁ + α₂`.
    rcases weight_sub_cases i j hh with hv | hv | hv | hv | hv | hv | hv | hv | hv
    · exact ⟨0, by rw [hv, simpleRootCharacter_zero]⟩
    · exact ⟨1, by rw [hv, simpleRootCharacter_one]⟩
    · exact absurd (hv.trans (by decide)) (hsum _ _ h₁ h₂)
    · exact absurd (hv.trans (by decide)) (hsum _ _ h₁ isPositiveRoot_shortSum)
    · exact absurd (hv.trans (by decide)) (hsum _ _ h₁ isPositiveRoot_highestShort)
    · exact absurd (hv.trans (by decide)) (hsum _ _ isPositiveRoot_shortSum
        isPositiveRoot_highestShort)
    · exact absurd (adjointWeightSpace_liftCharacter_eq_bot _ eq_zero_of_weight_twice_short)
        (hv ▸ hne)
    · exact absurd (adjointWeightSpace_liftCharacter_eq_bot _ eq_zero_of_weight_twice_shortSum)
        (hv ▸ hne)
    · exact absurd
        (adjointWeightSpace_liftCharacter_eq_bot _ eq_zero_of_weight_twice_highestShort)
        (hv ▸ hne)
  · rintro ⟨i, rfl⟩
    exact isSimpleRoot_simpleRootCharacter i

/-- **Bourbaki numbering of the intrinsic simple roots** of the short-root carrier over `𝔽₃`, for
its chosen split maximal torus and positive subgroup: node `i` goes to the raising root
`simpleRootCharacter i`. -/
def simpleRootCharacterEquiv :
    Fin 2 ≃ {α // splitMaximalTorus.IsSimpleRoot positiveDefiningIdeal α} :=
  Equiv.ofBijective (fun i => ⟨simpleRootCharacter i, isSimpleRoot_simpleRootCharacter i⟩)
    ⟨fun _ _ h => simpleRootCharacter_injective (congrArg Subtype.val h), fun α => by
      obtain ⟨i, hi⟩ := (isSimpleRoot_iff_exists_simpleRootCharacter α.val).mp α.property
      exact ⟨i, Subtype.ext hi.symm⟩⟩

/-- The intrinsic simple root at node `i` is the numbered raising root. -/
@[simp]
theorem simpleRootCharacterEquiv_apply (i : Fin 2) :
    (simpleRootCharacterEquiv i).val = simpleRootCharacter i := (rfl)

end

end TauCeti.G2ShortRoot.PrimeField
