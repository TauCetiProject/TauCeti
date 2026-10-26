/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Dimension

/-!
# The Weyl dimension product in type A₂

For the pinned simply connected root datum of type `A₂`, the three positive roots are
`α₁`, `α₂`, and `α₁ + α₂`.  Consequently the Weyl dimension product at the
dominant weight with fundamental-weight coordinates `(a, b)` is

`(a + 1)(b + 1)(a + b + 2) / 2`.

This is the root-datum computation needed to specialize the abstract Weyl dimension formula to
the `A₂` worked example.  The numerator and denominator are first stated integrally, making the
factor `2` contributed by the nonsimple positive root explicit; their quotient is stated in `ℚ`.

## Main results

* `DynkinType.posRootsFinset_typeA_two`: the positive roots of the pinned `A₂` datum.
* `DynkinType.prod_shiftedCorootPairing_typeA_two`: the numerator in the Weyl dimension formula.
* `DynkinType.prod_positiveCorootHeight_typeA_two`: the denominator in the formula.
* `DynkinType.weylDimensionProduct_typeA_two`: the `A₂` Weyl dimension product.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §24.3.
-/

public section

namespace TauCeti

open RootPairing

namespace DynkinType

/-- The highest positive root of the pinned `A₂` datum, indexed by the classical root
`e₀ - e₂ = α₁ + α₂`. -/
def typeA2HighestRootIndex : Fin 6 :=
  typeAIndexEquiv 2 ⟨(⟨0, by omega⟩, ⟨2, by omega⟩), by decide⟩

private theorem typeA2HighestRootIndex_ne_simple (i : Fin 2) :
    typeA2HighestRootIndex ≠ typeASimpleIndex 2 i := by
  intro h
  have h' := congrArg (typeAIndexEquiv 2).symm h
  simp only [typeA2HighestRootIndex, Equiv.symm_apply_apply,
    typeAIndexEquiv_symm_typeASimpleIndex] at h'
  fin_cases i <;> simp [Fin.ext_iff] at h'

private theorem typeASimpleIndex_two_ne : typeASimpleIndex 2 0 ≠ typeASimpleIndex 2 1 := by
  intro h
  have h' := congrArg Fin.val h
  norm_num [typeASimpleIndex_val] at h'

/-- The root indexed by `typeA2HighestRootIndex` is the sum of the two simple roots. -/
theorem root_typeA2HighestRootIndex :
    (typeASimplyConnectedRootDatum 2).root typeA2HighestRootIndex =
      (typeASimplyConnectedRootDatum 2).root (typeASimpleIndex 2 0) +
        (typeASimplyConnectedRootDatum 2).root (typeASimpleIndex 2 1) := by
  funext i
  fin_cases i
  · unfold typeA2HighestRootIndex
    rw [root_typeAIndexEquiv, root_typeASimpleIndex, root_typeASimpleIndex]
    simp [CartanMatrix.A]
  · unfold typeA2HighestRootIndex
    rw [root_typeAIndexEquiv, root_typeASimpleIndex, root_typeASimpleIndex]
    simp [CartanMatrix.A]

private theorem typeA2HighestRootIndex_mem_posRoots :
    typeA2HighestRootIndex ∈
      posRoots (typeASimplyConnectedRootDatum 2) (typeASimplyConnectedBase 2) := by
  rw [mem_posRoots]
  exact RootPairing.Base.IsPos.add
    ((typeASimplyConnectedBase 2).isPos_of_mem_support (by
      rw [mem_typeASimplyConnectedBase_support]
      simp))
    ((typeASimplyConnectedBase 2).isPos_of_mem_support (by
      rw [mem_typeASimplyConnectedBase_support]
      simp)) root_typeA2HighestRootIndex

/-- **The positive roots of the pinned `A₂` datum are `α₁`, `α₂`, and
`α₁ + α₂`.** -/
theorem posRootsFinset_typeA_two :
    posRootsFinset (typeASimplyConnectedRootDatum 2) (typeASimplyConnectedBase 2) =
      {typeASimpleIndex 2 0, typeASimpleIndex 2 1, typeA2HighestRootIndex} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact (mem_posRootsFinset _ _ _).mpr
        (support_subset_posRoots _ _ (by
          exact Finset.mem_coe.mpr (by
            rw [mem_typeASimplyConnectedBase_support]
            simp)))
    · exact (mem_posRootsFinset _ _ _).mpr
        (support_subset_posRoots _ _ (by
          exact Finset.mem_coe.mpr (by
            rw [mem_typeASimplyConnectedBase_support]
            simp)))
    · exact (mem_posRootsFinset _ _ _).mpr typeA2HighestRootIndex_mem_posRoots
  · rw [card_posRootsFinset, ncard_posRoots_typeASimplyConnectedRootDatum]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · norm_num
    · simpa using (typeA2HighestRootIndex_ne_simple 1).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨typeASimpleIndex_two_ne, (typeA2HighestRootIndex_ne_simple 0).symm⟩

/-- Pairing a weight with the highest coroot of type `A₂` sums its two
fundamental-weight coordinates. -/
theorem pairing_typeA2HighestRootIndex (x : Fin 2 → ℤ) :
    (typeASimplyConnectedRootDatum 2).toLinearMap x
        ((typeASimplyConnectedRootDatum 2).coroot typeA2HighestRootIndex) = x 0 + x 1 := by
  have hc : (typeASimplyConnectedRootDatum 2).coroot typeA2HighestRootIndex = ![1, 1] := by
    funext i
    unfold typeA2HighestRootIndex
    rw [coroot_typeAIndexEquiv]
    fin_cases i <;> simp
  rw [toLinearMap_typeASimplyConnectedRootDatum, hc]
  simp [dotProduct]

private theorem pairing_typeASimpleIndex_two (x : Fin 2 → ℤ) (i : Fin 2) :
    (typeASimplyConnectedRootDatum 2).toLinearMap x
        ((typeASimplyConnectedRootDatum 2).coroot (typeASimpleIndex 2 i)) = x i := by
  rw [coroot_typeASimpleIndex, toLinearMap_typeASimplyConnectedRootDatum]
  fin_cases i <;> simp [dotProduct, Pi.single_apply]

/-- The coroot indexed by `typeA2HighestRootIndex` is the sum of the two simple coroots. -/
theorem coroot_typeA2HighestRootIndex :
    (typeASimplyConnectedRootDatum 2).coroot typeA2HighestRootIndex =
      (typeASimplyConnectedRootDatum 2).coroot (typeASimpleIndex 2 0) +
        (typeASimplyConnectedRootDatum 2).coroot (typeASimpleIndex 2 1) := by
  funext i
  unfold typeA2HighestRootIndex
  rw [coroot_typeAIndexEquiv, coroot_typeASimpleIndex, coroot_typeASimpleIndex]
  fin_cases i <;> simp

private theorem height_flip_typeASimpleIndex_two (i : Fin 2) :
    (typeASimplyConnectedBase 2).flip.height (typeASimpleIndex 2 i) = 1 := by
  apply (typeASimplyConnectedBase 2).flip.height_one_of_mem_support
  rw [RootPairing.Base.flip_support]
  exact Finset.mem_coe.mpr (by
    rw [mem_typeASimplyConnectedBase_support, typeASimpleIndex_val]
    exact i.isLt)

/-- The highest coroot of type `A₂` has height two. -/
theorem height_flip_typeA2HighestRootIndex :
    (typeASimplyConnectedBase 2).flip.height typeA2HighestRootIndex = 2 := by
  rw [(typeASimplyConnectedBase 2).flip.height_add coroot_typeA2HighestRootIndex]
  rw [height_flip_typeASimpleIndex_two, height_flip_typeASimpleIndex_two]
  norm_num

attribute [simp↓] pairing_typeA2HighestRootIndex height_flip_typeA2HighestRootIndex

private theorem prod_posRootsFinset_typeA_two (f : Fin 6 → ℤ) :
    ∏ i ∈ posRootsFinset (typeASimplyConnectedRootDatum 2) (typeASimplyConnectedBase 2),
      f i =
        f (typeASimpleIndex 2 0) * f (typeASimpleIndex 2 1) * f typeA2HighestRootIndex := by
  rw [posRootsFinset_typeA_two]
  rw [Finset.prod_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨typeASimpleIndex_two_ne, (typeA2HighestRootIndex_ne_simple 0).symm⟩),
    Finset.prod_insert (by simpa using (typeA2HighestRootIndex_ne_simple 1).symm),
    Finset.prod_singleton]
  simp only [mul_assoc]

/-- **The Weyl numerator product in type `A₂`.** At the fundamental-weight coordinates
`(a, b)`, its three factors are `a + 1`, `b + 1`, and `a + b + 2`. -/
theorem prod_shiftedCorootPairing_typeA_two (a b : ℤ) :
    ∏ i ∈ posRootsFinset (typeASimplyConnectedRootDatum 2) (typeASimplyConnectedBase 2),
        ((typeASimplyConnectedRootDatum 2).toLinearMap ![a, b]
          ((typeASimplyConnectedRootDatum 2).coroot i) +
            (typeASimplyConnectedBase 2).flip.height i) =
      (a + 1) * (b + 1) * (a + b + 2) := by
  rw [prod_posRootsFinset_typeA_two]
  rw [pairing_typeASimpleIndex_two, pairing_typeASimpleIndex_two,
    pairing_typeA2HighestRootIndex, height_flip_typeASimpleIndex_two,
    height_flip_typeASimpleIndex_two, height_flip_typeA2HighestRootIndex]
  simp

/-- The denominator in the `A₂` Weyl dimension formula is `2`: its factors are `1`, `1`, and
`2`, the heights of the three positive coroots. -/
theorem prod_positiveCorootHeight_typeA_two :
    ∏ i ∈ posRootsFinset (typeASimplyConnectedRootDatum 2) (typeASimplyConnectedBase 2),
      (typeASimplyConnectedBase 2).flip.height i = 2 := by
  rw [prod_posRootsFinset_typeA_two, height_flip_typeASimpleIndex_two,
    height_flip_typeASimpleIndex_two, height_flip_typeA2HighestRootIndex]
  norm_num

/-- **The Weyl dimension product for type `A₂`.** At the weight with fundamental-weight
coordinates `(a, b)`, the quotient of the shifted coroot-pairing product by the positive-coroot
height product is `(a + 1)(b + 1)(a + b + 2) / 2`. -/
theorem weylDimensionProduct_typeA_two (a b : ℤ) :
    ((∏ i ∈ posRootsFinset
          (typeASimplyConnectedRootDatum 2) (typeASimplyConnectedBase 2),
        ((typeASimplyConnectedRootDatum 2).toLinearMap ![a, b]
          ((typeASimplyConnectedRootDatum 2).coroot i) +
            (typeASimplyConnectedBase 2).flip.height i) : ℤ) : ℚ) /
      ((∏ i ∈ posRootsFinset
          (typeASimplyConnectedRootDatum 2) (typeASimplyConnectedBase 2),
        (typeASimplyConnectedBase 2).flip.height i : ℤ) : ℚ) =
      (((a + 1) * (b + 1) * (a + b + 2) : ℤ) : ℚ) / 2 := by
  rw [prod_shiftedCorootPairing_typeA_two, prod_positiveCorootHeight_typeA_two]
  norm_num

end DynkinType

end TauCeti
