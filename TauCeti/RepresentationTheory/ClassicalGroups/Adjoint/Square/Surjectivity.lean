/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.SymmetricProduct
public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Products
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import Mathlib.Data.Fin.Basic

/-! # Surjectivity of the two adjoint-square contractions

For matrix size at least three, the Lie-bracket contraction onto trace-zero matrices is
surjective over any commutative ring. The bracket is also surjective in every size that is a
unit in the ring. The traceless symmetric contraction is surjective for sizes at least three
that are units in the scalar ring. These results give the injectivity of the two
trace-transpose embeddings.
-/

public section
namespace TauCeti.AdjointSquare
open Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K : Type*} {n : ℕ}
variable [CommRing K]
local notation "𝔰" => LieAlgebra.SpecialLinear.sl (Fin n)

open LieAlgebra.SpecialLinear (single val_single coe_symmetricProduct val_singleSubSingle)


private def pair (i j k l : Fin n) (h : i ≠ j) (h' : k ≠ l) (c : K) : 𝔰 K ⊗[K] 𝔰 K :=
  single i j h c ⊗ₜ[K] single k l h' 1

private theorem exists_third (i j : Fin n) (hn : 3 ≤ n) : ∃ k, i ≠ k ∧ k ≠ j := by
  obtain ⟨k, hik, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  exact ⟨k, hik.symm, hkj⟩

private theorem alternating_chain (i k j : Fin n) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j)
    (c : K) : (alternatingProductMap K n (pair i k k j hik hkj c)).val = Matrix.single i j c := by
  simp [pair, hij.symm]

private theorem alternating_cycle (i j : Fin n) (h : i ≠ j) (c : K) :
    (alternatingProductMap K n (pair i j j i h h.symm c)).val =
      Matrix.single i i c - Matrix.single j j c := by
  simp [pair]

/-- The Lie-bracket contraction onto trace-zero matrices is surjective over any commutative
ring when the matrix size is at least three. -/
theorem alternatingProductMap_surjective (K : Type*) [CommRing K] (n : ℕ) (hn : 3 ≤ n) :
    Function.Surjective (alternatingProductMap K n) := by
  apply (alternatingProductMap K n).toLinearMap.surjective_to_sl_of_matrix_units
  · intro i j hij
    obtain ⟨k, hik, hkj⟩ := exists_third i j hn
    exact LinearMap.mem_range.mpr ⟨_, Subtype.ext (alternating_chain i k j hik hkj hij 1)⟩
  · intro i j h
    exact LinearMap.mem_range.mpr ⟨_, Subtype.ext (alternating_cycle i j h 1)⟩

/-- If the matrix size is a unit in the scalar ring, the bracket contraction is surjective
in every size: subtracting a scalar from a diagonal unit makes it traceless without changing
its commutator with an off-diagonal unit. -/
theorem alternatingProductMap_surjective_of_isUnit (K : Type*) [CommRing K] (n : ℕ)
    (hn : IsUnit (n : K)) : Function.Surjective (alternatingProductMap K n) := by
  apply (alternatingProductMap K n).toLinearMap.surjective_to_sl_of_matrix_units
  · intro i j hij
    obtain ⟨X, r, hX⟩ := exists_sl_add_smul_one_eq (fun _ => by simpa using hn)
      (Matrix.single i i (1 : K))
    refine LinearMap.mem_range.mpr ⟨X ⊗ₜ[K] single i j hij 1, Subtype.ext ?_⟩
    rw [Representation.IntertwiningMap.toLinearMap_apply, alternatingProductMap_tmul,
      LieAlgebra.SpecialLinear.sl_bracket, val_single, eq_sub_of_add_eq hX]
    simp [sub_mul, mul_sub, hij.symm]
  · intro i j hij
    exact LinearMap.mem_range.mpr ⟨_, Subtype.ext (alternating_cycle i j hij 1)⟩

private theorem symmetric_chain [Invertible (Fintype.card (Fin n) : K)]
    (i k j : Fin n) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (c : K) :
    (symmetricProductMap K n (pair i k k j hik hkj c)).val = Matrix.single i j c := by
  simp [pair, coe_symmetricProduct, tracelessAnticommutator_def, hij.symm, hij]

private theorem symmetric_cycle [Invertible (Fintype.card (Fin n) : K)]
    (i k : Fin n) (h : i ≠ k) (c : K) :
    (symmetricProductMap K n (pair i k k i h h.symm c)).val =
      Matrix.single i i c + Matrix.single k k c -
        (2 * Ring.inverse (Fintype.card (Fin n) : K) * c) • 1 := by
  simp [pair, coe_symmetricProduct, tracelessAnticommutator_def]

/-- The traceless symmetric contraction onto trace-zero matrices is surjective for sizes
at least three that are units in the scalar ring. -/
theorem symmetricProductMap_surjective (K : Type*) [CommRing K] (n : ℕ)
    [Invertible (Fintype.card (Fin n) : K)]
    (hn : 3 ≤ n) :
    Function.Surjective (symmetricProductMap K n) := by
  apply (symmetricProductMap K n).toLinearMap.surjective_to_sl_of_matrix_units
  · intro i j hij
    obtain ⟨k, hik, hkj⟩ := exists_third i j hn
    exact LinearMap.mem_range.mpr ⟨_, Subtype.ext (symmetric_chain i k j hik hkj hij 1)⟩
  · intro i j _
    obtain ⟨k, hik, hkj⟩ := exists_third i j hn
    refine LinearMap.mem_range.mpr
      ⟨pair i k k i hik hik.symm 1 - pair j k k j hkj.symm hkj 1, Subtype.ext ?_⟩
    rw [Representation.IntertwiningMap.toLinearMap_apply, map_sub]
    rw [Submodule.coe_sub, symmetric_cycle, symmetric_cycle, val_singleSubSingle]
    abel

end TauCeti.AdjointSquare
