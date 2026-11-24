/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Products
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import Mathlib.Data.Fin.Basic

/-! # Surjectivity of the two adjoint-square contractions

For matrix size at least three, the Lie-bracket contraction onto trace-zero matrices is
surjective over any commutative ring. The traceless symmetric contraction is surjective
over a field in which the size is nonzero. These results give the injectivity of the two
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

open LieAlgebra.SpecialLinear (single val_single)


private def pair (i j k l : Fin n) (h : i ≠ j) (h' : k ≠ l) (c : K) : 𝔰 K ⊗[K] 𝔰 K :=
  single i j h c ⊗ₜ[K] single k l h' 1

private theorem exists_third (i j : Fin n) (hn : 3 ≤ n) : ∃ k, i ≠ k ∧ k ≠ j := by
  obtain ⟨k, hik, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  exact ⟨k, hik.symm, hkj⟩

/-- The matrix-unit spanning lemma reduces surjectivity to finding preimages of two families. -/
private theorem surjective_of_units (f : (𝔰 K ⊗[K] 𝔰 K) →ₗ[K] 𝔰 K)
    (off : ∀ i j : Fin n, i ≠ j → ∀ c : K, ∃ t, (f t).val = Matrix.single i j c)
    (diag : ∀ i j : Fin n, i ≠ j → ∀ c : K, ∃ t,
      (f t).val = Matrix.single i i c - Matrix.single j j c) :
    Function.Surjective f := by
  intro X
  let N := LinearMap.range ((𝔰 K).toSubmodule.subtype.comp f)
  have hx : X.val ∈ N := by
    apply TauCeti.mem_of_trace_eq_zero_of_single_mem (N := N)
    · intro i j hij c
      obtain ⟨t, ht⟩ := off i j hij c
      exact LinearMap.mem_range.mpr ⟨t, by
        simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using ht⟩
    · intro i j c
      by_cases h : i = j
      · subst j
        simpa only [sub_self] using N.zero_mem
      · obtain ⟨t, ht⟩ := diag i j h c
        exact LinearMap.mem_range.mpr ⟨t, by
          simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using ht⟩
    · exact LieAlgebra.SpecialLinear.mem_sl_iff.mp X.property
  obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hx
  refine ⟨t, Subtype.ext ?_⟩
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using ht

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
  apply surjective_of_units (alternatingProductMap K n).toLinearMap
  · intro i j hij c
    obtain ⟨k, hik, hkj⟩ := exists_third i j hn
    exact ⟨_, alternating_chain i k j hik hkj hij c⟩
  · intro i j h c
    exact ⟨_, alternating_cycle i j h c⟩

private theorem symmetric_chain {K : Type*} [Field K] [NeZero (n : K)]
    (i k j : Fin n) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (c : K) :
    (symmetricProductMap K n (pair i k k j hik hkj c)).val = Matrix.single i j c := by
  simp [pair, coe_symmetricProduct, tracelessAnticommutator_def, hij.symm, hij]

private theorem symmetric_cycle {K : Type*} [Field K] [NeZero (n : K)]
    (i k : Fin n) (h : i ≠ k) (c : K) :
    (symmetricProductMap K n (pair i k k i h h.symm c)).val =
      Matrix.single i i c + Matrix.single k k c -
        ((2 / n : K) * c) • 1 := by
  simp [pair, coe_symmetricProduct, tracelessAnticommutator_def]

/-- The traceless symmetric contraction onto trace-zero matrices is surjective for sizes
at least three that are nonzero in the scalar field. -/
theorem symmetricProductMap_surjective (K : Type*) [Field K] (n : ℕ) [NeZero (n : K)]
    (hn : 3 ≤ n) :
    Function.Surjective (symmetricProductMap K n) := by
  apply surjective_of_units (symmetricProductMap K n).toLinearMap
  · intro i j hij c
    obtain ⟨k, hik, hkj⟩ := exists_third i j hn
    exact ⟨_, symmetric_chain i k j hik hkj hij c⟩
  · intro i j _ c
    obtain ⟨k, hik, hkj⟩ := exists_third i j hn
    refine ⟨pair i k k i hik hik.symm c - pair j k k j hkj.symm hkj c, ?_⟩
    rw [Representation.IntertwiningMap.toLinearMap_apply, map_sub]
    rw [Submodule.coe_sub, symmetric_cycle, symmetric_cycle]
    abel

end TauCeti.AdjointSquare
