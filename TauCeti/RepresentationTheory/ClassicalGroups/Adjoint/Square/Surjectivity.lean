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

/-! # Surjectivity of the two adjoint-square contractions

Off-diagonal matrix units factor through the third index. The two remaining
diagonal coordinates use differences of diagonal units, since the trace is zero.
-/

public section
namespace TauCeti.AdjointSquare
open Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K : Type*}
variable [CommRing K]
local notation "𝔰" => LieAlgebra.SpecialLinear.sl (Fin 3)

open LieAlgebra.SpecialLinear (single val_single)


private def pair (i j k l : Fin 3) (h : i ≠ j) (h' : k ≠ l) (c : K) : 𝔰 K ⊗[K] 𝔰 K :=
  single i j h c ⊗ₜ[K] single k l h' 1

private theorem exists_third (i j : Fin 3) : ∃ k, i ≠ k ∧ k ≠ j := by
  decide +revert

/-- The matrix-unit spanning lemma reduces surjectivity to finding preimages of two families. -/
private theorem surjective_of_units (f : (𝔰 K ⊗[K] 𝔰 K) →ₗ[K] 𝔰 K)
    (off : ∀ i j : Fin 3, i ≠ j → ∀ c : K, ∃ t, (f t).val = Matrix.single i j c)
    (diag : ∀ i j : Fin 3, i ≠ j → ∀ c : K, ∃ t,
      (f t).val = Matrix.single i i c - Matrix.single j j c) :
    Function.Surjective f := by
  intro X
  let N := LinearMap.range ((𝔰 K).toSubmodule.subtype.comp f)
  have hx : X.val ∈ N := by
    apply TauCeti.mem_of_trace_eq_zero_of_single_mem (N := N) (fun h => off _ _ h)
    · intro i j c
      by_cases h : i = j
      · subst j
        simpa only [sub_self] using N.zero_mem
      · exact diag i j h c
    · exact LieAlgebra.SpecialLinear.mem_sl_iff.mp X.property
  obtain ⟨t, ht⟩ := hx
  exact ⟨t, Subtype.ext ht⟩

private theorem alternating_chain (i k j : Fin 3) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j)
    (c : K) : (alternatingProductMap K 3 (pair i k k j hik hkj c)).val = Matrix.single i j c := by
  simp [pair, hij.symm]

private theorem alternating_cycle (i j : Fin 3) (h : i ≠ j) (c : K) :
    (alternatingProductMap K 3 (pair i j j i h h.symm c)).val =
      Matrix.single i i c - Matrix.single j j c := by
  simp [pair]

/-- The Lie-bracket contraction onto the trace-zero three-by-three matrices is surjective
over any commutative ring. -/
theorem alternatingProductMap_surjective (K : Type*) [CommRing K] :
    Function.Surjective (alternatingProductMap K 3) := by
  apply surjective_of_units (alternatingProductMap K 3).toLinearMap
  · intro i j hij c
    obtain ⟨k, hik, hkj⟩ := exists_third i j
    exact ⟨_, alternating_chain i k j hik hkj hij c⟩
  · intro i j h c
    exact ⟨_, alternating_cycle i j h c⟩

private theorem symmetric_chain {K : Type*} [Field K] [NeZero (3 : K)]
    (i k j : Fin 3) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (c : K) :
    (symmetricProductMap K 3 (pair i k k j hik hkj c)).val = Matrix.single i j c := by
  simp [pair, coe_symmetricProduct, tracelessAnticommutator_def, hij.symm, hij]

private theorem symmetric_cycle {K : Type*} [Field K] [NeZero (3 : K)]
    (i k : Fin 3) (h : i ≠ k) (c : K) :
    (symmetricProductMap K 3 (pair i k k i h h.symm c)).val =
      Matrix.single i i c + Matrix.single k k c -
        ((2 / 3 : K) * c) • 1 := by
  simp [pair, coe_symmetricProduct, tracelessAnticommutator_def]

/-- The traceless symmetric contraction onto the trace-zero three-by-three matrices is
surjective when three is nonzero in the scalar field. -/
theorem symmetricProductMap_surjective (K : Type*) [Field K] [NeZero (3 : K)] :
    Function.Surjective (symmetricProductMap K 3) := by
  apply surjective_of_units (symmetricProductMap K 3).toLinearMap
  · intro i j hij c
    obtain ⟨k, hik, hkj⟩ := exists_third i j
    exact ⟨_, symmetric_chain i k j hik hkj hij c⟩
  · intro i j _ c
    obtain ⟨k, hik, hkj⟩ := exists_third i j
    refine ⟨pair i k k i hik hik.symm c - pair j k k j hkj.symm hkj c, ?_⟩
    rw [Representation.IntertwiningMap.toLinearMap_apply, map_sub]
    -- The Lie subalgebra inclusion preserves differences of trace-zero matrices.
    change ((symmetricProductMap K 3 (pair i k k i hik hik.symm c)).val -
      (symmetricProductMap K 3 (pair j k k j hkj.symm hkj c)).val) = _
    rw [symmetric_cycle, symmetric_cycle]
    abel

end TauCeti.AdjointSquare
