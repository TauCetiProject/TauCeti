/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic

/-!
# The Weyl group of `GL n` acting on weights

The permutation matrices normalize the diagonal torus and conjugation by them relabels its
entries, so they permute the joint eigenspaces of the torus: a permutation `σ` carries the weight
space of `l : Fin n → ℤ` isomorphically onto the weight space of `l ∘ σ⁻¹`
(`TauCeti.weightSpace_map_permutationGL`).  This is the `GL n` shadow of the Weyl group acting on
the weight lattice, and its first consequence is that weight multiplicities are constant on
`Sₙ`-orbits (`TauCeti.finrank_weightSpace_comp_perm`).

Every `Sₙ`-orbit on `Fin n → ℤ` contains exactly one weakly decreasing sequence, that is, exactly
one `TauCeti.DominantWeight` (`TauCeti.existsUnique_dominantWeight`): sorting supplies one and
`Tuple.unique_antitone` makes it unique.  So the dominant weights are a set of orbit
representatives, and the weights of a representation, with their multiplicities, are determined by
the dominant ones (`TauCeti.finrank_weightSpace_dominantWeightOf`).  That is what makes
`TauCeti.DominantWeight` the index type the highest-weight theory of `GL n` runs on.

## Implementation notes

The relabelling convention is fixed by `TauCeti.permutationGL_mul_diagGL_mul_inv`: conjugating
`diagGL t` by `permutationGL σ` gives `diagGL (t ∘ σ⁻¹)`.  Reading that identity backwards moves
`permutationGL σ` past a diagonal matrix and produces the weight `l ∘ σ⁻¹` on the image, so the
`σ⁻¹` in `TauCeti.weightSpace_map_permutationGL` is not a choice but the convention of the
conjugation lemma.  The orbit statements below are stated with a bare `σ` where no image is
involved, since `σ ↦ σ⁻¹` is a bijection of `Sₙ`.

The sorting permutation is `Tuple.sort` applied to the weight read in the order dual, because
`Tuple.sort` produces monotone rearrangements while a dominant weight is antitone.  Nothing else
about it is used: existence comes from `Tuple.monotone_sort` and uniqueness from
`Tuple.unique_antitone`, so the same orbit representative would result from any other sorting
procedure.

## Main definitions

* `TauCeti.dominantSort`: a permutation sorting a weight into weakly decreasing order.
* `TauCeti.dominantWeightOf`: the dominant weight in the `Sₙ`-orbit of a weight.

## Main results

* `TauCeti.existsUnique_dominantWeight`: **each `Sₙ`-orbit of weights contains exactly one
  dominant weight.**
* `TauCeti.weightSpace_map_permutationGL`: **a permutation matrix carries the weight space of `l`
  onto the weight space of `l ∘ σ⁻¹`.**
* `TauCeti.finrank_weightSpace_comp_perm`: weight multiplicities are constant on `Sₙ`-orbits.
* `TauCeti.weightSpace_eq_bot_comp_perm_iff`: so is being a weight at all.
* `TauCeti.finrank_weightSpace_dominantWeightOf` and
  `TauCeti.weightSpace_eq_bot_dominantWeightOf_iff`: the dominant representative carries the same
  multiplicity, so the weights of a representation are determined by the dominant ones.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15: the weights
  of `GL n` and the Weyl group `Sₙ` permuting them.
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "The maximal torus and weight spaces" and "Dominant weights", whose "`GLₙ` Weyl group
  `Sₙ` acting on `ℤⁿ`" is what this file supplies.
-/

public section

open Matrix Module

universe u v

namespace TauCeti

variable {n : ℕ}

/-! ### Sorting a weight into the dominant chamber -/

/-- A permutation rearranging a weight into weakly decreasing order.  It is `Tuple.sort` of the
weight read in the order dual, since `Tuple.sort` produces monotone rearrangements. -/
noncomputable def dominantSort (l : Fin n → ℤ) : Equiv.Perm (Fin n) :=
  Tuple.sort fun i => OrderDual.toDual (l i)

/-- Sorting makes a weight weakly decreasing. -/
theorem antitone_comp_dominantSort (l : Fin n → ℤ) : Antitone (l ∘ ⇑(dominantSort l)) :=
  fun _ _ hij => Tuple.monotone_sort (fun i => OrderDual.toDual (l i)) hij

/-- **The dominant weight in the `Sₙ`-orbit of a weight**: its weakly decreasing rearrangement. -/
noncomputable def dominantWeightOf (l : Fin n → ℤ) : DominantWeight n :=
  ⟨l ∘ ⇑(dominantSort l), antitone_comp_dominantSort l⟩

@[simp]
theorem coe_dominantWeightOf (l : Fin n → ℤ) :
    (dominantWeightOf l : Fin n → ℤ) = l ∘ ⇑(dominantSort l) :=
  (rfl)

/-- Any weakly decreasing rearrangement of a weight is its dominant representative. -/
theorem coe_dominantWeightOf_eq_of_antitone {l : Fin n → ℤ} {σ : Equiv.Perm (Fin n)}
    (h : Antitone (l ∘ ⇑σ)) : (dominantWeightOf l : Fin n → ℤ) = l ∘ ⇑σ :=
  Tuple.unique_antitone (antitone_comp_dominantSort l) h

/-- A dominant weight is its own dominant representative. -/
@[simp]
theorem dominantWeightOf_coe (d : DominantWeight n) : dominantWeightOf (d : Fin n → ℤ) = d :=
  Subtype.ext <| coe_dominantWeightOf_eq_of_antitone (l := (d : Fin n → ℤ)) (σ := 1)
    fun _ _ hij => d.antitone hij

/-- Rearranging a weight does not change its dominant representative. -/
@[simp]
theorem dominantWeightOf_comp (l : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    dominantWeightOf (l ∘ ⇑σ) = dominantWeightOf l :=
  Subtype.ext <| (coe_dominantWeightOf_eq_of_antitone (l := l)
    (σ := σ * dominantSort (l ∘ ⇑σ)) fun _ _ hij => antitone_comp_dominantSort (l ∘ ⇑σ) hij).symm

/-- **Each `Sₙ`-orbit of weights contains exactly one dominant weight**, so the dominant weights
are a set of representatives for the action of the Weyl group on the weight lattice. -/
theorem existsUnique_dominantWeight (l : Fin n → ℤ) :
    ∃! d : DominantWeight n, ∃ σ : Equiv.Perm (Fin n), (d : Fin n → ℤ) = l ∘ ⇑σ := by
  refine ⟨dominantWeightOf l, ⟨dominantSort l, rfl⟩, ?_⟩
  rintro ⟨d, hd⟩ ⟨σ, rfl⟩
  exact (dominantWeightOf_coe ⟨_, hd⟩).symm.trans (dominantWeightOf_comp l σ)

/-! ### Permuting the weight characters -/

section WeightChar

variable {k : Type u} [CommRing k]

/-- Permuting a weight is permuting the point of the torus the other way. -/
theorem weightChar_comp_perm (l : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (t : Fin n → kˣ) :
    weightChar k (l ∘ ⇑σ⁻¹) t = weightChar k l fun i => t (σ i) := by
  rw [weightChar_apply, weightChar_apply, torusCharacter_def, torusCharacter_def,
    ← Equiv.prod_comp σ fun i => t i ^ (l ∘ ⇑σ⁻¹) i]
  exact Finset.prod_congr rfl fun j _ => by simp

end WeightChar

/-! ### The Weyl group acting on the weight spaces -/

section Action

variable {k : Type u} [CommRing k] {W : Type v} [AddCommGroup W] [Module k W]
  (ρ : Representation k (GL (Fin n) k) W)

/-- Moving a permutation matrix past a diagonal one relabels the diagonal entries. -/
theorem diagGL_mul_permutationGL (σ : Equiv.Perm (Fin n)) (t : Fin n → kˣ) :
    diagGL t * permutationGL (k := k) σ =
      permutationGL (k := k) σ * diagGL fun i => t (σ i) := by
  have h : permutationGL (k := k) σ * (diagGL fun i => t (σ i)) * (permutationGL (k := k) σ)⁻¹
      = diagGL t := by
    rw [permutationGL_mul_diagGL_mul_inv]
    congr 1
    funext i
    simp
  rw [← h, inv_mul_cancel_right]

/-- Composing the actions of two permutation matrices. -/
private theorem permutationGL_apply_permutationGL_apply (σ τ : Equiv.Perm (Fin n)) (w : W) :
    ρ (permutationGL (k := k) σ) (ρ (permutationGL (k := k) τ) w) =
      ρ (permutationGL (k := k) (σ * τ)) w := by
  rw [map_mul, map_mul]
  exact (rfl)

/-- A permutation matrix acts invertibly. -/
private theorem permutationGL_inv_apply_permutationGL_apply (σ : Equiv.Perm (Fin n)) (w : W) :
    ρ (permutationGL (k := k) σ⁻¹) (ρ (permutationGL (k := k) σ) w) = w := by
  rw [permutationGL_apply_permutationGL_apply, inv_mul_cancel, map_one, map_one]
  exact (rfl)

/-- The action of a permutation matrix is injective, being invertible. -/
private theorem injective_permutationGL_apply (σ : Equiv.Perm (Fin n)) :
    Function.Injective (ρ (permutationGL (k := k) σ)) :=
  Function.LeftInverse.injective (permutationGL_inv_apply_permutationGL_apply ρ σ)

/-- Reindexing a weight by a permutation and back. -/
private theorem comp_perm_inv_comp_perm (l : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    (l ∘ ⇑σ⁻¹) ∘ ⇑σ = l := by
  funext i
  simp

/-- A permutation matrix carries weight vectors of `l` to weight vectors of `l ∘ σ⁻¹`. -/
private theorem permutationGL_apply_mem_weightSpace {σ : Equiv.Perm (Fin n)} {l : Fin n → ℤ}
    {w : W} (hw : w ∈ weightSpace ρ l) :
    ρ (permutationGL (k := k) σ) w ∈ weightSpace ρ (l ∘ ⇑σ⁻¹) := by
  rw [mem_weightSpace_iff]
  intro t
  rw [← Module.End.mul_apply, ← map_mul, diagGL_mul_permutationGL, map_mul, Module.End.mul_apply,
    apply_of_mem_weightSpace hw, map_smul, weightChar_comp_perm]

/-- **A permutation matrix carries the weight vectors of `l` exactly onto those of `l ∘ σ⁻¹`.** -/
theorem mem_weightSpace_comp_perm_iff (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) (w : W) :
    ρ (permutationGL (k := k) σ) w ∈ weightSpace ρ (l ∘ ⇑σ⁻¹) ↔ w ∈ weightSpace ρ l := by
  refine ⟨fun h => ?_, permutationGL_apply_mem_weightSpace ρ⟩
  have h' := permutationGL_apply_mem_weightSpace (σ := σ⁻¹) ρ h
  rwa [permutationGL_inv_apply_permutationGL_apply, inv_inv, comp_perm_inv_comp_perm] at h'

/-- **The permutation matrix of `σ` carries the weight space of `l` onto the weight space of
`l ∘ σ⁻¹`.** -/
theorem weightSpace_map_permutationGL (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) :
    (weightSpace ρ l).map (ρ (permutationGL (k := k) σ)) = weightSpace ρ (l ∘ ⇑σ⁻¹) := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact permutationGL_apply_mem_weightSpace ρ hw
  · refine ⟨ρ (permutationGL (k := k) σ⁻¹) v, ?_, ?_⟩
    · have h := permutationGL_apply_mem_weightSpace (σ := σ⁻¹) ρ hv
      rwa [inv_inv, comp_perm_inv_comp_perm] at h
    · rw [permutationGL_apply_permutationGL_apply, mul_inv_cancel, map_one, map_one]
      exact (rfl)

/-- **The linear equivalence between the weight spaces of `l` and of `l ∘ σ`** cut out by the
permutation matrix of `σ⁻¹`. -/
noncomputable def weightSpaceEquivCompPerm (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) :
    weightSpace ρ l ≃ₗ[k] weightSpace ρ (l ∘ ⇑σ) :=
  (Submodule.equivMapOfInjective _ (injective_permutationGL_apply ρ σ⁻¹) (weightSpace ρ l)).trans
    (LinearEquiv.ofEq _ _ (by rw [weightSpace_map_permutationGL, inv_inv]))

/-- **Weight multiplicities are constant on `Sₙ`-orbits.** -/
theorem finrank_weightSpace_comp_perm (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) :
    finrank k (weightSpace ρ (l ∘ ⇑σ)) = finrank k (weightSpace ρ l) :=
  (weightSpaceEquivCompPerm ρ σ l).symm.finrank_eq

/-- **Being a weight at all is constant on `Sₙ`-orbits.** -/
theorem weightSpace_eq_bot_comp_perm_iff (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) :
    weightSpace ρ (l ∘ ⇑σ) = ⊥ ↔ weightSpace ρ l = ⊥ := by
  have hmap : (weightSpace ρ l).map (ρ (permutationGL (k := k) σ⁻¹)) = weightSpace ρ (l ∘ ⇑σ) := by
    rw [weightSpace_map_permutationGL, inv_inv]
  rw [← hmap, Submodule.eq_bot_iff, Submodule.eq_bot_iff]
  refine ⟨fun h w hw => injective_permutationGL_apply ρ σ⁻¹ ?_, ?_⟩
  · rw [map_zero]
    exact h _ ⟨w, hw, rfl⟩
  · rintro h _ ⟨w, hw, rfl⟩
    rw [h w hw, map_zero]

/-- The dominant representative of a weight carries the same multiplicity. -/
theorem finrank_weightSpace_dominantWeightOf (l : Fin n → ℤ) :
    finrank k (weightSpace ρ (dominantWeightOf l : Fin n → ℤ)) = finrank k (weightSpace ρ l) := by
  rw [coe_dominantWeightOf, finrank_weightSpace_comp_perm]

/-- A weight occurs exactly when its dominant representative does, so the weights of a
representation are determined by the dominant ones. -/
theorem weightSpace_eq_bot_dominantWeightOf_iff (l : Fin n → ℤ) :
    weightSpace ρ (dominantWeightOf l : Fin n → ℤ) = ⊥ ↔ weightSpace ρ l = ⊥ := by
  rw [coe_dominantWeightOf, weightSpace_eq_bot_comp_perm_iff]

end Action

end TauCeti
