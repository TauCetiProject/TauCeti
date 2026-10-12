/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
one `TauCeti.DominantWeight` (`TauCeti.existsUnique_dominantWeight`).  So the dominant weights are
a set of orbit representatives, and whether a weight occurs, and with what multiplicity, can be
read off its dominant representative (`TauCeti.finrank_weightSpace_dominantWeightOf`,
`TauCeti.weightSpace_eq_bot_dominantWeightOf_iff`).  The highest-weight classification that
indexes the irreducibles of `GL n` by dominant weights is not proved here.

## Implementation notes

The `σ⁻¹` in `TauCeti.weightSpace_map_permutationGL` is the relabelling convention of
`TauCeti.permutationGL_mul_diagGL_mul_inv`, by which conjugating `diagGL t` by `permutationGL σ`
gives `diagGL (t ∘ σ⁻¹)`.  The orbit statements below are stated with a bare `σ` where no image is
involved, since `σ ↦ σ⁻¹` is a bijection of `Sₙ`.

## Main definitions

* `TauCeti.weightSpaceEquivCompPerm`: the linear equivalence between the weight spaces of `l` and
  of `l ∘ σ` cut out by a permutation matrix.

## Main results

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
-/

public section

open Matrix Module

universe u v

namespace TauCeti

variable {n : ℕ}

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

/-- The equivalence between the weight spaces of `l` and of `l ∘ σ` is the action of the
permutation matrix of `σ⁻¹`. -/
@[simp]
theorem coe_weightSpaceEquivCompPerm_apply (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ)
    (w : weightSpace ρ l) :
    (weightSpaceEquivCompPerm ρ σ l w : W) = ρ (permutationGL (k := k) σ⁻¹) (w : W) := by
  rw [weightSpaceEquivCompPerm, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.coe_equivMapOfInjective_apply]

/-- Its inverse is the action of the permutation matrix of `σ`. -/
@[simp]
theorem coe_weightSpaceEquivCompPerm_symm_apply (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ)
    (w : weightSpace ρ (l ∘ ⇑σ)) :
    (((weightSpaceEquivCompPerm ρ σ l).symm w : weightSpace ρ l) : W) =
      ρ (permutationGL (k := k) σ) (w : W) := by
  refine injective_permutationGL_apply ρ σ⁻¹ ?_
  rw [← coe_weightSpaceEquivCompPerm_apply, LinearEquiv.apply_symm_apply,
    permutationGL_inv_apply_permutationGL_apply]

/-- **Weight multiplicities are constant on `Sₙ`-orbits.** -/
@[simp]
theorem finrank_weightSpace_comp_perm (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) :
    finrank k (weightSpace ρ (l ∘ ⇑σ)) = finrank k (weightSpace ρ l) :=
  (weightSpaceEquivCompPerm ρ σ l).symm.finrank_eq

/-- **Being a weight at all is constant on `Sₙ`-orbits.** -/
@[simp]
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
@[simp]
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
