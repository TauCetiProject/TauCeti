/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.CongruenceLattice
public import TauCeti.RingTheory.Ideal.CoprimeCoset

/-!
# Elements of an ideal congruent to one, in the mixed space

For a nonzero integral ideal `𝔞` and a modulus `𝔪` with finite part `𝔪₀`, consider the elements
of `𝔞` that are congruent to one modulo `𝔪₀`.  **Provided there is at least one**, they form a
coset of `𝔞 * 𝔪₀` — the set is empty unless such an element exists, which is why the theorem below
takes a witness `ξ` rather than a hypothesis on `𝔞` alone.  A witness comes from coprimality of
`𝔞` and `𝔪₀`, via `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem`.

This file records what the images of those elements look like in the mixed space: a single
translate of `congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)`.

The lattice being translated depends only on `𝔪` and `𝔞`, not on the element chosen to name the
translate, so those images are the points of one translate of a fixed lattice.

Nothing here asks that `𝔞` represent a given ray class, nor divides out the congruence roots of
unity acting on the ray fundamental domain; a ray-class ideal count imposes both itself.

## Main results

* `TauCeti.GlobalNumberFields.image_setOf_mem_and_sub_one_mem_eq_vadd_congruenceLattice`:
  those images are a translate of the congruence lattice.
-/

public section

open IsDedekindDomain NumberField NumberField.mixedEmbedding

open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The elements congruent to one map onto a coset of the congruence lattice.**  For a nonzero
integral ideal `𝔞` and an element `ξ` of `𝔞` congruent to one modulo `𝔪₀`, the elements of `𝔞`
congruent to one modulo `𝔪₀` map onto the translate of
`congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)` by the image of `ξ`.

Such a `ξ` is what `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem` extracts from
coprimality of `𝔞` and `𝔪₀`, and the lattice on the right does not involve `ξ`: two such
choices give translates of the same lattice. -/
theorem image_setOf_mem_and_sub_one_mem_eq_vadd_congruenceLattice (𝔪 : Modulus K)
    (𝔞 : (Ideal (𝓞 K))⁰) {ξ : 𝓞 K} (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K))) (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) :
    (fun y : 𝓞 K ↦ mixedEmbedding K (y : K)) ''
        {α : 𝓞 K | α ∈ (𝔞 : Ideal (𝓞 K)) ∧ α - 1 ∈ 𝔪.finitePart} = mixedEmbedding K (ξ : K) +ᵥ
          (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞) : Set (mixedSpace K)) := by
  rw [Ideal.setOf_mem_and_sub_one_mem_eq_vadd_mul hξ𝔞 hξ𝔪, coe_congruenceLattice_mk0_eq_image]
  -- `rw` cannot finish here: the map in the statement is the coercion of the composite ring hom
  -- only up to unfolding, and `rw` matches syntactically
  exact Set.image_vadd_distrib ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)) ξ _

end TauCeti.GlobalNumberFields
