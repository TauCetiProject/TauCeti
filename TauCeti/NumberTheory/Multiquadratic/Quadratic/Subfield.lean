/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.Quadratic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Quadratic subfields of a multiquadratic field from subset products

For square roots `root i` of radicands `d i ∈ K` over a field `K`, the subset-product
root `∏_{i ∈ S} root i` squares into `K`: its square is the subset product `∏_{i ∈ S} d i` of the
radicands. Each subset therefore names a simple subfield `K(∏_{i ∈ S} root i)` of the
multiquadratic field `M = K(rootᵢ : i)`. Under square-class independence the nonempty ones are
genuinely quadratic (`TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare`,
which asks nothing of the characteristic), and when `2 ≠ 0` they are pairwise distinct: the
assignment `S ↦ K(∏_{i ∈ S} root i)` is injective on all finite subsets of the index type, the
empty subset going to `K`. This gives a concrete, arithmetic family of
quadratic subfields that the genus-field constructions consume, complementing the abstract
subfield/subspace dictionary of `TauCeti.NumberTheory.Multiquadratic.Subfield.Lattice` and
`TauCeti.NumberTheory.Multiquadratic.Subfield.Degree` (where a quadratic subfield is characterised
as a hyperplane of `𝔽₂ⁿ`).

The engine for distinctness is the standalone same-square-class criterion for simple quadratic
extensions, `TauCeti.IntermediateField.isSquare_mul_of_adjoin_simple_eq`: two square roots generate
the same simple extension only when their radicands lie in the same square class.

## Main results

* `TauCeti.Multiquadratic.prod_root_sq`: `(∏_{i ∈ S} root i)² = ∏_{i ∈ S} d i`.
* `TauCeti.Multiquadratic.prod_root_mem_adjoin`: the subset-product root lies in `M`.
* `TauCeti.Multiquadratic.adjoin_prod_root_injective`: distinct subsets give distinct
  subset-product subfields.

## Provenance

The one-step quadratic normal form this rests on
(`TauCeti.IntermediateField.mem_sup_adjoin_sq`,
`IntermediateField.finrank_sup_adjoin_simple_eq_mul_two`) is migrated, with the rest of the
basic multiquadratic theory, from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture. The subset-product
description of the quadratic subfields is assembled here from that normal form.
-/

public section

open IntermediateField TauCeti.IntermediateField
open scoped symmDiff

namespace TauCeti.Multiquadratic

section CommSemiring

variable {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- **The square of a subset-product root.** The product `∏_{i ∈ S} root i` of the chosen roots
over a finite subset `S` squares to the subset product `∏_{i ∈ S} d i` of the radicands. -/
theorem prod_root_sq (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (S : Finset ι) :
    (∏ i ∈ S, root i) ^ 2 = algebraMap K L (∏ i ∈ S, d i) := by
  simp only [← Finset.prod_pow, hroot, map_prod]

end CommSemiring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- **A subset-product root lies in the multiquadratic field.** Each `∏_{i ∈ S} root i` is a
product of generators of `M = K(rootᵢ : i)`, hence a member of `M`. -/
theorem prod_root_mem_adjoin (S : Finset ι) :
    (∏ i ∈ S, root i) ∈ IntermediateField.adjoin K (Set.range root) :=
  prod_mem fun i _ => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩

/-- **Distinct subsets give distinct subset-product subfields.** Under square-class independence
the map `S ↦ K(∏_{i ∈ S} root i)` from the finite subsets of the index type to the intermediate
fields of `L / K` is injective; the empty subset goes to `K` itself. -/
theorem adjoin_prod_root_injective [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Function.Injective fun S : Finset ι => IntermediateField.adjoin K {∏ i ∈ S, root i} := by
  classical
  have key {S T : Finset ι} (hS : S.Nonempty) (hST : IntermediateField.adjoin K
      {∏ i ∈ S, root i} = IntermediateField.adjoin K {∏ i ∈ T, root i}) : S = T := by
    -- The subset-product root of `S` generates a quadratic field, so it lies outside `K`.
    have hxb : (∏ i ∈ S, root i) ∉ (⊥ : IntermediateField K L) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.not.mp <| by
        rw [finrank_adjoin_simple_eq_two_of_not_isSquare (prod_root_sq hroot S) (hindep S hS)]
        omega
    -- Sharing a quadratic field puts the two subset products in one square class.
    have hsq : IsSquare ((∏ i ∈ S, d i) * ∏ i ∈ T, d i) :=
      isSquare_mul_of_adjoin_simple_eq (prod_root_sq hroot S) (prod_root_sq hroot T) hxb hST
    -- That product is the product over `S ∆ T` times the square of the product over `S ∩ T`,
    -- which is nonzero since every radicand is.
    have hfact : (∏ i ∈ S, d i) * ∏ i ∈ T, d i
        = (∏ i ∈ S ∆ T, d i) * (∏ i ∈ S ∩ T, d i) ^ 2 := by
      rw [symmDiff_eq_sup_sdiff_inf, Finset.sup_eq_union, Finset.inf_eq_inter,
        ← Finset.prod_union_inter, ← Finset.prod_sdiff Finset.inter_subset_union]
      ring
    have hne : (∏ i ∈ S ∩ T, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ h =>
      hindep {i} (Finset.singleton_nonempty i) (by simp [h])
    -- So the product over `S ∆ T` is a square, which forces `S ∆ T` to be empty.
    rw [← symmDiff_eq_bot, Finset.bot_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    refine fun hE => hindep _ hE ?_
    have := hsq.div (IsSquare.sq (∏ i ∈ S ∩ T, d i))
    rwa [hfact, mul_div_cancel_right₀ _ (pow_ne_zero 2 hne)] at this
  intro S T hST
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rcases T.eq_empty_or_nonempty with rfl | hT
    · rfl
    · exact (key hT hST.symm).symm
  · exact key hS hST

end TauCeti.Multiquadratic
