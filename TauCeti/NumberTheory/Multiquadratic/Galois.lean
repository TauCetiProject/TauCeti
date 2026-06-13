/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Ring.Commute
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.GroupTheory.Exponent

/-!
# The automorphism group of a multiquadratic field is elementary abelian of exponent two

For square roots `root i` of radicands `d i ∈ K`, every `K`-automorphism of the multiquadratic
field `K(rootᵢ : i)` sends each generator to another element with the same square. Hence applying
the automorphism twice fixes each generator, so it squares to the identity. Therefore the
automorphism group has exponent two and is abelian.

These are the "exponent-two and abelian" facts of the multiquadratic roadmap; the explicit
identification of the group with `(ℤ/2)ⁿ` is a separate, later step.

## Main results

* `TauCeti.Multiquadratic.aut_mul_self_eq_one`: every `σ : M ≃ₐ[K] M` satisfies `σ * σ = 1`.
* `TauCeti.Multiquadratic.aut_commute`: the automorphism group is commutative.

## Provenance

Generalised from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where these
facts were established for one concrete CM field.
-/

open IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- Every `K`-automorphism of the multiquadratic field `K(rootᵢ : i)` is an involution: fixing
`K` forces the image of each generator to have the same square as the generator, so applying the
automorphism twice fixes the generators. -/
@[simp]
theorem aut_mul_self_eq_one (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : IntermediateField.adjoin K (Set.range root) ≃ₐ[K]
      IntermediateField.adjoin K (Set.range root)) :
    σ * σ = 1 := by
  refine AlgEquiv.coe_algHom_injective ?_
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := K)
    (S := IntermediateField.adjoin K (Set.range root)) (s := Set.range root) rfl ?_
  rintro x ⟨i, rfl⟩
  have hmem : root i ∈ IntermediateField.adjoin K (Set.range root) := subset_adjoin _ _ ⟨i, rfl⟩
  set y : IntermediateField.adjoin K (Set.range root) := ⟨root i, hmem⟩ with hy
  have hsq : y ^ 2 = algebraMap K _ (d i) := by
    apply Subtype.ext
    have hcoe : ((y : L)) ^ 2 = algebraMap K L (d i) := by rw [hy]; exact hroot i
    simpa using hcoe
  have h1 : (σ y) ^ 2 = y ^ 2 := by rw [← map_pow, hsq, AlgEquiv.commutes, ← hsq]
  -- `σ` sends the generator to `± y`, so applying it twice returns `y`.
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h <;>
    simp [AlgEquiv.mul_apply, h, map_neg]

/-- The automorphism group of a multiquadratic field is commutative: every element has order
dividing two, so any two commute. -/
theorem aut_commute (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (a b : IntermediateField.adjoin K (Set.range root) ≃ₐ[K]
      IntermediateField.adjoin K (Set.range root)) :
    Commute a b :=
  Commute.of_orderOf_dvd_two
    (fun σ => orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact aut_mul_self_eq_one hroot σ)) a b

end TauCeti.Multiquadratic
