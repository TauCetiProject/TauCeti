/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PiTensorProduct.FiberwiseMul

/-!
# Tensor powers of an algebra with surjective structure map

If `algebraMap R A` is surjective, as for a quotient ring `R ⧸ I` or for `ZMod n` over `ℤ`, then
every element of `A` is the image of a scalar. Consequently all embeddings of `A` as a tensor
factor of `⨂[R] _ : ι, A` agree, and for a nonempty finite index type the tensor power is again
`A`, by multiplication of the tensor factors. This is the indexed analogue of
`LinearMap.mul'_bijective_of_surjective`. For `ZMod n` over `ℤ` it is the coefficient calculation
used when tensor induction is applied to the trivial `ZMod n`-representation.

## Main definitions

* `PiTensorProduct.constantAlgEquivOfSurjective`: multiplication of the tensor factors,
  `PiTensorProduct.mulAlgHom`, as an algebra equivalence from a nonempty finite tensor power of
  `A` to `A`.

## Main results

* `PiTensorProduct.singleAlgHom_eq_of_surjective`: the factor embeddings all agree.
* `PiTensorProduct.constantAlgEquivOfSurjective_tprod`: the equivalence multiplies the factors of
  a pure tensor.
* `PiTensorProduct.constantAlgEquivOfSurjective_symm_apply`: its inverse is the embedding of `A` as
  any one of the tensor factors.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R A ι : Type*} [CommSemiring R]

/-- If `algebraMap R A` is surjective, then the embeddings of `A` as the different tensor factors
of `⨂[R] _ : ι, A` all agree, since every element of `A` is the image of a scalar. -/
theorem singleAlgHom_eq_of_surjective [Semiring A] [Algebra R A] [DecidableEq ι]
    (h : Function.Surjective (algebraMap R A)) (i j : ι) :
    singleAlgHom (R := R) (A := fun _ : ι ↦ A) i = singleAlgHom (A := fun _ : ι ↦ A) j :=
  AlgHom.ext fun a ↦ by
    obtain ⟨r, rfl⟩ := h a
    simp only [AlgHom.commutes]

variable [CommSemiring A] [Algebra R A] [Fintype ι] [Nonempty ι]

/-- If `algebraMap R A` is surjective, then a nonempty finite tensor power of `A` over `R` is
canonically `A`, by multiplying the tensor factors. -/
noncomputable def constantAlgEquivOfSurjective (h : Function.Surjective (algebraMap R A)) :
    (⨂[R] _ : ι, A) ≃ₐ[R] A := by
  classical
  exact AlgEquiv.ofAlgHom mulAlgHom
    (singleAlgHom (A := fun _ : ι ↦ A) (Classical.arbitrary ι))
    (AlgHom.ext <| mulAlgHom_singleAlgHom _)
    (algHom_ext fun i ↦ AlgHom.ext fun a ↦ by
      simp only [AlgHom.comp_apply, mulAlgHom_singleAlgHom, singleAlgHom_eq_of_surjective h _ i,
        AlgHom.id_apply])

/-- The tensor-power equivalence multiplies the factors of a pure tensor. -/
@[simp]
theorem constantAlgEquivOfSurjective_tprod (h : Function.Surjective (algebraMap R A))
    (x : ι → A) : constantAlgEquivOfSurjective h (tprod R x) = ∏ i, x i := by
  simp [constantAlgEquivOfSurjective]

/-- The inverse of the tensor-power equivalence embeds `A` as any one of the tensor factors. -/
theorem constantAlgEquivOfSurjective_symm_apply [DecidableEq ι]
    (h : Function.Surjective (algebraMap R A)) (i : ι) (a : A) :
    (constantAlgEquivOfSurjective h).symm a = singleAlgHom i a := by
  rw [AlgEquiv.symm_apply_eq]
  exact (mulAlgHom_singleAlgHom i a).symm

end PiTensorProduct
